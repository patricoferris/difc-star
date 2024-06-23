module Difc_fstar

module Map = FStar.OrdMap
module Set = FStar.OrdSet
module List = FStar.List.Tot

(* A verified DIFC algorithm for user-defined principals. 
   
   This FStar program provides a means of extracting a DIFC
   checker that is verified. A user may define their own set 
   of principals providing they meet certain properties. *)

(* A label is an ordered map from principals to sets of principals.
   A principal can be any decidably equal type. 

   We also restrict labels to not being empty. *)

type label a f = m:(Map.ordmap a (Set.ordset a f) f) { ~(Map.equal m (Map.empty #a #(Set.ordset a f))) }

let equal (#p:eqtype) (#f:Map.cmp p) (m1 : label p f) (m2 : label p f) =
  Map.equal m1 m2

val lemma_map_update_empty :
  #k:eqtype -> 
  #v:Type ->
  #f:Map.cmp k ->
  key:k ->
  value:v ->
  Lemma 
  (ensures ~(Map.equal (Map.update #k #v #f key value (Map.empty #k #v #f)) (Map.empty #k #v #f)))
let lemma_map_update_empty #k #v #f key value =
  let t = Map.update #k #v #f key value (Map.empty #k #v #f) in
  Map.size_remove #k #v #f key t;
  assert (Map.size t <> 0);
  assert (Map.size (Map.empty #k #v #f) == 0)

(* A constructor for labels that also ensures they are non-empty *)
let v (#p:eqtype) (#f:Map.cmp p) (o : p) (v : Set.ordset p f) : label p f =
  lemma_map_update_empty #p #(Set.ordset p f) #f o v;
  Map.update o v (Map.empty)

(* The owners of a label is the domain of the ordered map *)
let owners #p #f (m : label p f) : s:(Set.ordset p f) { ~(Set.equal s (Set.empty #p #f)) } = Map.dom m

let readers_with_empty (#p:eqtype) #f (k : p) (l : label p f) : Set.ordset p f =
  match Map.select k l with
  | None -> Set.empty
  | Some v -> v 

(* The effective readers of a label is the set of all principals
   that the owners of the label agree to release the data to. *)
let effective_readers #p #f (m : label p f) : Set.ordset p f =
  let g (acc : Set.ordset p f) (k : p) =
    match Map.select k m with
	| None -> acc (* Actually not possible, should work into the proof *)
	| Some readers -> Set.intersect acc readers
  in
  (* Labels have at least one owner, this is an easier trick 
     to avoid having to use option types. *)
  Map.choose_m m;
  let _choosen_owner, choosen_readers = match Map.choose m with Some m -> m in
  Set.fold #p #(Set.ordset p f) g choosen_readers (owners m)

let subset_for_all #e #f (s1 : Set.ordset e f) (s2 : Set.ordset e f) :
  Lemma (requires Set.subset s1 s2)
        (ensures forall o. Set.mem o s1 ==> Set.mem o s2)
  = ()

val for_all: (#p:eqtype) -> (#f:Set.cmp p) -> (p -> Tot bool) -> Set.ordset p f -> Tot bool
let for_all f s = List.Tot.for_all f (Set.as_list s)

let is_a_restriction #p #f (l1 : label p f) (l2 : label p f) : prop =
  let pred (principal : p) : Tot bool =
    Set.subset (readers_with_empty principal l2) (readers_with_empty principal l1)
  in
  Set.subset (owners l1) (owners l2) /\ 
  for_all pred (owners l1)

let readers_agree (#p:eqtype) #f (o : p) (l1 : label p f) (l2 : label p f) =
 Set.subset (readers_with_empty o l1) (readers_with_empty o l2)

let for_all_mem
  (#p:eqtype)
  (#c:Set.cmp p)
  (f: (p -> Tot bool))
  (l: Set.ordset p c)
: Lemma
  (for_all f l <==> (forall x . Set.mem x l ==> f x))
= List.Tot.for_all_mem f (Set.as_list l)

(* The following two lemmas about [is_a_restriction] ensure it matches 
   the original definition by Myers et al. *)
let lemma_restriction_means_owner_subset #p #f (l1 : label p f) (l2 : label p f) :
 Lemma (requires is_a_restriction l1 l2)
       (ensures Set.subset (owners l1) (owners l2)) =
	   ()

val lemma_restriction_means_all_readers_agree :
  #p:eqtype ->
  #f:Map.cmp p ->
  l1:label p f ->
  l2:label p f ->
  Lemma (requires is_a_restriction l1 l2)
        (ensures forall o. Set.mem o (owners l1) ==> readers_agree o l2 l1)
let lemma_restriction_means_all_readers_agree #p #f l1 l2 =
  let pred (principal : p) : Tot bool =
    Set.subset (readers_with_empty principal l2) (readers_with_empty principal l1)
  in
  for_all_mem pred (owners l1)

let add (#p:eqtype) (#f:Map.cmp p) (o : p) (v : Set.ordset p f) (l : label p f) : label p f =
  Map.update o v l

let join (#p:eqtype) (#f:Map.cmp p) (l1 : label p f) (l2 : label p f) =
  let owners_l1 = owners l1 in
  let owners_l2 = owners l2 in
  let update_from_label 
    (o : p) 
	(from_label : label p f { Map.contains o from_label }) 
	(other_label : label p f) 
	(m : label p f) : (y : label p f {Map.contains o y}) =
     match Map.select o from_label, Map.select o other_label with
	  | Some rs, None -> add o rs m
	  | Some r1, Some r2 -> add o (Set.intersect r1 r2) m
  in
  let rec fold 
    (from_label : label p f)
	(os : list p { os <> [] /\ List.subset os (Set.as_list (owners from_label)) })
	(other_label : label p f)
	(macc : label p f) : (res : label p f) = match os with
    | [ o ] -> 
	  let v = update_from_label o from_label other_label macc in
	  assert (List.hd os = o);
	  assert (Map.contains o v);
	  v
	| o :: rest -> 
      let v = update_from_label o from_label other_label macc in
	  assert (List.hd os = o);
	  assert (Map.contains o v);
	  fold from_label rest other_label v
  in
  Map.choose_m l1;
  let choosen_owner, choosen_readers = match Map.choose l1 with Some m -> m in
  let start = v choosen_owner choosen_readers in
  let m1 = fold l1 (Set.as_list owners_l1) l2 start in
  (* lemma_restriction_means_owner_subset l1 m1; *)
  let m2 = fold l2 (Set.as_list owners_l2) l1 m1 in
  (* lemma_restriction_means_owner_subset l1 m2; *)
  m2

assume val lemma_join_is_a_restriction : 
  #p:eqtype ->
  #f:Map.cmp p ->
  l1 : label p f ->
  l2 : label p f ->
  Lemma (ensures is_a_restriction l1 (join l1 l2))
