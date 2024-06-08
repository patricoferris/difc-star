module Difc

module Map = FStar.OrdMap
module Set = FStar.OrdSet

(* A verified DIFC algorithm for user-defined principals. 
   
   This FStar program provides a means of extracting a DIFC
   checker that is verified. A user may define their own set 
   of principals providing they meet certain properties. *)

(* A label is an ordered map from principals to sets of principals.
   A principal can be any decidably equal type. *)

type label a f = Map.ordmap a (Set.ordset a f) f

(* The owners of a label is the domain of the ordered map *)
let owners #p #f (m : label p f) = Map.dom m

let readers_with_empty (#p:eqtype) #f (k : p) (l : label p f) : Set.ordset p f =
  match Map.select k l with
  | None -> Set.empty
  | Some v -> v 

(* The effective readers of a label is the set of all principals
   that the owners of the label agree to release the data to. *)
let effective_readers #p #f (m : label p f) : Set.ordset p f =
  let g (acc : Set.ordset p f) (k : p) =
    match Map.select k m with
	| None -> acc
	| Some readers ->
      Set.intersect acc readers
  in
  Set.fold #p #(Set.ordset p f) g Set.empty (owners m)

let subset_for_all #e #f (s1 : Set.ordset e f) (s2 : Set.ordset e f) :
  Lemma (requires Set.subset s1 s2)
        (ensures forall o. Set.mem o s1 ==> Set.mem o s2)
  = ()

val for_all: (#p:eqtype) -> (#f:Set.cmp p) -> (p -> Tot bool) -> Set.ordset p f -> Tot bool
let for_all f s = List.Tot.for_all f (Set.as_list s)

let is_a_restriction #p #f (l1 : label p f) (l2 : label p f) =
  let pred (principal : p) : Tot bool =
    Set.subset (readers_with_empty principal l2) (readers_with_empty principal l1)
  in
  Set.subset (owners l1) (owners l2) /\ 
  for_all pred (owners l1)

(* TODO: What is the best way to structure an F* proof?
   Here we define the function that is to be a restriction and then prove
   the lemmas that make up the definition? *)
let lemma_restriction_means_owner_subset #p #f (l1 : label p f) (l2 : label p f) :
 Lemma (requires is_a_restriction l1 l2)
       (ensures Set.subset (owners l1) (owners l2)) =
	   ()

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

