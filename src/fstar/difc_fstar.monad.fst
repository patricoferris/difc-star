module Difc_fstar.Monad

open Difc_fstar

module Map = FStar.OrdMap
module Set = FStar.OrdSet
module List = FStar.List.Tot

noeq
type difc_monad (a : Type) (p : eqtype) (f : Map.cmp p) = {
  value : a;
  label : label p f; 
}

let get_label (#a:Type) (#p:eqtype) (#f:Map.cmp p) (l : difc_monad a p f) = l.label

let return (#a:Type) (#p:eqtype) (#f:Map.cmp p) (l : label p f) (value : a) = { value; label = l }

let bind (#a:Type) (#b:Type) (#c:Type) (#p:eqtype) (#f:Map.cmp p) 
  (fn : a -> difc_monad b p f) 
  (v : difc_monad a p f) :
  res: difc_monad b p f { is_a_restriction (get_label v) (get_label res) } =
    let dm = fn v.value in
	let v_label = get_label v in
	let l' = join v_label dm.label in
	let res = { value = dm.value; label = l' } in
    lemma_join_is_a_restriction v_label dm.label;
	assert (equal (get_label res) (join v_label dm.label));
	res

let map (#a:Type) (#b:Type) (#c:Type) (#p:eqtype) (#f:Map.cmp p)
  (fn : a -> b)
  (v1 : difc_monad a p f)  =
  { value = fn v1.value; label = v1.label }

let pair (#a:Type) (#b:Type) (#c:Type) (#p:eqtype) (#f:Map.cmp p) 
  (v1 : difc_monad a p f) 
  (v2 : difc_monad b p f) =
  let v' = (v1.value, v2.value) in
  let l' = join v1.label v2.label in
  { value = v'; label = l' }
