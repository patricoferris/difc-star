open Prims
type ('a, 'p, 'f) difc_monad =
  {
  value: 'a ;
  label: ('p, unit) Difc_fstar.label }
let __proj__Mkdifc_monad__item__value :
  'a 'p . 'p FStar_OrdMap.cmp -> ('a, 'p, unit) difc_monad -> 'a =
  fun f -> fun projectee -> match projectee with | { value; label;_} -> value
let __proj__Mkdifc_monad__item__label :
  'a 'p .
    'p FStar_OrdMap.cmp ->
      ('a, 'p, unit) difc_monad -> ('p, unit) Difc_fstar.label
  =
  fun f -> fun projectee -> match projectee with | { value; label;_} -> label
let get_label :
  'a 'p .
    'p FStar_OrdMap.cmp ->
      ('a, 'p, unit) difc_monad -> ('p, unit) Difc_fstar.label
  = fun f -> fun l -> l.label
let return :
  'a 'p .
    'p FStar_OrdMap.cmp ->
      ('p, unit) Difc_fstar.label -> 'a -> ('a, 'p, unit) difc_monad
  = fun f -> fun l -> fun value -> { value; label = l }
let bind :
  'a 'b 'c 'p .
    'p FStar_OrdMap.cmp ->
      ('a -> ('b, 'p, unit) difc_monad) ->
        ('a, 'p, unit) difc_monad -> ('b, 'p, unit) difc_monad
  =
  fun f ->
    fun fn ->
      fun v ->
        let dm = fn v.value in
        let v_label = get_label f v in
        let l' = Difc_fstar.join f v_label dm.label in
        let res = { value = (dm.value); label = l' } in res
let map :
  'a 'b 'c 'p .
    'p FStar_OrdMap.cmp ->
      ('a -> 'b) -> ('a, 'p, unit) difc_monad -> ('b, 'p, unit) difc_monad
  =
  fun f -> fun fn -> fun v1 -> { value = (fn v1.value); label = (v1.label) }
let pair :
  'a 'b 'c 'p .
    'p FStar_OrdMap.cmp ->
      ('a, 'p, unit) difc_monad ->
        ('b, 'p, unit) difc_monad -> (('a * 'b), 'p, unit) difc_monad
  =
  fun f ->
    fun v1 ->
      fun v2 ->
        let v' = ((v1.value), (v2.value)) in
        let l' = Difc_fstar.join f v1.label v2.label in
        { value = v'; label = l' }