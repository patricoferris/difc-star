open Prims
type ('a, 'f) label =
  ('a, ('a, unit) FStar_OrdSet.ordset, unit) FStar_OrdMap.ordmap
type ('p, 'f, 'm1, 'm2) equal =
  ('p, ('p, unit) FStar_OrdSet.ordset, unit, unit, unit) FStar_OrdMap.equal
let v :
  'p .
    'p FStar_OrdMap.cmp ->
      'p -> ('p, unit) FStar_OrdSet.ordset -> ('p, unit) label
  =
  fun f ->
    fun o -> fun v1 -> FStar_OrdMap.update f o v1 (FStar_OrdMap.empty f)
let owners :
  'p .
    ('p -> 'p -> Prims.bool) ->
      ('p, unit) label -> ('p, unit) FStar_OrdSet.ordset
  = fun f -> fun m -> FStar_OrdMap.dom f m
let readers_with_empty :
  'p .
    ('p -> 'p -> Prims.bool) ->
      'p -> ('p, unit) label -> ('p, unit) FStar_OrdSet.ordset
  =
  fun f ->
    fun k ->
      fun l ->
        match FStar_OrdMap.select f k l with
        | FStar_Pervasives_Native.None -> FStar_OrdSet.empty f
        | FStar_Pervasives_Native.Some v1 -> v1
let effective_readers :
  'p .
    ('p -> 'p -> Prims.bool) ->
      ('p, unit) label -> ('p, unit) FStar_OrdSet.ordset
  =
  fun f ->
    fun m ->
      let g acc k =
        match FStar_OrdMap.select f k m with
        | FStar_Pervasives_Native.None -> acc
        | FStar_Pervasives_Native.Some readers ->
            FStar_OrdSet.intersect f readers acc in
      let uu___ = FStar_OrdMap.choose f m in
      match uu___ with
      | FStar_Pervasives_Native.Some (o, o_readers) ->
          let os = FStar_OrdSet.remove f o (owners f m) in
          FStar_OrdSet.fold f g o_readers os
let for_all :
  'p .
    'p FStar_OrdSet.cmp ->
      ('p -> Prims.bool) -> ('p, unit) FStar_OrdSet.ordset -> Prims.bool
  =
  fun f ->
    fun f1 ->
      fun s -> FStar_List_Tot_Base.for_all f1 (FStar_OrdSet.as_list f s)
type ('p, 'f, 'l1, 'l2) is_a_restriction = unit
let readers_agree :
  'p .
    ('p -> 'p -> Prims.bool) ->
      'p -> ('p, unit) label -> ('p, unit) label -> Prims.bool
  =
  fun f ->
    fun o ->
      fun l1 ->
        fun l2 ->
          FStar_OrdSet.subset f (readers_with_empty f o l1)
            (readers_with_empty f o l2)
let add :
  'p .
    'p FStar_OrdMap.cmp ->
      'p ->
        ('p, unit) FStar_OrdSet.ordset ->
          ('p, unit) label -> ('p, unit) label
  = fun f -> fun o -> fun v1 -> fun l -> FStar_OrdMap.update f o v1 l
let join :
  'p .
    'p FStar_OrdMap.cmp ->
      ('p, unit) label -> ('p, unit) label -> ('p, unit) label
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let owners_l1 = owners f l1 in
        let owners_l2 = owners f l2 in
        let update_from_label o from_label other_label m =
          match ((FStar_OrdMap.select f o from_label),
                  (FStar_OrdMap.select f o other_label))
          with
          | (FStar_Pervasives_Native.Some rs, FStar_Pervasives_Native.None)
              -> add f o rs m
          | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some
             r2) -> add f o (FStar_OrdSet.intersect f r1 r2) m in
        let rec fold from_label os other_label macc =
          match os with
          | o::[] ->
              let v1 = update_from_label o from_label other_label macc in v1
          | o::rest ->
              let v1 = update_from_label o from_label other_label macc in
              fold from_label rest other_label v1 in
        let uu___ =
          match FStar_OrdMap.choose f l1 with
          | FStar_Pervasives_Native.Some m -> m in
        match uu___ with
        | (choosen_owner, choosen_readers) ->
            let start = v f choosen_owner choosen_readers in
            let m1 = fold l1 (FStar_OrdSet.as_list f owners_l1) l2 start in
            let m2 = fold l2 (FStar_OrdSet.as_list f owners_l2) l1 m1 in m2