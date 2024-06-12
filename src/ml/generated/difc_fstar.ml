open Prims
type ('a, 'f) label =
  ('a, ('a, unit) FStar_OrdSet.ordset, unit) FStar_OrdMap.ordmap
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
        | FStar_Pervasives_Native.Some v -> v
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
            FStar_OrdSet.intersect f acc readers in
      let uu___ =
        match FStar_OrdMap.choose f m with
        | FStar_Pervasives_Native.Some m1 -> m1 in
      match uu___ with
      | (_choosen_owner, choosen_readers) ->
          FStar_OrdSet.fold f g choosen_readers (owners f m)
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