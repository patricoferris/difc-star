(* Raw FStar generated code *)
module Low_level = Difc_fstar
module M = FStar_OrdMap

module type Principal = sig
  type t

  val equal : t -> t -> bool
end

module Make (P : Principal) = struct
  type 'a t = (P.t, 'a, unit) FStar_OrdMap.ordmap

  (* Don't expose! *)
  let empty = M.empty P.equal
  let add o v = M.update P.equal o v
  let v owner readers = empty |> add owner readers
  let owners v = Low_level.owners P.equal v
  let effective_readers v = Low_level.effective_readers P.equal v
end
