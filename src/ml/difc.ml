(* Raw FStar generated code *)
module Low_level = Difc_fstar
module M = FStar_OrdMap

module type Principal = sig
  type t

  val equal : t -> t -> bool
end

module Make (P : Principal) = struct
  type t = (P.t, P.t list, unit) FStar_OrdMap.ordmap

  (* Don't expose! *)
  let empty = M.empty P.equal
  let add o v = M.update P.equal o v
  let v owner readers = empty |> add owner readers
  let owners v = Low_level.owners P.equal v
  let effective_readers v = Low_level.effective_readers P.equal v

  module Monad = struct
    type v = t
    type 'a t = ('a, P.t, unit) Difc_fstar_monad.difc_monad

    let label (v : 'a t) = v.label
    let return (l : v) (v : 'a) : 'a t = Difc_fstar_monad.return P.equal l v

    let bind (fn : 'a -> 'b t) (v : 'a t) : 'b t =
      Difc_fstar_monad.bind P.equal fn v

    let map (fn : 'a -> 'b) (v : 'a t) : 'b t =
      Difc_fstar_monad.map P.equal fn v

    let map_pair (f : 'a -> 'b -> 'c) (m : 'a t) (n : 'b t) : 'c t =
      Difc_fstar_monad.map_pair P.equal f m n

    module Syntax = struct
      let ( let+ ) v f = map f v
      let ( let* ) v f = bind f v
    end
  end
end
