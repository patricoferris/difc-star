(* Raw FStar generated code *)
module Low_level = Difc_fstar
module S = FStar_OrdSet
module M = FStar_OrdMap

module type Principal = sig
  type t

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit
end

module Make (P : Principal) = struct
  type t = (P.t, (P.t, unit) S.ordset, unit) FStar_OrdMap.ordmap

  (* Don't expose! *)
  let empty = M.empty P.equal
  let add o v = M.update P.equal o (List.sort compare v)
  let v owner readers = empty |> add owner readers
  let owners v = Low_level.owners P.equal v
  let effective_readers v = Low_level.effective_readers P.equal v
  let pp_pair f1 f2 =
    (fun ppf (a, b) -> Format.fprintf ppf "(%a, %a)" f1 a f2 b)
  
  let pp ppf (f : t) =
    let owners = M.dom P.equal f in
    let rec fold acc = function
      | [] -> List.rev acc
      | o :: os ->
      match M.select P.equal o f with
      | Some rs ->
        fold ((o, S.as_list P.equal rs) :: acc) os
      | None -> fold acc os
    in
    let lst = fold [] owners in
    Format.fprintf ppf "%a" Format.(pp_print_list (pp_pair P.pp (pp_print_list P.pp))) lst

  module Monad = struct
    type 'a t = ('a, P.t, unit) Difc_fstar_monad.difc_monad

    let label (v : 'a t) = v.label
    let return l (v : 'a) : 'a t = Difc_fstar_monad.return P.equal l v

    let bind (fn : 'a -> 'b t) (v : 'a t) : 'b t =
      Difc_fstar_monad.bind P.equal fn v
    
    let map (fn : 'a -> 'b) (v : 'a t) : 'b t = Difc_fstar_monad.map P.equal fn v
      
    let pair v1 v2 =
      Difc_fstar_monad.pair P.equal v1 v2

    module Syntax = struct
      let ( let+ ) v f = map f v
      let ( let* ) v f = bind f v
    end
  end
end
