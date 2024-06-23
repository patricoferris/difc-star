
(* Raw FStar generated code *)
module Low_level = Difc_fstar
module M = FStar_OrdMap

module type Principal = sig
  type t

  val equal : t -> t -> bool
  
  val pp : Format.formatter -> t -> unit
end

module Make (P : Principal) : sig 
  type t

  val pp : Format.formatter -> t -> unit

  val v : P.t -> P.t list -> t
  (* A new label with a single owner and set of readers *)

  val add : P.t -> P.t list -> t -> t

  val owners : t -> P.t list

  val effective_readers : t -> P.t list

  module Monad : sig
    type label := t
    type 'a t
    (** Labelled values *)

    val label : 'a t -> label

    val return : label -> 'a -> 'a t

    val bind : ('a -> 'b t) -> 'a t -> 'b t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val pair : 'a t -> 'b t -> ('a * 'b) t

    module Syntax : sig
     val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
     val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
    end
  end
end
