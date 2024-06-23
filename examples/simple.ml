
let f = FStar_OrdSet.intersect
module User = struct
  type t = { username : string }

  let equal a b = String.equal a.username b.username

  let pp ppf v = Format.pp_print_string ppf v.username
end

module Users = Difc.Make (User)

let alice = User.{ username = "Alice" }
let bob = User.{ username = "Bob" }
let charlie = User.{ username = "Charlie" }
let meredith = User.{ username = "Meredith" }
let map = Users.v alice [ alice; bob ] 
          |> Users.add charlie [ alice; meredith; bob ]
          |> Users.add meredith [ alice ]
let owners = Users.owners map
let ef = Users.effective_readers map

let () =
  print_endline "Owners:";
  List.iter (Format.printf "%a\n%!" User.pp) owners;
  print_endline "\nEffective Reader Set:";
  List.iter (Format.printf "%a\n%!" User.pp) ef

