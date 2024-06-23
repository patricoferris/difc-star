difc*
-----

Formalisation of DIFC 
([A Decentralized Model for Information Flow Control](https://www.cs.cornell.edu/andru/papers/iflow-sosp97/paper.html)) using FStar.

Create a custom DIFC model with a user-defined principal.

```ocaml
module User = struct
  type t = { username : string }

  let equal a b = String.equal a.username b.username

  let pp ppf v = Format.pp_print_string ppf v.username
end

module Users = Difc.Make (User)
module M = Users.Monad
open M.Syntax

(* Some users *)
let anil = User.{ username = "Anil" }
let ryan = User.{ username = "Ryan" }
let jessica = User.{ username = "Jessica" }
let michael = User.{ username = "Michael" }
let maddy = User.{ username = "Maddy" }
let patrick = User.{ username = "Patrick" }
```

Track labels using the built-in operators.

```ocaml
# let ryans_label = Users.v ryan [ michael; anil ];;
val ryans_label : Users.t = <abstr>
# let jessicas_label = Users.v jessica [ maddy; anil ];;
val jessicas_label : Users.t = <abstr>
# let patricks_label = Users.v patrick [ ryan; anil ];;
val patricks_label : Users.t = <abstr>
```

Combine data and restrict the resulting label.

```ocaml
# let v =
    let* patricks_data = M.return patricks_label "Super " in
    let* ryans_data = M.return ryans_label " secret " in
    let+ jessicas_data = M.return jessicas_label "data" in 
    patricks_data ^ ryans_data ^ jessicas_data
val v : string M.t = <abstr>
```

We can look at the new data's label.

```ocaml
# M.label v |> Users.owners
- : User.t list =
[{User.username = "Patrick"}; {User.username = "Ryan"};
 {User.username = "Jessica"}]
# M.label v |> Users.effective_readers
- : User.t list = [{User.username = "Anil"}]
```
