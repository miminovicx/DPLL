open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_5_1 = [[1;2;3];[1-2;-3];[1;-4];[-2;-3;-4];[-1;-2;3];[5;6];[5;-6];[2;-5];[-1;-5]]
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let rec simplifie i clauses =
  match clauses with
  | [] -> [[]]
  | v :: rest -> 
      if List.mem i v then
        match rest with
        | [] -> []
        | _ :: _ -> simplifie i rest
      else if List.mem (-i) v then
        let rec remove a list = 
          match list with
          | [] -> []
          | h :: t ->
            if(h = a) then
              remove a t
            else
              h::(remove a t) 
        in
        match rest with
        | [] -> [(remove (-i) v)]
        | _ :: _ -> [(remove (-i) v)]@(simplifie i rest)
      else
        match rest with
        | [] -> [v]
        | _ :: _ -> [v]@(simplifie i rest)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int option
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, retourne None *)
let rec unitaire clauses =
  match clauses with
  | [] -> None
  | c :: r -> if List.length c = 1 then 
                Some (List.hd c)
              else
                unitaire r
;;
    
(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, retourne None *)
let pur clauses =
  let flat_clauses = List.flatten clauses in
  (* del  : int -> int list -> int list
          - si 'lit' apparait positivement ou négativement dans
            'list', supprime ce littéral
          - sinon, retourne la liste (retournée) *)
  let rec del lit list =
    match list with
    | [] -> []
    | v :: r -> 
       if (v = lit) || (v = -lit) then
         del lit r
       else
         v::(del lit r)
  in
  (* pur_aux : int list -> int option
             - si 'list' est vide ou qu'il n'y a pas de littéral
               pur, retourne None
             - si il y un littéral pur, retourne le premier trouvé *)
  let rec pur_aux list =
    match list with
    | [] -> None
    | h :: t ->
       let is_opposite e = (e = -h) in
       if List.exists is_opposite list then
         pur_aux (del h list)
       else
         Some h
  in
  pur_aux flat_clauses
;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation
  else if List.mem [] clauses then None 
  else
    match unitaire clauses with
    | Some u_l ->
       solveur_dpll_rec (simplifie u_l clauses) (u_l :: interpretation)
    | None ->
       match pur clauses with
       | Some p_l ->
            solveur_dpll_rec (simplifie p_l clauses) (p_l :: interpretation)
       | None ->
          let p = List.hd (List.hd clauses) in
          let branch =
            solveur_dpll_rec (simplifie p clauses) (p::interpretation) in
          match branch with
          | None ->
             solveur_dpll_rec (simplifie (-p) clauses) (p::interpretation)
          | _ -> branch

(* tests *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () = 
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
