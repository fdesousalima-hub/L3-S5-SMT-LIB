(* Ce mini-projet porte sur l'apprentissage d'automates séparateurs.
   La lecture de la Section 16.3 des notes de cours est fortement
   recommandée. Le code que vous devez écrire prend en entrée deux
   listes de mots I et E, lues à partir d'un fichier passé en argument
   et renvoie sur la sortie standard le code SMT-LIB à faire passer
   dans une solveur SMT, comme Z3.
 *)

open Printf

(* ensembles de test : ensemble I *)
let li = ["";"ab"]

(* ensembles de test : ensemble E *)
let le = ["aa";"b"]


(* ======================================================================= *)
(* EXERCICE 1 : extraire  l'alphabet de l'automate.
   La fonction alphabet_from_list prend en entrée une liste de
   chaînes de caractères et retourne une liste triée de
   caractères sans duplication.
 *)
(* explode : string -> char list
   prend une chaîne de caractères et renvoie la liste de ses caractères
 *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(* add_list : 'a list -> 'a list -> 'a list
   - prend en entrée une liste c_add de caractères et la liste des caractère final
   - renvoie la liste final avec les nouveaux caractères non existant dans la liste final
     apparaissant dans l
  *)
let rec add_list c_add c =
  match c_add with
  | [] -> c
  | x :: rest_c_add -> if List.mem x c then add_list rest_c_add c
                                       else add_list rest_c_add (x :: c)

(* alphabet_from_list_aux : string list -> char list -> char list
   - prend en entrée une liste l de chaînes de caractères et la liste des caractère
   - renvoie la liste triée et sans duplication de caractères
     apparaissant dans l
  *)
let rec alphabet_from_list_aux l c =
  match l with
  | [] -> List.sort compare c
  | str :: reste_l -> alphabet_from_list_aux reste_l (add_list (explode str) c)

(* alphabet_from_list : string list -> char list
   - prend en entrée une liste l de chaînes de caractères
   - renvoie la liste triée et sans duplication de caractères
     apparaissant dans l
 *)
let alphabet_from_list l =
  alphabet_from_list_aux l []
(* test *)
(* let a = alphabet_from_list (li @ le) *)

(* ======================================================================= *)
(* EXERCICE 2 : définition de l'alphabet A et de l'arbre préfixe T en
   SMT-LIB Pour les listes données en exemple, la sortie de la
   fonction declare_types doit être la chaîne de caractères
   "(declare-datatypes () ((A a b) (T e ea eaa eab eb)))" *)


(* prefixes : string -> string list
   renvoie la liste des préfixes d'une chaîne de caractères
   Nous allons ajouter à chaque préfixe le caractère 'e'.
   Par exemple, prefixes "aba" = ["e"; "ea"; "eab"; "eaba"] *)
let rec prefixes s =
  match s with
  | "" -> ["e"]
  | x ->  prefixes (String.sub s 0 (String.length s - 1)) @ ["e" ^ x]

(* prefixes_of_list_aux : string list -> string list -> string list
   renvoie la liste triée et sans doublons des préfixes des chaînes
   de caractères d'une liste donnée *)
let rec prefixes_of_list_aux l liste =
  match l with
  | [] -> List.sort compare liste
  | str :: reste_l -> prefixes_of_list_aux reste_l (add_list (prefixes str) liste)


(* prefixes_of_list : string list -> string list
   renvoie la liste triée et sans doublons des préfixes des chaînes
   de caractères d'une liste donnée *)
let prefixes_of_list l =
  prefixes_of_list_aux l []

(* concat_char : char list -> string
   prend une liste de caractères [c_1; ...; c_n] et renvoie une chaîne
   de la forme "c_1... c_n" *)
let rec concat_char l =
  match l with
  | [] -> ""
  | x :: reste_l -> " " ^ String.make 1 x ^ concat_char reste_l

(* concat_string : string list -> string
   prend une liste de string [s_1; ...; s_n] et renvoie une chaîne
   de la forme "s_1... s_n" *)
let rec concat_string l =
  match l with
  | [] -> ""
  | x :: reste_l -> " " ^ x ^ concat_string reste_l

(* declare_types_alphabet : char list -> string
   prend une liste de caractères [c_1; ...; c_n] et renvoie une chaîne
   de la forme "(A c_1... c_n)" *)
let declare_types_alphabet cl =
  "(A " ^ (concat_char cl) ^ ")"

(* declare_types_trie : string list -> string
   prend une liste l de chaînes de caractères et
   renvoie une chaîne de la forme "(T es_1 ... es_n)" où
   s_1... s_n est une énumération de tous les
   prefixes des chaînes apparaissant dans l *)
let declare_types_trie l =
  "(T " ^ (concat_string (prefixes_of_list l)) ^ ")"

(* declare_types : string list -> char list -> string *)
let declare_types l cl =
  (* à compléter *)
  "(declare-datatypes () (" ^ (declare_types_alphabet cl) ^ " " ^ (declare_types_trie l) ^ "))\n"

(* test *)
(* Printf.printf "%s" (declare_types (li @ le) a) *)


(* ======================================================================= *)
(* EXERCICE 3 : définir une chaîne de caractères pour les définitions
   en SMT-LIB de
   - l'ensemble d'états Q,
   - la fonction delta de transition de l'automate,
   - l'ensemble final des états acceptants et
   - la fonction f,
   ainsi que les assertions associées.
   Ces définitions ne dépendent pas des listes de mots acceptés ou rejetés. *)

let define_sorts_and_functions  =
  (* à compléter *)
  "(define-sort Q () Int)\n(declare-const n Q)\n(assert (> n 0))\n
(declare-fun delta (Q A) Q)\n(assert (forall ((q Q) (a A))\n(and (>= (delta q a) 0) (< (delta q a) n))))\n
(declare-fun final (Q) Bool)\n
(declare-fun f (T) Q)\n(assert (forall ((x T))\n(and (>= (f x) 0) (< (f x) n))))\n
(assert (= 0 (f e)))\n"

(* ======================================================================= *)
(* EXERCICE 4 : contraintes sur les transitions
   La fonction assert_transition_constraints prend en entrée une trie
   et retourne une chaîne qui modélise les contraintes sur les transitions
   de l'automate décrites par la formule (56). *)

(* eq_trans_constr : string -> char -> string
   renvoie une chaîne de caractères qui correspond à une formule atomique pour
   la transition étiquetée avec 'a' à partir de l'état s
   Par exemple, pour s = "abc" et  c = 'd' on a
   eq_trans_constr outputs "(= (f abcd)  (delta (f abc)  d))" *)
let eq_trans_constr s c =
  "(= (f " ^ s ^ (String.make 1 c) ^ ")  (delta (f " ^ s ^  ")  " ^ (String.make 1 c) ^ "))\n"

(* list_transition_constraints : string list -> string list
   prend une liste de chaînes de caractères et génère une liste
   de formules atomiques ou de chaînes vides comme suit
   - pour une chaîne non vide de la forme sa on obtient
     une chaine correspondant à l'équation f(sa) = delta (fs) a
   - pour la chaîne vide on obtient la chaîne vide *)
let rec list_transition_constraints l =
    match l with
    | [] -> []
    | str :: reste_l -> match str with
                        | "" -> list_transition_constraints reste_l
                        | "e" -> list_transition_constraints reste_l
                        | x -> (eq_trans_constr (String.sub str 0 ((String.length str)-1)) (String.get str ((String.length str)-1)))
                               :: (list_transition_constraints reste_l)
(* assert_transition_constraints : string list -> string
   prend en entrée une liste de mots et renvoie une chaîne qui modélise
   les contraintes sur les transitions de l'automate décrit par la
   formule (56).
   Par exemple, pour la liste [""; "ab"; "aa"; "b"] on obtient la chaîne
   "(assert (and
               (= (f ea)  (delta (f e)  a))
               (= (f eaa)  (delta (f ea)  a))
               (= (f eab)  (delta (f ea)  b))
               (= (f eb)  (delta (f e)  b))))"
 *)
let assert_transition_constraints l =
"(assert (and \n" ^ concat_string (list_transition_constraints (prefixes_of_list l)) ^ "))\n"

(* test *)
(* Printf.printf "%s" (assert_transition_constraints (li @ le)) *)

(* ======================================================================= *)
(* EXERCICE 5 : contraintes sur les états acceptants La fonction
   assert_acceptance prend en entrée deux listes de mots et retourne
   une chaîne de caractères qui modélise les contraintes sur les états
   acceptants décrites par la formule (57). *)

(* eq_accept : string -> string
   - prend une chaîne de caractères s et renvoie une chaîne de caractères
   qui modélise l'appartenance de s à l'ensemble final des états acceptants *)
let eq_accept s =
  "(final (f e" ^ s ^ "))\n"

(* eq_non_accept : string -> string
   - prend une chaîne de caractères s et renvoie une chaîne de caractères
   qui modélise la non-appartenance de s à l'ensemble final des états acceptants
 *)
let eq_non_accept s =
    "(not(final (f e" ^ s ^ ")))\n"

    (* assert_acceptance_aux : string list -> bool > string
       prend une listes de chaînes de caractères, et renvoie une
       chaine qui modélise les contraintes sur les états acceptants
       décrites par la formule (52). *)
let rec assert_acceptance_aux l acceptant =
  match l with
  | [] -> ""
  | s::reste_l -> if acceptant then (eq_accept s) ^ assert_acceptance_aux reste_l acceptant
    else (eq_non_accept s) ^ assert_acceptance_aux reste_l acceptant
(* assert_acceptance : string list -> string list > string
   prend deux listes de chaînes de caractères, li et le, et renvoie une
   chaine qui modélise les contraintes sur les états acceptants
   décrites par la formule (52).
   Les mots dans li sont acceptés et les mots dans le ne le sont pas. *)
let assert_acceptance li le  =
  "(assert (and \n"^ (assert_acceptance_aux li true)^(assert_acceptance_aux le false)^"))\n";;


(* test *)
(* Printf.printf "%s" (assert_acceptance li le) *)

(* ======================================================================= *)
(* EXERCICE 6 :
   La fonction smt_code prend en entrée deux listes de mots
   et retourne une chaîne de caractères qui donne l'implémentation
   en SMT-LIB. *)

(* smt_code : string list -> string list -aux> string
   prend deux listes de chaînes de caractères, li et le, et renvoie une chaîne
   de caractères qui donne l'implémentation en SMT-LIB.
   Les mots dans li sont acceptés et les mots dans le ne le sont pas.
   Pour vérifier votre algorithme, vous pouvez essayer le code SMT-LIB
   que vous obtenez dans le solveur Z3: https://rise4fun.com/z3 *)
let smt_code li le =
  declare_types (li @ le) (alphabet_from_list (li @ le)) ^ "\n" ^
  define_sorts_and_functions ^ "\n" ^
  assert_transition_constraints (li @ le) ^ "\n" ^
  assert_acceptance li le ^ "\n" ^
  "(check-sat-using (then qe smt))\n
(get-model)\n
(exit)\n"

(* test *)
(* Printf.printf "%s" (smt_code li le) *)


(* ======================================================================= *)
(* lire deux listes de chaîne de caractères I et E d'un fichier *)
(* Ne pas modifier cette partie *)

let input_line_opt ic =
  try Some (input_line ic)
  with End_of_file -> None

let read_lines ic =
  let rec aux acc =
    match input_line_opt ic with
    | Some line -> aux (line::acc)
    | None -> (List.rev acc)
  in
  aux []

let lines_of_file filename =
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  (lines)

let read_lists_from_file (filename: string): ((string list) * (string list))  =
  let lines = lines_of_file filename in
  (String.split_on_char ' ' (List.nth lines 0),
   String.split_on_char ' ' (List.nth lines 1))

let () =
  let (li,le) = (read_lists_from_file Sys.argv.(1)) in
  Printf.printf "%s" (smt_code li le)
