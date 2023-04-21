type f2poly = int list

(* declaration polynome test *)
let p : f2poly = [ 0; 3 ]

(*converti f2poly en 01list *)
let f2poly_to_01list p =
  let rec aux acc i p =
    match p with
    | h :: t when i = h -> aux (1 :: acc) (i + 1) t
    | h :: t when i != h -> aux (0 :: acc) (i + 1) (h :: t)
    | _ -> acc
  in
  aux [] 0 p

(* declaration de la somme *)
let ( ++ ) (a : bool) (b : bool) = if a = b then false else true

(* declaration de la multiplication *)
let ( && ) (a : int) (b : int) = a + b

(* ex1.2 *)
(* renvoie true le monome de degré x d'un polynome existe, false sinon. *)
let rec monome x = function
  | [] -> false
  | m :: _ when m = x -> true
  | _ :: l -> monome x l

(* ex1.2 *)
(* fonction de somme de 2 polynome *)
let ( +++ ) (x : f2poly) (y : f2poly) : f2poly =
  let rec aux (l : f2poly) (r : f2poly) (acc : f2poly) =
    match (l, r) with
    | la :: l, ra :: r when la = ra -> aux l r acc
    | la :: l, (ra :: _ as r) when la < ra -> aux l r (la :: acc)
    | (la :: _ as l), ra :: r when la > ra -> aux l r (ra :: acc)
    | [], r -> List.rev acc @ r
    | l, _ -> List.rev acc @ l
  in
  aux x y []

let somme (x : f2poly) (y : f2poly) : f2poly =
  let rec aux (l : f2poly) (r : f2poly) (acc : f2poly) =
    match (l, r) with
    | la :: l, ra :: r when la = ra -> aux l r acc
    | la :: l, (ra :: _ as r) when la < ra -> aux l r (la :: acc)
    | (la :: _ as l), ra :: r when la > ra -> aux l r (ra :: acc)
    | [], r -> List.rev acc @ r
    | l, _ -> List.rev acc @ l
  in
  aux x y []
;;

p +++ [ 0; 1 ]

(* ex1.2 *)
(* fonction multCoeff qui multiplie un polynome par une constante *)
let multCoeff (p : f2poly) x = if x = true then p else [];;

(* test de la fonction multCoeff *)
multCoeff [ 0; 1; 3 ] true

(* degre renvoie le degre d'un polynome *)
let degre (p : f2poly) =
  let aux (p : f2poly) = match p with la :: _ -> la | [] -> -1 in
  aux (List.rev p)
;;

(* Test de la fonction degre *)
degre [ 0; 1; 3 ]

(* multXn calcul le produit du polynome par un monome X^n *)
let multXn (p : f2poly) x =
  let rec aux (p : f2poly) x acc =
    match p with la :: p -> aux p x ((la + x) :: acc) | [] -> List.rev acc
  in
  aux p x []
;;

(* test multXn *)
multXn p 2

(* cut renvoie un couple avec le polynome et privé du monome de degre i *)
let cut (p : f2poly) x =
  let rec aux (p : f2poly) x pacc acc =
    match p with
    | pa :: p when pa < x -> aux p x (pa :: pacc) acc
    | pa :: p -> aux p x pacc ((pa - x) :: acc)
    | [] -> (List.rev pacc, List.rev acc)
  in
  aux p x [] []
;;

(* test de la fonction cut *)
cut p 2

(* multNaive fonction de multiplication de polynome naive *)
let multNaive (p1 : f2poly) (p2 : f2poly) =
  let rec aux (p1 : f2poly) (p2 : f2poly) (c : f2poly) i =
    if i < degre p1 then
      aux p1 p2
        (somme (List.rev c) (multXn (multCoeff p2 (monome i p1)) i))
        (i + 1)
    else somme c (multXn (multCoeff p2 (monome i p1)) i)
  in
  aux p1 p2 [] 0
;;

(* test de multNaive *)
multNaive p p;;
multNaive [ 0; 3 ] [ 1; 2 ]

(* fonction qui remet en ordre le polynome *)
(* let comparPoly x y = (fst x) - (fst y);;
   let sortPoly (p: poly) :poly = List.sort comparPoly p;; *)

let rec multPoly (p1 : f2poly) (p2 : f2poly) =
  if degre p1 <= 0 then multCoeff p2 (monome 0 p1)
  else if degre p2 <= 0 then multCoeff p1 (monome 0 p2)
  else
    let k = max (degre p1) (degre p2) in
    let k2 = k + (k mod 2) in
    let aux ((a0 : f2poly), (a1 : f2poly)) ((b0 : f2poly), (b1 : f2poly)) =
      let c0 = multPoly a0 b0 in
      let c2 = multPoly a1 b1 in
      let u = multPoly (somme a0 a1) (somme b0 b1) in
      let c1 = somme (somme u c0) c2 in
      somme (somme c0 (multXn c1 (k2 / 2))) (multXn c2 k2)
    in
    aux (cut p1 (k2 / 2)) (cut p2 (k2 / 2))
;;

(* test de la fonction multPoly *)
multPoly p p;;
multPoly [ 0; 3 ] [ 1; 2 ]

let reverse x (p : f2poly) =
  let rec aux x (p : f2poly) (acc : f2poly) =
    match p with a :: p -> aux x p ((-a + x) :: acc) | [] -> acc
  in
  aux x p []
;;

(* test de reverse *)
reverse 2 p

let moduloXn (p : f2poly) x : f2poly = List.filter (function p -> p < x) p
let p3 : f2poly = [ 0; 1; 2; 3 ];;

moduloXn p 2

(* fonction inverse_mod qui fonctionne ! verifié sur feuille avec p3 1 et p3 2 *)
let inverse_mod (p : f2poly) x =
  let rec aux (acc : f2poly) i =
    let tmp = multPoly p (multPoly acc acc) in
    if x > i then aux (moduloXn (somme acc tmp) (2 * (i + 1))) (i + 1) else acc
  in
  aux [ 0 ] 0
;;

inverse_mod p 2

let cd (p : f2poly) =
  let aux (p : f2poly) = match p with _ :: _ -> 1. | [] -> 0. in
  aux (List.rev p)

let sub (a : f2poly) (b : f2poly) = somme a b

let div_naive a b =
  if b = [] then failwith "Division par zero"
  else
    let db = degre b in
    let rec aux acc a =
      let da = degre a in
      if da < db then (acc, a)
      else aux ((da - db) :: acc) (sub a (multXn b (da - db)))
    in
    aux [] a

(* test de la dvision naive *)
(* div_naive [0;2;4;6;7] [1;2];; *)


(* EX2 Q3: *)
(* calcul de l'odre *)
let ordre (x : f2poly) =
  let rec aux acc accn n =
    if degre x > degre acc + n - accn then aux acc accn (n + 1)
    else if sub (multXn acc (n - accn)) x = [ 0 ] then n
    else aux (sub (multXn acc (n - accn)) x) n (n + 1)
  in
  aux [ 0 ] 0 1
;;

(* test de l'ordre de x3+x2+x+1 == 4 *)
ordre [ 0; 1; 2; 3 ]

(* crée le polynome de degre d et avec les degres entre n et low present *)
let create_poly d n low =
  let rec aux acc low =
    if low = n + 1 then acc else aux (somme acc [ low ]) (low + 1)
  in
  aux [ d ] low

(* genere la list de tout les polynomes de degre d *)
let generate_degre_poly d =
  let rec aux acc n low =
    if low = d then acc
    else if n = d then aux acc (low + 1) (low + 1)
    else
      let tmp = create_poly d n low in
      aux (tmp :: acc) (n + 1) low
  in
  aux [ [ d ] ] 0 0

(* exercice 2 Q4 fonction est irreductible ? *)
let irreductible (p : f2poly) =
  let rec aux acc diviseur =
    match diviseur with
    | poly :: div when snd (div_naive p poly) = [] -> false
    | _ :: div -> aux acc div
    | [] when acc = degre p - 1 -> true
    | [] -> aux (acc + 1) (generate_degre_poly (acc + 1))
  in
  aux 1 (generate_degre_poly 1)

(* fonction outils pow, fait x puissance n *)
let pow x n = int_of_float (float_of_int x ** float_of_int n)

(* crée le polynome primitif dans f2poly de degre > n *)
let create_primitif n =
  if n <= 0 then failwith "Division par zero"
  else
    let rec aux acc m =
      match acc with
      | a :: rest when irreductible a != true || ordre a != pow 2 n - 1 ->
          aux rest m
      | a :: rest -> a
      | [] -> aux (generate_degre_poly (m + 1)) (m + 1)
    in
    aux (generate_degre_poly n) n

(* partie 2 *)
type lfsr = (int * bool) list

let prod (a : int) (b : int) = a + b

let (good_lfsr : lfsr) =
  [
    (1, false);
    (0, true);
    (0, false);
    (1, true);
    (0, true);
    (1, false);
    (1, true);
    (0, false);
    (0, false);
    (1, true);
    (1, false);
    (1, true);
    (0, true);
    (1, false);
    (1, true);
    (0, false);
    (1, true);
    (0, false);
    (0, true);
    (1, true);
    (0, false);
    (0, false);
    (1, true);
    (0, false);
    (0, false);
    (1, true);
  ]

let ( -- ) a b = if a == b then 1 else 0
let sommef2 a b = if a == b then 0 else 1

(* 2) *)

(* Renvoie le nieme element de la list lfsr r0,...rl-1  (l taille de la liste) *)
let get_n_lfsr (n : int) (l : lfsr) =
  let rec aux (i : int) (n : int) (l : lfsr) =
    match l with
    | (h, h1) :: t when i == n -> h
    | (h, h1) :: t when i <= n -> aux (i + 1) n t
    | [] -> failwith "erreur list ou n"
    | _ -> failwith "erreur list ou n"
  in
  aux 0 n (List.rev l)

(* Renvoie la valeur du premier branchement de l *)
let rec get_first_branchement (l : lfsr) =
  match l with
  | (i, b) :: t when b == true -> i
  | (i, b) :: t when b == false -> get_first_branchement t
  | _ -> failwith "aucun branchements"

(* Prend en argument un lfsr et renvoie la liste des valeur située aux branchement *)
let get_value_at_branchement (l : lfsr) =
  let rec aux (acc : int list) (l : lfsr) =
    match l with
    | (i, b) :: t when b == true -> aux (acc @ [ i ]) t
    | (i, b) :: t when b == false -> aux acc t
    | _ -> acc
  in
  aux [] l

let x = get_value_at_branchement lfsr1

(* renvoie la sommef2 de la liste *)
let f2somme_list (l : int list) =
  let rec aux acc l =
    match l with h :: t -> aux (sommef2 acc h) t | [] -> acc
  in
  aux 0 l

(* Renvoie true si n est un branchement de l false sinon  *)
let is_branchement (n : int) (l : lfsr) =
  let rec aux i n l =
    match l with
    | (x, b) :: t when i == n -> b
    | (x, b) :: t when i != n -> aux (i + 1) n t
    | _ -> failwith "Erreur is_branchement"
  in
  aux 0 n l

(* Ajoute r a la liste l en supprimant le dernier terme de la liste l*)
let add_ri r l =
  let size = List.length l in
  let rec aux (acc : lfsr) r l i =
    let list_to_sum = get_value_at_branchement l in
    let (sum : int) = f2somme_list list_to_sum in
    match l with
    | a when i == 0 -> aux [ (sum, is_branchement i l) ] r l (i + 1)
    | (x, b) :: t when i < size ->
        aux (acc @ [ (get_n_lfsr (size - i) l, is_branchement i l) ]) r l (i + 1)
    | _ -> acc
  in
  aux [] r l 0

(* Calcul de V au rang n *)
let cycle_ri l n =
  let rec aux acc i =
    let newlfsr = add_ri (f2somme_list (get_value_at_branchement l)) acc in
    match i with i when i < n -> aux newlfsr (i + 1) | i when i >= n -> acc
  in
  aux l 0

(*  calcul efficace de la nième valeur rn (n ≥ 0) de la suite (ri)i≥0.*)
let get_rn_from_ri l i n =
  let ri = cycle_ri l i in
  get_n_lfsr n ri

(* EXERCICE 4 *)

(* 2) *)

(* Renvoie le polynome R(X) du LFSR l*)
let getRX l =
  let rec aux acc l it =
    match l with
    | (h, b) :: t ->
        if b then aux (acc @ [ it ]) t (it + 1) else aux acc t (it + 1)
    | _ -> 0 :: acc
  in
  aux [] l 1

(* Renvoie Alpha_i du LFSR l  ex: getAlpha [(1,false);(0;true);(1;false)] 2 -> 0 car false*)
let getAlpha l i =
  let rec aux l it =
    match l with
    | (a, b) :: t ->
        if i == 0 then 1
        else if it == i then if b then 1 else 0
        else aux t (it + 1)
    | _ -> failwith "Erreur getAlpha"
  in
  aux l 1

(* Renvoie R_i du LFSR 1 ex: getR [1;0;|0|;0;1;1;0] 4 -> 0*)
let getR l i = fst (List.nth l i)
(*let rec aux l it = match List.rev l with
     | (a,b)::t ->
         if it == i then a
         else aux t (it+1)
     | _ -> failwith "Erreur getR"
  in aux l 0;;*)

let firstSomme i l =
  let rec aux acc j =
    let alpha = getAlpha l (i - j) and r = getR l j in
    let th = prod alpha r in
    match j with
    | j ->
        print_int alpha;
        print_int r;
        print_int th;
        if j < i then aux (sommef2 acc th) (j + 1) else sommef2 acc th
  in
  aux 0 0

let secondSomme l =
  let size = List.length l - 1 in
  let rec aux acc i =
    let sum = firstSomme i l in
    match i with
    | i -> if i < size then aux (acc @ [ sum ]) (i + 1) else acc @ [ sum ]
  in
  aux [] 0

(* Renvoie le polynome G(X) du LFSR l (List.rev pour coller a notre model de LFSR)*)
let getGX l = List.rev (secondSomme l)

(**)
let getTriplet l = (List.length l, getGX l, getRX l)

(*QUESTION 3*)

let tri = (8, [ 1; 0; 0; 1; 0; 1; 1; 0 ], [ 0; 2; 4; 5; 7 ])

(* [(1,false);(0,true);(0,false);(1,true);(0,true);(1,false);(1,true);(0,false)];;*)
let tripletToLFSR t =
  let ((l, gx, rx) as triplet) = t in
  let rec aux acc gx rx it =
    print_int it;
    match (gx, rx) with
    | g, rh :: rt when rh == 0 -> aux acc g rt (it + 1)
    | gh :: gt, rh :: rt when rh == it ->
        if it <= l then aux (acc @ [ (gh, true) ]) gt rt (it + 1)
        else acc @ [ (gh, true) ]
    | gh :: gt, rh :: rt when rh != it ->
        if it <= l then aux (acc @ [ (gh, false) ]) gt (rh :: rt) (it + 1)
        else acc @ [ (gh, false) ]
    | gh :: gt, [] -> aux (acc @ [ (gh, false) ]) gt [] (it + 1)
    | _ -> acc
  in
  aux [] gx rx 0
;;

tripletToLFSR tri

(* Renvoie le polynome de plus haut degres entre a et b*)
let plus_haut_degres a b =
  let dega = degre a and degb = degre b in
  if dega > degb then a else b

let plus_bas_degres a b =
  let dega = degre a and degb = degre b in
  if dega > degb then b else a

let rec smallest_triplet t =
  let ((l, gx, rx) as triplet) = t in
  let ax = plus_haut_degres gx rx and bx = plus_bas_degres gx rx in
  let ((q, r) as res_div) = div_naive ax bx in
  if r == [] then
    let newax = fst (div_naive ax q) and newbx = fst (div_naive bx q) in
    smallest_triplet (max (degre newax) (degre newbx), newax, newbx)
  else t

let chiffrage mot lfsr =
  let rec aux acc mot i =
    match mot with
    | h :: t -> aux (acc @ [ sommef2 h (get_n_lfsr i lfsr) ]) t (i + 1)
    | _ -> acc
  in
  aux [] mot 0
