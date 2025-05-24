type prop = V of int | Vrai | Faux | Et of prop * prop | Ou of prop * prop | Imp of prop * prop | Equiv of prop * prop |
            Non of prop ;;

type cond = W of int | Vrai_bis | Faux_bis | Si of cond * cond * cond ;; 



(* Etape 1*)

let rec transforme f =
  match f with 
  | V i -> W i
  | Vrai -> Vrai_bis
  | Faux -> Faux_bis
  (*La  vrai structure générale c'est --> Si(W(i),Vrai_bis,Faux_bis) comme le if then else vue en cours *)
  | Non(f) -> Si(transforme f, Faux_bis, Vrai_bis)   (*Inversion du Vrai et Faux sur la feuille sinon Non(Faux) = Si(Faux_bis,Vrai_bis,Faux_bis)= Faux *) 
  | Et(f1, f2) -> Si(transforme f1, transforme f2, Faux_bis)(*Si F1 est Faux, alors on renvoie Faux_bis. Sinon f1=vrai => on récursive sur f2*)
  | Ou(f1, f2) -> Si(transforme f1, Vrai_bis, transforme f2)(*Si f1 est Vrai, alors on renvoie vrai sinon récursive pour voir le bool de f2*)
  | Imp(f1, f2) -> Si(transforme f1, transforme f2, Vrai_bis)(* SI f1=Faux => Vrai pour tt cas. Donc tout de suite vrai, Sinon f1=Vrai => récu de f2*)
  | Equiv(f1, f2) -> Si(Si(transforme f1, transforme f2, Vrai_bis), Si(transforme f2, transforme f1, Vrai_bis), Faux_bis) 
  (*equiv = f1 => f2 ET f2 => f1. Si f1 => f2 est vrai, on voit pour f2 => f1. Sinon f1=>f2 est faux donc f2 => f1 est vrai mais les 2 sont diff donc directe false*)
;;

(*Etape 2*)
let rec for_normale f = 
  match f with
  | W i -> W i (*Renvoie la valeur inchangée*)
  | Vrai_bis -> Vrai_bis 
  | Faux_bis -> Faux_bis 
  | Si(cond1, cond2, cond3) -> (*Si f est construit avec Si tel que f = Si(cond1, cond2, cond3*)
      let n_cond1 = for_normale cond1 in (*Appel récursif sur chaque condition*)
      let n_cond2 = for_normale cond2 in
      let n_cond3 = for_normale cond3 in
      match n_cond1 with (*Nouveau matching sur la première condition pour s'assurer que deux Si ne se suivent pas*)
      | W _ | Vrai_bis | Faux_bis -> Si(n_cond1, n_cond2, n_cond3) (*Si n_cond1 valeur ou un boolean on renvoie une valeur de type Si(ncond1, ncond2, 
                                                                   ncond3)*)
      | Si(cond1', cond2', cond3') -> for_normale (Si(cond1', Si(cond2', n_cond2, n_cond3), Si(cond3', n_cond2, n_cond3))) (*Si deux Si se suivent,                                                                                                                 appel récursif en appliquant                                                                                                                         l'égalité donné sur le poly*)
;;

(*Etape 3*)

(*fonction qui recherche une paire dans une liste donnée*)
let rec verif_couple e l = 
  match l with
  |(i,b)::liste -> if i=e then [(i,b)] else verif_couple e liste
  |[] -> [] ;;
  
(*C'est juste de la tradution de pseudo code en Ocaml*)
let rec eval f e =
  match f with
  | Vrai_bis -> true
  | Faux_bis -> false 
  | W i -> 
      let tmp1 = verif_couple i e in
      (match tmp1 with 
       | [(i,b)] -> b
       | _ -> false)
  | Si(g,h,k) ->  
      match g with
      | Vrai_bis -> eval h e
      | Faux_bis -> eval k e 
      | W i' -> 
          let tmp2 = verif_couple i' e in
          (match tmp2 with
           | [(i',b)] -> if b then eval h e else eval k e
           | _ -> 
               let e1 = (i',true)::e in 
               let e2 = (i',false)::e in 
               (eval h e1) && (eval k e2))
      | Si(_, _, _) -> false
;;
               
  
                                              (*Affichage*)

(*Pour afficher les formules propositionnelles*)
let rec affiche_prop = function
  | V i -> "V" ^ string_of_int i
  | Vrai -> "Vrai"
  | Faux -> "Faux"
  | Et (p1, p2) -> "(" ^ affiche_prop p1 ^ " ∧ " ^ affiche_prop p2 ^ ")"
  | Ou (p1, p2) -> "(" ^ affiche_prop p1 ^ " ∨ " ^ affiche_prop p2 ^ ")"
  | Imp (p1, p2) -> "(" ^ affiche_prop p1 ^ " => " ^ affiche_prop p2 ^ ")"
  | Equiv (p1, p2) -> "(" ^ affiche_prop p1 ^ " ⇔ " ^ affiche_prop p2 ^ ")"
  | Non p -> "(¬" ^ affiche_prop p ^ ")"
;;

(*Pour afficher les formules conditionnelles*)
let rec affiche_cond = function
  | W i -> "W" ^ string_of_int i
  | Vrai_bis -> "Vrai_bis"
  | Faux_bis -> "Faux_bis"
  | Si (c1, c2, c3) -> "(Si " ^ affiche_cond c1 ^ ", " ^ affiche_cond c2 ^ ", " ^ affiche_cond c3 ^ ")" 
;;

(*Pour afficher le resultat de l'evaluation*)
let affiche_eval bool =
  match bool with
  | true -> "Vrai (C'est une tautologie)"
  | false -> "Faux (Ce n'est pas une tautologie)"
;; 

											(*Tests*)

(* On crée une formule propositionnelle *)

(*let formule_prop = Ou(V 1, Non(V 1)) ;;*)

(*let formule_prop = Ou(V 1, Non(V 2)) ;;*)

(*let formule_prop = Imp (Non(Faux),Ou(Non(Non(Faux)),Non(Vrai))) ;; *)

(*let formule_prop = Et(Non(Faux),Vrai) ;;*) 

(*let formule_prop = Non (Non (Non (V 1))) ;; *)

(*let formule_prop = Et(Vrai, Ou(V(1), Non(Faux))) ;; *)

(*let formule_prop = Ou(Vrai, Faux) ;; *)

(* On transforme cette dernière en formule conditionnelle *)

(*let formule_cond = Si (Si (W 1, Vrai_bis, Faux_bis), Si (W 2, Vrai_bis, Faux_bis), Si (W 3, Vrai_bis, Faux_bis));; *)

(*let formule_cond = Si (Si (Si (W 1, Vrai_bis, Faux_bis), Si (W 2, Vrai_bis, Faux_bis), Si (W 3, Vrai_bis, Faux_bis)), Si (W 4, Vrai_bis, Faux_bis), Si (W 5, Vrai_bis, Faux_bis)) ;; *)

let formule_cond = transforme formule_prop ;; 

(*On passe ensuite la formule conditionnelle en formule normale*)
let formule_norm = for_normale formule_cond ;;

(*On vérifie si c'est une tautologie*)
let formule_eval = eval formule_norm [] ;;


print_endline "Formule propositionnelle :" ;;
print_endline (affiche_prop formule_prop) ;;
print_endline "Formule conditionnelle :" ;;
print_endline (affiche_cond formule_cond) ;;
print_endline "Formule en forme normale :" ;;
print_endline (affiche_cond formule_norm) ;;
print_endline "Résultat de l'évaluation :" ;;
print_endline (affiche_eval formule_eval) ;;
