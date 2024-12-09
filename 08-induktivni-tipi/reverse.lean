def reverse {A : Type} : List A -> List A := 
  fun xs => 
    match xs with 
    | [] => []
    | x :: xs' => reverse (xs') ++ [x]

def reverseAux {A : Type} : List A -> List A -> List A := 
  fun xs acc => 
    match xs with 
    | [] => acc
    | x :: xs' => reverseAux xs' (x :: acc)

def reverse' {A : Type} : List A -> List A := 
  fun xs => reverseAux xs []


  theorem pomozna {A : Type} : ∀ {lst : List A}, ∀ {acc : List A}, reverseAux lst acc = (reverse lst) ++ acc := 
    by 
      intro lst
      induction lst with 
      | nil => 
        intro acc
        simp [reverseAux, reverse]
      | cons x xs' ih => 
        intro acc
        simp [reverseAux, reverse]
        rw [ih]

  theorem reverse_eq_reverse' {A : Type} : ∀ {xs : List A}, reverse lst = reverse' lst :=
    by
      intro xs
      rw [reverse']
      rw [pomozna]
      sorry --to trditev smo ze na enih prejsnih vajah dokazali, dokaz je tam