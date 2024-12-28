set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n =>
    match n with 
    | .zero => 0
    | .succ n => vsota_prvih n + (n + 1)

-- #eval vsota_prvih 100

theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) := by
  intros n
  induction n with 
    | zero => 
      simp [vsota_prvih]
    | succ n ih =>
      simp [vsota_prvih]
      simp [Nat.left_distrib]
      simp [ih]
      simp [Nat.left_distrib, Nat.right_distrib, Nat.two_mul, Nat.add_assoc]
      rw [Nat.add_comm n 1]
      rw [← Nat.add_assoc]
      rw [Nat.add_comm]
      -- Zna biti bolje resljivo s calc taktiko

theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 := by
  intros n
  induction n with 
  | zero => 
    simp [vsota_prvih]
  | succ n ih => 
    rw[← gauss]
    simp

/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

def obrni {A : Type} : {n : Nat} → Vektor A n → Vektor A n :=
  fun vec =>
  match vec with 
  | .prazen => Vektor.prazen
  | .sestavljen x xs => stakni (obrni xs) (.sestavljen x .prazen)

def glava {A : Type} {n : Nat} : Vektor A n → Option A :=
  fun vec =>
  match vec with
  | .prazen => Option.none
  | .sestavljen x _ => Option.some x

def rep {A : Type} {n : Nat} : Vektor A n → Option (Vektor A (n - 1)) :=
  fun vec =>
  match vec with
  | .prazen => Option.none
  | .sestavljen _ xs => Option.some xs 

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  by 
    apply Iff.intro 
    . intro h 
      apply And.intro 
      . intro hb 
        apply h 
        left
        assumption
      . intro hc 
        apply h 
        right
        assumption
    . intro h hbc 
      cases hbc
      . apply h.left 
        assumption
      . apply h.right 
        assumption

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) := by
  intros A
  intros P Q 
  . intro h
    . intro h1 
      intros x 
      exact h x (h1 x)

theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) := 
  by
    intro A
    intro P Q
    apply Iff.intro
    . intro R
      intro hR
      intro x
      apply R x hR
    . intro R
      intro x
      intro hR
      apply R hR x

theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) := by
    intro G P g
    apply Classical.byCases
    . intro obstaja
      exists g
    
    . intro pivec_pije_ostali_ne
      have ne_pijejo_vsi : ¬ ∀ (h : G), P h := by
        intro pijejo_vsi
        apply pivec_pije_ostali_ne
        intro _ 
        exact pijejo_vsi
      have nekdo_ne_pije : ∃ (i : G), ¬ P i := by
        apply Classical.not_forall.mp
        exact ne_pijejo_vsi
      have ⟨ p, nPp ⟩ := nekdo_ne_pije
      exists p
      intro Pp
      apply Classical.byContradiction
      intro _
      exact nPp Pp

/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A t
  induction t with 
  | prazno => simp [zrcali]
  | sestavljeno l x d ihl ihd => 
    simp [zrcali]
    rw [ihl]
    rw [ihd]
    simp

theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A t
  induction t with
  | prazno => 
    rw [zrcali]
  | sestavljeno l x d ihl ihd =>
    rw [zrcali]
    rw [visina]
    rw [ihl, ihd]
    rw [visina]
    rw [Nat.max_comm]

theorem lema_aux : ∀ {A : Type}, ∀ {t : Drevo A}, ∀ {lst : List A},
  elementi'.aux t lst = elementi t ++ lst := 
by
  intro A t
  induction t with 
  | prazno => 
    simp [elementi'.aux]
    simp [elementi]
  | sestavljeno l x d ihl ihd => 
    simp [elementi, elementi'.aux]
    intro lst
    rw [ihd]
    rw [← List.cons_append]
    rw [← ihl]

theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intro A t
  induction t with 
  | prazno =>
    rw [elementi]
    rw [elementi']
    rw [elementi'.aux]
  | sestavljeno l x d ihl ihd => 
    rw [elementi]
    rw [elementi']
    rw [lema_aux]
    simp [elementi]