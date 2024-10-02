def Agent := String
deriving Repr, BEq

inductive Message (σ : Nat) where
| empty : Message σ
| text : String → Message σ
| agent : Agent → Message σ
| symmetricKey : Agent → Agent → Message σ → Message σ
| publicKey : Agent → Message σ
| secretKey : Agent → Message σ
| encrypt : Message σ → Message σ → Message σ
| concat : Message σ → Message σ → Message σ
deriving Repr, BEq

notation " #μ " i => Message.empty i
notation " # " t " # " => Message.text t
notation " pk( " i " ) " => Message.publicKey i
notation " sk( " i " ) " => Message.secretKey i
notation " ⦃| " m " |⦄ " k  => Message.encrypt m k
notation " ag( " i " ) " => Message.agent i 
notation " text( " t " ) " => Message.text t 
notation m₁ " ‖ " m₂ => Message.concat m₁ m₂

inductive Formula (σ : Nat) where
| atom : Fin σ → Formula σ
| true : Formula σ 
| neg : Formula σ → Formula σ
| implies : Formula σ → Formula σ → Formula σ
| belief : Agent → Formula σ → Formula σ
| awareness : Agent → Message σ → Formula σ
| send : Agent → Agent → Message σ → Formula σ → Formula σ
| recv : Agent → Message σ → Formula σ → Formula σ
| gen : Agent → Message σ → Formula σ → Formula σ 
| fresh : Agent → Message σ → Formula σ 
deriving Repr, BEq 

notation " #ϕ " i => Formula.atom i
notation " ⊤ " => Formula.true 
notation " ~ " φ => Formula.neg φ
notation " ⊥ " => (~⊤)
notation φ " implies " ψ => Formula.implies φ ψ
notation φ " ⋁ " ψ => ((~φ) implies ψ)
notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))
notation " 𝔹 " i " , " φ => Formula.belief i φ
notation " 𝕏 " i " , " m => Formula.awareness i m
notation " Δ " i " , " m => Formula.fresh i m 
notation " 𝕂 " i " , " φ => (𝔹 i, φ) ⋀ φ 
notation " [send " i " , " j " (" μ " )] " φ => Formula.send i j μ φ
notation " [recv " i " (" μ ")]" φ => Formula.recv i μ φ
notation " [gen " i " (" μ ")]" φ => Formula.gen i μ φ 

def FreshMessage (m : Message σ) (la : List Agent) : Formula σ := 
  List.foldr (fun p q => p ⋁ q) ⊥ $ List.map (fun ag => (Δ ag, m)) la 

notation "Δ" m "[of " la "]" => FreshMessage m la 

-- def SupremumOverDeltaAgents (m : Message σ) (la : List Agent) : Bool := 
--   (List.map (fun ag => (Δ ag, m)) la).contains m

-- def SupremumOverDeltaAgentsAsFormula (a : Agent) (m : Message σ) (la : List Agent) : Formula σ :=
--   if SupremumOverDeltaAgents a m la then φ else (~φ)

notation " 𝔼 " i "[of " li "]" m => (𝕏 i, m) ⋀ (Δ m [of li])

variable { τ : Nat }
variable { m : Message σ }
def la : List Agent := [ "Alice", "Bob" ]
#check 𝔼 "Alice" [of la] m


-- notation φ " ⋁ " ψ => (~φ) implies ψ
-- notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))

/-
  **Proof system**
-/

def Context (σ : Nat) := List $ Formula σ

inductive Proof {σ : Nat} : Context σ → Formula σ → Prop  
| ax { Γ } { p : Formula σ } (h : Γ.Mem p) : Proof Γ p 
| pl₁ { Γ } { p q : Formula σ } : Proof Γ (p implies (q implies p))
| pl₂ { Γ } { p q r : Formula σ } : Proof Γ $ (p implies (q implies r)) implies ((p implies q) implies (p implies r)) 
| pl₃ { Γ } { p q : Formula σ } : Proof Γ $ ((~p) implies ~q) implies (((~p) implies q) implies p)
| KαSend { Γ } { φ ψ : Formula σ } {a b : Agent} { m : Message σ } : Proof Γ $ ([send a,b(m)](φ implies ψ)) implies (([send a,b(m)]φ) implies ([send a,b(m)]ψ))
| KαRecv { Γ } { φ ψ : Formula σ } {b : Agent} { m : Message σ } : Proof Γ $ ([recv b(m)](φ implies ψ)) implies (([recv b(m)]φ) implies ([recv b(m)]ψ))
| K𝔹 { Γ } { φ ψ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, (φ implies ψ)) implies ((𝔹 a, φ) implies (𝔹 a, ψ))
| D { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) implies ~(𝔹 a, (~φ))
| _4 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) implies (𝔹 a, (𝔹 a, φ)) 
| _5 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (~(𝔹 a, φ)) implies (𝔹 a, (~(𝔹 a, φ))) 
--
| MP { Γ } { p q : Formula σ } (hpq : Proof Γ $ p implies q) (hp : Proof Γ p) : Proof Γ q
| NECB { Γ } { φ : Formula σ } {a : Agent} (hφ : Proof Γ φ) : Proof Γ $ 𝔹 a, φ 
| NECSend { Γ } {φ : Formula σ} {a b : Agent} {m : Message σ} (hφ : Proof Γ φ) : Proof Γ $ [send a,b(m)]φ 
--
| FreshConst { Γ } {a : Agent} {m : Message σ} : Proof Γ $ (Δ a, m) implies (𝕏 a, m)
-- Natural Deduction
| AndLeft { Γ } {a : Agent} {φ ψ : Formula σ} (h : Proof Γ $ φ ⋀ ψ) : Proof Γ φ  
| AndRight { Γ } {a : Agent} {φ ψ : Formula σ} (h : Proof Γ $ φ ⋀ ψ) : Proof Γ ψ 
| AndIntro { Γ } {a : Agent} {φ ψ : Formula σ} (h₁ : Proof Γ $ φ) (h₂ : Proof Γ $ ψ) : Proof Γ $ φ ⋀ ψ 
| BDistOverConj { Γ } {a : Agent} {φ ψ : Formula σ} (h₁ : Proof Γ $ (𝔹 a, φ)) (h₂ : Proof Γ $ (𝔹 a, ψ)) : Proof Γ $ (𝔹 a, (φ ⋀ ψ))
| BDistFromConj_left { Γ } {a : Agent} {φ ψ : Formula σ} (h : Proof Γ $ 𝔹 a, (φ ⋀ ψ)) : Proof Γ $ 𝔹 a, φ 
| BDistFromConj_right { Γ } {a : Agent} {φ ψ : Formula σ} (h : Proof Γ $ 𝔹 a, (φ ⋀ ψ)) : Proof Γ $ 𝔹 a, ψ
| BMP { Γ } {a : Agent} {φ ψ : Formula σ} (h₀ : Proof Γ $ 𝔹 a, (φ implies ψ)) (h₁ : Proof Γ $ 𝔹 a, φ) : Proof Γ $ 𝔹 a, ψ 

notation Γ " ⊢ " φ => Proof Γ φ 

def World (σ : Nat) := Context σ 

structure Model (σ : Nat) := 
  Worlds : List $ World σ 
  R𝔹 : Agent → World σ → World σ → Bool 
  RPDLSend : Agent → Agent → Message σ → World σ → World σ → Bool 
  RPDLRecv : Agent → Message σ → World σ → World σ → Bool
  RPDLGen : Agent → Message σ → World σ → World σ → Bool 
  Valuation : Fin σ → World σ → Bool
  ValuationConstants : Agent → Message σ → World σ → Bool
  ValuationFresh : Agent → Message σ → World σ → Bool 
  BSerial : ∀ (a : Agent) (x : World σ), ∃ (y : World σ), R𝔹 a x y 
  BTrans : ∀ (a : Agent) (x : World σ) (y : World σ) (z : World σ), ((R𝔹 a x y ∧ R𝔹 a y z) → R𝔹 a x z)  
  BEuclid : ∀ (a : Agent) (x : World σ) (y : World σ) (z : World σ), ((R𝔹 a x y ∧ R𝔹 a x z) → R𝔹 a y z)
  FreshIsConstant : ∀ (a : Agent) (m : Message σ) (x : World σ), ((ValuationFresh a m x) → (ValuationConstants a m x))
  
@[simp]
def ModelSatisfiesInState {σ : Nat} (M : Model σ) (w : World σ) (φ : Formula σ) : Prop := 
  match φ with 
  | Formula.atom p => Model.Valuation M p w   
  | Formula.true => True 
  | 𝕏 a, m => Model.ValuationConstants M a m w
  | Δ a, m => Model.ValuationFresh M a m w 
  | ~φ => ¬ (ModelSatisfiesInState M w φ)
  | (φ implies ψ) => (ModelSatisfiesInState M w φ) → (ModelSatisfiesInState M w ψ)
  | 𝔹 a, φ => ∀ (v : World σ), ((Model.R𝔹 M a w v) → (ModelSatisfiesInState M v φ)) 
  | [send a,b(m)] φ => ∀ (v : World σ), ((Model.RPDLSend M a b m w v) → (ModelSatisfiesInState M v φ))
  | [recv b(m)] φ => ∀ (v : World σ), ((Model.RPDLRecv M b m w v) → (ModelSatisfiesInState M v φ))
  | [gen a(m)] φ => ∀ (v : World σ), (Model.RPDLGen M a m w v) → (ModelSatisfiesInState M v φ)
  

def List.subsetOf {α : Type} [BEq α] (l₀ : List α) (l₁ : List α) : Bool := 
  match l₀ with 
  | [] => True 
  | (head :: tail) => l₁.contains head && List.subsetOf tail l₁  

def List.equals {α : Type} [BEq α] (l₀ : List α) (l₁ : List α) : Bool :=
  l₀.subsetOf l₁ && l₁.subsetOf l₀

instance : BEq $ World σ where 
  beq v w := v.equals w 

@[simp]
def ModelSatisfies {σ : Nat} (M : Model σ) (φ : Formula σ) := 
  ∀ (w : World σ), M.Worlds.Mem w →  ModelSatisfiesInState M w φ 

@[simp]
def ModelSatisfiesContext {σ : Nat} (M : Model σ) (Γ : Context σ) : World σ → Prop := 
  fun (w : World σ) => ∀ (φ : Formula σ), ((Γ.Mem φ) → (ModelSatisfiesInState M w φ))

set_option allowUnsafeReducibility true

@[reducible]
inductive SemanticCsq {σ : Nat} (Γ : Context σ) (φ : Formula σ) : Prop :=
  | is_true (m : ∀ (M : Model σ) (w : World σ), (M.Worlds.Mem w) → ((ModelSatisfiesContext M Γ w) → ModelSatisfiesInState M w φ)) 

notation Γ " ⊧₀ " φ => SemanticCsq Γ φ 

open Classical 


@[simp]
theorem currying_uncurrying { p q : Prop } : (p ∧ q → r) ↔ (p → q → r) := by 
  apply Iff.intro 
  . intros h hp hq 
    exact h $ And.intro hp hq 
  . intros h₁ h₂ 
    exact (h₁ $ And.left h₂) $ And.right h₂ 

-- @[simp]
-- theorem forward {α : Type} {p : α → Prop} {y : α} (h : ∀ x, (p y → p x)) : p y → ∀ x, p x := by 
--   intro py 
--   intro x 
--   apply h
--   exact py 

-- @[simp]
-- theorem backward {a : Type} {p : α → Prop} {y : α} (h : p y → ∀ x, p x) : ∀ x, (p y → p x) := by 
--   intros x py 
--   apply (h py)   

theorem Soundness {σ : Nat} (Γ : Context σ) (φ : Formula σ) : (Γ ⊢ φ) → (Γ ⊧₀ φ) := by 
  intros h
  induction h 
  case ax ψ h₀ => 
    apply SemanticCsq.is_true; intros M w _ h₂; dsimp at h₂ 
    specialize h₂ ψ; 
    exact h₂ h₀ 
  case pl₁ p q =>
    apply SemanticCsq.is_true; intros M w _ h₂; dsimp at h₂ 
    dsimp at *; specialize h₂ p; intros h₃ _; exact h₃ 
  case pl₂ p q r => 
    apply SemanticCsq.is_true; intros M w _ _ ; dsimp at *
    intros h₃ h₄ h₅; exact (h₃ h₅) (h₄ h₅) 
  case pl₃ p q => 
    apply SemanticCsq.is_true; intros M w _ _ ; dsimp at * 
    intros h₃ h₄; apply byContradiction (fun (hp : ¬ModelSatisfiesInState M w p) => 
      let h₅ := h₃ hp ; let h₆ := h₄ hp ; show False from h₅ h₆)
  case KαSend φ ψ a b m => 
    apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
    intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
    intro h₄; exact (h₂ h₄) (h₃ h₄) 
  case KαRecv φ ψ b m => 
    apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
    intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
    intro h₄; exact (h₂ h₄) (h₃ h₄) 
  case K𝔹 φ ψ a => 
    apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
    intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
    intro h₄; exact (h₂ h₄) (h₃ h₄)
  case D φ a => 
    apply SemanticCsq.is_true; intros M w _ _; 
    intros h₀ h₁
    dsimp at * 
    let hSerial := M.BSerial a w
    apply Exists.elim hSerial 
    intro v 
    specialize h₀ v 
    specialize h₁ v 
    intro wRBv
    have := h₀ wRBv
    have := h₁ wRBv
    contradiction 
  case _4 φ a => 
    apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
    intros h₀ u h₂ v h₃; specialize h₀ v 
    let hTrans := M.BTrans a w u v; simp at hTrans 
    exact h₀ $ (hTrans h₂) h₃ 
  case _5 φ a => 
    apply SemanticCsq.is_true; intros M w _ _ 
    dsimp at * 
    intros h₀ u h₁ h₂
    let hEuclid := M.BEuclid a w u 
    simp [*] at h₀ 
    apply Exists.elim h₀ 
    intro t 
    specialize h₂ t 
    specialize hEuclid t 
    intro h₃ 
    have h₄ := And.left h₃ 
    have h₅ := And.intro h₁ h₄ 
    have h₆ := hEuclid h₅ 
    have h₇ := h₂ h₆ 
    have h₈ := And.right h₃ 
    contradiction 
  case MP p q h₂ h₃ h₄ h₅ =>
    apply SemanticCsq.is_true
    intros M w wmem ctt 
    cases h₄ with | is_true h₆ => 
    cases h₅ with | is_true h₇ =>
    specialize h₆ M w 
    specialize h₇ M w 
    let h₈ := (h₆ wmem) ctt 
    let h₉ := (h₇ wmem) ctt 
    dsimp at h₈ 
    exact h₈ h₉ 
  case NECB p a h₀ h₁ =>
    apply SemanticCsq.is_true
    intros M w mem ctt 
    intros v rel 
    cases h₁ with | is_true h₂ =>
    specialize h₂ M w mem ctt 
    have h := @SemanticCsq.is_true σ Γ (𝔹 a, φ)
    sorry 
  case NECSend p q r a h₀ h₁ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    intros v rel 
    simp [*] at * 
    specialize ctt p 
    cases h₁ with | is_true h₂ =>
    specialize h₂ M w mem 
    have ax := @Proof.ax σ Γ p 
    sorry 
  case FreshConst a m => 
    apply SemanticCsq.is_true 
    intros M w _ _ 
    dsimp at * 
    exact (M.FreshIsConstant a m w) 
  case AndLeft a p q h₀ h₁ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₃ => 
    skip 
    specialize h₃ M w mem ctt 
    simp [*] at * 
    exact And.left h₃ 
  case AndRight a p q h₀ h₁ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₃ => 
    specialize h₃ M w mem ctt 
    simp [*] at * 
    exact And.right h₃ 
  case AndIntro a p q h₀ h₁ h₂ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₃ => 
    cases h₂ with | is_true h₄ => 
    specialize h₃ M w mem ctt 
    specialize h₄ M w mem ctt 
    simp 
    trivial 
  case BDistOverConj a p q r h₀ h₁ h₂ =>
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₃ =>
    cases h₂ with | is_true h₄ =>
    specialize h₃ M w mem ctt 
    specialize h₄ M w mem ctt 
    simp 
    intro v 
    dsimp at h₃ 
    dsimp at h₄ 
    specialize h₃ v 
    specialize h₄ v 
    intro rel 
    have h₅ := h₃ rel 
    have h₆ := h₄ rel 
    trivial 
  case BDistFromConj_left a p r h₀ h₁ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₂ =>
    specialize h₂ M w mem ctt 
    simp [*] at * 
    intro v rel 
    specialize h₂ v
    have h₃ := h₂ rel 
    exact And.left h₃   
  case BDistFromConj_right a p r h₀ h₁ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₂ =>
    specialize h₂ M w mem ctt 
    simp [*] at * 
    intro v rel 
    specialize h₂ v
    have h₃ := h₂ rel 
    exact And.right h₃   
  case BMP _ a p r h₀ h₁ h₂ => 
    apply SemanticCsq.is_true 
    intros M w mem ctt 
    cases h₁ with | is_true h₃ =>
    cases h₂ with | is_true h₄ =>
    specialize h₃ M w mem ctt 
    specialize h₄ M w mem ctt 
    simp [*] at * 
    intro v rel 
    specialize h₃ v
    specialize h₄ v 
    have h₅ := h₃ rel
    have h₆ := h₄ rel 
    exact h₅ h₆ 


/-
  **Structural Rules for explicit knowledge**
-/

open Formula 
open Proof 

variable {a b b₁ b₂ : Agent}
variable {m m₁ m₂ k : Message σ}
variable {Γ : Context σ}


def X₁_1 : Formula σ := (𝕏 a, (m₁.concat m₂)) implies ((𝕏 a, m₁) ⋀ (𝕏 a, m₂))
def X₁_2 : Formula σ := ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) implies (𝕏 a, (m₁.concat m₂))
def X₂_1 : Formula σ := (𝕏 a, (Message.symmetricKey a b k)) implies (𝕏 b, (Message.symmetricKey b a k))
def X₂_2 : Formula σ := (𝕏 b, (Message.symmetricKey b a k)) implies (𝕏 a, (Message.symmetricKey a b k))
def X₃ : Formula σ := ((𝕏 a, ⦃|m|⦄ pk(b)) ⋀ (𝕏 a, sk(b))) implies (𝕏 a, m)
def X₄ : Formula σ := ((𝕏 a, ⦃|m|⦄ sk(b)) ⋀ (𝕏 a, pk(b))) implies (𝕏 a, m)
def X₅ : Formula σ := ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) implies 𝕏 a, ⦃|m₁|⦄m₂ 
def X₆ : Formula σ := ((𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) ⋀ (𝕏 a, (Message.symmetricKey a b k))) implies (𝕏 a, m)
def X₇ : Formula σ := (𝕏 a, ag(a))

/-
  **General Axioms for actions**
-/

variable {φ : Formula σ}

def H₀ : Formula σ := ([send b,a(m)]φ) implies ([recv a(m)]φ)
def H₁ : Formula σ := ([send b,a(m)] φ) implies (𝕏 b, m)
def H₂ : Formula σ := ([recv a(m)]φ) implies (𝕏 a, m)
def H₂' : Formula σ := ([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) implies (𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k))

def H₅ : Formula σ := (([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) ⋀ (𝔹 a, (𝕏 a, m))) implies 𝔹 a, ([send b,a(m)]φ)

/-
  **Secret key axiom**
-/

def SK : Formula σ := (𝕏 a, (Message.symmetricKey a b k)) ⋀ (𝕏 b, (Message.symmetricKey a b k))

/-
  **BAN Logic Theory**
-/

open Formula 
open Proof 

variable {a b : Agent}
variable {m : Message σ}
variable {φ : Formula σ}
variable {Γ : Context σ}

def H₀B : Formula σ := (([send b,a(m)] φ) ⋀ (Δ m [of [a, b]])) implies ([recv a(m)] φ)
def H₃B : Formula σ := ([gen b(m)]φ) implies ((Δ m [of [a,b]]))


def BANTheory : Context σ := 
[
  @H₀B σ a b m φ, 
  @H₁ σ a b m φ, 
  @H₂ σ a m φ,
  @H₂' σ a b m k φ,
  @H₃B σ a b m φ,
  @H₅ σ a b m k φ,
  @SK σ a b k,
  @X₁_1 σ a m₁ m₂,
  @X₆ σ a b m k
] 

theorem NV {a b : Agent} { m : Message σ } : 
      ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (Δ m [of [a, b]])) 
    → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ (𝔹 a, ([send b, a(m)]φ))) 
    → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ (𝔹 a, (𝔼 b [of [a,b]] m))) := by 
  intros h₁ h₂  
  have h₁t  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ ([send b,a(m)] φ) implies (𝕏 b, m) := by repeat constructor 
  have h₁tn : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (([send b,a(m)] φ) implies (𝕏 b, m)) := NECB h₁t 
  have h₁₉  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝕏 b, m) := BMP h₁tn h₂ 
  have h₂₀  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, ((𝕏 b, m) ⋀ (Δ m [of [a, b]])) := BDistOverConj h₁₉ h₁
  have h₂₁  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, 𝔼 b [of [a, b]] m := h₂₀ 
  exact h₂₁  

def JR : Formula σ := (𝔹 a, ([gen b(m)]φ)) ⋀ (𝔹 a, (𝔼 b [of [a, b]] m)) implies (𝔼 a [of [a, b]] m)

theorem JR_with_assumptions {a b : Agent} {m : Message σ } : 
    ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, ([gen b(m)]φ))
  → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝔼 b [of [a, b]] m))
  → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ [recv a(m)]φ)
  → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝔼 a [of [a, b]] m)) := by 
  intros h₀ _ h₃ 
  have h₃b  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ ([gen b(m)]φ) implies ((Δ m [of [a,b]])) := by repeat constructor 
  have h₃bn : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (([gen b(m)]φ) implies ((Δ m [of [a,b]]))) := NECB h₃b 
  have h₂   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (Δ m [of [a,b]]) := BMP h₃bn h₀ 
  have h₁t  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ ([recv a(m)]φ) implies (𝕏 a, m) := by repeat constructor 
  have h₃   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝕏 a, m := MP h₁t h₃ 
  have h₃n  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝕏 a, m) := NECB h₃ 
  have h₄   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, ((𝕏 a, m) ⋀ (Δ m [of [a,b]])) := BDistOverConj h₃n h₂ 
  have h₅   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝔼 a [of [a, b]] m) := h₄ 
  exact h₅ 


theorem MMSK {a b : Agent} {m k : Message σ} :
    ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ [recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ)
  → ((@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, ([send b,a(m)]φ)) := by 
  intros h₀ 
  have h₁   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ ([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) implies 𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k) := by repeat constructor 
  have h₁n  : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) implies 𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) := NECB h₁ 
  have h₂   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ (𝔹 a, ([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ)) implies 𝔹 a, (𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) := MP K𝔹 h₁n 
  have h₃   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢  𝔹 a, (𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) := MP h₂ (NECB h₀)
  have sk   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ (𝕏 a, (Message.symmetricKey a b k)) ⋀ (𝕏 b, (Message.symmetricKey a b k)) := by repeat constructor 
  have hskb : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝕏 a, (Message.symmetricKey a b k)) := NECB $ @AndLeft σ (@BANTheory σ m₁ m₂ k a b m φ) a (𝕏 a, (Message.symmetricKey a b k)) (𝕏 b, (Message.symmetricKey a b k)) sk
  have h₄   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, ((𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) ⋀ (𝕏 a, (Message.symmetricKey a b k))) := BDistOverConj h₃ hskb 
  have x₆   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ ((𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) ⋀ (𝕏 a, (Message.symmetricKey a b k))) implies (𝕏 a, m) := by repeat constructor 
  have h₅   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ 𝔹 a, (𝕏 a, m) := MP (MP K𝔹 (NECB x₆)) h₄ 
  have h₆   : (@BANTheory σ m₁ m₂ k a b m φ) ⊢ (([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) ⋀ (𝔹 a, (𝕏 a, m))) implies 𝔹 a, ([send b,a(m)]φ) := by repeat constructor 
  exact MP h₆ (@AndIntro σ (@BANTheory σ m₁ m₂ k a b m φ) a ([recv a(⦃|m|⦄ (Message.symmetricKey a b k))]φ) (𝔹 a, (𝕏 a, m)) h₀ h₅)


def SC₁ : Formula σ := 𝔹 a, ([send b, a(m₁.concat m₂)]φ) implies (𝔹 a, [send b,a(m₁)]φ)
def SC₂ : Formula σ := ([recv a(m₁.concat m₂)]φ) implies ([recv a(m₁)]φ)
/-
  **Generated model section**
-/


def State (σ : Nat) := List (List $ Message σ)

def EmptyMessage (σ : Nat) : Message σ := Message.empty
def EmptyState {σ : Nat} : State σ := [[]]

structure AutomaticallyGeneratedModel (σ : Nat) :=
  Agents : List Agent
  States : List $ State σ
  R𝕂 : List $ (Agent × List Nat)
  R𝔹 : List $ (Agent × List Nat)
  RPDLSend : List $ (Agent × Agent × Message σ × List Nat)
  RPDLRecv : List $ (Agent × Message σ × List Nat)
  RPDLGen : List $ (Agent × Message σ × List Nat)

def List.getAtIndex {α : Type} (list : List α) (i : Nat) : Option α :=
  match i with
  | 0 => list.head?
  | i' + 1 => List.getAtIndex (list.tail!) i'

def List.getAtIndex! {α : Type} (list : List α) (i : Nat) (default : α) : α :=
  match list.getAtIndex i with
  | none => default
  | some result => result

def MessageContext (σ : Nat) := List $ Message σ

def DeductionClosureStep {σ : Nat} (Γ : MessageContext σ) (Γc : MessageContext σ) : MessageContext σ :=
  match Γ with 
  | [] => [] 
  | (m :: tail) => match m with 
    | ⦃|m'|⦄k => if Γc.contains k && !Γc.contains m' then m' :: m :: DeductionClosureStep tail Γc else m :: DeductionClosureStep tail Γc
    | m₁ ‖ m₂ => 
    if Γc.contains (m₁ ‖ m₂) then 
      if Γc.contains m₁ then 
        if Γc.contains m₂ then 
          m :: DeductionClosureStep tail Γc 
        else 
          m :: m₂ :: DeductionClosureStep tail Γc 
      else 
        if Γc.contains m₂ then 
          m :: m₁ :: DeductionClosureStep tail Γc 
        else 
          m :: m₁ :: m₂ :: DeductionClosureStep tail Γc 
    else m :: DeductionClosureStep tail Γc 
    | _ => m :: DeductionClosureStep tail Γc

set_option maxHeartbeats 800000

def DeductionClosure {σ : Nat} (Γ : MessageContext σ) : MessageContext σ := 
  let Γ₀ := DeductionClosureStep Γ Γ
  let Γ₁ := DeductionClosureStep Γ₀ Γ₀ 
  let Γ₂ := DeductionClosureStep Γ₁ Γ₁ 
  Γ₂ 


def MessageInfer {σ : Nat} (Γ : MessageContext σ) (m : Message σ) : Bool := 
  let Γ' := DeductionClosure Γ
  match m with 
  | Message.empty => True
  | m₁ ‖ m₂ => Γ'.contains (m₁ ‖ m₂) || (Γ'.contains m₁ && Γ'.contains m₂) 
  | ⦃|m₁|⦄m₂ => Γ'.contains (⦃|m₁|⦄m₂) || (Γ'.contains m₁ && Γ'.contains m₂)
  | sk(i) => Γ'.contains $ sk(i)
  | pk(i) => Γ'.contains $ pk(i)
  | ag(i) => Γ'.contains $ ag(i)
  | text(t) => Γ'.contains $ text(t)
  | Message.symmetricKey i j k => Γ'.contains $ Message.symmetricKey i j k 

notation Γ " ⊢μ " m => MessageInfer Γ m 

def AwarenessSatisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (m : Message σ) : Bool := 
  let modelAgents : List Agent := M.Agents
  let numberOfAgents : Nat := modelAgents.length
  let zippedAgentList := List.zip modelAgents $ List.range numberOfAgents
  let agentStatePosition : Nat := ((zippedAgentList.filter (fun (ag, _) => ag == agent)).map (fun (_, pos) => pos)).getAtIndex! 0 0
  let currentState : State σ := M.States.getAtIndex! wIndex EmptyState 
  let currentAgentState := currentState.getAtIndex! agentStatePosition []
  currentAgentState ⊢μ m 

def ModalKBStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (relation : List $ (Agent × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (ag, _) => ag == agent)).map (fun (_, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 


def PDLSendStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (i : Agent) (j : Agent) (m : Message σ) (relation : List $ (Agent × Agent × Message σ × List Nat)) : List Nat := 
  let agentRelation : List $ List Nat := ((relation.filter (fun (agi, agj, msg, _) => agi == i && agj == j && msg == m)).map (fun (_, _, _, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 

def PDLRecvStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 

def PDLGenStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 

def SatisfiesAtState {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) (wIndex : Nat) : Bool :=
  match φ with
  | Formula.atom _ => True 
  | Formula.true => True 
  | φ implies ψ => (SatisfiesAtState M φ wIndex) → (SatisfiesAtState M ψ wIndex)
  | ~φ => !(SatisfiesAtState M φ wIndex) 
  | 𝕏 agent, m => AwarenessSatisfies M wIndex agent m  
  | Δ agent, m => AwarenessSatisfies M wIndex agent m 
  | 𝔹 agent, φ => 
    let accessibleStates := ModalKBStates M wIndex agent M.R𝔹
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | [send i, j(m)] φ => 
    let accessibleStates := PDLSendStates M wIndex i j m M.RPDLSend
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | [recv j(m)] φ => 
    let accessibleStates := PDLRecvStates M wIndex j m M.RPDLRecv 
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | [gen i(m)] φ => 
    let accessibleStates := PDLGenStates M wIndex i m M.RPDLGen
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 

notation M " at " w " ⊧ " φ => SatisfiesAtState M φ w

def Satisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) : Bool := 
  let allStates := List.range $ M.States.length 
  let satisfiesAllStates := allStates.map (fun state => M at state ⊧ φ)
  satisfiesAllStates.foldr (fun x y => x && y) True 

notation M " ⊧ " φ => Satisfies M φ 

/-
  **Generate model**
-/

structure ProtocolAction (σ : Nat) := 
  Sender: Agent
  Receiver: Agent
  Message: Message σ 

instance EmptyProtocolAction {σ : Nat} : ProtocolAction σ := 
{
  Sender := "",
  Receiver := "",
  Message := Message.empty 
}  

structure Protocol (σ : Nat) :=
  Agents : List Agent 
  SymmetricKeys : List $ (Agent × Agent × Message σ)
  Specification : List $ ProtocolAction σ 

def GetAllSubMessages {σ : Nat} (m : Message σ) : List $ Message σ := 
  match m with 
  | Message.empty => [] 
  | text(t) => [text(t) ]
  | ag(i) => [ag(i) ]
  | Message.symmetricKey k i j => [Message.symmetricKey k i j]
  | pk(i) => [pk(i) ]
  | sk(i) => [sk(i) ]
  | ⦃|m|⦄k => GetAllSubMessages m ++ [k] 
  | m₁ ‖ m₂ => GetAllSubMessages m₁ ++ GetAllSubMessages m₂   

def GetAllMessagesFromList {σ : Nat} (list : List $ Message σ) : List $ Message σ := 
  match list with 
  | [] => [] 
  | (message :: tail) => 
    match message with 
    | Message.empty => tail 
    | text(t) => text(t) :: tail 
    | ag(i) => ag(i) :: tail 
    | Message.symmetricKey k i j => (Message.symmetricKey k i j) :: tail 
    | pk(i) => pk(i) :: tail 
    | sk(i) => sk(i) :: tail 
    | ⦃|m|⦄k => GetAllSubMessages (⦃|m|⦄k) ++ [⦃|m|⦄k] ++ tail 
    | m₁ ‖ m₂ => GetAllSubMessages (m₁ ‖ m₂) ++ [m₁ ‖ m₂] ++ tail 

def List.removeDuplicates {α : Type} [BEq α] (list : List α) : List α := 
  match list with 
  | [] => []
  | (head :: tail) => if tail.contains head then tail else head :: tail 

def AppendAgentNewKnowledge {σ : Nat} (P : Protocol σ) (agent : Agent) (currentState : State σ) (newKnowledge : List $ Message σ) : State σ := 
  let agentsNumber := P.Agents.length 
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber
  let agentPosition := ((agentsPositions.filter (fun (ag, _) => ag == agent)).map (fun (_, pos) => pos)).getAtIndex! 0 0
  let stateForAgents := currentState.zip $ List.range $ agentsNumber 
  let newState := stateForAgents.map (fun (ik, pos) => 
    if pos == agentPosition then (ik.append newKnowledge).removeDuplicates else ik 
  )
  newState

def BuildFromActions {σ : Nat} (P : Protocol σ) (currentStateIndex : Nat) (states : List $ State σ) (statesLeft : Nat)
  : (List $ State σ) 
  × (List $ (Agent × Agent × Message σ × List Nat)) 
  × (List $ (Agent × Message σ × List Nat)) := 
  match statesLeft with 
  | 0 => ([], [], [])
  | n + 1 => 
    let currentAction := P.Specification.getAtIndex! currentStateIndex ({ Sender := "", Receiver := "", Message := Message.empty })
    let sender := currentAction.Sender 
    let receiver := currentAction.Receiver 
    let message := currentAction.Message 
    let lastState := states.getAtIndex! (states.length - 1) EmptyState 
    let newState := AppendAgentNewKnowledge P sender lastState [message] 
  
    let newUpdatedState := 
      if currentStateIndex != 0 then 
        let lastAction := P.Specification.getAtIndex! (currentStateIndex - 1) ({ Sender := "", Receiver := "", Message := Message.empty })
        let lastReceiver := lastAction.Receiver 
        let lastMessage := lastAction.Message 
        AppendAgentNewKnowledge P lastReceiver newState [lastMessage]
      else newState 

    (newUpdatedState :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).fst, 
    if message != Message.empty then 
      ((sender, receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst) 
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst,
    if message != Message.empty then 
      ((receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd) 
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd
    )

def BuildModel {σ : Nat} (P : Protocol σ) : AutomaticallyGeneratedModel σ := 
  let specification := P.Specification 
  let agentsNumber := P.Agents.length 
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber

  let initialAction := specification.getAtIndex! 0 EmptyProtocolAction
  let agentsInitialKnowledgeEmpty : List $ List $ Message σ := List.replicate agentsNumber [] 
  let initialAgentPosition := ((agentsPositions.filter (fun (ag, _) => ag == initialAction.Sender)).map (fun (_, pos) => pos)).getAtIndex! 0 0

  let agentsInitialKnowledge := ((agentsInitialKnowledgeEmpty.zip (List.range agentsNumber)).map (fun (ik, agentPos) => 
    if agentPos == initialAgentPosition then ik.append [initialAction.Message] else ik.append []))

  let agentsInitialKnowledgeKeys := (agentsInitialKnowledge.zip (List.range agentsNumber)).map (fun (ik, pos) => 
    let agentByPos := ((agentsPositions.filter (fun ((_ : Agent), y) => y == pos)).map (fun ((x : Agent), (_ : Nat)) => x)).getAtIndex! 0 ""
    let searchInSymmetricKeys := P.SymmetricKeys.filter (fun ((x : Agent), (y : Agent), (_ : Message σ)) => x == agentByPos || y == agentByPos)
    let key := if searchInSymmetricKeys.length > 0 then (searchInSymmetricKeys.getAtIndex! 0 (("", "", Message.empty) : Agent × Agent × Message σ)).snd.snd else Message.empty 
    let otherAgentsPublicKeys : List $ Message σ := (P.Agents.filter (fun ag => ag != agentByPos)).map (fun ag => pk(ag))
    if key != Message.empty then (ik.append [key, sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys else (ik.append [sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys
    )
  
  let initialState : State σ := agentsInitialKnowledgeKeys

  let result := BuildFromActions P 0 [initialState] (specification.length + 1)

  let states := result.fst 
  let pdlRelationSend := result.snd.fst 

  let firstOccuranceForEveryAgent := P.Agents.map (fun agent => 
    let firstState : Nat := (((pdlRelationSend.filter (fun (ag, _, _, _) => ag == agent)).map (fun (_, _, _, ls) => ls)).getAtIndex! 0 []).getAtIndex! 0 0 
    (agent, firstState)
  )

  let numberOfStates := states.length 

  let knowledge_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) => 
    let allStates := List.range numberOfStates 
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x <= y then [x, y] else []))))
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => list.getAtIndex! 0 0 >= initialAgentState) 
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != [])
  )

  let knowledge := List.foldr (fun x y => x ++ y) [] knowledge_relation 

  let belief_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) => 
    let allStates := List.range numberOfStates 
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x < y then [x, y] else [])))) ++ [[allStates.getAtIndex! (allStates.length - 1) 0, allStates.getAtIndex! (allStates.length - 1) 0]]
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => list.getAtIndex! 0 0 >= initialAgentState) 
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != [])
  )

  let belief := List.foldr (fun x y => x ++ y) [] belief_relation 

  {
    Agents := P.Agents,
    States := states,
    R𝕂 := knowledge,
    R𝔹 := belief,
    RPDLSend := pdlRelationSend,
    RPDLRecv := result.snd.snd,
    RPDLGen := [],
  }

/-
  **OSS**
-/

section OSS
  instance OSS {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r"]
    SymmetricKeys := []
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|#"i"# ‖ #"ni"#|⦄pk("r") }
    ]
  }

  def OSSModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSS

  #reduce OSSModel 

  #reduce OSSModel ⊧ 𝕏 "i", #"ni"#

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] (𝕏 "r", (⦃|#"i"# ‖ #"ni"#|⦄pk("r")))

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

  

end OSS

section OSSE
  instance OSSE {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := []
    Specification := [
      { Sender := "e", Receiver := "r", Message := ⦃|#"i"# ‖ #"ne"#|⦄pk("r") }
    ]
  }

  def OSSEModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSSE

  #reduce OSSEModel 

  #reduce OSSEModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

end OSSE

/-
  **Needham Schroeder**
-/

section NeedhamSchroeder
  instance NeedhamSchroeder {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r"]
    SymmetricKeys := [] 
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "r", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroeder

  #reduce NeedhamSchroederModel

  #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ((𝕂 "r", 𝕏 "i", #"ni"#) ⋀ (𝕂 "i", 𝕏 "r", #"ni"#))
  -- true

  -- #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ([recv "i"(⦃|#"ni"# ‖ #"nr"# |⦄pk("i"))] 𝕂 "i", 𝕏 "r", #"nr"#)
  -- true 

end NeedhamSchroeder

section NeedhamSchroederMitM
  instance NeedhamSchroederMitM {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := [] 
    Specification := [
      { Sender := "i", Receiver := "e", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "e", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("e") },
      { Sender := "e", Receiver := "i", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "e", Message := ⦃|#"nr"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederMitMModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroederMitM

  #reduce NeedhamSchroederMitMModel

  -- #reduce NeedhamSchroederMitMModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] 𝕂 "r", 𝕏 "i", #"ni"#
  -- true 

  -- #reduce NeedhamSchroederMitMModel ⊧ 𝕂 "i", 𝕏 "r", #"ni"#
  -- false 
end NeedhamSchroederMitM
