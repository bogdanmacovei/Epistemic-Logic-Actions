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
| neg : Formula σ → Formula σ
| implies : Formula σ → Formula σ → Formula σ
| belief : Agent → Formula σ → Formula σ
| awareness : Agent → Message σ → Formula σ
| send : Agent → Agent → Message σ → Formula σ → Formula σ
| recv : Agent → Message σ → Formula σ → Formula σ
deriving Repr, BEq 

notation " #ϕ " i => Formula.atom i
notation " ~ " φ => Formula.neg φ
notation φ " ⊃ " ψ => Formula.implies φ ψ
notation φ " ⋁ " ψ => ((~φ) ⊃ ψ)
notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))
notation " 𝔹 " i " , " φ => Formula.belief i φ
notation " 𝕏 " i " , " m => Formula.awareness i m
notation " 𝕂 " i " , " φ => (𝔹 i, φ) ⋀ φ 
notation " [send " i " , " j " (" μ " )] " φ => Formula.send i j μ φ
notation " [recv " i " (" μ ")]" φ => Formula.recv i μ φ

notation φ " ⋁ " ψ => (~φ) ⊃ ψ
notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))

/-
  **Proof system**
-/

def Context (σ : Nat) := List $ Formula σ

inductive Proof {σ : Nat} : Context σ → Formula σ → Prop  
| ax { Γ } { p : Formula σ } (h : Γ.contains p) : Proof Γ p 
| pl₁ { Γ } { p q : Formula σ } : Proof Γ (p ⊃ (q ⊃ p))
| pl₂ { Γ } { p q r : Formula σ } : Proof Γ $ (p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)) 
| pl₃ { Γ } { p q : Formula σ } : Proof Γ $ ((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p)
| KαSend { Γ } { φ ψ : Formula σ } {a b : Agent} { m : Message σ } : Proof Γ $ ([send a,b(m)](φ ⊃ ψ)) ⊃ (([send a,b(m)]φ) ⊃ ([send a,b(m)]ψ))
| KαRecv { Γ } { φ ψ : Formula σ } {b : Agent} { m : Message σ } : Proof Γ $ ([recv b(m)](φ ⊃ ψ)) ⊃ (([recv b(m)]φ) ⊃ ([recv b(m)]ψ))
| K𝔹 { Γ } { φ ψ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, (φ ⊃ ψ)) ⊃ ((𝔹 a, φ) ⊃ (𝔹 a, ψ))
| D { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⊃ ~(𝔹 a, (~φ))
| _4 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⊃ (𝔹 a, (𝔹 a, φ)) 
| _5 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (~(𝔹 a, φ)) ⊃ (𝔹 a, (~(𝔹 a, φ))) 
--
| MP { Γ } { p q : Formula σ } (hpq : Proof Γ $ p ⊃ q) (hp : Proof Γ p) : Proof Γ q
| NECB { Γ } { φ : Formula σ } {a : Agent} (hφ : Proof Γ φ) : Proof Γ $ 𝔹 a, φ 

notation Γ " ⊢ " φ => Proof Γ φ 

def World (σ : Nat) := Context σ 

structure Model (σ : Nat) := 
  Worlds : List $ World σ 
  R𝔹 : Agent → World σ → World σ → Bool 
  RPDLSend : Agent → Agent → Message σ → World σ → World σ → Bool 
  RPDLRecv : Agent → Message σ → World σ → World σ → Bool
  Valuation : Fin σ → World σ → Bool
  ValuationConstants : Agent → Message σ → World σ → Bool    
  BSerial : ∀ (a : Agent) (x : World σ), ∃ (y : World σ), R𝔹 a x y 
  BTrans : ∀ (a : Agent) (x : World σ) (y : World σ) (z : World σ), ((R𝔹 a x y ∧ R𝔹 a y z) → R𝔹 a x z)  
  BEuclid : ∀ (a : Agent) (x : World σ) (y : World σ) (z : World σ), ((R𝔹 a x y ∧ R𝔹 a x z) → R𝔹 a y z) 
  
@[simp]
def ModelSatisfiesInState {σ : Nat} (M : Model σ) (w : World σ) (φ : Formula σ) : Prop := 
  match φ with 
  | Formula.atom p => Model.Valuation M p w   
  | 𝕏 a, m => Model.ValuationConstants M a m w 
  | ~φ => ¬ (ModelSatisfiesInState M w φ)
  | φ ⊃ ψ => (ModelSatisfiesInState M w φ) → (ModelSatisfiesInState M w ψ)
  | 𝔹 a, φ => ∀ (v : World σ), ((Model.R𝔹 M a w v) → (ModelSatisfiesInState M v φ)) 
  | [send a,b(m)] φ => ∀ (v : World σ), ((Model.RPDLSend M a b m w v) → (ModelSatisfiesInState M v φ))
  | [recv b(m)] φ => ∀ (v : World σ), ((Model.RPDLRecv M b m w v) → (ModelSatisfiesInState M v φ))
  

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
  ∀ (w : World σ), M.Worlds.contains w →  ModelSatisfiesInState M w φ 

@[simp]
def ModelSatisfiesContext {σ : Nat} (M : Model σ) (Γ : Context σ) : World σ → Prop := 
  fun (w : World σ) => ∀ (φ : Formula σ), ((Γ.contains φ) → (ModelSatisfiesInState M w φ))

@[reducible]
inductive SemanticCsq {σ : Nat} (Γ : Context σ) (φ : Formula σ) : Prop :=
  | is_true (m : ∀ (M : Model σ) (w : World σ), (M.Worlds.contains w) → ((ModelSatisfiesContext M Γ w) → ModelSatisfiesInState M w φ)) 

notation Γ " ⊧₀ " φ => SemanticCsq Γ φ 

open Classical 


@[simp]
theorem currying_uncurrying { p q : Prop } : (p ∧ q → r) ↔ (p → q → r) := by 
  apply Iff.intro 
  . intros h hp hq 
    exact h $ And.intro hp hq 
  . intros h₁ h₂ 
    exact (h₁ $ And.left h₂) $ And.right h₂ 

@[simp]
theorem forward {α : Type} {p : α → Prop} {y : α} (h : ∀ x, (p y → p x)) : p y → ∀ x, p x := by 
  intro py 
  intro x 
  apply h
  exact py 

@[simp]
theorem backward {a : Type} {p : α → Prop} {y : α} (h : p y → ∀ x, p x) : ∀ x, (p y → p x) := by 
  intros x py 
  apply (h py)   

-- theorem Soundness {σ : Nat} (Γ : Context σ) (φ : Formula σ) : (Γ ⊢ φ) → (Γ ⊧₀ φ) := by 
--   intros h
--   induction h 
--   case ax ψ h₀ => 
--     apply SemanticCsq.is_true; intros M w _ h₂; dsimp at h₂ 
--     specialize h₂ ψ; exact h₂ h₀ 
--   case pl₁ p q =>
--     apply SemanticCsq.is_true; intros M w _ h₂; dsimp at h₂ 
--     dsimp at *; specialize h₂ p; intros h₃ _; exact h₃ 
--   case pl₂ p q r => 
--     apply SemanticCsq.is_true; intros M w _ _ ; dsimp at *
--     intros h₃ h₄ h₅; exact (h₃ h₅) (h₄ h₅) 
--   case pl₃ p q => 
--     apply SemanticCsq.is_true; intros M w _ _ ; dsimp at * 
--     intros h₃ h₄; apply byContradiction (fun (hp : ¬ModelSatisfiesInState M w p) => 
--       let h₅ := h₃ hp ; let h₆ := h₄ hp ; show False from h₅ h₆)
--   case KαSend φ ψ a b m => 
--     apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
--     intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
--     intro h₄; exact (h₂ h₄) (h₃ h₄) 
--   case KαRecv φ ψ b m => 
--     apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
--     intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
--     intro h₄; exact (h₂ h₄) (h₃ h₄) 
--   case K𝔹 φ ψ a => 
--     apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
--     intros h₂ h₃ v; specialize h₂ v; specialize h₃ v 
--     intro h₄; exact (h₂ h₄) (h₃ h₄)
--   case D φ a => 
--     apply SemanticCsq.is_true; intros M w _ _; 
--     intros h₀ h₁
--     dsimp at * 
--     let hEuclid := M.BEuclid a w w w 
--     sorry 
--   case _4 φ a => 
--     apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
--     intros h₀ u h₂ v h₃; specialize h₀ v 
--     let hTrans := M.BTrans a w u v; simp at hTrans 
--     exact h₀ $ (hTrans h₂) h₃ 
--   case _5 φ a => 
--     apply SemanticCsq.is_true; intros M w _ _; dsimp at * 
--     intros h₀ u h₁ h₂
--     let hTrans := M.BTrans a w u 
--     simp [*] at hTrans 
--     let hAnd := And.intro h₁ h₂ 
--     simp [*] at hAnd 
--     sorry 
--   case MP p q h₂ h₃ h₄ h₅ =>
--     apply SemanticCsq.is_true; intros M w th₀ th₁ 
--     have hmp := Proof.MP h₂ h₃ 
--     have hSound := Soundness Γ q 
--     have hq := hSound hmp 
--     induction hq with 
--     | is_true ih => 
--       specialize ih M w 
--       exact (ih th₀) th₁ 
--   case NECB p a h₀ h₁ =>
--     apply SemanticCsq.is_true; intros M w th₀ th₁ 
--     dsimp at * 
--     specialize th₁ p 
--     intros v hv 
--     sorry 





#check ModelSatisfiesInState

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

def ModalKBStates {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (relation : List $ (Agent × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (ag, _) => ag == agent)).map (fun (_, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 


def PDLSendStates {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (i : Agent) (j : Agent) (m : Message σ) (relation : List $ (Agent × Agent × Message σ × List Nat)) : List Nat := 
  let agentRelation : List $ List Nat := ((relation.filter (fun (agi, agj, msg, _) => agi == i && agj == j && msg == m)).map (fun (_, _, _, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 

def PDLRecvStates {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => list.getAtIndex! 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => list.getAtIndex! 1 0)
  accessibleStates 

def SatisfiesAtState {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) (wIndex : Nat) : Bool :=
  match φ with
  | Formula.atom _ => True 
  | φ ⊃ ψ => (SatisfiesAtState M φ wIndex) → (SatisfiesAtState M ψ wIndex)
  | ~φ => !(SatisfiesAtState M φ wIndex) 
  | 𝕏 agent, m => AwarenessSatisfies M wIndex agent m  
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
    let agentByPos := ((agentsPositions.filter (fun ((x : Agent), y) => y == pos)).map (fun ((x : Agent), (_ : Nat)) => x)).getAtIndex! 0 ""
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
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x < y then [x, y] else []))))
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

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

end OSS

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