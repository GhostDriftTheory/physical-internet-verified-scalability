import Std

set_option autoImplicit false

/-
Physical Internet Verified Scalability Core v1.0

This single Lean 4 file formalizes a structural claim, not a historical one.
It does not prove that a named product is uniquely necessary.  It proves
general facts about public packet observations, exact public release,
semantic sufficiency, portable evidence sufficiency, path independence,
trace composition, non-replay, and field necessity counterexamples.
-/

namespace PhysicalInternet

universe u v w q r

/-!
## 1. General sufficiency and factorization

An observation is sufficient for a family of decisions when two states with
the same observation cannot be separated by any decision in that family.
The quotient below is the ordinary observation quotient; the canonical
decision quotient is introduced in the next section.
-/

def Sufficient
    {X : Type u} {Z : Type v} {Y : Type w}
    (obs : X -> Z) (family : (X -> Y) -> Prop) : Prop :=
  forall x y, obs x = obs y -> forall f, family f -> f x = f y

def PredicateSufficient
    {X : Type u} {Z : Type v}
    (obs : X -> Z) (p : X -> Prop) : Prop :=
  forall x y, obs x = obs y -> (p x <-> p y)

def FactorsThrough
    {X : Type u} {Z : Type v} {Y : Type w}
    (obs : X -> Z) (f : X -> Y) : Prop :=
  exists g : Z -> Y, forall x, f x = g (obs x)

theorem factors_imply_sufficient
    {X : Type u} {Z : Type v} {Y : Type w}
    {obs : X -> Z} {family : (X -> Y) -> Prop}
    (hFactors : forall f, family f -> FactorsThrough obs f) :
    Sufficient obs family := by
  intro x y hxy f hf
  cases hFactors f hf with
  | intro g hg =>
      calc
        f x = g (obs x) := hg x
        _ = g (obs y) := congrArg g hxy
        _ = f y := (hg y).symm

def ObsRel
    {X : Type u} {Z : Type v}
    (obs : X -> Z) : X -> X -> Prop :=
  fun x y => obs x = obs y

def ObsSetoid
    {X : Type u} {Z : Type v}
    (obs : X -> Z) : Setoid X where
  r := ObsRel obs
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact Eq.trans hxy hyz

def ObsQuot
    {X : Type u} {Z : Type v}
    (obs : X -> Z) : Type u :=
  Quotient (ObsSetoid obs)

def toObsQuot
    {X : Type u} {Z : Type v}
    (obs : X -> Z) (x : X) : ObsQuot obs :=
  Quotient.mk (ObsSetoid obs) x

def factorOnQuot
    {X : Type u} {Z : Type v} {Y : Type w}
    {obs : X -> Z} (f : X -> Y)
    (hConst : forall x y, ObsRel obs x y -> f x = f y) :
    ObsQuot obs -> Y :=
  Quotient.lift f hConst

theorem factorOnQuot_spec
    {X : Type u} {Z : Type v} {Y : Type w}
    {obs : X -> Z} {f : X -> Y}
    (hConst : forall x y, ObsRel obs x y -> f x = f y)
    (x : X) :
    factorOnQuot f hConst (toObsQuot obs x) = f x := by
  rfl

theorem factors_on_quot_iff_sufficient_single
    {X : Type u} {Z : Type v} {Y : Type w}
    {obs : X -> Z} {f : X -> Y} :
    (forall x y, obs x = obs y -> f x = f y) <->
      (exists g : ObsQuot obs -> Y,
        forall x, f x = g (toObsQuot obs x)) := by
  constructor
  next =>
    intro hConst
    exists factorOnQuot f hConst
    intro x
    rfl
  next =>
    intro hFactor x y hxy
    cases hFactor with
    | intro g hg =>
        calc
          f x = g (toObsQuot obs x) := hg x
          _ = g (toObsQuot obs y) := by
            apply congrArg g
            apply Quotient.sound
            exact hxy
          _ = f y := (hg y).symm

theorem same_packet_same_decision
    {X : Type u} {Packet : Type v} {Y : Type w}
    {packet : X -> Packet} {family : (X -> Y) -> Prop}
    (hSufficient : Sufficient packet family)
    {x y : X} (hxy : packet x = packet y)
    {decision : X -> Y} (hDecision : family decision) :
    decision x = decision y :=
  hSufficient x y hxy decision hDecision

theorem mixed_fiber_no_perfect_evaluator
    {X : Type u} {Packet : Type v} {Y : Type w}
    {packet : X -> Packet} {decision : X -> Y}
    {x y : X}
    (hSamePacket : packet x = packet y)
    (hMixed : Not (decision x = decision y)) :
    Not (exists eval : Packet -> Y,
      forall z, decision z = eval (packet z)) := by
  intro hEval
  cases hEval with
  | intro eval hEval =>
      have hSameDecision : decision x = decision y := by
        calc
          decision x = eval (packet x) := hEval x
          _ = eval (packet y) := congrArg eval hSamePacket
          _ = decision y := (hEval y).symm
      exact hMixed hSameDecision

/-!
## 2. Canonical decision quotient

The canonical semantic kernel is not a quotient by all data.  It is the
quotient by all decisions that must be preserved.  Any packet that is
sufficient for those decisions must refine this canonical quotient.
-/

def DecisionEquivalent
    {X : Type u} {Y : Type v}
    (family : (X -> Y) -> Prop)
    (x y : X) : Prop :=
  forall f, family f -> f x = f y

theorem decisionEquivalent_refl
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    (x : X) :
    DecisionEquivalent family x x := by
  intro f _hf
  rfl

theorem decisionEquivalent_symm
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    {x y : X}
    (h : DecisionEquivalent family x y) :
    DecisionEquivalent family y x := by
  intro f hf
  exact (h f hf).symm

theorem decisionEquivalent_trans
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    {x y z : X}
    (hxy : DecisionEquivalent family x y)
    (hyz : DecisionEquivalent family y z) :
    DecisionEquivalent family x z := by
  intro f hf
  exact Eq.trans (hxy f hf) (hyz f hf)

def DecisionSetoid
    {X : Type u} {Y : Type v}
    (family : (X -> Y) -> Prop) : Setoid X where
  r := DecisionEquivalent family
  iseqv := by
    constructor
    · intro x
      exact decisionEquivalent_refl x
    · intro x y h
      exact decisionEquivalent_symm h
    · intro x y z hxy hyz
      exact decisionEquivalent_trans hxy hyz

def DecisionQuotient
    {X : Type u} {Y : Type v}
    (family : (X -> Y) -> Prop) : Type u :=
  Quotient (DecisionSetoid family)

def toDecisionQuotient
    {X : Type u} {Y : Type v}
    (family : (X -> Y) -> Prop) (x : X) :
    DecisionQuotient family :=
  Quotient.mk (DecisionSetoid family) x

def decisionFactor
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    (f : X -> Y) (hf : family f) :
    DecisionQuotient family -> Y :=
  Quotient.lift f (by
    intro x y hxy
    exact hxy f hf)

theorem decision_factors_through_canonical_quotient
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    {f : X -> Y} (hf : family f) :
    FactorsThrough (toDecisionQuotient family) f := by
  exists decisionFactor f hf
  intro x
  rfl

theorem canonical_decision_quotient_sufficient
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    {x y : X}
    (hxy :
      toDecisionQuotient family x =
        toDecisionQuotient family y) :
    forall f, family f -> f x = f y := by
  intro f hf
  let g := decisionFactor f hf
  calc
    f x = g (toDecisionQuotient family x) := by rfl
    _ = g (toDecisionQuotient family y) := congrArg g hxy
    _ = f y := by rfl

theorem any_sufficient_packet_refines_canonical_quotient
    {X : Type u} {Y : Type v} {Packet : Type w}
    {family : (X -> Y) -> Prop}
    {packet : X -> Packet}
    (hSufficient : Sufficient packet family)
    {x y : X}
    (hPacket : packet x = packet y) :
    toDecisionQuotient family x =
      toDecisionQuotient family y := by
  apply Quotient.sound
  change DecisionEquivalent family x y
  intro f hf
  exact hSufficient x y hPacket f hf

def sufficientPacketToCanonicalQuotient
    {X : Type u} {Y : Type v} {Packet : Type w}
    {family : (X -> Y) -> Prop}
    {packet : X -> Packet}
    (hSufficient : Sufficient packet family) :
    ObsQuot packet -> DecisionQuotient family :=
  Quotient.lift (toDecisionQuotient family) (by
    intro x y hxy
    exact any_sufficient_packet_refines_canonical_quotient
      hSufficient hxy)

theorem sufficient_packet_factors_to_canonical_quotient
    {X : Type u} {Y : Type v} {Packet : Type w}
    {family : (X -> Y) -> Prop}
    {packet : X -> Packet}
    (hSufficient : Sufficient packet family)
    (x : X) :
    sufficientPacketToCanonicalQuotient
        (family := family) (packet := packet) hSufficient
        (toObsQuot packet x) =
      toDecisionQuotient family x := by
  rfl

theorem canonical_decision_factor_unique
    {X : Type u} {Y : Type v}
    {family : (X -> Y) -> Prop}
    {f : X -> Y}
    {g₁ g₂ : DecisionQuotient family -> Y}
    (h₁ : forall x, f x = g₁ (toDecisionQuotient family x))
    (h₂ : forall x, f x = g₂ (toDecisionQuotient family x)) :
    g₁ = g₂ := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  calc
    g₁ (toDecisionQuotient family x) = f x := (h₁ x).symm
    _ = g₂ (toDecisionQuotient family x) := h₂ x

/-!
## 3. Disposition and release interpretation

Common semantics does not mean common business rules.  Different participants
may keep different requirements; the shared kernel only makes those
requirements interpretable over a common decision-relevant space.
-/

inductive Disposition where
  | satisfied
  | violated
  | unknown
  | conflict

def ReleaseDecision (d : Disposition) : Prop :=
  match d with
  | Disposition.satisfied => True
  | Disposition.violated => False
  | Disposition.unknown => False
  | Disposition.conflict => False

/-!
## 4. Robust release and mixed fibers

Robust release accepts an evidence value only when every world compatible
with that value is acceptable.  It is sound and maximal among all sound
verifiers that can look only at that observation.
-/

def Sound
    {World : Type u} {Evidence : Type v}
    (obs : World -> Evidence)
    (safe : World -> Prop)
    (verifier : Evidence -> Prop) : Prop :=
  forall omega, verifier (obs omega) -> safe omega

def Complete
    {World : Type u} {Evidence : Type v}
    (obs : World -> Evidence)
    (safe : World -> Prop)
    (verifier : Evidence -> Prop) : Prop :=
  forall omega, safe omega -> verifier (obs omega)

def RobustRelease
    {World : Type u} {Evidence : Type v}
    (obs : World -> Evidence)
    (safe : World -> Prop)
    (e : Evidence) : Prop :=
  And
    (exists omega, obs omega = e)
    (forall omega, obs omega = e -> safe omega)

theorem robust_release_sound
    {World : Type u} {Evidence : Type v}
    {obs : World -> Evidence} {safe : World -> Prop}
    {omega : World}
    (hRelease : RobustRelease obs safe (obs omega)) :
    safe omega :=
  hRelease.right omega rfl

theorem robust_release_maximal
    {World : Type u} {Evidence : Type v}
    {obs : World -> Evidence} {safe : World -> Prop}
    {verifier : Evidence -> Prop}
    (hSound : Sound obs safe verifier)
    {e : Evidence}
    (hObserved : exists omega, obs omega = e)
    (hAccept : verifier e) :
    RobustRelease obs safe e := by
  constructor
  · exact hObserved
  · intro omega hOmega
    apply hSound omega
    exact Eq.subst hOmega.symm hAccept

theorem mixed_fiber_not_releasable
    {World : Type u} {Evidence : Type v}
    {obs : World -> Evidence} {safe : World -> Prop}
    {e : Evidence} {bad : World}
    (hBadObs : obs bad = e)
    (hBad : Not (safe bad)) :
    Not (RobustRelease obs safe e) := by
  intro hRelease
  exact hBad (hRelease.right bad hBadObs)

theorem mixed_fiber_no_sound_complete_verifier
    {World : Type u} {Evidence : Type v}
    {obs : World -> Evidence} {safe : World -> Prop}
    {good bad : World}
    (hSameEvidence : obs good = obs bad)
    (hGood : safe good)
    (hBad : Not (safe bad)) :
    Not (exists verifier : Evidence -> Prop,
      And (Sound obs safe verifier) (Complete obs safe verifier)) := by
  intro hVerifier
  cases hVerifier with
  | intro verifier hv =>
      have vGood : verifier (obs good) := hv.right good hGood
      have vBad : verifier (obs bad) := Eq.subst hSameEvidence vGood
      exact hBad (hv.left bad vBad)

theorem refinement_monotonicity
    {World : Type u} {Coarse : Type v} {Fine : Type w}
    {coarse : World -> Coarse} {fine : World -> Fine}
    {forget : Fine -> Coarse}
    (hRefines : forall omega, coarse omega = forget (fine omega))
    {safe : World -> Prop} {omega : World}
    (hCoarseRelease : RobustRelease coarse safe (coarse omega)) :
    RobustRelease fine safe (fine omega) := by
  constructor
  · exact Exists.intro omega rfl
  · intro omega' hFine
    apply hCoarseRelease.right omega'
    calc
      coarse omega' = forget (fine omega') := hRefines omega'
      _ = forget (fine omega) := congrArg forget hFine
      _ = coarse omega := (hRefines omega).symm

theorem dropped_field_impossibility
    {World : Type u} {Full : Type v} {Reduced : Type w}
    {fullObs : World -> Full} {drop : Full -> Reduced}
    {safe : World -> Prop} {good bad : World}
    (hSameReduced :
      drop (fullObs good) = drop (fullObs bad))
    (hGood : safe good)
    (hBad : Not (safe bad)) :
    Not (exists verifier : Reduced -> Prop,
      And
        (Sound (fun omega => drop (fullObs omega)) safe verifier)
        (Complete (fun omega => drop (fullObs omega)) safe verifier)) := by
  intro hVerifier
  cases hVerifier with
  | intro verifier hv =>
      have vGood : verifier (drop (fullObs good)) := hv.right good hGood
      have vBad : verifier (drop (fullObs bad)) :=
        Eq.subst hSameReduced vGood
      exact hBad (hv.left bad vBad)

theorem trust_only_observation_insufficient
    {World : Type u} {TrustView : Type v}
    {trustView : World -> TrustView}
    {adoptable : World -> Prop} {safeWorld badWorld : World}
    (hSameTrust : trustView safeWorld = trustView badWorld)
    (hSafe : adoptable safeWorld)
    (hBad : Not (adoptable badWorld)) :
    Not (exists verifier : TrustView -> Prop,
      And
        (Sound trustView adoptable verifier)
        (Complete trustView adoptable verifier)) :=
  mixed_fiber_no_sound_complete_verifier hSameTrust hSafe hBad

/-!
## 5. Joint semantic/evidence federation model

The public release verifier sees one joint packet.  It is not given separate
semantic and evidence verifiers.  Joint completeness is stronger than
nontrivial liveness; nontrivial liveness alone does not imply sufficiency.
-/

structure FederationModel where
  SemanticWorld : Type u
  EvidenceWorld : Type v
  SemanticPacket : Type w
  EvidencePacket : Type q
  semanticPacket : SemanticWorld -> SemanticPacket
  evidencePacket : EvidenceWorld -> EvidencePacket
  semanticOK : SemanticWorld -> Prop
  evidenceOK : EvidenceWorld -> Prop

def JointSound
    (M : FederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  forall s e,
    jointVerifier (M.semanticPacket s, M.evidencePacket e) ->
      M.semanticOK s ∧ M.evidenceOK e

def JointComplete
    (M : FederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  forall s e,
    M.semanticOK s ∧ M.evidenceOK e ->
      jointVerifier (M.semanticPacket s, M.evidencePacket e)

def NontrivialLive
    (M : FederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  exists s e,
    M.semanticOK s ∧
    M.evidenceOK e ∧
    jointVerifier (M.semanticPacket s, M.evidencePacket e)

/-!
## 6. Non-circular dual sufficiency theorems

These are the central non-circular results.  From one public joint verifier,
joint soundness, joint completeness, and one good witness on the other side,
we derive that the corresponding public packet is sufficient.
-/

theorem exact_joint_release_implies_semantic_sufficiency
    {M : FederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : JointSound M jointVerifier)
    (hComplete : JointComplete M jointVerifier)
    (hEvidenceExists : exists e, M.evidenceOK e) :
    PredicateSufficient M.semanticPacket M.semanticOK := by
  cases hEvidenceExists with
  | intro e0 he0 =>
      intro x y hxy
      constructor
      · intro hx
        have hReleaseX :
            jointVerifier (M.semanticPacket x, M.evidencePacket e0) :=
          hComplete x e0 (And.intro hx he0)
        have hReleaseY :
            jointVerifier (M.semanticPacket y, M.evidencePacket e0) := by
          simpa [hxy] using hReleaseX
        exact (hSound y e0 hReleaseY).left
      · intro hy
        have hReleaseY :
            jointVerifier (M.semanticPacket y, M.evidencePacket e0) :=
          hComplete y e0 (And.intro hy he0)
        have hReleaseX :
            jointVerifier (M.semanticPacket x, M.evidencePacket e0) := by
          simpa [hxy.symm] using hReleaseY
        exact (hSound x e0 hReleaseX).left

theorem exact_joint_release_implies_evidence_sufficiency
    {M : FederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : JointSound M jointVerifier)
    (hComplete : JointComplete M jointVerifier)
    (hSemanticExists : exists s, M.semanticOK s) :
    PredicateSufficient M.evidencePacket M.evidenceOK := by
  cases hSemanticExists with
  | intro s0 hs0 =>
      intro x y hxy
      constructor
      · intro hx
        have hReleaseX :
            jointVerifier (M.semanticPacket s0, M.evidencePacket x) :=
          hComplete s0 x (And.intro hs0 hx)
        have hReleaseY :
            jointVerifier (M.semanticPacket s0, M.evidencePacket y) := by
          simpa [hxy] using hReleaseX
        exact (hSound s0 y hReleaseY).right
      · intro hy
        have hReleaseY :
            jointVerifier (M.semanticPacket s0, M.evidencePacket y) :=
          hComplete s0 y (And.intro hs0 hy)
        have hReleaseX :
            jointVerifier (M.semanticPacket s0, M.evidencePacket x) := by
          simpa [hxy.symm] using hReleaseY
        exact (hSound s0 x hReleaseX).right

theorem exact_joint_release_implies_dual_sufficiency
    {M : FederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : JointSound M jointVerifier)
    (hComplete : JointComplete M jointVerifier)
    (hSemanticExists : exists s, M.semanticOK s)
    (hEvidenceExists : exists e, M.evidenceOK e) :
    PredicateSufficient M.semanticPacket M.semanticOK ∧
    PredicateSufficient M.evidencePacket M.evidenceOK := by
  constructor
  · exact exact_joint_release_implies_semantic_sufficiency
      hSound hComplete hEvidenceExists
  · exact exact_joint_release_implies_evidence_sufficiency
      hSound hComplete hSemanticExists

/-
The v1.0 model below makes compatibility explicit.  The direct product model
above is recovered as the special case `compatible := fun _ _ => True`.
This avoids silently assuming that every semantic world can be paired with
every evidence world.
-/

structure SupportedFederationModel where
  SemanticWorld : Type u
  EvidenceWorld : Type v
  SemanticPacket : Type w
  EvidencePacket : Type q
  semanticPacket : SemanticWorld -> SemanticPacket
  evidencePacket : EvidenceWorld -> EvidencePacket
  semanticOK : SemanticWorld -> Prop
  evidenceOK : EvidenceWorld -> Prop
  compatible : SemanticWorld -> EvidenceWorld -> Prop

def SupportedJointSound
    (M : SupportedFederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  forall s e,
    M.compatible s e ->
    jointVerifier (M.semanticPacket s, M.evidencePacket e) ->
      M.semanticOK s ∧ M.evidenceOK e

def SupportedJointComplete
    (M : SupportedFederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  forall s e,
    M.compatible s e ->
    M.semanticOK s ->
    M.evidenceOK e ->
      jointVerifier (M.semanticPacket s, M.evidencePacket e)

def SupportedJointExact
    (M : SupportedFederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) :
    Prop :=
  SupportedJointSound M jointVerifier ∧
  SupportedJointComplete M jointVerifier

def SemanticallyComparable
    (M : SupportedFederationModel.{u, v, w, q})
    (x y : M.SemanticWorld) : Prop :=
  exists e,
    M.compatible x e ∧
    M.compatible y e ∧
    M.evidenceOK e

def EvidentiallyComparable
    (M : SupportedFederationModel.{u, v, w, q})
    (x y : M.EvidenceWorld) : Prop :=
  exists s,
    M.compatible s x ∧
    M.compatible s y ∧
    M.semanticOK s

def SemanticFiberBridge
    (M : SupportedFederationModel.{u, v, w, q}) : Prop :=
  forall x y,
    M.semanticPacket x = M.semanticPacket y ->
    SemanticallyComparable M x y

def EvidenceFiberBridge
    (M : SupportedFederationModel.{u, v, w, q}) : Prop :=
  forall x y,
    M.evidencePacket x = M.evidencePacket y ->
    EvidentiallyComparable M x y

theorem exact_supported_release_implies_semantic_sufficiency_on_comparable_fibers
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : SupportedJointSound M jointVerifier)
    (hComplete : SupportedJointComplete M jointVerifier) :
    forall x y,
      M.semanticPacket x = M.semanticPacket y ->
      SemanticallyComparable M x y ->
      (M.semanticOK x <-> M.semanticOK y) := by
  intro x y hPacket hComparable
  rcases hComparable with ⟨e0, hxCompat, hyCompat, heOK⟩
  constructor
  · intro hxOK
    have hReleaseX :
        jointVerifier (M.semanticPacket x, M.evidencePacket e0) :=
      hComplete x e0 hxCompat hxOK heOK
    have hReleaseY :
        jointVerifier (M.semanticPacket y, M.evidencePacket e0) := by
      simpa [hPacket] using hReleaseX
    exact (hSound y e0 hyCompat hReleaseY).left
  · intro hyOK
    have hReleaseY :
        jointVerifier (M.semanticPacket y, M.evidencePacket e0) :=
      hComplete y e0 hyCompat hyOK heOK
    have hReleaseX :
        jointVerifier (M.semanticPacket x, M.evidencePacket e0) := by
      simpa [hPacket.symm] using hReleaseY
    exact (hSound x e0 hxCompat hReleaseX).left

theorem exact_supported_release_implies_evidence_sufficiency_on_comparable_fibers
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : SupportedJointSound M jointVerifier)
    (hComplete : SupportedJointComplete M jointVerifier) :
    forall x y,
      M.evidencePacket x = M.evidencePacket y ->
      EvidentiallyComparable M x y ->
      (M.evidenceOK x <-> M.evidenceOK y) := by
  intro x y hPacket hComparable
  rcases hComparable with ⟨s0, hxCompat, hyCompat, hsOK⟩
  constructor
  · intro hxOK
    have hReleaseX :
        jointVerifier (M.semanticPacket s0, M.evidencePacket x) :=
      hComplete s0 x hxCompat hsOK hxOK
    have hReleaseY :
        jointVerifier (M.semanticPacket s0, M.evidencePacket y) := by
      simpa [hPacket] using hReleaseX
    exact (hSound s0 y hyCompat hReleaseY).right
  · intro hyOK
    have hReleaseY :
        jointVerifier (M.semanticPacket s0, M.evidencePacket y) :=
      hComplete s0 y hyCompat hsOK hyOK
    have hReleaseX :
        jointVerifier (M.semanticPacket s0, M.evidencePacket x) := by
      simpa [hPacket.symm] using hReleaseY
    exact (hSound s0 x hxCompat hReleaseX).right

theorem exact_supported_release_implies_dual_sufficiency
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : SupportedJointSound M jointVerifier)
    (hComplete : SupportedJointComplete M jointVerifier)
    (hSemBridge : SemanticFiberBridge M)
    (hEvBridge : EvidenceFiberBridge M) :
    PredicateSufficient M.semanticPacket M.semanticOK ∧
    PredicateSufficient M.evidencePacket M.evidenceOK := by
  constructor
  · intro x y hPacket
    exact exact_supported_release_implies_semantic_sufficiency_on_comparable_fibers
      hSound hComplete x y hPacket (hSemBridge x y hPacket)
  · intro x y hPacket
    exact exact_supported_release_implies_evidence_sufficiency_on_comparable_fibers
      hSound hComplete x y hPacket (hEvBridge x y hPacket)

def productSupportedModel
    (M : FederationModel.{u, v, w, q}) :
    SupportedFederationModel.{u, v, w, q} where
  SemanticWorld := M.SemanticWorld
  EvidenceWorld := M.EvidenceWorld
  SemanticPacket := M.SemanticPacket
  EvidencePacket := M.EvidencePacket
  semanticPacket := M.semanticPacket
  evidencePacket := M.evidencePacket
  semanticOK := M.semanticOK
  evidenceOK := M.evidenceOK
  compatible := fun _s _e => True

theorem product_model_has_semantic_fiber_bridge
    (M : FederationModel.{u, v, w, q})
    (hEvidenceExists : exists e, M.evidenceOK e) :
    SemanticFiberBridge (productSupportedModel M) := by
  intro x y _hPacket
  rcases hEvidenceExists with ⟨e0, he0⟩
  exact ⟨e0, trivial, trivial, he0⟩

theorem product_model_has_evidence_fiber_bridge
    (M : FederationModel.{u, v, w, q})
    (hSemanticExists : exists s, M.semanticOK s) :
    EvidenceFiberBridge (productSupportedModel M) := by
  intro x y _hPacket
  rcases hSemanticExists with ⟨s0, hs0⟩
  exact ⟨s0, trivial, trivial, hs0⟩

theorem product_model_exact_release_implies_dual_sufficiency
    {M : FederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : JointSound M jointVerifier)
    (hComplete : JointComplete M jointVerifier)
    (hSemanticExists : exists s, M.semanticOK s)
    (hEvidenceExists : exists e, M.evidenceOK e) :
    PredicateSufficient M.semanticPacket M.semanticOK ∧
    PredicateSufficient M.evidencePacket M.evidenceOK := by
  let SM := productSupportedModel M
  have hs : SupportedJointSound SM jointVerifier := by
    intro s e _hCompat hRelease
    exact hSound s e hRelease
  have hc : SupportedJointComplete SM jointVerifier := by
    intro s e _hCompat hsOK heOK
    exact hComplete s e ⟨hsOK, heOK⟩
  exact exact_supported_release_implies_dual_sufficiency
    (M := SM) hs hc
    (product_model_has_semantic_fiber_bridge M hEvidenceExists)
    (product_model_has_evidence_fiber_bridge M hSemanticExists)

def LiveAt
    (M : SupportedFederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop)
    (s : M.SemanticWorld)
    (e : M.EvidenceWorld) : Prop :=
  M.compatible s e ∧
  M.semanticOK s ∧
  M.evidenceOK e ∧
  jointVerifier (M.semanticPacket s, M.evidencePacket e)

theorem semantic_mixed_fiber_blocks_soundness_and_local_liveness
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    {semGood semBad : M.SemanticWorld}
    {evGood : M.EvidenceWorld}
    (hSame : M.semanticPacket semGood = M.semanticPacket semBad)
    (hBadCompat : M.compatible semBad evGood)
    (hSemBad : Not (M.semanticOK semBad)) :
    Not (
      SupportedJointSound M jointVerifier ∧
      LiveAt M jointVerifier semGood evGood) := by
  intro hBoth
  have hLive := hBoth.right
  have hReleaseBad :
      jointVerifier (M.semanticPacket semBad, M.evidencePacket evGood) := by
    simpa [hSame] using hLive.right.right.right
  exact hSemBad ((hBoth.left semBad evGood hBadCompat hReleaseBad).left)

theorem evidence_mixed_fiber_blocks_soundness_and_local_liveness
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    {evGood evBad : M.EvidenceWorld}
    {semGood : M.SemanticWorld}
    (hSame : M.evidencePacket evGood = M.evidencePacket evBad)
    (hBadCompat : M.compatible semGood evBad)
    (hEvBad : Not (M.evidenceOK evBad)) :
    Not (
      SupportedJointSound M jointVerifier ∧
      LiveAt M jointVerifier semGood evGood) := by
  intro hBoth
  have hLive := hBoth.right
  have hReleaseBad :
      jointVerifier (M.semanticPacket semGood, M.evidencePacket evBad) := by
    simpa [hSame] using hLive.right.right.right
  exact hEvBad ((hBoth.left semGood evBad hBadCompat hReleaseBad).right)

theorem safe_live_public_packet_trilemma
    {World : Type u} {Packet : Type v}
    {packet : World -> Packet} {ok : World -> Prop}
    {jointVerifier : Packet -> Prop}
    {good bad : World}
    (hSame : packet good = packet bad)
    (hGoodRelease : jointVerifier (packet good))
    (hBad : Not (ok bad))
    (hSound : forall world, jointVerifier (packet world) -> ok world) :
    False := by
  have hBadRelease : jointVerifier (packet bad) := by
    simpa [hSame] using hGoodRelease
  exact hBad (hSound bad hBadRelease)

namespace NoBridgeCounterexample

inductive SemWorld where
  | semGood
  | semBad

inductive EvWorld where
  | evForGood
  | evForBad

def semPacket (_s : SemWorld) : Unit := ()

def evPacket : EvWorld -> Bool
  | EvWorld.evForGood => true
  | EvWorld.evForBad => false

def semOK : SemWorld -> Prop
  | SemWorld.semGood => True
  | SemWorld.semBad => False

def evOK (_e : EvWorld) : Prop := True

def compatible : SemWorld -> EvWorld -> Prop
  | SemWorld.semGood, EvWorld.evForGood => True
  | SemWorld.semBad, EvWorld.evForBad => True
  | _, _ => False

def model : SupportedFederationModel where
  SemanticWorld := SemWorld
  EvidenceWorld := EvWorld
  SemanticPacket := Unit
  EvidencePacket := Bool
  semanticPacket := semPacket
  evidencePacket := evPacket
  semanticOK := semOK
  evidenceOK := evOK
  compatible := compatible

def jointVerifier (p : Unit × Bool) : Prop :=
  p.2 = true

theorem joint_sound : SupportedJointSound model jointVerifier := by
  intro s e hCompat hRelease
  cases s <;> cases e <;> simp [model, compatible, jointVerifier, evPacket, semOK, evOK] at *

theorem joint_complete : SupportedJointComplete model jointVerifier := by
  intro s e hCompat hSem hEv
  cases s <;> cases e <;> simp [model, compatible, jointVerifier, evPacket, semOK, evOK] at *

theorem semantic_packet_not_sufficient :
    Not (PredicateSufficient model.semanticPacket model.semanticOK) := by
  intro hSufficient
  have hIff := hSufficient SemWorld.semGood SemWorld.semBad rfl
  exact hIff.mp trivial

theorem semantic_fiber_bridge_fails :
    Not (SemanticFiberBridge model) := by
  intro hBridge
  rcases hBridge SemWorld.semGood SemWorld.semBad rfl with
    ⟨e, hGoodCompat, hBadCompat, _hEvOK⟩
  cases e <;> simp [model, compatible] at hGoodCompat hBadCompat

theorem exact_joint_release_without_fiber_bridge_does_not_imply_semantic_sufficiency :
    (exists jointVerifier,
      SupportedJointSound model jointVerifier ∧
      SupportedJointComplete model jointVerifier) ∧
    Not (PredicateSufficient model.semanticPacket model.semanticOK) ∧
    Not (SemanticFiberBridge model) := by
  exact ⟨⟨jointVerifier, joint_sound, joint_complete⟩,
    semantic_packet_not_sufficient,
    semantic_fiber_bridge_fails⟩

end NoBridgeCounterexample

/-!
## 7. Safe-live-peer-independence trilemma

If a public packet fiber contains both an acceptable and an unacceptable
world, then a verifier that sees only that packet cannot be both sound and
complete.  Packet-only input is the formal meaning of peer independence here.
-/

theorem semantic_mixed_fiber_no_exact_peer_verifier
    {M : FederationModel.{u, v, w, q}}
    {semGood semBad : M.SemanticWorld}
    {evGood : M.EvidenceWorld}
    (hSame :
      M.semanticPacket semGood = M.semanticPacket semBad)
    (hSemGood : M.semanticOK semGood)
    (hSemBad : Not (M.semanticOK semBad))
    (hEvGood : M.evidenceOK evGood) :
    Not (exists jointVerifier,
      JointSound M jointVerifier ∧ JointComplete M jointVerifier) := by
  intro hExists
  cases hExists with
  | intro jointVerifier hBoth =>
      have hReleaseGood :
          jointVerifier
            (M.semanticPacket semGood, M.evidencePacket evGood) :=
        hBoth.right semGood evGood (And.intro hSemGood hEvGood)
      have hReleaseBad :
          jointVerifier
            (M.semanticPacket semBad, M.evidencePacket evGood) := by
        simpa [hSame] using hReleaseGood
      exact hSemBad ((hBoth.left semBad evGood hReleaseBad).left)

theorem evidence_mixed_fiber_no_exact_peer_verifier
    {M : FederationModel.{u, v, w, q}}
    {evGood evBad : M.EvidenceWorld}
    {semGood : M.SemanticWorld}
    (hSame :
      M.evidencePacket evGood = M.evidencePacket evBad)
    (hEvGood : M.evidenceOK evGood)
    (hEvBad : Not (M.evidenceOK evBad))
    (hSemGood : M.semanticOK semGood) :
    Not (exists jointVerifier,
      JointSound M jointVerifier ∧ JointComplete M jointVerifier) := by
  intro hExists
  cases hExists with
  | intro jointVerifier hBoth =>
      have hReleaseGood :
          jointVerifier
            (M.semanticPacket semGood, M.evidencePacket evGood) :=
        hBoth.right semGood evGood (And.intro hSemGood hEvGood)
      have hReleaseBad :
          jointVerifier
            (M.semanticPacket semGood, M.evidencePacket evBad) := by
        simpa [hSame] using hReleaseGood
      exact hEvBad ((hBoth.left semGood evBad hReleaseBad).right)

theorem safe_live_peer_independence_trilemma
    {World : Type u} {Packet : Type v}
    {packet : World -> Packet} {ok : World -> Prop}
    {good bad : World}
    (hSame : packet good = packet bad)
    (hGood : ok good)
    (hBad : Not (ok bad)) :
    Not (exists verifier : Packet -> Prop,
      Sound packet ok verifier ∧ Complete packet ok verifier) :=
  mixed_fiber_no_sound_complete_verifier hSame hGood hBad

/-!
## 8. Homogeneous paths

This homogeneous path model is kept for compatibility with v0.1.  It is the
simple case where every participant uses the same local state type.
-/

inductive Path (State : Type u) where
  | nil : Path State
  | cons : (State -> State) -> Path State -> Path State

namespace Path

def run
    {State : Type u} : Path State -> State -> State
  | nil, x => x
  | cons step rest, x => run rest (step x)

def PreservesAll
    {State : Type u} {Packet : Type v}
    (packet : State -> Packet) : Path State -> Prop
  | nil => True
  | cons step rest =>
      And
        (forall x, packet (step x) = packet x)
        (PreservesAll packet rest)

theorem packet_preserved_along_path
    {State : Type u} {Packet : Type v}
    {packet : State -> Packet} :
    forall path : Path State,
      PreservesAll packet path ->
      forall x, packet (run path x) = packet x := by
  intro path
  induction path with
  | nil =>
      intro _ x
      rfl
  | cons step rest ih =>
      intro hAll x
      exact Eq.trans (ih hAll.right (step x)) (hAll.left x)

def DependsOnlyOnPacket
    {State : Type u} {Packet : Type v} {Decision : Type w}
    (packet : State -> Packet)
    (decision : State -> Decision) : Prop :=
  exists eval : Packet -> Decision,
    forall x, decision x = eval (packet x)

theorem path_decision_independent
    {State : Type u} {Packet : Type v} {Decision : Type w}
    {packet : State -> Packet}
    {decision : State -> Decision}
    {p q : Path State}
    (hp : PreservesAll packet p)
    (hq : PreservesAll packet q)
    (hDecision : DependsOnlyOnPacket packet decision) :
    forall x, decision (run p x) = decision (run q x) := by
  intro x
  cases hDecision with
  | intro eval hEval =>
      have hPacketP : packet (run p x) = packet x :=
        packet_preserved_along_path p hp x
      have hPacketQ : packet (run q x) = packet x :=
        packet_preserved_along_path q hq x
      calc
        decision (run p x) = eval (packet (run p x)) := hEval (run p x)
        _ = eval (packet x) := congrArg eval hPacketP
        _ = eval (packet (run q x)) := (congrArg eval hPacketQ).symm
        _ = decision (run q x) := (hEval (run q x)).symm

end Path

/-!
## 9. Heterogeneous paths

Participants may have different local state types.  A heterogeneous path is
indexed by its start and end participant.  If every step preserves a common
packet, then every finite path preserves that packet.
-/

inductive HPath
    {Participant : Type u}
    (LocalState : Participant -> Type v) :
    Participant -> Participant -> Type (max u v) where
  | id {i : Participant} : HPath LocalState i i
  | comp {i j k : Participant}
      (step : LocalState i -> LocalState j)
      (rest : HPath LocalState j k) :
      HPath LocalState i k

namespace HPath

def run
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    {i j : Participant}
    (path : HPath LocalState i j) :
    LocalState i -> LocalState j :=
  match path with
  | id => fun x => x
  | comp step rest => fun x => run rest (step x)

def PreservesAll
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    {Packet : Type w}
    (encode : forall i, LocalState i -> Packet)
    {i j : Participant}
    (path : HPath LocalState i j) : Prop :=
  match path with
  | id => True
  | comp (i := start) (j := mid) step rest =>
      (forall x, encode mid (step x) = encode start x) ∧
      PreservesAll encode rest

theorem heterogeneous_packet_preserved_along_path
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    {Packet : Type w}
    {encode : forall i, LocalState i -> Packet}
    {i j : Participant}
    (path : HPath LocalState i j)
    (hPreserves : PreservesAll encode path) :
    forall x, encode j (run path x) = encode i x := by
  induction path with
  | id =>
      intro x
      rfl
  | comp step rest ih =>
      intro x
      exact Eq.trans (ih hPreserves.right (step x)) (hPreserves.left x)

def DependsOnlyOnPacket
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    {Packet : Type w} {Decision : Type q}
    (encode : forall i, LocalState i -> Packet)
    (j : Participant)
    (decision : LocalState j -> Decision) : Prop :=
  exists eval : Packet -> Decision,
    forall x, decision x = eval (encode j x)

theorem heterogeneous_path_decision_independent
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    {Packet : Type w} {Decision : Type q}
    {encode : forall i, LocalState i -> Packet}
    {i j : Participant}
    {p q : HPath LocalState i j}
    {decision : LocalState j -> Decision}
    (hp : PreservesAll encode p)
    (hq : PreservesAll encode q)
    (hDecision : DependsOnlyOnPacket encode j decision) :
    forall x, decision (run p x) = decision (run q x) := by
  intro x
  cases hDecision with
  | intro eval hEval =>
      have hpPacket : encode j (run p x) = encode i x :=
        heterogeneous_packet_preserved_along_path p hp x
      have hqPacket : encode j (run q x) = encode i x :=
        heterogeneous_packet_preserved_along_path q hq x
      calc
        decision (run p x) = eval (encode j (run p x)) := hEval (run p x)
        _ = eval (encode i x) := congrArg eval hpPacket
        _ = eval (encode j (run q x)) := (congrArg eval hqPacket).symm
        _ = decision (run q x) := (hEval (run q x)).symm

end HPath

/-!
## 10. Common frames and zero holonomy

For reversible, fully coherent translation systems, path independence means
the system already factors through a common frame.  This is a complete and
invertible model; non-invertible logistics mappings need weaker packet
preservation instead.
-/

structure Iso (A : Type u) (B : Type v) where
  toFun : A -> B
  invFun : B -> A
  left_inv : forall x, invFun (toFun x) = x
  right_inv : forall y, toFun (invFun y) = y

structure CommonFrame
    {Participant : Type u}
    (LocalState : Participant -> Type v) where
  CommonState : Type w
  frame : forall i, Iso (LocalState i) CommonState

namespace CommonFrame

def translation
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    (i j : Participant) :
    LocalState i -> LocalState j :=
  fun x => (cf.frame j).invFun ((cf.frame i).toFun x)

theorem common_frame_translation_identity
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    (i : Participant)
    (x : LocalState i) :
    translation cf i i x = x := by
  exact (cf.frame i).left_inv x

theorem common_frame_translation_composition
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    (i j k : Participant)
    (x : LocalState i) :
    translation cf j k (translation cf i j x) =
      translation cf i k x := by
  unfold translation
  rw [(cf.frame j).right_inv]

theorem common_frame_induces_path_independence
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    (i j k : Participant)
    (x : LocalState i) :
    translation cf j k (translation cf i j x) =
      translation cf i k x :=
  common_frame_translation_composition cf i j k x

theorem common_frame_induces_zero_holonomy
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    (i j : Participant)
    (x : LocalState i) :
    translation cf j i (translation cf i j x) = x := by
  calc
    translation cf j i (translation cf i j x) =
        translation cf i i x :=
      common_frame_translation_composition cf i j i x
    _ = x := common_frame_translation_identity cf i x

end CommonFrame

structure CoherentTranslationSystem
    {Participant : Type u}
    (LocalState : Participant -> Type v) where
  translate : forall i j, LocalState i -> LocalState j
  id_translate : forall i (x : LocalState i), translate i i x = x
  comp_translate :
    forall i j k (x : LocalState i),
      translate j k (translate i j x) = translate i k x

def coherentCommonFrame
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (system : CoherentTranslationSystem LocalState)
    (base : Participant) :
    CommonFrame LocalState where
  CommonState := LocalState base
  frame := fun i =>
    { toFun := system.translate i base
      invFun := system.translate base i
      left_inv := by
        intro x
        calc
          system.translate base i (system.translate i base x) =
              system.translate i i x :=
            system.comp_translate i base i x
          _ = x := system.id_translate i x
      right_inv := by
        intro x
        calc
          system.translate i base (system.translate base i x) =
              system.translate base base x :=
            system.comp_translate base i base x
          _ = x := system.id_translate base x }

theorem coherent_translation_system_factors_through_base
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (system : CoherentTranslationSystem LocalState)
    (base i j : Participant)
    (x : LocalState i) :
    system.translate i j x =
      CommonFrame.translation (coherentCommonFrame system base) i j x := by
  unfold CommonFrame.translation coherentCommonFrame
  exact (system.comp_translate i base j x).symm

structure TranslationNetwork where
  Participant : Type u
  LocalState : Participant -> Type v
  Edge : Participant -> Participant -> Type w
  translate :
    forall {i j : Participant},
      Edge i j ->
      LocalState i ->
      LocalState j

inductive Route
    {Participant : Type u}
    (Edge : Participant -> Participant -> Type v) :
    Participant -> Participant -> Type (max u v) where
  | id {i : Participant} : Route Edge i i
  | cons {i j k : Participant}
      (edge : Edge i j)
      (rest : Route Edge j k) :
      Route Edge i k

namespace Route

def run
    (N : TranslationNetwork.{u, v, w})
    {i j : N.Participant}
    (route : Route N.Edge i j) :
    N.LocalState i -> N.LocalState j :=
  match route with
  | id => fun x => x
  | cons edge rest => fun x => run N rest (N.translate edge x)

def EdgePreservesPacket
    (N : TranslationNetwork.{u, v, w})
    {Packet : Type q}
    (encode : forall i, N.LocalState i -> Packet) :
    Prop :=
  forall {i j : N.Participant}
    (edge : N.Edge i j)
    (x : N.LocalState i),
    encode j (N.translate edge x) = encode i x

theorem route_preserves_packet
    (N : TranslationNetwork.{u, v, w})
    {Packet : Type q}
    {encode : forall i, N.LocalState i -> Packet}
    (hEdge : EdgePreservesPacket N encode)
    {i j : N.Participant}
    (route : Route N.Edge i j) :
    forall x, encode j (run N route x) = encode i x := by
  induction route with
  | id =>
      intro x
      rfl
  | cons edge rest ih =>
      intro x
      exact Eq.trans (ih (N.translate edge x)) (hEdge edge x)

def DecisionDependsOnlyOnPacket
    (N : TranslationNetwork.{u, v, w})
    {Packet : Type q} {Decision : Type r}
    (encode : forall i, N.LocalState i -> Packet)
    (decision : forall i, N.LocalState i -> Decision) :
    Prop :=
  exists eval : Packet -> Decision,
    forall i (x : N.LocalState i), decision i x = eval (encode i x)

theorem route_decision_independent
    (N : TranslationNetwork.{u, v, w})
    {Packet : Type q} {Decision : Type r}
    {encode : forall i, N.LocalState i -> Packet}
    {decision : forall i, N.LocalState i -> Decision}
    (hEdge : EdgePreservesPacket N encode)
    (hDecision : DecisionDependsOnlyOnPacket N encode decision)
    {i j : N.Participant}
    (p qroute : Route N.Edge i j) :
    forall x,
      decision j (run N p x) =
      decision j (run N qroute x) := by
  intro x
  rcases hDecision with ⟨eval, hEval⟩
  have hp : encode j (run N p x) = encode i x :=
    route_preserves_packet N hEdge p x
  have hq : encode j (run N qroute x) = encode i x :=
    route_preserves_packet N hEdge qroute x
  calc
    decision j (run N p x) =
        eval (encode j (run N p x)) := hEval j (run N p x)
    _ = eval (encode i x) := congrArg eval hp
    _ = eval (encode j (run N qroute x)) := (congrArg eval hq).symm
    _ = decision j (run N qroute x) := (hEval j (run N qroute x)).symm

end Route

namespace CommonFrame

def network
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState) :
    TranslationNetwork.{u, v, max u v} where
  Participant := Participant
  LocalState := LocalState
  Edge := fun _i _j => PUnit
  translate := fun {i} {j} _edge => translation cf i j

theorem common_frame_route_equals_direct_translation
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    {i j : Participant}
    (route : Route (network cf).Edge i j) :
    forall x : LocalState i,
      Route.run (network cf) route x = translation cf i j x := by
  induction route with
  | @id idx =>
      intro x
      exact (common_frame_translation_identity cf idx x).symm
  | @cons start mid finish edge rest ih =>
      intro x
      calc
        Route.run (network cf) (Route.cons edge rest) x =
            Route.run (network cf) rest (translation cf start mid x) := rfl
        _ = translation cf mid finish (translation cf start mid x) :=
            ih (translation cf start mid x)
        _ = translation cf start finish x :=
            common_frame_translation_composition cf start mid finish x

theorem common_frame_all_routes_equal
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    {i j : Participant}
    (p qroute : Route (network cf).Edge i j)
    (x : LocalState i) :
    Route.run (network cf) p x =
      Route.run (network cf) qroute x := by
  have hp :
      Route.run (network cf) p x = translation cf i j x :=
    common_frame_route_equals_direct_translation (cf := cf) p x
  have hq :
      Route.run (network cf) qroute x = translation cf i j x :=
    common_frame_route_equals_direct_translation (cf := cf) qroute x
  exact hp.trans hq.symm

theorem common_frame_all_loops_are_identity
    {Participant : Type u}
    {LocalState : Participant -> Type v}
    (cf : CommonFrame.{u, v, w} LocalState)
    {i : Participant}
    (loop : Route (network cf).Edge i i)
    (x : LocalState i) :
    Route.run (network cf) loop x = x := by
  have hLoop :
      Route.run (network cf) loop x = translation cf i i x :=
    common_frame_route_equals_direct_translation (cf := cf) loop x
  exact hLoop.trans (common_frame_translation_identity cf i x)

end CommonFrame

/-!
## 11. Pairwise integration cost

The quadratic claim below is conditional: it models independent bilateral
checks for every pair, with no reuse through a third-party or common kernel.
It does not say that every non-kernel system must literally be a complete
graph.
-/

def BilateralByJoin : Nat -> Nat
  | 0 => 0
  | n + 1 => BilateralByJoin n + n

def KernelByJoin (n : Nat) : Nat :=
  n

theorem bilateral_join_increment (n : Nat) :
    BilateralByJoin (n + 1) = BilateralByJoin n + n := by
  rfl

theorem kernel_join_increment (n : Nat) :
    KernelByJoin (n + 1) = KernelByJoin n + 1 := by
  rfl

theorem bilateral_by_join_closed_form (n : Nat) :
    2 * BilateralByJoin n + n = n * n := by
  induction n with
  | zero =>
      simp [BilateralByJoin]
  | succ n ih =>
      simp [
        BilateralByJoin,
        Nat.succ_mul,
        Nat.mul_succ,
        Nat.mul_add,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ] at *
      omega

theorem bilateral_increment_exceeds_kernel_after_two
    (n : Nat) (hTwo : 2 <= n) :
    KernelByJoin (n + 1) - KernelByJoin n <
      BilateralByJoin (n + 1) - BilateralByJoin n := by
  simp [KernelByJoin, BilateralByJoin]
  omega

/-!
## 12. Local kernel onboarding

This only proves locality of the conformance obligation.  It is not an
economic proof of all scaling costs.
-/

def AllConform
    {Participant : Type u}
    (ConformsToKernel : Participant -> Prop) :
    List Participant -> Prop
  | [] => True
  | member :: rest =>
      ConformsToKernel member ∧ AllConform ConformsToKernel rest

theorem add_member_requires_only_local_conformance
    {Participant : Type u}
    {ConformsToKernel : Participant -> Prop}
    {members : List Participant}
    {newMember : Participant}
    (hExisting : AllConform ConformsToKernel members)
    (hNew : ConformsToKernel newMember) :
    AllConform ConformsToKernel (newMember :: members) :=
  And.intro hNew hExisting

structure KernelAdapter
    (Packet : Type u)
    (Decision : Type v)
    (sharedEvaluator : Packet -> Decision) where
  LocalState : Type u
  encode : LocalState -> Packet
  localDecision : LocalState -> Decision
  factorsThrough :
    forall x, localDecision x = sharedEvaluator (encode x)

def AdapterInteroperable
    {Packet : Type u}
    {Decision : Type v}
    {sharedEvaluator : Packet -> Decision}
    (left right : KernelAdapter Packet Decision sharedEvaluator) :
    Prop :=
  forall x y,
    left.encode x = right.encode y ->
    left.localDecision x = right.localDecision y

structure KernelMembershipModel
    (Participant : Type u)
    (Packet : Type v)
    (Decision : Type w) where
  sharedEvaluator : Packet -> Decision
  adapter : Participant -> KernelAdapter Packet Decision sharedEvaluator

def KernelMembershipModel.ConformsToKernel
    {Participant : Type u}
    {Packet : Type v}
    {Decision : Type w}
    (_K : KernelMembershipModel Participant Packet Decision)
    (_member : Participant) : Prop :=
  True

def KernelMembershipModel.Interoperable
    {Participant : Type u}
    {Packet : Type v}
    {Decision : Type w}
    (K : KernelMembershipModel Participant Packet Decision)
    (a b : Participant) : Prop :=
  AdapterInteroperable (K.adapter a) (K.adapter b)

theorem two_kernel_adapters_interoperate
    {Packet : Type u}
    {Decision : Type v}
    {sharedEvaluator : Packet -> Decision}
    (left right : KernelAdapter Packet Decision sharedEvaluator) :
    AdapterInteroperable left right := by
  intro x y hSame
  calc
    left.localDecision x = sharedEvaluator (left.encode x) :=
      left.factorsThrough x
    _ = sharedEvaluator (right.encode y) := congrArg sharedEvaluator hSame
    _ = right.localDecision y := (right.factorsThrough y).symm

theorem two_conforming_members_interoperate
    {Participant : Type u}
    {Packet : Type v}
    {Decision : Type w}
    (K : KernelMembershipModel Participant Packet Decision)
    {a b : Participant}
    (_ha : K.ConformsToKernel a)
    (_hb : K.ConformsToKernel b) :
    K.Interoperable a b :=
  two_kernel_adapters_interoperate (K.adapter a) (K.adapter b)

theorem all_conform_member
    {Participant : Type u}
    {ConformsToKernel : Participant -> Prop}
    {members : List Participant}
    {member : Participant}
    (hAll : AllConform ConformsToKernel members)
    (hMem : member ∈ members) :
    ConformsToKernel member := by
  induction members with
  | nil =>
      cases hMem
  | cons head tail ih =>
      cases hMem with
      | head =>
          exact hAll.left
      | tail _ hTail =>
          exact ih hAll.right hTail

theorem new_member_interoperates_with_all_existing
    {Participant : Type u}
    {Packet : Type v}
    {Decision : Type w}
    (K : KernelMembershipModel Participant Packet Decision)
    {members : List Participant}
    {newMember oldMember : Participant}
    (hExisting : AllConform K.ConformsToKernel members)
    (hNew : K.ConformsToKernel newMember)
    (hOld : oldMember ∈ members) :
    K.Interoperable newMember oldMember :=
  two_conforming_members_interoperate K hNew
    (all_conform_member hExisting hOld)

/-!
## 13. Accountability certificates

The certificate records pre/post state, action, versions, authority, evidence,
time window, and nonce.  Validity is separated into independent predicates.
-/

structure AccountabilityCertificate
    (State Action Version Authority EvidenceRoot Time Nonce : Type u) where
  pre : State
  action : Action
  post : State
  requirementVersion : Version
  verifierVersion : Version
  authority : Authority
  previousEvidenceRoot : Option EvidenceRoot
  evidenceRoot : EvidenceRoot
  evaluatedAt : Time
  expiresAt : Time
  nonce : Nonce

abbrev Cert
    (State Action Version Authority EvidenceRoot Time Nonce : Type u) :=
  AccountabilityCertificate
    State Action Version Authority EvidenceRoot Time Nonce

structure CertificateChecks
    (State Action Version Authority EvidenceRoot Time Nonce : Type u) where
  TransitionValid : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  AuthorityValid : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  RequirementVersionValid : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  VerifierVersionValid : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  Fresh : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  EvidenceValid : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  NonceUnused : Cert State Action Version Authority EvidenceRoot Time Nonce -> Prop
  TimeLE : Time -> Time -> Prop
  RequirementVersionCompatible : Version -> Version -> Prop
  VerifierVersionCompatible : Version -> Version -> Prop

def CertificateValid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (cert : Cert State Action Version Authority EvidenceRoot Time Nonce) :
    Prop :=
  checks.TransitionValid cert ∧
  checks.AuthorityValid cert ∧
  checks.RequirementVersionValid cert ∧
  checks.VerifierVersionValid cert ∧
  checks.Fresh cert ∧
  checks.EvidenceValid cert ∧
  checks.NonceUnused cert ∧
  checks.TimeLE cert.evaluatedAt cert.expiresAt

def CertificateLink
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (first second :
      Cert State Action Version Authority EvidenceRoot Time Nonce) :
    Prop :=
  first.post = second.pre ∧
  checks.RequirementVersionCompatible
    first.requirementVersion second.requirementVersion ∧
  checks.VerifierVersionCompatible
    first.verifierVersion second.verifierVersion ∧
  second.previousEvidenceRoot = some first.evidenceRoot ∧
  checks.TimeLE first.evaluatedAt second.evaluatedAt ∧
  checks.TimeLE second.evaluatedAt first.expiresAt

structure CertificateComposition
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    where
  first : Cert State Action Version Authority EvidenceRoot Time Nonce
  second : Cert State Action Version Authority EvidenceRoot Time Nonce
  checks : CertificateChecks State Action Version Authority EvidenceRoot Time Nonce
  link : CertificateLink checks first second

def compose
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (first second :
      Cert State Action Version Authority EvidenceRoot Time Nonce)
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (hLink : CertificateLink checks first second) :
    CertificateComposition
      (State := State) (Action := Action) (Version := Version)
      (Authority := Authority) (EvidenceRoot := EvidenceRoot)
      (Time := Time) (Nonce := Nonce) :=
  { first := first, second := second, checks := checks, link := hLink }

def CompositionValid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (composition :
      CertificateComposition
        (State := State) (Action := Action) (Version := Version)
        (Authority := Authority) (EvidenceRoot := EvidenceRoot)
        (Time := Time) (Nonce := Nonce)) :
  Prop :=
  CertificateValid checks composition.first ∧
  CertificateValid checks composition.second ∧
  CertificateLink checks composition.first composition.second

def StepPreserves
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (invariant : State -> Prop)
    (cert : Cert State Action Version Authority EvidenceRoot Time Nonce) :
    Prop :=
  invariant cert.pre -> invariant cert.post

def CompositionPreserves
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (invariant : State -> Prop)
    (composition :
      CertificateComposition
        (State := State) (Action := Action) (Version := Version)
        (Authority := Authority) (EvidenceRoot := EvidenceRoot)
        (Time := Time) (Nonce := Nonce)) :
    Prop :=
  invariant composition.first.pre -> invariant composition.second.post

def LocalCompositionSound
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce) :
  Prop :=
  forall first second (hLink : CertificateLink checks first second),
    CertificateValid checks first ->
    CertificateValid checks second ->
    CompositionValid checks (compose first second checks hLink)

theorem certificate_composition_valid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {first second :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    (hLink : CertificateLink checks first second)
    (hFirst : CertificateValid checks first)
    (hSecond : CertificateValid checks second) :
    CompositionValid checks (compose first second checks hLink) :=
  ⟨hFirst, hSecond, hLink⟩

theorem linked_pair_preserves_invariant
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {invariant : State -> Prop}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {first second :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    (hLink : CertificateLink checks first second)
    (hFirst : StepPreserves invariant first)
    (hSecond : StepPreserves invariant second) :
    CompositionPreserves invariant (compose first second checks hLink) := by
  intro hPre
  have hMid : invariant first.post := hFirst hPre
  have hSecondPre : invariant second.pre := by
    simpa [hLink.left] using hMid
  exact hSecond hSecondPre

/-!
## 14. Nonce consumption and non-replay

Nonce use is modeled as a state predicate.  Consuming a nonce makes that
nonce used, hence the same nonce cannot satisfy the unused requirement again.
-/

def UsedNonce (Nonce : Type u) : Type u :=
  Nonce -> Prop

def NonceUnused
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce) : Prop :=
  Not (used nonce)

def consume
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce) :
    UsedNonce Nonce :=
  fun n => n = nonce ∨ used n

theorem consumed_nonce_is_used
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce) :
    consume used nonce nonce := by
  exact Or.inl rfl

theorem consumed_nonce_not_unused
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce) :
    Not (NonceUnused (consume used nonce) nonce) := by
  intro hUnused
  exact hUnused (consumed_nonce_is_used used nonce)

def AuthorizedByNonce
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce) : Prop :=
  NonceUnused used nonce

theorem same_nonce_cannot_be_authorized_twice
    {Nonce : Type u}
    (used : UsedNonce Nonce)
    (nonce : Nonce)
    (_hFirst : AuthorizedByNonce used nonce) :
    Not (AuthorizedByNonce (consume used nonce) nonce) :=
  consumed_nonce_not_unused used nonce

/-!
## 15. Arbitrary trace composition

A linked trace is intrinsically connected by post/pre state.  Validity and
stepwise invariant preservation are separate; validity is included in the
trace theorem to match operational verification obligations.
-/

inductive LinkedTrace
    (State Action Version Authority EvidenceRoot Time Nonce : Type u) :
    State -> State -> Type u where
  | nil (s : State) :
      LinkedTrace State Action Version Authority EvidenceRoot Time Nonce s s
  | cons
      (cert :
        Cert State Action Version Authority EvidenceRoot Time Nonce)
      {finish : State}
      (rest :
        LinkedTrace
          State Action Version Authority EvidenceRoot Time Nonce
          cert.post finish) :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        cert.pre finish

namespace LinkedTrace

def certs
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    (trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish) :
    List (Cert State Action Version Authority EvidenceRoot Time Nonce) :=
  match trace with
  | nil _ => []
  | cons cert rest => cert :: certs rest

def CertificatesValid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce) :
    List (Cert State Action Version Authority EvidenceRoot Time Nonce) -> Prop
  | [] => True
  | cert :: rest => CertificateValid checks cert ∧ CertificatesValid checks rest

def AdjacentLinksValid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce) :
    List (Cert State Action Version Authority EvidenceRoot Time Nonce) -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      CertificateLink checks first second ∧
      AdjacentLinksValid checks (second :: rest)

def Valid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish) : Prop :=
  CertificatesValid checks (certs trace) ∧
  AdjacentLinksValid checks (certs trace)

def StepwisePreserves
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    (invariant : State -> Prop)
    (trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish) : Prop :=
  match trace with
  | nil _ => True
  | cons cert rest =>
      StepPreserves invariant cert ∧ StepwisePreserves invariant rest

theorem linked_trace_preserves_invariant
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {invariant : State -> Prop}
    {start finish : State}
    {trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish}
    (_hValid : Valid checks trace)
    (hSteps : StepwisePreserves invariant trace)
    (hStart : invariant start) :
    invariant finish := by
  let rec go
      {start finish : State}
      (trace :
        LinkedTrace
          State Action Version Authority EvidenceRoot Time Nonce
          start finish)
      (hSteps : StepwisePreserves invariant trace)
      (hStart : invariant start) :
      invariant finish :=
    match trace with
    | nil _ => hStart
    | cons _cert rest => go rest hSteps.right (hSteps.left hStart)
  exact go trace hSteps hStart

theorem certificates_valid_tail
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {cert :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {rest : List (Cert State Action Version Authority EvidenceRoot Time Nonce)}
    (hValid : CertificatesValid checks (cert :: rest)) :
    CertificatesValid checks rest :=
  hValid.right

theorem adjacent_links_tail
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {first :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {rest : List (Cert State Action Version Authority EvidenceRoot Time Nonce)}
    (hLinks : AdjacentLinksValid checks (first :: rest)) :
    AdjacentLinksValid checks rest := by
  cases rest with
  | nil =>
      trivial
  | cons second tail =>
      cases tail with
      | nil =>
          trivial
      | cons third tail2 =>
          exact hLinks.right

theorem valid_trace_prefix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {cert :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {finish : State}
    {rest :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        cert.post finish}
    (hValid : Valid checks (LinkedTrace.cons cert rest)) :
    CertificateValid checks cert :=
  hValid.left.left

theorem valid_trace_head
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {cert :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {finish : State}
    {rest :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        cert.post finish}
    (hValid : Valid checks (LinkedTrace.cons cert rest)) :
    CertificateValid checks cert :=
  valid_trace_prefix hValid

theorem valid_trace_suffix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {cert :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {finish : State}
    {rest :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        cert.post finish}
    (hValid : Valid checks (LinkedTrace.cons cert rest)) :
    Valid checks rest :=
  ⟨certificates_valid_tail hValid.left, adjacent_links_tail hValid.right⟩

theorem valid_trace_tail
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {cert :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {finish : State}
    {rest :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        cert.post finish}
    (hValid : Valid checks (LinkedTrace.cons cert rest)) :
    Valid checks rest :=
  valid_trace_suffix hValid

theorem valid_trace_adjacent_link
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {first second :
      Cert State Action Version Authority EvidenceRoot Time Nonce}
    {rest : List (Cert State Action Version Authority EvidenceRoot Time Nonce)}
    (hLinks : AdjacentLinksValid checks (first :: second :: rest)) :
    CertificateLink checks first second :=
  hLinks.left

def append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start middle finish : State}
    (left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle)
    (right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish) :
    LinkedTrace
      State Action Version Authority EvidenceRoot Time Nonce
      start finish :=
  match left with
  | nil _ => right
  | cons cert rest => cons cert (append rest right)

def AppendBoundaryLink
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start middle finish : State}
    (checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce)
    (left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle)
    (right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish) : Prop :=
  AdjacentLinksValid checks (certs (append left right))

theorem certificates_valid_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    (left right :
      List (Cert State Action Version Authority EvidenceRoot Time Nonce))
    (hLeft : CertificatesValid checks left)
    (hRight : CertificatesValid checks right) :
    CertificatesValid checks (left ++ right) := by
  induction left with
  | nil =>
      exact hRight
  | cons cert rest ih =>
      exact ⟨hLeft.left, ih hLeft.right⟩

theorem certificates_valid_left_of_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    (left right :
      List (Cert State Action Version Authority EvidenceRoot Time Nonce))
    (hValid : CertificatesValid checks (left ++ right)) :
    CertificatesValid checks left := by
  induction left with
  | nil =>
      trivial
  | cons cert rest ih =>
      exact ⟨hValid.left, ih hValid.right⟩

theorem certificates_valid_right_of_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    (left right :
      List (Cert State Action Version Authority EvidenceRoot Time Nonce))
    (hValid : CertificatesValid checks (left ++ right)) :
    CertificatesValid checks right := by
  induction left with
  | nil =>
      exact hValid
  | cons cert rest ih =>
      exact ih hValid.right

theorem adjacent_links_left_of_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    (left right :
      List (Cert State Action Version Authority EvidenceRoot Time Nonce))
    (hLinks : AdjacentLinksValid checks (left ++ right)) :
    AdjacentLinksValid checks left := by
  induction left with
  | nil =>
      trivial
  | cons first rest ih =>
      cases rest with
      | nil =>
          trivial
      | cons second tail =>
          exact ⟨hLinks.left, ih hLinks.right⟩

theorem adjacent_links_right_of_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    (left right :
      List (Cert State Action Version Authority EvidenceRoot Time Nonce))
    (hLinks : AdjacentLinksValid checks (left ++ right)) :
    AdjacentLinksValid checks right := by
  induction left with
  | nil =>
      exact hLinks
  | cons first rest ih =>
      exact ih (adjacent_links_tail hLinks)

theorem certs_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start middle finish : State}
    (left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle)
    (right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish) :
    certs (append left right) = certs left ++ certs right := by
  induction left with
  | nil s =>
      rfl
  | cons cert rest ih =>
      simp [append, certs, ih]

theorem valid_trace_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hLeft : Valid checks left)
    (hRight : Valid checks right)
    (hBoundary : AppendBoundaryLink checks left right) :
    Valid checks (append left right) := by
  constructor
  · rw [certs_append]
    exact certificates_valid_append (certs left) (certs right)
      hLeft.left hRight.left
  · exact hBoundary

theorem valid_append_implies_valid_prefix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hValid : Valid checks (append left right)) :
    Valid checks left := by
  constructor
  · have hCerts := hValid.left
    rw [certs_append] at hCerts
    exact certificates_valid_left_of_append (certs left) (certs right) hCerts
  · have hLinks := hValid.right
    rw [certs_append] at hLinks
    exact adjacent_links_left_of_append (certs left) (certs right) hLinks

theorem valid_append_implies_valid_suffix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hValid : Valid checks (append left right)) :
    Valid checks right := by
  constructor
  · have hCerts := hValid.left
    rw [certs_append] at hCerts
    exact certificates_valid_right_of_append (certs left) (certs right) hCerts
  · have hLinks := hValid.right
    rw [certs_append] at hLinks
    exact adjacent_links_right_of_append (certs left) (certs right) hLinks

theorem trace_valid_append_iff
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish} :
    Valid checks (append left right) <->
      Valid checks left ∧
      Valid checks right ∧
      AppendBoundaryLink checks left right := by
  constructor
  · intro hValid
    exact ⟨
      valid_append_implies_valid_prefix hValid,
      valid_append_implies_valid_suffix hValid,
      hValid.right⟩
  · intro hAll
    exact valid_trace_append hAll.left hAll.right.left hAll.right.right

theorem valid_prefix_of_valid_full_trace
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {prefixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {suffixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hValid : Valid checks (append prefixTrace suffixTrace)) :
    Valid checks prefixTrace :=
  valid_append_implies_valid_prefix hValid

theorem invalid_suffix_makes_full_trace_invalid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle finish : State}
    {prefixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {suffixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hSuffixInvalid : Not (Valid checks suffixTrace)) :
    Not (Valid checks (append prefixTrace suffixTrace)) := by
  intro hFull
  exact hSuffixInvalid (valid_append_implies_valid_suffix hFull)

theorem trace_prefix_preserves_invariant
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {invariant : State -> Prop}
    {start middle : State}
    {prefixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    (hValid : Valid checks prefixTrace)
    (hSteps : StepwisePreserves invariant prefixTrace)
    (hStart : invariant start) :
    invariant middle :=
  linked_trace_preserves_invariant hValid hSteps hStart

theorem invalid_suffix_preserves_established_prefix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {invariant : State -> Prop}
    {start middle finish : State}
    {prefixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {suffixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    (hPrefix : Valid checks prefixTrace)
    (hSteps : StepwisePreserves invariant prefixTrace)
    (hStart : invariant start)
    (hSuffixInvalid : Not (Valid checks suffixTrace)) :
    Valid checks prefixTrace ∧
    invariant middle ∧
    Not (Valid checks (append prefixTrace suffixTrace)) :=
  ⟨hPrefix,
   trace_prefix_preserves_invariant hPrefix hSteps hStart,
   invalid_suffix_makes_full_trace_invalid hSuffixInvalid⟩

theorem invalid_suffix_does_not_invalidate_established_prefix
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {checks :
      CertificateChecks
        State Action Version Authority EvidenceRoot Time Nonce}
    {start middle : State}
    {prefixTrace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    (hPrefix : Valid checks prefixTrace)
    {finish : State}
    (_suffix :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish) :
    Valid checks prefixTrace :=
  hPrefix

def nonces
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    (trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish) :
    List Nonce :=
  match trace with
  | nil _ => []
  | cons cert rest => cert.nonce :: nonces rest

def consumeTrace
    {Nonce : Type u}
    (used : UsedNonce Nonce) :
    List Nonce -> UsedNonce Nonce
  | [] => used
  | nonce :: rest => consumeTrace (consume used nonce) rest

def TraceNonceValidList
    {Nonce : Type u}
    (initialUsed : UsedNonce Nonce) :
    List Nonce -> Prop
  | [] => True
  | nonce :: rest =>
      NonceUnused initialUsed nonce ∧
      TraceNonceValidList (consume initialUsed nonce) rest

theorem trace_nonce_valid_tail
    {Nonce : Type u}
    {initialUsed : UsedNonce Nonce}
    {nonce : Nonce}
    {rest : List Nonce}
    (hValid : TraceNonceValidList initialUsed (nonce :: rest)) :
    TraceNonceValidList (consume initialUsed nonce) rest :=
  hValid.right

theorem accepted_trace_nonce_not_previously_used
    {Nonce : Type u}
    {initialUsed : UsedNonce Nonce}
    {nonce : Nonce}
    {rest : List Nonce}
    (hValid : TraceNonceValidList initialUsed (nonce :: rest)) :
    NonceUnused initialUsed nonce :=
  hValid.left

theorem trace_nonce_valid_avoids_used
    {Nonce : Type u}
    {used : UsedNonce Nonce}
    {nonce : Nonce}
    {rest : List Nonce}
    (hAlreadyUsed : used nonce)
    (hValid : TraceNonceValidList used rest) :
    nonce ∉ rest := by
  induction rest generalizing used with
  | nil =>
      intro hMem
      cases hMem
  | cons head tail ih =>
      intro hMem
      cases hValid with
      | intro hHead hTail =>
          cases hMem with
          | head =>
              exact hHead hAlreadyUsed
          | tail _ hTailMem =>
              exact ih (Or.inr hAlreadyUsed) hTail hTailMem

theorem trace_nonce_valid_no_used_member
    {Nonce : Type u}
    {used : UsedNonce Nonce}
    {nonce : Nonce}
    {rest : List Nonce}
    (hValid : TraceNonceValidList (consume used nonce) rest) :
    nonce ∉ rest :=
  trace_nonce_valid_avoids_used
    (consumed_nonce_is_used used nonce) hValid

theorem accepted_trace_nonce_not_reused_later
    {Nonce : Type u}
    {initialUsed : UsedNonce Nonce}
    {nonce : Nonce}
    {rest : List Nonce}
    (hValid : TraceNonceValidList initialUsed (nonce :: rest)) :
    nonce ∉ rest :=
  trace_nonce_valid_no_used_member hValid.right

theorem trace_nonce_valid_list_implies_nodup
    {Nonce : Type u}
    {initialUsed : UsedNonce Nonce}
    {noncesList : List Nonce}
    (hValid : TraceNonceValidList initialUsed noncesList) :
    noncesList.Nodup := by
  induction noncesList generalizing initialUsed with
  | nil =>
      simp
  | cons nonce rest ih =>
      exact List.nodup_cons.mpr
        ⟨accepted_trace_nonce_not_reused_later hValid,
         ih hValid.right⟩

theorem trace_nonce_valid_list_append
    {Nonce : Type u}
    {initialUsed : UsedNonce Nonce}
    (left right : List Nonce) :
    TraceNonceValidList initialUsed (left ++ right) <->
      TraceNonceValidList initialUsed left ∧
      TraceNonceValidList (consumeTrace initialUsed left) right := by
  induction left generalizing initialUsed with
  | nil =>
      simp [TraceNonceValidList, consumeTrace]
  | cons nonce rest ih =>
      constructor
      · intro hValid
        have hTail := hValid.right
        have hBoth := (ih (initialUsed := consume initialUsed nonce)).mp hTail
        exact ⟨⟨hValid.left, hBoth.left⟩, hBoth.right⟩
      · intro hBoth
        exact ⟨
          hBoth.left.left,
          (ih (initialUsed := consume initialUsed nonce)).mpr
            ⟨hBoth.left.right, hBoth.right⟩⟩

theorem nonces_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start middle finish : State}
    (left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle)
    (right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish) :
    nonces (append left right) = nonces left ++ nonces right := by
  induction left with
  | nil s =>
      rfl
  | cons cert rest ih =>
      simp [append, nonces, ih]

def TraceNonceValid
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    (initialUsed : UsedNonce Nonce)
    (trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish) : Prop :=
  TraceNonceValidList initialUsed (nonces trace)

theorem trace_nonce_valid_implies_nodup
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start finish : State}
    {trace :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start finish}
    {initialUsed : UsedNonce Nonce}
    (hValid : TraceNonceValid initialUsed trace) :
    (nonces trace).Nodup := by
  exact trace_nonce_valid_list_implies_nodup hValid

theorem trace_nonce_valid_append
    {State Action Version Authority EvidenceRoot Time Nonce : Type u}
    {start middle finish : State}
    {left :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        start middle}
    {right :
      LinkedTrace
        State Action Version Authority EvidenceRoot Time Nonce
        middle finish}
    {initialUsed : UsedNonce Nonce}
    (hLeft : TraceNonceValid initialUsed left)
    (hRight :
      TraceNonceValid (consumeTrace initialUsed (nonces left)) right) :
    TraceNonceValid initialUsed (append left right) := by
  unfold TraceNonceValid at *
  rw [nonces_append]
  exact (trace_nonce_valid_list_append (initialUsed := initialUsed)
    (nonces left) (nonces right)).mpr ⟨hLeft, hRight⟩

end LinkedTrace

/-!
## 16. Concrete field-necessity counterexamples

Each counterexample has a good world and a bad world.  The full observation
distinguishes them, but a projection that drops the named field identifies
them, so no sound and complete packet-only verifier exists.
-/

namespace FieldNecessity

inductive AccountabilityField where
  | cargoBinding
  | requirementVersion
  | verifierVersion
  | freshness
  | authority
  | nonce
  | evidenceWindow
  | prePostBinding
  deriving DecidableEq

structure FullAccountabilityPacket where
  cargoBinding : Bool
  requirementVersion : Bool
  verifierVersion : Bool
  freshness : Bool
  authority : Bool
  nonce : Bool
  evidenceWindow : Bool
  prePostBinding : Bool

def getField
    (field : AccountabilityField)
    (packet : FullAccountabilityPacket) : Bool :=
  match field with
  | AccountabilityField.cargoBinding => packet.cargoBinding
  | AccountabilityField.requirementVersion => packet.requirementVersion
  | AccountabilityField.verifierVersion => packet.verifierVersion
  | AccountabilityField.freshness => packet.freshness
  | AccountabilityField.authority => packet.authority
  | AccountabilityField.nonce => packet.nonce
  | AccountabilityField.evidenceWindow => packet.evidenceWindow
  | AccountabilityField.prePostBinding => packet.prePostBinding

def fieldPacket
    (target : AccountabilityField)
    (value : Bool) : FullAccountabilityPacket :=
  { cargoBinding :=
      if target = AccountabilityField.cargoBinding then value else true
    requirementVersion :=
      if target = AccountabilityField.requirementVersion then value else true
    verifierVersion :=
      if target = AccountabilityField.verifierVersion then value else true
    freshness :=
      if target = AccountabilityField.freshness then value else true
    authority :=
      if target = AccountabilityField.authority then value else true
    nonce :=
      if target = AccountabilityField.nonce then value else true
    evidenceWindow :=
      if target = AccountabilityField.evidenceWindow then value else true
    prePostBinding :=
      if target = AccountabilityField.prePostBinding then value else true }

inductive FieldWorld where
  | good
  | bad

def fieldSafe : FieldWorld -> Prop
  | FieldWorld.good => True
  | FieldWorld.bad => False

def fullObservation
    (target : AccountabilityField) :
    FieldWorld -> FullAccountabilityPacket
  | FieldWorld.good => fieldPacket target true
  | FieldWorld.bad => fieldPacket target false

def dropAccountabilityField
    (target : AccountabilityField)
    (packet : FullAccountabilityPacket) :
    AccountabilityField -> Bool :=
  fun field =>
    if field = target then true else getField field packet

theorem full_observation_distinguishes_target
    (target : AccountabilityField) :
    fullObservation target FieldWorld.good ≠
      fullObservation target FieldWorld.bad := by
  intro h
  have hField :
      getField target (fullObservation target FieldWorld.good) =
        getField target (fullObservation target FieldWorld.bad) :=
    congrArg (getField target) h
  cases target <;> simp [fullObservation, fieldPacket, getField] at hField

theorem dropped_accountability_field_collides
    (target : AccountabilityField) :
    dropAccountabilityField target
        (fullObservation target FieldWorld.good) =
      dropAccountabilityField target
        (fullObservation target FieldWorld.bad) := by
  funext field
  by_cases h : field = target
  · simp [dropAccountabilityField, h]
  · cases target <;> cases field <;>
      simp [dropAccountabilityField, fullObservation, fieldPacket, getField] at h ⊢

def FieldDropImpossible (target : AccountabilityField) : Prop :=
  fullObservation target FieldWorld.good ≠
    fullObservation target FieldWorld.bad ∧
  Not (exists verifier : (AccountabilityField -> Bool) -> Prop,
    Sound
      (fun world =>
        dropAccountabilityField target (fullObservation target world))
      fieldSafe verifier ∧
    Complete
      (fun world =>
        dropAccountabilityField target (fullObservation target world))
      fieldSafe verifier)

theorem field_drop_impossible
    (target : AccountabilityField) :
    FieldDropImpossible target := by
  constructor
  · exact full_observation_distinguishes_target target
  · exact dropped_field_impossibility
      (fullObs := fullObservation target)
      (drop := dropAccountabilityField target)
      (safe := fieldSafe)
      (good := FieldWorld.good)
      (bad := FieldWorld.bad)
      (dropped_accountability_field_collides target)
      trivial
      (by intro h; cases h)

theorem every_accountability_field_is_necessary :
    forall target : AccountabilityField, FieldDropImpossible target :=
  field_drop_impossible

inductive CargoBindingWorld where
  | correctCargo
  | swappedCargo

def cargoSafe : CargoBindingWorld -> Prop
  | CargoBindingWorld.correctCargo => True
  | CargoBindingWorld.swappedCargo => False

def cargoFull : CargoBindingWorld -> Bool
  | CargoBindingWorld.correctCargo => true
  | CargoBindingWorld.swappedCargo => false

def dropCargoBinding (_ : Bool) : Unit := ()

theorem drop_cargo_binding_impossible :
    FieldDropImpossible AccountabilityField.cargoBinding :=
  field_drop_impossible AccountabilityField.cargoBinding

inductive RequirementVersionWorld where
  | currentPolicy
  | oldPolicyAccepted

def requirementVersionSafe : RequirementVersionWorld -> Prop
  | RequirementVersionWorld.currentPolicy => True
  | RequirementVersionWorld.oldPolicyAccepted => False

def requirementVersionFull : RequirementVersionWorld -> Bool
  | RequirementVersionWorld.currentPolicy => true
  | RequirementVersionWorld.oldPolicyAccepted => false

def dropRequirementVersion (_ : Bool) : Unit := ()

theorem drop_requirement_version_impossible :
    FieldDropImpossible AccountabilityField.requirementVersion :=
  field_drop_impossible AccountabilityField.requirementVersion

inductive VerifierVersionWorld where
  | currentVerifier
  | staleVerifier

def verifierVersionSafe : VerifierVersionWorld -> Prop
  | VerifierVersionWorld.currentVerifier => True
  | VerifierVersionWorld.staleVerifier => False

def verifierVersionFull : VerifierVersionWorld -> Bool
  | VerifierVersionWorld.currentVerifier => true
  | VerifierVersionWorld.staleVerifier => false

def dropVerifierVersion (_ : Bool) : Unit := ()

theorem drop_verifier_version_impossible :
    FieldDropImpossible AccountabilityField.verifierVersion :=
  field_drop_impossible AccountabilityField.verifierVersion

inductive FreshnessWorld where
  | freshEvidence
  | expiredEvidence

def freshnessSafe : FreshnessWorld -> Prop
  | FreshnessWorld.freshEvidence => True
  | FreshnessWorld.expiredEvidence => False

def freshnessFull : FreshnessWorld -> Bool
  | FreshnessWorld.freshEvidence => true
  | FreshnessWorld.expiredEvidence => false

def dropFreshness (_ : Bool) : Unit := ()

theorem drop_freshness_impossible :
    FieldDropImpossible AccountabilityField.freshness :=
  field_drop_impossible AccountabilityField.freshness

inductive AuthorityWorld where
  | authorizedActor
  | unauthorizedActor

def authoritySafe : AuthorityWorld -> Prop
  | AuthorityWorld.authorizedActor => True
  | AuthorityWorld.unauthorizedActor => False

def authorityFull : AuthorityWorld -> Bool
  | AuthorityWorld.authorizedActor => true
  | AuthorityWorld.unauthorizedActor => false

def dropAuthority (_ : Bool) : Unit := ()

theorem drop_authority_impossible :
    FieldDropImpossible AccountabilityField.authority :=
  field_drop_impossible AccountabilityField.authority

inductive NonceWorld where
  | firstUse
  | replayedUse

def nonceSafe : NonceWorld -> Prop
  | NonceWorld.firstUse => True
  | NonceWorld.replayedUse => False

def nonceFull : NonceWorld -> Bool
  | NonceWorld.firstUse => true
  | NonceWorld.replayedUse => false

def dropNonce (_ : Bool) : Unit := ()

theorem drop_nonce_impossible :
    FieldDropImpossible AccountabilityField.nonce :=
  field_drop_impossible AccountabilityField.nonce

inductive EvidenceWindowWorld where
  | completeWindow
  | truncatedWindow

def evidenceWindowSafe : EvidenceWindowWorld -> Prop
  | EvidenceWindowWorld.completeWindow => True
  | EvidenceWindowWorld.truncatedWindow => False

def evidenceWindowFull : EvidenceWindowWorld -> Bool
  | EvidenceWindowWorld.completeWindow => true
  | EvidenceWindowWorld.truncatedWindow => false

def dropEvidenceWindow (_ : Bool) : Unit := ()

theorem drop_evidence_window_impossible :
    FieldDropImpossible AccountabilityField.evidenceWindow :=
  field_drop_impossible AccountabilityField.evidenceWindow

inductive PrePostBindingWorld where
  | linkedTransition
  | splicedTransition

def prePostBindingSafe : PrePostBindingWorld -> Prop
  | PrePostBindingWorld.linkedTransition => True
  | PrePostBindingWorld.splicedTransition => False

def prePostBindingFull : PrePostBindingWorld -> Bool
  | PrePostBindingWorld.linkedTransition => true
  | PrePostBindingWorld.splicedTransition => false

def dropPrePostBinding (_ : Bool) : Unit := ()

theorem drop_pre_post_binding_impossible :
    FieldDropImpossible AccountabilityField.prePostBinding :=
  field_drop_impossible AccountabilityField.prePostBinding

end FieldNecessity

/-!
## 17. Trust-only insufficiency

Even a complete, symmetric, transitive mutual trust view is not a sufficient
statistic for a particular cargo, time, and execution.  The issue is not
non-transitivity; the issue is missing event-specific evidence.
-/

inductive TrustSubject where
  | shipper
  | carrier

def TrustGraph := TrustSubject -> TrustSubject -> Prop

def CompleteTrust (g : TrustGraph) : Prop :=
  forall a b, g a b

def SymmetricTrust (g : TrustGraph) : Prop :=
  forall a b, g a b -> g b a

def TransitiveTrust (g : TrustGraph) : Prop :=
  forall a b c, g a b -> g b c -> g a c

def perfectTrust : TrustGraph :=
  fun _ _ => True

inductive TrustExecutionWorld where
  | validExecution
  | invalidExecution

def trustObservation (_ : TrustExecutionWorld) : TrustGraph :=
  perfectTrust

def executionOK : TrustExecutionWorld -> Prop
  | TrustExecutionWorld.validExecution => True
  | TrustExecutionWorld.invalidExecution => False

theorem perfect_mutual_trust_still_insufficient :
    CompleteTrust perfectTrust ∧
    SymmetricTrust perfectTrust ∧
    TransitiveTrust perfectTrust ∧
    Not (exists verifier : TrustGraph -> Prop,
      Sound trustObservation executionOK verifier ∧
      Complete trustObservation executionOK verifier) := by
  refine And.intro ?complete (And.intro ?symmetric (And.intro ?transitive ?impossible))
  · intro _a _b
    trivial
  · intro _a _b _h
    trivial
  · intro _a _b _c _hab _hbc
    trivial
  · exact trust_only_observation_insufficient
      (trustView := trustObservation)
      (adoptable := executionOK)
      (safeWorld := TrustExecutionWorld.validExecution)
      (badWorld := TrustExecutionWorld.invalidExecution)
      rfl trivial (by intro h; cases h)

/-!
## 18. Requirement composition

Different participants may impose different requirements.  Collective
eligibility is the conjunction of all requirements over the shared world.
-/

structure Requirement (World : Type u) where
  holds : World -> Prop

def CollectiveEligible
    {World : Type u} {Participant : Type v}
    (req : Participant -> Requirement World)
    (world : World) : Prop :=
  forall i, (req i).holds world

/-!
## 19. Operational verified scalability

This structure records a public joint verifier and operational properties.
It intentionally does not contain semantic sufficiency, evidence sufficiency,
or separate semantic/evidence verifiers as fields.
-/

structure VerifiedScalableFederation
    (M : SupportedFederationModel.{u, v, w, q})
    (N : TranslationNetwork.{u, v, w})
    {Decision : Type r}
    (routePacket : forall i, N.LocalState i -> M.SemanticPacket)
    (decision : forall i, N.LocalState i -> Decision)
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    (checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce)
    (invariant : CertState -> Prop)
    (K : KernelMembershipModel N.Participant M.SemanticPacket Decision) where
  jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop
  jointSound : SupportedJointSound M jointVerifier
  jointComplete : SupportedJointComplete M jointVerifier
  edgePreservesPacket : Route.EdgePreservesPacket N routePacket
  decisionFactorsThroughPacket :
    Route.DecisionDependsOnlyOnPacket N routePacket decision
  routeDecisionIndependent :
    forall {i j : N.Participant}
      (p qroute : Route N.Edge i j)
      (x : N.LocalState i),
      decision j (Route.run N p x) =
      decision j (Route.run N qroute x)
  traceInvariantPreserved :
    forall {start finish : CertState}
      (trace :
        LinkedTrace
          CertState CertAction CertVersion CertAuthority
          CertEvidenceRoot CertTime CertNonce
          start finish),
      LinkedTrace.Valid checks trace ->
      LinkedTrace.StepwisePreserves invariant trace ->
      invariant start ->
      invariant finish
  newMemberInteroperable :
    forall {members : List N.Participant}
      {newMember oldMember : N.Participant},
      AllConform K.ConformsToKernel members ->
      K.ConformsToKernel newMember ->
      oldMember ∈ members ->
      K.Interoperable newMember oldMember
  failureLocalized :
    forall {start middle : CertState}
      {prefixTrace :
        LinkedTrace
          CertState CertAction CertVersion CertAuthority
          CertEvidenceRoot CertTime CertNonce
          start middle}
      {finish : CertState}
      (suffixTrace :
        LinkedTrace
          CertState CertAction CertVersion CertAuthority
          CertEvidenceRoot CertTime CertNonce
          middle finish),
      LinkedTrace.Valid checks prefixTrace ->
      LinkedTrace.StepwisePreserves invariant prefixTrace ->
      invariant start ->
      Not (LinkedTrace.Valid checks suffixTrace) ->
      LinkedTrace.Valid checks prefixTrace ∧
      invariant middle ∧
      Not (LinkedTrace.Valid checks
        (LinkedTrace.append prefixTrace suffixTrace))

/-
Dual sufficiency is already forced by the public RELEASE part of verified
scalability.  Route independence, trace preservation, membership locality,
and failure locality are additional operational requirements; adding them
does not weaken the necessity of semantic and evidence sufficiency.
-/
theorem verified_scalable_federation_requires_dual_sufficiency
    {M : SupportedFederationModel.{u, v, w, q}}
    {N : TranslationNetwork.{u, v, w}}
    {Decision : Type r}
    {routePacket : forall i, N.LocalState i -> M.SemanticPacket}
    {decision : forall i, N.LocalState i -> Decision}
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    {checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce}
    {invariant : CertState -> Prop}
    {K : KernelMembershipModel N.Participant M.SemanticPacket Decision}
    (F :
      VerifiedScalableFederation
        M N routePacket decision checks invariant K)
    (hSemBridge : SemanticFiberBridge M)
    (hEvBridge : EvidenceFiberBridge M) :
    PredicateSufficient M.semanticPacket M.semanticOK ∧
    PredicateSufficient M.evidencePacket M.evidenceOK :=
  exact_supported_release_implies_dual_sufficiency
    F.jointSound F.jointComplete hSemBridge hEvBridge

theorem semantic_mixed_fiber_blocks_verified_scalable_federation
    {M : SupportedFederationModel.{u, v, w, q}}
    {N : TranslationNetwork.{u, v, w}}
    {Decision : Type r}
    {routePacket : forall i, N.LocalState i -> M.SemanticPacket}
    {decision : forall i, N.LocalState i -> Decision}
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    {checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce}
    {invariant : CertState -> Prop}
    {K : KernelMembershipModel N.Participant M.SemanticPacket Decision}
    {semGood semBad : M.SemanticWorld}
    {evGood : M.EvidenceWorld}
    (hSame : M.semanticPacket semGood = M.semanticPacket semBad)
    (hGoodCompat : M.compatible semGood evGood)
    (hBadCompat : M.compatible semBad evGood)
    (hSemGood : M.semanticOK semGood)
    (hSemBad : Not (M.semanticOK semBad))
    (hEvGood : M.evidenceOK evGood) :
    Not (Nonempty (
      VerifiedScalableFederation
        M N routePacket decision checks invariant K)) := by
  intro hF
  rcases hF with ⟨F⟩
  have hReleaseGood :
      F.jointVerifier (M.semanticPacket semGood, M.evidencePacket evGood) :=
    F.jointComplete semGood evGood hGoodCompat hSemGood hEvGood
  have hReleaseBad :
      F.jointVerifier (M.semanticPacket semBad, M.evidencePacket evGood) := by
    simpa [hSame] using hReleaseGood
  exact hSemBad ((F.jointSound semBad evGood hBadCompat hReleaseBad).left)

theorem evidence_mixed_fiber_blocks_verified_scalable_federation
    {M : SupportedFederationModel.{u, v, w, q}}
    {N : TranslationNetwork.{u, v, w}}
    {Decision : Type r}
    {routePacket : forall i, N.LocalState i -> M.SemanticPacket}
    {decision : forall i, N.LocalState i -> Decision}
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    {checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce}
    {invariant : CertState -> Prop}
    {K : KernelMembershipModel N.Participant M.SemanticPacket Decision}
    {evGood evBad : M.EvidenceWorld}
    {semGood : M.SemanticWorld}
    (hSame : M.evidencePacket evGood = M.evidencePacket evBad)
    (hGoodCompat : M.compatible semGood evGood)
    (hBadCompat : M.compatible semGood evBad)
    (hEvGood : M.evidenceOK evGood)
    (hEvBad : Not (M.evidenceOK evBad))
    (hSemGood : M.semanticOK semGood) :
    Not (Nonempty (
      VerifiedScalableFederation
        M N routePacket decision checks invariant K)) := by
  intro hF
  rcases hF with ⟨F⟩
  have hReleaseGood :
      F.jointVerifier (M.semanticPacket semGood, M.evidencePacket evGood) :=
    F.jointComplete semGood evGood hGoodCompat hSemGood hEvGood
  have hReleaseBad :
      F.jointVerifier (M.semanticPacket semGood, M.evidencePacket evBad) := by
    simpa [hSame] using hReleaseGood
  exact hEvBad ((F.jointSound semGood evBad hBadCompat hReleaseBad).right)

/-!
## 20. Explicit-assumption sufficiency direction

This is a sufficiency theorem inside the stated formal model, not a proof
that the entire physical logistics world has been modeled.  Physical binding,
cryptographic binding, resource completeness, and execution gates remain
explicit assumptions.
-/

structure TypedOperationalAssumptions
    (M : SupportedFederationModel.{u, v, w, q})
    (N : TranslationNetwork.{u, v, w})
    {Decision : Type r}
    (routePacket : forall i, N.LocalState i -> M.SemanticPacket)
    (decision : forall i, N.LocalState i -> Decision)
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    (checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce)
    (invariant : CertState -> Prop)
    (K : KernelMembershipModel N.Participant M.SemanticPacket Decision) where
  semanticEvaluator : M.SemanticPacket -> Prop
  semanticEvaluatorCorrect :
    forall s, semanticEvaluator (M.semanticPacket s) <-> M.semanticOK s
  evidenceEvaluator : M.EvidencePacket -> Prop
  evidenceEvaluatorCorrect :
    forall e, evidenceEvaluator (M.evidencePacket e) <-> M.evidenceOK e
  edgePreservesPacket : Route.EdgePreservesPacket N routePacket
  decisionFactorsThroughPacket :
    Route.DecisionDependsOnlyOnPacket N routePacket decision

structure ActualExecutionBridge
    (M : SupportedFederationModel.{u, v, w, q})
    (jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop) where
  ActualWorld : Type r
  actualSemantic : ActualWorld -> M.SemanticWorld
  actualEvidence : ActualWorld -> M.EvidenceWorld
  Executed : ActualWorld -> Prop
  PhysicalConditionHolds : ActualWorld -> Prop
  ResourceFeasible : ActualWorld -> Prop
  ActualSafe : ActualWorld -> Prop
  compatibleActual :
    forall actual,
      M.compatible (actualSemantic actual) (actualEvidence actual)
  executionRequiresRelease :
    forall actual,
      Executed actual ->
      jointVerifier
        (M.semanticPacket (actualSemantic actual),
         M.evidencePacket (actualEvidence actual))
  physicalBindingSound :
    forall actual,
      M.evidenceOK (actualEvidence actual) ->
      PhysicalConditionHolds actual
  resourceModelSound :
    forall actual,
      M.semanticOK (actualSemantic actual) ->
      ResourceFeasible actual
  actualSafety :
    forall actual,
      M.semanticOK (actualSemantic actual) ->
      M.evidenceOK (actualEvidence actual) ->
      PhysicalConditionHolds actual ->
      ResourceFeasible actual ->
      ActualSafe actual

theorem executed_world_is_safe
    {M : SupportedFederationModel.{u, v, w, q}}
    {jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop}
    (hSound : SupportedJointSound M jointVerifier)
    (B : ActualExecutionBridge M jointVerifier)
    {actual : B.ActualWorld}
    (hExecuted : B.Executed actual) :
    B.ActualSafe actual := by
  have hRelease := B.executionRequiresRelease actual hExecuted
  have hOK :=
    hSound (B.actualSemantic actual) (B.actualEvidence actual)
      (B.compatibleActual actual) hRelease
  have hPhysical := B.physicalBindingSound actual hOK.right
  have hResource := B.resourceModelSound actual hOK.left
  exact B.actualSafety actual hOK.left hOK.right hPhysical hResource

theorem common_kernel_and_accountability_suffice_under_typed_assumptions
    {M : SupportedFederationModel.{u, v, w, q}}
    {N : TranslationNetwork.{u, v, w}}
    {Decision : Type r}
    {routePacket : forall i, N.LocalState i -> M.SemanticPacket}
    {decision : forall i, N.LocalState i -> Decision}
    {CertState CertAction CertVersion CertAuthority
      CertEvidenceRoot CertTime CertNonce : Type r}
    {checks :
      CertificateChecks
        CertState CertAction CertVersion CertAuthority
        CertEvidenceRoot CertTime CertNonce}
    {invariant : CertState -> Prop}
    {K : KernelMembershipModel N.Participant M.SemanticPacket Decision}
    (A :
      TypedOperationalAssumptions
        M N routePacket decision checks invariant K) :
    Nonempty (
      VerifiedScalableFederation
        M N routePacket decision checks invariant K) := by
  let jointVerifier : M.SemanticPacket × M.EvidencePacket -> Prop :=
    fun p => A.semanticEvaluator p.1 ∧ A.evidenceEvaluator p.2
  have hSound : SupportedJointSound M jointVerifier := by
    intro s e _hCompat hJoint
    exact ⟨
      (A.semanticEvaluatorCorrect s).mp hJoint.left,
      (A.evidenceEvaluatorCorrect e).mp hJoint.right⟩
  have hComplete : SupportedJointComplete M jointVerifier := by
    intro s e _hCompat hs he
    exact ⟨
      (A.semanticEvaluatorCorrect s).mpr hs,
      (A.evidenceEvaluatorCorrect e).mpr he⟩
  refine Nonempty.intro ?federationValue
  refine
    { jointVerifier := jointVerifier
      jointSound := hSound
      jointComplete := hComplete
      edgePreservesPacket := A.edgePreservesPacket
      decisionFactorsThroughPacket := A.decisionFactorsThroughPacket
      routeDecisionIndependent := ?route
      traceInvariantPreserved := ?trace
      newMemberInteroperable := ?member
      failureLocalized := ?failure }
  · intro i j p qroute x
    exact Route.route_decision_independent
      N A.edgePreservesPacket A.decisionFactorsThroughPacket p qroute x
  · intro start finish trace hValid hSteps hStart
    exact LinkedTrace.linked_trace_preserves_invariant
      hValid hSteps hStart
  · intro members newMember oldMember hExisting hNew hOld
    exact new_member_interoperates_with_all_existing
      K hExisting hNew hOld
  · intro start middle prefixTrace finish suffixTrace hPrefix hSteps hStart hSuffixInvalid
    exact LinkedTrace.invalid_suffix_preserves_established_prefix
      hPrefix hSteps hStart hSuffixInvalid

/-!
## 21. Optimization is not enough

Optimization selects a candidate.  Decision semantics makes the candidate
and requirements mean the same thing.  Accountability verification checks
that the requirements hold for the particular execution.
-/

theorem perfect_optimizer_is_not_enough
    {World : Type u} {OptView : Type v} {Plan : Type w}
    {optView : World -> OptView}
    {candidate : World -> Plan}
    {adoptable : World -> Plan -> Prop}
    {omegaSafe omegaBad : World}
    (hSameView : optView omegaSafe = optView omegaBad)
    (hSamePlan : candidate omegaSafe = candidate omegaBad)
    (hAdoptable : adoptable omegaSafe (candidate omegaSafe))
    (hNotAdoptable : Not (adoptable omegaBad (candidate omegaBad))) :
    Not (exists verifier : OptView -> Plan -> Prop,
      And
        (forall omega,
          verifier (optView omega) (candidate omega) ->
            adoptable omega (candidate omega))
        (forall omega,
          adoptable omega (candidate omega) ->
            verifier (optView omega) (candidate omega))) := by
  intro hVerifier
  cases hVerifier with
  | intro verifier hv =>
      have hAcceptSafe :
          verifier (optView omegaSafe) (candidate omegaSafe) :=
        hv.right omegaSafe hAdoptable
      have hAcceptSameView :
          verifier (optView omegaBad) (candidate omegaSafe) :=
        by simpa [hSameView] using hAcceptSafe
      have hAcceptBad :
          verifier (optView omegaBad) (candidate omegaBad) :=
        by simpa [hSamePlan] using hAcceptSameView
      exact hNotAdoptable (hv.left omegaBad hAcceptBad)

theorem optimization_view_not_adoptability_sufficient
    {M : FederationModel.{u, v, w, q}}
    {OptView : Type r} {Plan : Type u}
    {optView : M.SemanticWorld × M.EvidenceWorld -> OptView}
    {candidate : M.SemanticWorld × M.EvidenceWorld -> Plan}
    {worldGood worldBad : M.SemanticWorld × M.EvidenceWorld}
    (hSameView : optView worldGood = optView worldBad)
    (hSamePlan : candidate worldGood = candidate worldBad)
    (hGood :
      M.semanticOK worldGood.1 ∧ M.evidenceOK worldGood.2)
    (hBad :
      Not (M.semanticOK worldBad.1 ∧ M.evidenceOK worldBad.2)) :
    Not (exists verifier : OptView -> Plan -> Prop,
      And
        (forall world,
          verifier (optView world) (candidate world) ->
            (M.semanticOK world.1 ∧ M.evidenceOK world.2))
        (forall world,
          (M.semanticOK world.1 ∧ M.evidenceOK world.2) ->
            verifier (optView world) (candidate world))) :=
  perfect_optimizer_is_not_enough
    (optView := optView)
    (candidate := candidate)
    (adoptable := fun world _plan =>
      M.semanticOK world.1 ∧ M.evidenceOK world.2)
    hSameView hSamePlan hGood hBad

theorem optimizer_output_does_not_determine_verified_adoptability
    {M : SupportedFederationModel.{u, v, w, q}}
    {OptView : Type r} {Plan : Type u}
    {optView : M.SemanticWorld × M.EvidenceWorld -> OptView}
    {candidate : M.SemanticWorld × M.EvidenceWorld -> Plan}
    {worldGood worldBad : M.SemanticWorld × M.EvidenceWorld}
    (hSameView : optView worldGood = optView worldBad)
    (hSamePlan : candidate worldGood = candidate worldBad)
    (hGood :
      M.compatible worldGood.1 worldGood.2 ∧
      M.semanticOK worldGood.1 ∧
      M.evidenceOK worldGood.2)
    (hBad :
      Not (
        M.compatible worldBad.1 worldBad.2 ∧
        M.semanticOK worldBad.1 ∧
        M.evidenceOK worldBad.2)) :
    Not (exists verifier : OptView -> Plan -> Prop,
      And
        (forall world,
          verifier (optView world) (candidate world) ->
            (M.compatible world.1 world.2 ∧
             M.semanticOK world.1 ∧
             M.evidenceOK world.2))
        (forall world,
          (M.compatible world.1 world.2 ∧
           M.semanticOK world.1 ∧
           M.evidenceOK world.2) ->
            verifier (optView world) (candidate world))) :=
  perfect_optimizer_is_not_enough
    (optView := optView)
    (candidate := candidate)
    (adoptable := fun world _plan =>
      M.compatible world.1 world.2 ∧
      M.semanticOK world.1 ∧
      M.evidenceOK world.2)
    hSameView hSamePlan hGood hBad

/-!
## 22. Finite examples

These examples instantiate the abstract theorems with tiny finite models:
an exact comparable federation, a no-bridge counterexample, a three-node
route comparison, a two-certificate trace, and a field-necessity corollary.
-/

namespace FiniteExamples

inductive One where
  | star

def comparableModel : SupportedFederationModel where
  SemanticWorld := One
  EvidenceWorld := One
  SemanticPacket := Unit
  EvidencePacket := Unit
  semanticPacket := fun _ => ()
  evidencePacket := fun _ => ()
  semanticOK := fun _ => True
  evidenceOK := fun _ => True
  compatible := fun _ _ => True

def comparableVerifier (_p : Unit × Unit) : Prop := True

theorem comparable_example_dual_sufficiency :
    PredicateSufficient
        comparableModel.semanticPacket comparableModel.semanticOK ∧
    PredicateSufficient
        comparableModel.evidencePacket comparableModel.evidenceOK := by
  apply exact_supported_release_implies_dual_sufficiency
    (jointVerifier := comparableVerifier)
  · intro s e hCompat hRelease
    exact ⟨trivial, trivial⟩
  · intro s e hCompat hs he
    trivial
  · intro x y hPacket
    exact ⟨One.star, trivial, trivial, trivial⟩
  · intro x y hPacket
    exact ⟨One.star, trivial, trivial, trivial⟩

theorem no_bridge_example :
    (exists jointVerifier,
      SupportedJointSound NoBridgeCounterexample.model jointVerifier ∧
      SupportedJointComplete NoBridgeCounterexample.model jointVerifier) ∧
    Not (
      PredicateSufficient
        NoBridgeCounterexample.model.semanticPacket
        NoBridgeCounterexample.model.semanticOK) ∧
    Not (SemanticFiberBridge NoBridgeCounterexample.model) :=
  NoBridgeCounterexample.exact_joint_release_without_fiber_bridge_does_not_imply_semantic_sufficiency

inductive Participant3 where
  | A
  | B
  | C

def Local3 (_p : Participant3) : Type := Unit

inductive Edge3 : Participant3 -> Participant3 -> Type where
  | ab : Edge3 Participant3.A Participant3.B
  | bc : Edge3 Participant3.B Participant3.C
  | ac : Edge3 Participant3.A Participant3.C

def network3 : TranslationNetwork where
  Participant := Participant3
  LocalState := Local3
  Edge := Edge3
  translate := by
    intro i j edge x
    cases edge <;> exact ()

def routeABC : Route network3.Edge Participant3.A Participant3.C :=
  Route.cons Edge3.ab (Route.cons Edge3.bc Route.id)

def routeAC : Route network3.Edge Participant3.A Participant3.C :=
  Route.cons Edge3.ac Route.id

def encode3 (i : network3.Participant) (_x : network3.LocalState i) :
    Unit := ()

def decision3 (i : network3.Participant) (_x : network3.LocalState i) :
    Unit := ()

theorem three_participant_routes_agree :
    decision3 Participant3.C (Route.run network3 routeABC ()) =
    decision3 Participant3.C (Route.run network3 routeAC ()) := by
  apply Route.route_decision_independent
    (N := network3)
    (encode := encode3)
    (decision := decision3)
  · intro i j edge x
    cases edge <;> rfl
  · exists fun _ => ()
    intro i x
    rfl

abbrev TraceCert :=
  Cert Bool Unit Unit Unit Unit Unit Bool

def cert1 : TraceCert :=
  { pre := false
    action := ()
    post := true
    requirementVersion := ()
    verifierVersion := ()
    authority := ()
    previousEvidenceRoot := none
    evidenceRoot := ()
    evaluatedAt := ()
    expiresAt := ()
    nonce := false }

def cert2 : TraceCert :=
  { pre := true
    action := ()
    post := false
    requirementVersion := ()
    verifierVersion := ()
    authority := ()
    previousEvidenceRoot := some ()
    evidenceRoot := ()
    evaluatedAt := ()
    expiresAt := ()
    nonce := true }

def trace2 :
    LinkedTrace Bool Unit Unit Unit Unit Unit Bool false false :=
  LinkedTrace.cons cert1 (LinkedTrace.cons cert2 (LinkedTrace.nil false))

theorem trace2_nonce_valid :
    LinkedTrace.TraceNonceValid (fun _ => False) trace2 := by
  simp [
    trace2,
    cert1,
    cert2,
    LinkedTrace.TraceNonceValid,
    LinkedTrace.TraceNonceValidList,
    LinkedTrace.nonces,
    NonceUnused,
    consume
  ]

theorem trace2_nonce_nodup :
    (LinkedTrace.nonces trace2).Nodup :=
  LinkedTrace.trace_nonce_valid_implies_nodup trace2_nonce_valid

theorem field_necessity_example :
    FieldNecessity.FieldDropImpossible
      FieldNecessity.AccountabilityField.nonce :=
  FieldNecessity.drop_nonce_impossible

end FiniteExamples

end PhysicalInternet
