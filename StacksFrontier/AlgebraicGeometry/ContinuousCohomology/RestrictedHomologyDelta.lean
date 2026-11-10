module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InvariantsDeltaForget
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypePermutation
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.DualHomological

/-!
# Homology of a profinite group with finite coefficients

Let `φ : G → Γ` be a continuous homomorphism of compact groups and `Λ` a finite ring, not
necessarily commutative: the source's coefficient rings are finite rings acting on left modules
([Stacks, Section 03SZ], `trace.tex` lines 385–388, and Section 03VJ, line 3210). For a finite left
`Λ`-module `M` with a continuous action of `Γ`, the homology of `G` with coefficients in `M` is
`H_i(G, M) = H^i(G, M^∨)^∨`,
the character dual of the continuous cohomology of `G` with coefficients in the character module
`M^∨ = Hom(M, ℚ/ℤ)`, a left `Λᵐᵒᵖ`-module (right `Λ`-module), whose cohomology is a left
`Λᵐᵒᵖ`-module and dualizes back to a left `Λ`-module. This is the "trivial duality"
`H^i(G, M)^∧ = H_i(G, M^∧)` of the source (Section 03VI): for finite `M` the continuous homology
`L_i H_0(G, M)` of `G`, computed on compact modules, is the dual of the cohomology of the discrete
module `M^∨`, and it agrees with the continuous homology `lim_U Tor^{Λ[G/U]}_i(Λ, M)` over the
open normal subgroups `U` of `G`. For `G` topologically finitely generated it is also
`Tor^{Λ[[G]]}_i(M, Λ)` (the notes on homology in the source, `trace.tex`, lines 3163–3169); that
identification is not used here.

`M ↦ H_i(G, M)` is a homological δ-functor (`Stacks.ContinuousCohomology.restrictedHomologyDelta`),
and `H_0(G, M)` is, naturally in `M`, the module of coinvariants `M_G`
(`Stacks.ContinuousCohomology.restrictedHomologyZeroIso`).

## Main definitions

* `Stacks.ContinuousCohomology.restrictedHomologyDelta`.
* `Stacks.ContinuousCohomology.restrictedCoinvariantsFunctor` — `M ↦ M_G`.
* `Stacks.ContinuousCohomology.restrictedHomologyZeroIso` — `H_0(G, -) ≅ (-)_G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

open scoped CharacterModule.MulOppositeAction

universe w

namespace Stacks.ContinuousCohomology

section Representation

variable {Λ : Type} [Ring Λ] {G : Type w} [Group G] {V : Type w} [AddCommGroup V] [Module Λ V]
  (σ : Representation Λ G V)

/-- The contragredient of a restricted representation is the restriction of the contragredient. -/
lemma characterRepresentation_apply_of_eq {Γ : Type w} [Group Γ] (τ : Representation Λ Γ V)
    (φ : G →* Γ) (hσ : ∀ g, σ g = τ (φ g)) (g : G) (c : CharacterModule V) :
    characterRepresentation σ g c = characterRepresentation τ (φ g) c :=
  DFunLike.ext _ _ fun m ↦ by
    rw [characterRepresentation_apply, characterRepresentation_apply, hσ, map_inv]

/-- An invariant character kills the differences `g • v - v`, hence their span. -/
lemma invariant_character_eq_zero {c : CharacterModule V}
    (hc : ∀ g, characterRepresentation σ g c = c) {x : V}
    (hx : x ∈ Stacks.Trace.coinvariantsKer σ) : c x = 0 := by
  have key : ∀ x ∈ Stacks.Trace.coinvariantsKer σ, ∀ a : Λ, c (a • x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨g, v⟩, rfl⟩ := hy
      intro a
      have h1 : c (σ g⁻¹⁻¹ (a • v)) = c (a • v) := DFunLike.congr_fun (hc g⁻¹) (a • v)
      rw [inv_inv] at h1
      change c (a • (σ g v - v)) = 0
      rw [smul_sub, ← map_smul, map_sub, h1, sub_self]
    | zero => intro a; rw [smul_zero, map_zero]
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add, hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [smul_smul]; exact hy _
  simpa using key x hx 1

/-- **Invariant characters are characters of the coinvariants**:
`(V^∨)^G ≃ (V_G)^∨`, for any submodule `P` of `V^∨` whose members are the invariant characters. -/
def invariantsCharacterEquiv (P : Submodule Λᵐᵒᵖ (CharacterModule V))
    (hP : ∀ c, c ∈ P ↔ ∀ g, characterRepresentation σ g c = c) :
    P ≃ₗ[Λᵐᵒᵖ] CharacterModule (Stacks.Trace.coinvariants σ) where
  toFun c := QuotientAddGroup.lift (Stacks.Trace.coinvariantsKer σ).toAddSubgroup c.1
    fun _ hx ↦ invariant_character_eq_zero σ ((hP c.1).mp c.2) hx
  map_add' _ _ := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H v => rfl
  map_smul' _ _ := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H v => rfl
  invFun c := ⟨c.comp (QuotientAddGroup.mk' (Stacks.Trace.coinvariantsKer σ).toAddSubgroup),
    (hP _).mpr fun g ↦ DFunLike.ext _ _ fun v ↦ by
      change c (Submodule.Quotient.mk (σ g⁻¹ v) : Stacks.Trace.coinvariants σ) =
        c (Submodule.Quotient.mk v)
      congr 1
      rw [Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨(g⁻¹, v), rfl⟩⟩
  left_inv _ := rfl
  right_inv c := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H v => rfl

/-- **`#V^G = #(V^∨)_G`** for a finite module `V`: invariant characters of `V^∨` are the characters
of its coinvariants, and `V ≅ (V^∨)^∨`. -/
theorem natCard_invariants_eq_natCard_coinvariants_characterRepresentation [Finite V] :
    Nat.card {v : V // ∀ g, σ g v = v} =
      Nat.card (Stacks.Trace.coinvariants (characterRepresentation σ)) := by
  let σ' := characterRepresentation σ
  let P : Submodule Λᵐᵒᵖᵐᵒᵖ (CharacterModule (CharacterModule V)) :=
    { carrier := {c | ∀ g, characterRepresentation σ' g c = c}
      add_mem' := fun {a b} ha hb g ↦ by
        change characterRepresentation σ' g (a + b) = a + b
        rw [map_add, ha g, hb g]
      zero_mem' := fun g ↦ map_zero _
      smul_mem' := fun r c hc g ↦ by
        change characterRepresentation σ' g (r • c) = r • c
        rw [map_smul, hc g] }
  have : Finite (CharacterModule V) := CharacterModule.finite V
  have : Finite (Stacks.Trace.coinvariants σ') :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  rw [← CharacterModule.natCard_eq (Stacks.Trace.coinvariants σ'),
    ← Nat.card_congr (invariantsCharacterEquiv σ' P fun _ ↦ Iff.rfl).toEquiv]
  have hev : ∀ (g : G) (v : V), characterRepresentation σ' g (AddMonoidHom.eval v) =
      AddMonoidHom.eval (σ g v) := fun g v ↦ DFunLike.ext _ _ fun c ↦ by
    change c (σ g⁻¹⁻¹ v) = c (σ g v)
    rw [inv_inv]
  exact Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.ofBijective (AddMonoidHom.eval : V →+ CharacterModule (CharacterModule V))
      (CharacterModule.eval_bijective V)) fun v ↦ by
      change (∀ g, σ g v = v) ↔ ∀ g, characterRepresentation σ' g (AddMonoidHom.eval v) =
        AddMonoidHom.eval v
      refine forall_congr' fun g ↦ ?_
      rw [hev]
      exact (CharacterModule.eval_injective V).eq_iff.symm)

end Representation

/-- Enough injectives for continuous discrete modules at the module universe of the group, pinned:
the general instance is indexed by `max u v w`, which instance search cannot match with `w`. -/
local instance (priority := 3000) enoughInjectives_continuousModule_sameUniverse (Λ : Type)
    [Ring Λ] (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, w, w} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, w, 0} Λ G

variable (Λ : Type) [Ring Λ] [Finite Λ] {G Γ : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Γ]
  [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  (φ : G →ₜ* Γ)

/-- **The homological δ-functor `M ↦ H_i(G, M) = H^i(G, M^∨)^∨`** on finite `Λ`-modules with a
continuous `Γ`-action, `G` acting through `φ`. -/
def restrictedHomologyDelta :
    Stacks.CategoryHomology.HomologicalDeltaFunctor (FiniteTypeContinuousModule.{0, w, w} Λ Γ)
      (ModuleCat.{w} Λ) :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.ofDeltaFunctorDual
    (restrictedCohomologyDelta Λᵐᵒᵖ φ) (finiteTypeContinuousModuleDual.{0, w, w} Λ Γ)

/-- **The coinvariants `M ↦ M_G`** of finite `Λ`-modules with a continuous `Γ`-action, `G` acting
through `φ`. -/
def restrictedCoinvariantsFunctor :
    FiniteTypeContinuousModule.{0, w, w} Λ Γ ⥤ ModuleCat.{w} Λ where
  obj N := ModuleCat.of Λ (Stacks.Trace.coinvariants
    (finiteTypeContinuousModuleRepresentation Λ G ((finiteTypeContinuousModuleRes Λ φ).obj N)))
  map v := ModuleCat.ofHom (finiteTypeContinuousModuleCoinvariantsMap Λ G
    ((finiteTypeContinuousModuleRes Λ φ).map v))
  map_id _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    rfl

/-- The coinvariants of a finite `Λ`-module with a continuous `H`-action are finite. -/
instance finite_coinvariants_finiteTypeContinuousModuleRepresentation {H : Type w} [Group H]
    [TopologicalSpace H] (N : FiniteTypeContinuousModule.{0, w, w} Λ H) :
    Finite (Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ H N)) := by
  have : Module.Finite Λ N.obj.obj.obj.V := N.property
  have : Finite N.obj.obj.obj.V := Module.finite_of_finite Λ
  exact Finite.of_surjective _ (Submodule.mkQ_surjective _)

/-- The invariants of the dual are the dual of the coinvariants. -/
def restrictedInvariantsDualIsoApp (N : (FiniteTypeContinuousModule.{0, w, w} Λ Γ)ᵒᵖ) :
    (continuousModuleRingInvariants.{0, w, w} Λᵐᵒᵖ G).obj
        ((finiteTypeContinuousModuleToRes Λᵐᵒᵖ φ).obj
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Γ).obj N)) ≅
      (CharacterModule.moduleCatDualFunctor Λ).obj
        (Opposite.op ((restrictedCoinvariantsFunctor Λ φ).obj N.unop)) :=
  (invariantsCharacterEquiv (finiteTypeContinuousModuleRepresentation
      Λ G ((finiteTypeContinuousModuleRes Λ φ).obj N.unop))
      (continuousModuleInvariantsSubmodule.{0, w, w} Λᵐᵒᵖ G
        ((finiteTypeContinuousModuleToRes Λᵐᵒᵖ φ).obj
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Γ).obj N))) fun c ↦
      show (∀ g, characterRepresentation (finiteTypeContinuousModuleRepresentation Λ Γ N.unop)
          (φ g) c = c) ↔ _ from forall_congr' fun g ↦ Iff.of_eq (congrArg (fun z ↦ z = c)
        (characterRepresentation_apply_of_eq _ (finiteTypeContinuousModuleRepresentation Λ Γ N.unop)
          φ.toMonoidHom (fun _ ↦ rfl) g c).symm)).toModuleIso

/-- The invariants of the dual are the dual of the coinvariants, naturally. -/
def restrictedInvariantsDualIso :
    finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙ finiteTypeContinuousModuleToRes Λᵐᵒᵖ φ ⋙
        continuousModuleRingInvariants.{0, w, w} Λᵐᵒᵖ G ≅
      (restrictedCoinvariantsFunctor Λ φ).op ⋙ CharacterModule.moduleCatDualFunctor Λ :=
  NatIso.ofComponents (restrictedInvariantsDualIsoApp Λ φ)
    (fun {N N'} v ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply CharacterModule.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x => rfl)

/-- Pontryagin duality on the coinvariants: `M_G ≅ ((M_G)^∨)^∨`, naturally. -/
def restrictedCoinvariantsEvalIso :
    restrictedCoinvariantsFunctor Λ φ ≅
      ((restrictedCoinvariantsFunctor Λ φ).op ⋙ CharacterModule.moduleCatDualFunctor Λ).rightOp ⋙
        CharacterModule.moduleCatDualOfMulOppositeFunctor Λ :=
  NatIso.ofComponents (fun _ ↦ (CharacterModule.evalEquiv _ Λ).toModuleIso)
    (fun _ ↦ rfl)

/-- `H⁰(G, -)` on the dual is the invariants of the dual. -/
def restrictedCohomologyZeroDualIso :
    finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙ (restrictedCohomologyDelta Λᵐᵒᵖ φ).functor 0 ≅
      (restrictedCoinvariantsFunctor Λ φ).op ⋙ CharacterModule.moduleCatDualFunctor Λ :=
  Functor.isoWhiskerLeft (finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙
      finiteTypeContinuousModuleToRes Λᵐᵒᵖ φ)
    (eqToIso (rfl : (invariantsDelta.{0, w, w} Λᵐᵒᵖ (G := G)).functor 0 =
        (continuousModuleRingInvariants.{0, w, w} Λᵐᵒᵖ G).rightDerived 0) ≪≫
      (continuousModuleRingInvariants.{0, w, w} Λᵐᵒᵖ G).rightDerivedZeroIsoSelf) ≪≫
    restrictedInvariantsDualIso Λ φ

/-- A natural isomorphism of contravariant functors gives one of their `rightOp`s. -/
def natIsoRightOp {C D : Type*} [Category C] [Category D] {F G : Cᵒᵖ ⥤ D} (α : F ≅ G) :
    G.rightOp ≅ F.rightOp where
  hom := NatTrans.rightOp α.hom
  inv := NatTrans.rightOp α.inv
  hom_inv_id := NatTrans.ext (funext fun X ↦ Quiver.Hom.unop_inj (α.inv_hom_id_app (Opposite.op X)))
  inv_hom_id := NatTrans.ext (funext fun X ↦ Quiver.Hom.unop_inj (α.hom_inv_id_app (Opposite.op X)))

/-- **`H_0(G, M) ≅ M_G`**, naturally in `M`. -/
def restrictedHomologyZeroIso :
    (restrictedHomologyDelta Λ φ).functor 0 ≅ restrictedCoinvariantsFunctor Λ φ :=
  Functor.isoWhiskerRight (natIsoRightOp (restrictedCohomologyZeroDualIso Λ φ)).symm
      (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ) ≪≫
    (restrictedCoinvariantsEvalIso Λ φ).symm

end Stacks.ContinuousCohomology

end
