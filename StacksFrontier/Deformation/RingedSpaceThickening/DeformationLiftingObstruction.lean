module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPresentationComparison
public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationLiftEquiv
public import StacksFrontier.Deformation.RingedSpaceThickening.LiftingObstructionBothClauses
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedPullbackActingGroup
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentInverseImageExt
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a morphism of first order thickenings of ringed spaces (Stacks 08U8)

Let `D` be a commutative cube of ringed spaces as in **Stacks 08U9** — first order thickenings
`i₁ : X₁ ⟶ X'₁`, `t₁ : S₁ ⟶ S'₁` in front, `i₂ : X₂ ⟶ X'₂`, `t₂ : S₂ ⟶ S'₂` at the back, the
structure morphisms and the comparisons `g : X₂ ⟶ X₁`, `S₂ ⟶ S₁`, `S'₂ ⟶ S'₁` — together with the
modules `𝒢_j = Ker(i_j^♯)`, a `g`-map `ν : 𝒢₁ ⟶ 𝒢₂`, and front and back solutions of the
problem of **Stacks 08U7** making the diagram of ideal rows of **Stacks 08UA** commute
(`AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram`). **Stacks 08U8** asserts:

1. there is a canonical element of `Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)` whose vanishing is
   necessary and sufficient for the existence of a morphism of ringed spaces `X'₂ ⟶ X'₁` fitting
   into (08U9) compatibly with `ν`;
2. if such a morphism exists, the set of all of them is a principal homogeneous space under
   `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂) = Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)
     = Ext⁰_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)`.

This file proves both, in the source's own spelling of the groups and with nothing assumed
beyond `D`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.canonicalObstructionClass`: for the one-site diagram
  of the source's reduction, the class of Step 1 read in `Ext¹(NL_{𝒪₁/𝒪_{B₁}}, g_*𝒢₂)`, the
  presentation `α` of Step 1 being removed by the comparison quasi-isomorphism
  `NL(α) ⟶ NL_{𝒪₁/𝒪_{B₁}}` of **Stacks 08TY**.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.obstructionClass`: **the
  canonical element of clause (1)**, in `Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.liftAct`: **the action of
  clause (2)** of `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)` on the morphisms fitting into the diagram.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.obstructionClass_eq_zero_iff`:
  clause (1).
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.liftAct_zero`,
  `liftAct_add`, `existsUnique_liftAct`: clause (2).
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.lifting_obstruction_and_torsor`:
  **Stacks 08U8**, both clauses together.

## Implementation notes

The proof is the source's. Its reduction to one space is
`DeformationIdealDiagram.toFirstOrderLiftDiagram`, the diagram of sheaves of rings on `X₂`
obtained by pulling the front back along `g`, with `DeformationIdealDiagram.liftEquiv`
identifying the morphisms of ringed spaces fitting into (08U9) compatibly with `ν` with the
homomorphisms of sheaves of rings fitting into the reduced diagram. On one space, Steps 1 to 3
of the source's proof are `liftDiagramObstructionClass_eq_zero_iff`, and the principal
homogeneous space structure is `FirstOrderLiftDiagram.existsUnique_translateHom`. The passage
between the groups of the reduced situation and those of the source's statement —
`Ext¹_{g⁻¹𝒪_{X₁}}(NL_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂) = Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)` and
`Hom_{g⁻¹𝒪_{X₁}}(Ω_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)` — is
`inverseImageNaiveCotangentExtOneAddEquiv` and `inverseImageDifferentialsHomAddEquiv`.

The action of clause (2) is the source's: a homomorphism `θ : Ω_{X₁/S₁} ⟶ g_*𝒢₂` moves a lift,
read on `X₂` as a homomorphism `φ : g⁻¹𝒪_{X'₁} ⟶ 𝒪_{X'₂}`, to `φ + θ ∘ d`
(`liftAct_spec`); it is not merely asserted to exist.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

universe v u w

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

/-! ### The class of Step 1, read on the canonical naive cotangent complex -/

section Canonical

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-- The comparison `NL(α) ⟶ NL_{𝒪₁/𝒪_{B₁}}` of **Stacks 08TL** for the presentation `α` of
Step 1 of the proof of **Stacks 08U8**. -/
abbrev liftDiagramNaiveCotangentComparison :=
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f (FirstOrderLiftDiagram.pairPresheaf D)
    (FirstOrderLiftDiagram.pairAlpha D)

/-- The comparison `NL(α) ⟶ NL_{𝒪₁/𝒪_{B₁}}` is an isomorphism in the derived category: it is a
quasi-isomorphism by **Stacks 08TY**. -/
instance isIso_Q_map_liftDiagramNaiveCotangentComparison :
    IsIso (DerivedCategory.Q.map (liftDiagramNaiveCotangentComparison D)) := by
  have := Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site.{v, u,
    max u v w, max u v w} J D.front.OB D.front.O D.front.f
    (FirstOrderLiftDiagram.pairPresheaf D) (FirstOrderLiftDiagram.pairAlpha D)
  infer_instance

omit [J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective CommRingCat] [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The underlying object of the canonical two-term structure of `NL(α)` is the image in the
derived category of the naive cotangent complex of the presentation. -/
theorem liftDiagramNaiveCotangentTwoTerm_obj_eq :
    (liftDiagramNaiveCotangentTwoTerm D).obj =
      DerivedCategory.Q.obj
        (Stacks.SheafOfModules.presentationNaiveCotangentComplex.{v, u, max u v w, max u v w}
          J D.front.OB D.front.O D.front.f (FirstOrderLiftDiagram.pairPresheaf D)
          (FirstOrderLiftDiagram.pairAlpha D)) := rfl

/-- **The class of Step 1 on the canonical naive cotangent complex.** The class
`liftDiagramObstructionClass D ∈ Ext¹(NL(α), g_*𝒢₂)` of the difference homomorphism `ξ` of
Step 1 of the proof of **Stacks 08U8**, transported to `Ext¹(NL_{𝒪₁/𝒪_{B₁}}, g_*𝒢₂)` along the
comparison quasi-isomorphism `NL(α) ⟶ NL_{𝒪₁/𝒪_{B₁}}` of **Stacks 08TY**. This removes the
choice of the presentation `α`. -/
def canonicalObstructionClass :
    DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, max u v w}
          J D.front.OB D.front.O D.front.f) ⟶
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O)) 0).obj
          (FirstOrderLiftDiagram.pushedIdeal D))⟦(1 : ℤ)⟧ :=
  (asIso (DerivedCategory.Q.map (liftDiagramNaiveCotangentComparison D))).inv ≫
    eqToHom (liftDiagramNaiveCotangentTwoTerm_obj_eq D).symm ≫ liftDiagramObstructionClass D

/-- **Steps 1 to 3 of the proof of Stacks 08U8, on one site.** The class of Step 1 on the
canonical naive cotangent complex vanishes exactly when the reduced diagram has a lift. -/
theorem canonicalObstructionClass_eq_zero_iff :
    canonicalObstructionClass D = 0 ↔ Nonempty (FirstOrderLiftDiagram.Lift D) := by
  rw [← liftDiagramObstructionClass_eq_zero_iff D, canonicalObstructionClass,
    Limits.comp_eq_zero_iff_of_epi, Limits.comp_eq_zero_iff_of_epi]

end Canonical

/-! ### Stacks 08U8 -/

namespace DeformationIdealDiagram

open Stacks.SheafOfModules (inverseImageMiddleRing inverseImageBaseRing inverseImageFirstRingMap
  ringedSpaceStructureMap)
open RingedSpaceModuleAdjunction

variable (D : DeformationIdealDiagram.{u})

/-- **The canonical element of clause (1) of Stacks 08U8**, in
`Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)`. It is the class of the difference homomorphism `ξ` of
Step 1 of the source's proof, for the source's reduction of the diagram to sheaves of rings on
`X₂` (`DeformationIdealDiagram.toFirstOrderLiftDiagram`), read on the canonical naive
cotangent complex `NL_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}` (`canonicalObstructionClass`) and carried to
the source's group by `inverseImageNaiveCotangentExtOneAddEquiv`. -/
def obstructionClass : extOnePulledNaiveCotangent D.cube.g D.cube.f₁ D.G₂ :=
  inverseImageNaiveCotangentExtOneAddEquiv D.cube.g D.cube.f₁ D.G₂
    (canonicalObstructionClass D.toFirstOrderLiftDiagram)

/-- **Stacks Project, Tag 08U8, clause (1).** The canonical element of
`Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)` vanishes if and only if there is a morphism of ringed spaces
`X'₂ ⟶ X'₁` fitting into (08U9) compatibly with `ν`. -/
theorem obstructionClass_eq_zero_iff : D.obstructionClass = 0 ↔ Nonempty D.Lifts :=
  (AddEquiv.map_eq_zero_iff _).trans
    ((canonicalObstructionClass_eq_zero_iff D.toFirstOrderLiftDiagram).trans
      ⟨fun ⟨p⟩ => ⟨D.liftEquiv.symm p⟩, fun ⟨φ⟩ => ⟨D.liftEquiv φ⟩⟩)

/-- The acting group of clause (2) in the source's first spelling,
`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`. -/
abbrev ActingGroup :=
  (show SheafOfModules.{u} (structureSheafRing D.cube.X₁) from relativeDifferentials D.cube.f₁) ⟶
    (modulePushforward D.cube.g).obj D.G₂

/-- The acting group of clause (2) of the reduced diagram on `X₂` — the homomorphisms
`Ω_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}} ⟶ 𝒢₂` — is the source's `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`. -/
def actingGroupEquiv :
    (FirstOrderLiftDiagram.frontDifferentials D.toFirstOrderLiftDiagram ⟶
        FirstOrderLiftDiagram.pushedIdeal D.toFirstOrderLiftDiagram) ≃+ D.ActingGroup :=
  inverseImageDifferentialsHomAddEquiv D.cube.g D.cube.f₁ D.G₂

/-- **The action of clause (2) of Stacks 08U8**: a homomorphism `θ : Ω_{X₁/S₁} ⟶ g_*𝒢₂` acts on
a morphism `X'₂ ⟶ X'₁` fitting into (08U9) compatibly with `ν` by translating the corresponding
homomorphism `φ : g⁻¹𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of the reduced diagram by the derivation `θ ∘ d`
(`liftAct_spec`). -/
def liftAct (θ : D.ActingGroup) (φ : D.Lifts) : D.Lifts :=
  D.liftEquiv.symm (FirstOrderLiftDiagram.translateHom D.toFirstOrderLiftDiagram
    (D.liftEquiv φ) (D.actingGroupEquiv.symm θ))

/-- Read on `X₂`, the action of `θ` on `φ` translates `φ` by `θ`. -/
private theorem liftEquiv_liftAct (θ : D.ActingGroup) (φ : D.Lifts) :
    D.liftEquiv (D.liftAct θ φ) = FirstOrderLiftDiagram.translateHom D.toFirstOrderLiftDiagram
      (D.liftEquiv φ) (D.actingGroupEquiv.symm θ) :=
  Equiv.apply_symm_apply D.liftEquiv _

/-- **The formula for the action of clause (2)**, which pins it down: read on `X₂`, the action of
`θ` adds to `φ` the image in `𝒪_{X'₂}` of the derivation `θ ∘ d` of the reduced diagram. -/
theorem liftAct_spec (θ : D.ActingGroup) (φ : D.Lifts)
    (U : (TopologicalSpace.Opens D.cube.X₂.carrier)ᵒᵖ)
    (x : D.toFirstOrderLiftDiagram.front.O'.obj.obj U) :
    (D.liftEquiv (D.liftAct θ φ)).hom.hom.app U x =
      (D.liftEquiv φ).hom.hom.app U x +
        D.toFirstOrderLiftDiagram.back.incl
          (((FirstOrderLiftDiagram.derivationEquivDifferentialsHom
            D.toFirstOrderLiftDiagram).symm (D.actingGroupEquiv.symm θ)).toFun U x) :=
  congrArg (fun p : D.toFirstOrderLiftDiagram.Lift => p.hom.hom.app U x)
    (D.liftEquiv_liftAct θ φ)

/-- **Stacks Project, Tag 08U8, clause (2)**: the zero homomorphism acts trivially. -/
theorem liftAct_zero (φ : D.Lifts) : D.liftAct 0 φ = φ :=
  D.liftEquiv.injective (by
    simp only [liftEquiv_liftAct, map_zero, FirstOrderLiftDiagram.translateHom_zero])

/-- **Stacks Project, Tag 08U8, clause (2)**: the action is additive. -/
theorem liftAct_add (φ : D.Lifts) (θ θ' : D.ActingGroup) :
    D.liftAct θ' (D.liftAct θ φ) = D.liftAct (θ + θ') φ :=
  D.liftEquiv.injective (by
    simp only [liftEquiv_liftAct, FirstOrderLiftDiagram.translateHom_add, map_add])

/-- **Stacks Project, Tag 08U8, clause (2)**: any morphism fitting into (08U9) compatibly with `ν`
is carried to any other by exactly one homomorphism `Ω_{X₁/S₁} ⟶ g_*𝒢₂`. -/
theorem existsUnique_liftAct (φ ψ : D.Lifts) : ∃! θ : D.ActingGroup, D.liftAct θ φ = ψ := by
  obtain ⟨a, ha, huniq⟩ := FirstOrderLiftDiagram.existsUnique_translateHom
    D.toFirstOrderLiftDiagram (D.liftEquiv φ) (D.liftEquiv ψ)
  refine ⟨D.actingGroupEquiv a, D.liftEquiv.injective ?_, fun θ hθ => ?_⟩
  · simp only [liftEquiv_liftAct, D.actingGroupEquiv.symm_apply_apply, ha]
  · exact D.actingGroupEquiv.symm_apply_eq.1
      (huniq _ ((D.liftEquiv_liftAct θ φ).symm.trans (congrArg D.liftEquiv hθ)))

/-- The principal homogeneous space structure of clause (2), as an `AddTorsor`, once a morphism
fitting into the diagram exists; its action is `liftAct`. -/
@[instance_reducible, ega "0 20.1.3" "more general"]
def liftTorsor (φ₀ : D.Lifts) : AddTorsor D.ActingGroup D.Lifts where
  vadd θ φ := D.liftAct θ φ
  zero_vadd φ := D.liftAct_zero φ
  add_vadd θ θ' φ := by
    change D.liftAct (θ + θ') φ = D.liftAct θ (D.liftAct θ' φ)
    rw [D.liftAct_add, add_comm]
  vsub ψ φ := (D.existsUnique_liftAct φ ψ).choose
  nonempty := ⟨φ₀⟩
  vsub_vadd' ψ φ := (D.existsUnique_liftAct φ ψ).choose_spec.1
  vadd_vsub' θ φ := ((D.existsUnique_liftAct φ (D.liftAct θ φ)).choose_spec.2 θ rfl).symm

/-- **Stacks Project, Tag 08U8.** In the situation of **Stacks 08U9** — a commutative cube of
ringed spaces whose horizontal arrows are first order thickenings, with `𝒢_j = Ker(i_j^♯)`, a
`g`-map `ν : 𝒢₁ ⟶ 𝒢₂`, and front and back solutions of **Stacks 08U7** making the diagram of
ideal rows of **Stacks 08UA** commute (`D : DeformationIdealDiagram`):

1. the canonical element `D.obstructionClass` of `Ext¹_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)` vanishes
   if and only if there is a morphism of ringed spaces `X'₂ ⟶ X'₁` fitting into (08U9)
   compatibly with `ν`;
2. if there is such a morphism, the set of all of them is a principal homogeneous space under
   `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`: the action `liftAct` (given by the source's formula,
   `liftAct_spec`) is trivial at `0`, additive, and simply transitive, and is the action of an
   `AddTorsor` structure on the set.

The other two spellings of the acting group in the source's display are identified with this
one by `actingGroupPullbackAddEquiv` (`Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)`) and
`extZeroDerivedPullbackNaiveCotangentAddEquiv` (`Ext⁰_{𝒪_{X₂}}(Lg^*NL_{X₁/S₁}, 𝒢₂)`). -/
@[stacks 08U8, ega "0 20.1.3" "more general", ega "IV 16.5.14" "more general"]
theorem lifting_obstruction_and_torsor :
    (D.obstructionClass = 0 ↔ Nonempty D.Lifts) ∧
      (∀ φ : D.Lifts, D.liftAct 0 φ = φ) ∧
      (∀ (φ : D.Lifts) (θ θ' : D.ActingGroup),
        D.liftAct θ' (D.liftAct θ φ) = D.liftAct (θ + θ') φ) ∧
      (∀ φ ψ : D.Lifts, ∃! θ : D.ActingGroup, D.liftAct θ φ = ψ) ∧
      (∀ _φ₀ : D.Lifts, ∃ T : AddTorsor D.ActingGroup D.Lifts,
        ∀ (θ : D.ActingGroup) (φ ψ : D.Lifts), T.vadd θ φ = ψ ↔ D.liftAct θ φ = ψ) :=
  ⟨D.obstructionClass_eq_zero_iff, D.liftAct_zero, D.liftAct_add, D.existsUnique_liftAct,
    fun φ₀ => ⟨D.liftTorsor φ₀, fun _ _ _ => Iff.rfl⟩⟩

/-- The source's second spelling of the acting group of clause (2):
`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂) = Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)`, by the adjunction
`g^* ⊣ g_*`. -/
def actingGroupPullbackAddEquiv :
    D.ActingGroup ≃+
      ((modulePullback D.cube.g).obj
          (show SheafOfModules.{u} (structureSheafRing D.cube.X₁) from
            relativeDifferentials D.cube.f₁) ⟶ D.G₂) :=
  ((modulePullbackPushforwardAdjunction D.cube.g).homAddEquiv _ _).symm

end DeformationIdealDiagram

end AlgebraicGeometry.RingedSpaceThickening

end
