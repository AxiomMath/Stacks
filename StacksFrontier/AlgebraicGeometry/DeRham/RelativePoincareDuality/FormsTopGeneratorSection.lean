module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChangeTransverse
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinPointClass
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupDegreeZero
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgeProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopFibreLine
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareRankIso
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.IsIsoAppTop
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gysin class of a section generates the top cohomology of differential forms

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper and smooth of relative dimension `n` with
`A ⟶ Γ(X, 𝒪_X)` bijective, and `σ : Spec A ⟶ X` a section of `f`, with image `Z`. The section is
a closed immersion of a smooth `A`-scheme into a smooth one, so it is Koszul regular with conormal
sheaf finite locally free of rank `n`, and the Gysin map of [Stacks, Tag 0G8A] gives the class

`ξ = γ^{0,0}(1) ∈ Hⁿ(X, Ωⁿ_{X/A})`

of the proof of [Stacks, Tag 0G8J]. This file proves the claim of that proof that `ξ` is a basis
element, in the form: the class of `ξ` generates the top Čech cohomology `Hⁿ(Č(𝒰, Ωⁿ_{X/A}))` of
any finite affine covering as an `A`-module.

The source's argument: by top-degree base change and Nakayama's lemma it suffices that the image
of `ξ` on every closed fibre `X_𝔪` generates `Hⁿ(X_𝔪, Ωⁿ)`
(`Stacks.Cech.exists_sub_smul_eq_d_of_forall_closedFibre`). That space is a line
(`AlgebraicGeometry.TopDegreeDifferential.exists_eq_globalSmul_of_ne_zero`, from
[Stacks, Tag 0FW4]): `X_𝔪` is geometrically connected because `Γ(X, 𝒪_X) = A`, hence irreducible.
The image of `ξ` is the Gysin class of the base-changed section by [Stacks, Tag 0G8D], whose
conormal hypothesis holds because both conormal sheaves are finite locally free of rank `n`; and
the Gysin map of the rational point is injective on `H⁰` by duality, the argument of
[Stacks, Tag 0G8E].

## Main definitions

* `Stacks.DeRham.CohomologicalGysin.subschemeUnitClass`: the class of `1` in `H⁰(X, i_*Ω⁰_{Z/S})`.
* `Stacks.DeRham.CohomologicalGysin.gysinUnitClass`: `γ^{0,0}(1)` for a Koszul regular closed
  immersion of conormal rank `c`.
* `Stacks.DeRham.CohomologicalGysin.sectionGysinClass`: `ξ = γ^{0,0}(1)` for a section.

## Main results

* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_subschemeUnitClass`: the pullback of `1` is `1`.
* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_gysinUnitClass`: `γ^{0,0}(1)` is compatible
  with base change ([Stacks, Tag 0G8D] with the pullback of `1` computed).
* `Stacks.DeRham.CohomologicalGysin.isPullback_section_diagonal`,
  `Stacks.DeRham.CohomologicalGysin.diagonal_koszul_and_conormalRank`,
  `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_diagonalGysinUnitClass`: `(σ ∘ f, id)^*η = ξ`
  for the Gysin class `η` of the diagonal.
* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_sectionGysinClass_ne_zero`: the image of `ξ`
  on a closed fibre is nonzero.
* `Stacks.Cech.span_eq_top_of_forall_closedFibre_ne_zero`: a class of the top cohomology of forms
  that is nonzero on every closed fibre generates the top Čech cohomology.
* `Stacks.Cech.span_sectionGysinClass_eq_top`: `ξ` generates the top Čech cohomology.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.DeRham.CohomologicalGysin

section UnitClass

variable {Z X S : Scheme.{u}} (π : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The degree-zero class of `1 ∈ Γ(Z, Ω^0_{Z/S})`, read on `X` as a class of
`H^0(X, i_*Ω^0_{Z/S})`. -/
def subschemeUnitClass :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ 0 (pushforwardRelativeForms i π ((0 : ℕ) : ℤ)) :=
  ((secF (structureSheafRing X.toRingedSpace) ⊤).toRightDerivedZero.app
    (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))).hom ((subschemeFormUnit i π).eval (op ⊤))

end UnitClass

section SectionClass

variable {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] (n : ℕ) [SmoothOfRelativeDimension n f] [Smooth (σ ≫ f)]
  [FormallyUnramified (σ ≫ f)]

/-- **The Gysin class `ξ = γ^{0,0}(1)` of a section** `σ` of a morphism `f` smooth of relative
dimension `n`, in `H^n(X, Ω^n_{X/S})`: the Gysin map of [Stacks, Tag 0G8A] at the `γ^0` of
[Stacks, Tag 0G86], applied to `1 ∈ H^0(Z, Ω^0_{Z/S})` read on `X`. -/
def sectionGysinClass :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ (0 + n)
      (relativeDifferentialForms f (((0 : ℕ) : ℤ) + (n : ℤ))) :=
  (gysinCohomologyMap (Set.range σ.base) (isClosed_range_base σ) n
    (pushforwardRelativeForms σ f ((0 : ℕ) : ℤ))
    (relativeDifferentialForms f (((0 : ℕ) : ℤ) + (n : ℤ)))
    (supportVanishing_of_formallyUnramified σ f n 0)
    (conormalGysinHom σ f 0 (conormalRank_of_formallyUnramified σ f n) ≫
      (conormalGysinTargetIso σ f n 0).hom) 0).hom (subschemeUnitClass f σ)

end SectionClass

section UnitPullback

variable {Z X S Z' X' S' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
  (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S) [IsClosedImmersion i] [IsClosedImmersion i']

/-- Base change of forms carries the unit section of `i_*Ω⁰_{Z/S}` to that of `i'_*Ω⁰_{Z'/S'}`. -/
private theorem subschemeFormBaseChange_subschemeFormUnit {Z X S Z' X' S' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S')
    (t : S' ⟶ S) (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t) :
    subschemeFormBaseChange i i' h g π π' t left_comm right_comm ((0 : ℕ) : ℤ) ⊤
      ((subschemeFormUnit i π).eval (op ⊤)) = (subschemeFormUnit i' π').eval (op (g ⁻¹ᵁ ⊤)) := by
  refine ((congrArg (subschemeFormBaseChange i i' h g π π' t left_comm right_comm ((0 : ℕ) : ℤ) ⊤)
    (subschemeFormUnit_eval i π ⊤)).trans
    (subschemeFormBaseChange_subschemeFormPullback i i' h g π π' t left_comm right_comm
      ((0 : ℕ) : ℤ) ⊤ _)).trans ?_
  refine (congrArg (subschemeFormPullback i' π' ((0 : ℕ) : ℤ) (g ⁻¹ᵁ ⊤))
    (relativeDifferentialFormsPullback_one g π π' t right_comm ⊤)).trans ?_
  exact (subschemeFormUnit_eval i' π' (g ⁻¹ᵁ ⊤)).symm

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- **The pullback of the unit class is the unit class**: for a commutative diagram
`Z' → X' → S'` over `Z → X → S`, the pullback map on `H⁰` of [Stacks, Tag 01F9] at the pullback
of forms `i_*Ω⁰_{Z/S} ⟶ g_*i'_*Ω⁰_{Z'/S'}` carries the class of `1 ∈ Γ(Z, Ω⁰_{Z/S})` to the
class of `1 ∈ Γ(Z', Ω⁰_{Z'/S'})`: in degree zero the pullback map is the map on global sections
(`Stacks.DeRham.GysinCohomologyBaseChange.toRightDerivedZero_comp_pullbackHgroup`), and pulling
back forms is unital. -/
theorem pullbackHgroup_subschemeUnitClass (left_comm : h ≫ i = i' ≫ g)
    (right_comm : g ≫ π = π' ≫ t) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 0 0 (by simp)
      (gysinBaseChangeSourceHom i i' h g π π' t left_comm right_comm ((0 : ℕ) : ℤ))).hom
        (subschemeUnitClass π i) = subschemeUnitClass π' i' := by
  have key := congrArg (fun φ => φ.hom ((subschemeFormUnit i π).eval (op (⊤ : X.Opens))))
    (toRightDerivedZero_comp_pullbackHgroup g.toLRSHom.toShHom
      (gysinBaseChangeSourceHom i i' h g π π' t left_comm right_comm ((0 : ℕ) : ℤ)))
  refine key.trans ?_
  unfold subschemeUnitClass
  refine congrArg ((secF (structureSheafRing X'.toRingedSpace) ⊤).toRightDerivedZero.app
    (pushforwardRelativeForms i' π' ((0 : ℕ) : ℤ))).hom ?_
  exact subschemeFormBaseChange_subschemeFormUnit i i' h g π π' t left_comm right_comm

end UnitPullback

section GysinUnitClass

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
  (π : X ⟶ S) [Smooth π]

/-- **The Gysin class `γ^{0,0}(1) ∈ H^c(X, Ω^c_{X/S})`** of a Koszul regular closed immersion
`i : Z ⟶ X` of finite presentation with conormal sheaf finite locally free of rank `c`, `X`
smooth over `S`: the Gysin map of [Stacks, Tag 0G8A] at the `γ^0` of [Stacks, Tag 0G86],
applied to `1 ∈ H^0(Z, Ω^0_{Z/S})` read on `X`. -/
def gysinUnitClass (hkos : IsKoszulRegularImmersion i) {c : ℕ} (hE : ConormalRank i c) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ (0 + c)
      (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ))) :=
  (gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
    (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))
    (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)))
    (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms i π hkos
      c hE 0)
    (conormalGysinHom i π 0 hE ≫ (conormalGysinTargetIso i π c 0).hom) 0).hom
    (subschemeUnitClass π i)

/-- **The Gysin class of `1` is compatible with base change** ([Stacks, Tag 0G8D] at `p = q = 0`,
with the pullback of `1` computed in degree zero): for a cartesian square of closed immersions
`Z' → X'` over `Z → X` satisfying the hypotheses of [Stacks, Tag 0G8D], the pullback map of
[Stacks, Tag 01F9] carries `γ^{0,0}(1)` on `X` to `γ^{0,0}(1)` on `X'`. -/
theorem pullbackHgroup_gysinUnitClass {Z' X' S' : Scheme.{u}} (i' : Z' ⟶ X')
    [IsClosedImmersion i'] [LocallyOfFinitePresentation i'] (h : Z' ⟶ Z) (g : X' ⟶ X)
    (π' : X' ⟶ S') [Smooth π'] (t : S' ⟶ S) {c : ℕ} (hE : ConormalRank i c)
    (hE' : ConormalRank i' c) (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t)
    (hconormal : IsIso (Stacks.Immersion.immersionConormalSheafMap i' i h g
      (congrArg (fun k => k.toLRSHom.toShHom) hcart.w.symm)))
    (hkos : IsKoszulRegularImmersion i) (hkos' : IsKoszulRegularImmersion i') :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
      (((0 : ℕ) : ℤ) + (c : ℤ)) (0 + c) (by omega)
      (formsBaseChangeHom g π π' t right_comm (((0 : ℕ) : ℤ) + (c : ℤ)))).hom
        (gysinUnitClass i π hkos hE) = gysinUnitClass i' π' hkos' hE' := by
  have key := congrArg (fun φ => φ.hom (subschemeUnitClass π i))
    (conormalGysinCohomologyMap_pullback i i' h g π π' t hE hE' hcart right_comm hconormal
      hkos hkos' 0 0)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at key
  refine key.trans ?_
  unfold gysinUnitClass
  exact congrArg _ (pullbackHgroup_subschemeUnitClass i i' h g π π' t hcart.w right_comm)

end GysinUnitClass

section SectionClassEq

variable {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] (n : ℕ) [SmoothOfRelativeDimension n f] [Smooth (σ ≫ f)]
  [FormallyUnramified (σ ≫ f)] [Smooth f]

/-- The Gysin class of a section is the Gysin class of `1` of the section as a Koszul regular
closed immersion of conormal rank `n`. -/
theorem sectionGysinClass_eq_gysinUnitClass :
    sectionGysinClass f σ n = gysinUnitClass σ f (isKoszulRegularImmersion_of_smooth_of_smooth σ f)
      (conormalRank_of_formallyUnramified σ f n) :=
  rfl

end SectionClassEq

section Diagonal

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)

omit [IsSeparated f] in
include hσ in
/-- **The pullback of the diagonal along `(σ ∘ f, id)` is the section**: the square
`Z → X`, `Z → X ×_S X` with `Z = S` embedded by `σ` on both sides, `X → X ×_S X` the diagonal and
`(σ ∘ f, id) : X ⟶ X ×_S X`, is cartesian. -/
theorem isPullback_section_diagonal :
    IsPullback σ σ (pullback.diagonal f)
      (pullback.lift (f ≫ σ) (𝟙 X) (by rw [Category.assoc, hσ, Category.comp_id,
        Category.id_comp])) := by
  have : IsIso (σ ≫ f) := by rw [hσ]; infer_instance
  refine (pullback_lift_diagonal_isPullback σ f).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (pullback.snd (σ ≫ f) f)) (Iso.refl _) (by simp)
    (by rw [Iso.refl_hom, Category.id_comp, asIso_hom]; exact pullback.lift_snd _ _ _)
    (by simp) ?_
  have hw : pullback.fst (σ ≫ f) f = pullback.snd (σ ≫ f) f ≫ f :=
    (Category.comp_id _).symm.trans ((congrArg (pullback.fst (σ ≫ f) f ≫ ·) hσ.symm).trans
      pullback.condition)
  apply pullback.hom_ext
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, Category.assoc, pullback.lift_fst,
      pullback.map]
    rw [hw, Category.assoc]
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, Category.assoc, pullback.lift_snd,
      pullback.map]

end Diagonal

section DiagonalClass

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- The diagonal of `f : X ⟶ S` smooth of relative dimension `n` is a section of the first
projection, smooth of relative dimension `n`; so it is Koszul regular with conormal sheaf finite
locally free of rank `n` ([Stacks, Tag 067R]). -/
theorem diagonal_koszul_and_conormalRank :
    haveI : LocallyOfFinitePresentation (pullback.diagonal f) := by
      have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
        rw [pullback.diagonal_fst]; infer_instance
      exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
    IsKoszulRegularImmersion (pullback.diagonal f) ∧ ConormalRank (pullback.diagonal f) n := by
  have : SmoothOfRelativeDimension n (pullback.fst f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
      (IsPullback.of_hasPullback f f).flip inferInstance
  have : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  have : FormallyUnramified (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact ⟨isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.fst f f),
    conormalRank_of_formallyUnramified _ (pullback.fst f f) n⟩

include σ in
/-- **The pullback of the Gysin class of the diagonal along `(σ ∘ f, id)` is the Gysin class of
the section** ("`(s, id)^*η = ξ`" in the proof of [Stacks, Tag 0G8J]): for `f : X ⟶ Spec A`
proper and smooth of relative dimension `n` with a section `σ`, let `η = γ^{0,0}(1)` be the Gysin
class of the diagonal `Δ : X ⟶ X ×_A X` in `Hⁿ(X ×_A X, Ωⁿ_{X ×_A X/A})` and
`ξ = γ^{0,0}(1)` that of `σ` in `Hⁿ(X, Ωⁿ_{X/A})`. Then `(σ ∘ f, id)^*η = ξ`: the preimage of the
diagonal is the image of the section (`isPullback_section_diagonal`), both conormal sheaves have
rank `n`, and [Stacks, Tag 0G8D] applies. -/
theorem pullbackHgroup_diagonalGysinUnitClass (hσ : σ ≫ f = 𝟙 _) :
    haveI : LocallyOfFinitePresentation (pullback.diagonal f) := by
      have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
        rw [pullback.diagonal_fst]; infer_instance
      exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (pullback.lift (f ≫ σ) (𝟙 X) (by rw [Category.assoc, hσ, Category.comp_id,
          Category.id_comp])).toLRSHom.toShHom) (0 : ℤ)
      (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom (pullback.lift (f ≫ σ) (𝟙 X) (by rw [Category.assoc, hσ,
          Category.comp_id, Category.id_comp])) (pullback.fst f f ≫ f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id])
        (((0 : ℕ) : ℤ) + (n : ℤ)))).hom
      (gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f)
        (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2) =
      sectionGysinClass f σ n := by
  have : LocallyOfFinitePresentation (pullback.diagonal f) := by
    have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
      rw [pullback.diagonal_fst]; infer_instance
    exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hcart := isPullback_section_diagonal f σ hσ
  have hE := conormalRank_of_formallyUnramified σ f n
  rw [sectionGysinClass_eq_gysinUnitClass]
  exact pullbackHgroup_gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f) σ σ _ f (𝟙 _)
    (diagonal_koszul_and_conormalRank f n).2 hE hcart _
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_conormalRank σ (pullback.diagonal f) σ
      _ hcart.flip hE (diagonal_koszul_and_conormalRank f n).2)
    (diagonal_koszul_and_conormalRank f n).1 (isKoszulRegularImmersion_of_smooth_of_smooth σ f)

end DiagonalClass

section Fibre

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- **The unit is nonzero on a nonempty open**: the unit of `Ω^•_{Y/T}` over a nonempty open is
nonzero, since `Ω^0_{Y/T} = 𝒪_Y` carries it to `1`. -/
theorem relativeDifferentialFormsAlgebra_one_ne_zero {Y T : Scheme.{u}} (q : Y ⟶ T)
    (U : Y.Opens) [Nonempty U] :
    (relativeDifferentialFormsAlgebra q).one.eval (op U) ≠ 0 := by
  intro h
  have h1 := (deRhamAlgebras q).exteriorPieceZeroIsoUnit_one (op U)
  rw [show (deRhamAlgebras q).exterior.one.eval (op U) = 0 from h, map_zero] at h1
  exact zero_ne_one (α := Γ(Y, U)) h1

/-- **The image of `ξ` on a closed fibre is nonzero.** For `f : X ⟶ Spec A` proper and smooth of
relative dimension `n` with a section `σ`, and a maximal ideal `𝔪` of `A`, the pullback of
`ξ = γ^{0,0}(1)` to `X' = X ×_{Spec A} Spec A/𝔪` is nonzero: by [Stacks, Tag 0G8D] it is the
Gysin class of the base-changed section applied to the pullback of `1`, which is `1`, and the
Gysin map of a rational point of a proper smooth scheme over a field is injective on `H⁰`, by the
duality argument of [Stacks, Tag 0G8E]. -/
theorem pullbackHgroup_sectionGysinClass_ne_zero (hσ : σ ≫ f = 𝟙 _) (m : Ideal A) [m.IsMaximal]
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of (A ⧸ m))) (g : X' ⟶ X)
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
      (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
      (formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))) hsq.w
        (((0 : ℕ) : ℤ) + (n : ℤ)))).hom (sectionGysinClass f σ n) ≠ 0 := by
  classical
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  set t := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) with ht
  -- the base-changed section
  let σ' : Spec (.of (A ⧸ m)) ⟶ X' := hsq.lift (t ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσ' : σ' ≫ f' = 𝟙 _ := hsq.lift_snd _ _ _
  have hσg : σ' ≫ g = t ≫ σ := hsq.lift_fst _ _ _
  have hcart : IsPullback t σ' σ g := by
    have hout : IsPullback (σ' ≫ f') t t (σ ≫ f) := by
      rw [hσ', hσ]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact (IsPullback.of_right hout hσg hsq.flip).flip
  -- instances on the fibre
  have : IsProper f' := MorphismProperty.of_isPullback hsq ‹IsProper f›
  have : SmoothOfRelativeDimension n f' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback hsq inferInstance
  have : Smooth f' := SmoothOfRelativeDimension.smooth n f'
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsIso (σ' ≫ f') := by rw [hσ']; infer_instance
  have : Smooth (σ' ≫ f') := by rw [hσ']; infer_instance
  have : FormallyUnramified (σ' ≫ f') := by rw [hσ']; infer_instance
  have : IsClosedImmersion σ' := by
    have : IsClosedImmersion (σ' ≫ f') := by rw [hσ']; infer_instance
    exact IsClosedImmersion.of_comp σ' f'
  have : LocallyOfFinitePresentation σ' := by
    have : LocallyOfFinitePresentation (σ' ≫ f') := by rw [hσ']; infer_instance
    exact locallyOfFinitePresentation_of_comp σ' f'
  have hspec : IsClosedImmersion t :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk m))
      Ideal.Quotient.mk_surjective
  have : IsClosedImmersion g :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hspec
  have : Fact (Topology.IsClosedEmbedding g.toLRSHom.toShHom.hom.base) := ⟨g.isClosedEmbedding⟩
  -- [Stacks, Tag 0G8D]
  have hE := conormalRank_of_formallyUnramified σ f n
  have hE' := conormalRank_of_formallyUnramified σ' f' n
  have hcon := Stacks.Immersion.isIso_immersionConormalSheafMap_of_conormalRank σ' σ t g
    hcart.flip hE' hE
  have key := congrArg (fun φ => φ.hom (subschemeUnitClass f σ))
    (conormalGysinCohomologyMap_pullback σ σ' t g f f' t hE hE' hcart hsq.w hcon
      (isKoszulRegularImmersion_of_smooth_of_smooth σ f)
      (isKoszulRegularImmersion_of_smooth_of_smooth σ' f') 0 0)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at key
  show (pullbackHgroup _ _ _ _ _ _).hom ((gysinCohomologyMap _ _ _ _ _ _ _ 0).hom
    (subschemeUnitClass f σ)) ≠ 0
  rw [key]
  -- the Gysin map of the rational point is injective on `H⁰`, by duality
  have : (show X'.Modules from pushforwardRelativeForms σ' f' (((0 : ℕ) : ℤ))).IsQuasicoherent :=
    have := isQuasicoherent_relativeDifferentialForms (σ' ≫ f') 0
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom σ'
      (relativeDifferentialForms (σ' ≫ f') ((0 : ℕ) : ℤ)) inferInstance
  have hinj := injective_gysinCohomologyMap_zero_of_duality f' (Set.range σ'.base)
    (isClosed_range_base σ') n (pushforwardRelativeForms σ' f' (((0 : ℕ) : ℤ)))
    (relativeDifferentialForms f' (((0 : ℕ) : ℤ) + (n : ℤ)))
    (supportVanishing_of_formallyUnramified σ' f' n 0)
    (conormalGysinHom σ' f' 0 hE' ≫ (conormalGysinTargetIso σ' f' n 0).hom)
    (cohomologySupportedOn_pushforwardRelativeForms σ' f' (n : ℤ)) (fun h =>
      conormalGysinHom_ne_zero_of_isIso f' σ' n hE'
        ((Iso.cancel_iso_hom_right _ _ (conormalGysinTargetIso σ' f' n 0)).1
          (h.trans zero_comp.symm)))
    (finrank_globalSections_pushforwardRelativeForms_zero f' σ')
    ((Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f' n).1.some ≪≫ (DerivedCategory.singleFunctor X'.Modules (-(n : ℤ))).mapIso
        (eqToIso (by rw [Nat.cast_zero, zero_add]; rfl)))
  intro h0
  have h1 := hinj (h0.trans (map_zero _).symm)
  -- the pullback of `1` to the fibre is nonzero, since it is computed on sections
  set src := gysinBaseChangeSourceHom σ σ' t g f f' t hcart.w hsq.w ((0 : ℕ) : ℤ)
  set x := (subschemeFormUnit σ f).eval (op (⊤ : X.Opens))
  have e := pullbackHgroup_eq_map_comp (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom)
    (0 : ℤ) ((0 : ℕ) : ℤ) 0 (by omega) src
  have h1' : ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
      ((0 : ℕ) : ℤ) 0 (by omega) (𝟙 ((modulePushforward g.toLRSHom.toShHom).obj
        (pushforwardRelativeForms σ' f' ((0 : ℕ) : ℤ)))))).hom
      (((Hfunctor (structureSheafRing X.toRingedSpace) ⊤ 0).map src).hom
        (subschemeUnitClass f σ)) = 0 := by
    have := congrArg (fun φ => φ.hom (subschemeUnitClass f σ)) e
    exact this.symm.trans h1
  have hiso := isIso_pullbackHgroup_canonical_id g.toLRSHom.toShHom (0 : ℤ) ((0 : ℕ) : ℤ) 0
    (by omega) (pushforwardRelativeForms σ' f' ((0 : ℕ) : ℤ))
  have h2 := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ hiso).1
    (h1'.trans (map_zero _).symm)
  have hnat := congrArg (fun φ => φ.hom x)
    ((secF (structureSheafRing X.toRingedSpace) ⊤).toRightDerivedZero.naturality src)
  have h3 : ((secF (structureSheafRing X.toRingedSpace) ⊤).map src).hom x = 0 :=
    (ConcreteCategory.bijective_of_isIso
      ((secF (structureSheafRing X.toRingedSpace) ⊤).toRightDerivedZero.app _)).1
      (hnat.trans (h2.trans (map_zero _).symm))
  have h4 : ((secF (structureSheafRing X.toRingedSpace) ⊤).map src).hom x =
      (relativeDifferentialFormsAlgebra (σ' ≫ f')).one.eval (op (σ' ⁻¹ᵁ (g ⁻¹ᵁ ⊤))) := by
    exact (subschemeFormBaseChange_subschemeFormUnit σ σ' t g f f' t hcart.w hsq.w).trans
      (subschemeFormUnit_eq_one σ' f' (g ⁻¹ᵁ ⊤))
  have : Nonempty (σ' ⁻¹ᵁ (g ⁻¹ᵁ (⊤ : X.Opens))) :=
    ⟨⟨Classical.arbitrary (Spec (.of (A ⧸ m))), by simp⟩⟩
  exact relativeDifferentialFormsAlgebra_one_ne_zero (σ' ≫ f') _ (h4.symm.trans h3)

end Fibre

end Stacks.DeRham.CohomologicalGysin

namespace Stacks.Cech

open Stacks.DeRham.CohomologicalGysin

section Classes

variable {R : Type u} [CommRing R]

/-- Every class of the homology of a cochain complex of modules is the class of a cocycle. -/
theorem exists_homologyClassOf_eq (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (x : K.homology (q + 1)) :
    ∃ (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0), homologyClassOf K q y hy = x := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (q + 1))).1 inferInstance x
  refine ⟨(K.iCycles (q + 1)).hom c, ?_, ?_⟩
  · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.iCycles_d,
      ModuleCat.hom_zero, LinearMap.zero_apply]
  · unfold homologyClassOf
    congr 1
    apply (ModuleCat.mono_iff_injective (K.iCycles (q + 1))).mp inferInstance
    rw [iCycles_cycleOf]

/-- The class of a cocycle is linear in the cocycle. -/
theorem homologyClassOf_sub_smul (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (y z : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0)
    (hz : K.d (q + 1) (q + 1 + 1) z = 0) (a : R)
    (hyz : K.d (q + 1) (q + 1 + 1) (y - a • z) = 0) :
    homologyClassOf K q (y - a • z) hyz =
      homologyClassOf K q y hy - a • homologyClassOf K q z hz := by
  have hcyc : cycleOf K q (y - a • z) hyz = cycleOf K q y hy - a • cycleOf K q z hz := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (q + 1))).mp inferInstance
    rw [map_sub, map_smul, iCycles_cycleOf, iCycles_cycleOf, iCycles_cycleOf]
  unfold homologyClassOf
  rw [hcyc, map_sub, map_smul]

end Classes

section Generator

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

attribute [local instance] Scheme.Hom.isQuasicoherent_relativeDifferentialForms

/-- **A class of the top cohomology of differential forms whose images on all closed fibres are
nonzero generates it.** Let `A` be Noetherian, `f : X ⟶ Spec A` proper and smooth of relative
dimension `e + 1` with `A ⟶ Γ(X, 𝒪_X)` bijective and with a section, and `𝒰` a finite affine
covering. If the pullback of `x ∈ H^{e+1}(X, Ω^{e+1}_{X/A})` to every closed fibre is nonzero,
then the class of `x` generates `H^{e+1}(Č(𝒰, Ω^{e+1}_{X/A}))` as an `A`-module: on a closed
fibre, which is irreducible because `f` is geometrically connected, the top cohomology of forms is
a line ([Stacks, Tag 0FW4]), and top-degree base change and Nakayama's lemma conclude.

The degrees `d`, `P`, `M` are arbitrary spellings of `e + 1`, so that the statement applies to the
classes the Gysin map produces in degree `0 + (e + 1)`. -/
theorem span_eq_top_of_forall_closedFibre_ne_zero [IsNoetherianRing A] [IsProper f]
    [IsIso f.appTop] (e : ℕ) [SmoothOfRelativeDimension (e + 1) f] (σ : Spec (.of A) ⟶ X)
    (hσ : σ ≫ f = 𝟙 _) {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i)) {d : ℕ} {P M : ℤ}
    (hd : d = e + 1) (hP : P = ((e + 1 : ℕ) : ℤ)) (hM : M - 0 = d)
    [(f.relativeDifferentialForms P).IsQuasicoherent]
    (x : Hgroup X.ringCatSheaf ⊤ d (f.relativeDifferentialForms P))
    (hx : ∀ (m : Ideal A) [m.IsMaximal] (X' : Scheme.{u}) (f' : X' ⟶ Spec (.of (A ⧸ m)))
      (g : X' ⟶ X) (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))),
      (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 M d hM
        (formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))) hsq.w
          P)).hom x ≠ 0) :
    Submodule.span A {show ↑((alternatingCechModuleComplex f U
        (f.relativeDifferentialForms P)).homology d) from
      (hgroupIsoAlternatingCechModuleHomology f U hU (fun _ s => inter_isAffineOpen f U hUaff s)
        (f.relativeDifferentialForms P) d).hom x} = ⊤ := by
  classical
  have := Fintype.ofFinite I
  subst hd hP
  obtain rfl : M = ((e + 1 : ℕ) : ℤ) := by omega
  set K := alternatingCechModuleComplex f U (f.relativeDifferentialForms ((e + 1 : ℕ) : ℤ))
  set E := hgroupIsoAlternatingCechModuleHomology f U hU
    (fun _ s => inter_isAffineOpen f U hUaff s) (f.relativeDifferentialForms ((e + 1 : ℕ) : ℤ))
    (e + 1)
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have hflat : IsFlatOver f.toLRSHom.toShHom (f.relativeDifferentialForms ((e + 1 : ℕ) : ℤ)) :=
    have := ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f (e + 1)
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f _
  have := Scheme.Hom.isCoherent_relativeDifferentialForms f (e + 1)
  have hfib : ∀ s : Spec (.of A),
      topologicalKrullDim (f.fiber s) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    have hsms := smoothOfRelativeDimension_fiberToSpecResidueField f (e + 1) s
    rcases isEmpty_or_nonempty (f.fiber s) with hE | hN
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hE]
      exact bot_le
    · exact (@topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field _ _ _ hN (e + 1) _
        hsms).le
  obtain ⟨z, hz, hzx⟩ := exists_homologyClassOf_eq K e (E.hom x)
  rw [eq_top_iff]
  intro w _
  obtain ⟨y, hy, rfl⟩ := exists_homologyClassOf_eq K e w
  obtain ⟨a, v, hv⟩ := exists_sub_smul_eq_d_of_forall_closedFibre f U hU hUaff (e + 1) e hflat
    hfib z hz (by
      -- the input on the closed fibres
      intro m hm X' f' g hsq y'
      let : Field (A ⧸ m) := Ideal.Quotient.field m
      set t := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) with ht
      have hxz : E.inv (homologyClassOf K e z hz) = x := by
        rw [hzx]
        exact Iso.hom_inv_id_apply E _
      rw [hxz]
      -- the fibre is a line
      let σ' : Spec (.of (A ⧸ m)) ⟶ X' := hsq.lift (t ≫ σ) (𝟙 _) (by
        rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
      have hσ' : σ' ≫ f' = 𝟙 _ := hsq.lift_snd _ _ _
      have : IsProper f' := MorphismProperty.of_isPullback hsq ‹IsProper f›
      have : SmoothOfRelativeDimension (e + 1) f' :=
        (smoothOfRelativeDimension_isStableUnderBaseChange (n := e + 1)).of_isPullback hsq
          inferInstance
      have : Smooth f' := SmoothOfRelativeDimension.smooth (e + 1) f'
      have : ConnectedSpace X' :=
        (Stacks.SteinFactorization.geometricallyConnected_of_isIso_appTop
          f).geometrically_connectedSpace t g f' hsq
      have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
      have : IrreducibleSpace X' := irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace f'
      have : Nonempty X' := ⟨σ'.base (Classical.arbitrary _)⟩
      have hd := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (e + 1) f'
      obtain ⟨c₀, hc₀⟩ := AlgebraicGeometry.TopDegreeDifferential.exists_eq_globalSmul_of_ne_zero
        f' σ' hσ' (e + 1) hd _ (hx m X' f' g hsq) y'
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c₀
      exact ⟨c, hc₀⟩) y hy
  have hyz : K.d (e + 1) (e + 1 + 1) (y - a • z) = 0 := by
    rw [map_sub, map_smul, hy, hz, smul_zero, sub_zero]
  have h0 : homologyClassOf K e (y - a • z) hyz = 0 :=
    (homologyClassOf_eq_zero_iff K e _ hyz).2 ⟨v, hv⟩
  rw [homologyClassOf_sub_smul K e y z hy hz a hyz, sub_eq_zero] at h0
  rw [h0, hzx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- **The Gysin class of a section generates the top cohomology of differential forms**
([Stacks, Tag 0G8J], the claim that `ξ` is a basis element). Let `A` be Noetherian,
`f : X ⟶ Spec A` proper and smooth of relative dimension `e + 1` with `A ⟶ Γ(X, 𝒪_X)` bijective,
`σ` a section of `f` and `𝒰` a finite affine covering. Then the class of `ξ = γ^{0,0}(1)`
generates the top Čech cohomology `H^{0+(e+1)}(Č(𝒰, Ω^{0+(e+1)}_{X/A}))` as an `A`-module. -/
@[sga "7 XI 1.1" "generation clause"]
theorem span_sectionGysinClass_eq_top [IsNoetherianRing A] [IsProper f] [IsIso f.appTop]
    (e : ℕ) [SmoothOfRelativeDimension (e + 1) f] (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ]
    [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]
    (hσ : σ ≫ f = 𝟙 _) {I : Type u} [Fintype I] [LinearOrder I] (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i)) :
    Submodule.span A {show ↑((alternatingCechModuleComplex f U
        (f.relativeDifferentialForms (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))).homology (0 + (e + 1)))
      from (hgroupIsoAlternatingCechModuleHomology f U hU
        (fun _ s => inter_isAffineOpen f U hUaff s)
        (f.relativeDifferentialForms (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) (0 + (e + 1))).hom
        (sectionGysinClass f σ (e + 1))} = ⊤ :=
  span_eq_top_of_forall_closedFibre_ne_zero f e σ hσ U hU hUaff (Nat.zero_add _) (by simp)
    (by omega) (sectionGysinClass f σ (e + 1))
    (fun m _ _ f' g hsq => pullbackHgroup_sectionGysinClass_ne_zero f (e + 1) σ hσ m f' g hsq)

end Generator

end Stacks.Cech

end
