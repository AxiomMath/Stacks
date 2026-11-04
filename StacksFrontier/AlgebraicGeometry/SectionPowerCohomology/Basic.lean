module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionPowerMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoveringNumber.Basic

/-!
# Powers of a section of an invertible module acting on cohomology

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s ∈ Γ(X, L)` a global section. A power
`sⁿ` acts on the cohomology of a module `F` as the map `Hᵖ(X, F) ⟶ Hᵖ(X, F ⊗ L^{⊗ n})` induced by
multiplication by `sⁿ`. [Stacks, Tag 01XR] says that if `X` is quasi-compact and quasi-separated
and the nonvanishing open `X_s` is affine, then every positive-degree cohomology class of a
quasi-coherent module is annihilated by some power of `s`; it is
`Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero` in
`StacksFrontier/AlgebraicGeometry/SectionPowerCohomology/QuasiCompact.lean`. This file records the
cases in which the cohomology group itself vanishes, where the zeroth power already kills every
class.

## Main results

* `Stacks.SheafOfModules.hrestrict_eq_zero_of_isAffineOpen_nonvanishingOpen`: a positive-degree
  cohomology class of a quasi-coherent module restricts to zero on an affine nonvanishing open,
  by [Stacks, Tag 01XB].
* `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero_of_isZero`: a class in a vanishing
  cohomology group is annihilated by the zeroth power of the section.
* `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero_of_isAffine` and
  `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero_of_finite_affine_cover`: the
  conclusion of [Stacks, Tag 01XR] for an affine ambient scheme ([Stacks, Tag 01XB]), and in the
  degrees at least the size of a finite affine cover of a scheme with affine diagonal
  ([Stacks, Tag 01XI]).

## Implementation notes

Multiplication by a power of `s` is `Stacks.SheafOfModules.sectionPowerAction` applied to a
morphism `𝒪_X ⟶ L^{⊗ n}` representing `sⁿ`, the representing morphisms being those cut out by
`Stacks.SheafOfModules.IsSectionPowerHom`; the conclusion quantifies over such a morphism rather
than naming `Stacks.SheafOfModules.sectionPowerHom`, so that it can be used with any
representative. Cohomology is the right derived functor `Hgroup` of sections, in which
[Stacks, Tag 01XB] and [Stacks, Tag 01XI] are stated.

The invertible module and the module whose cohomology is taken are both written over
`structureSheafRing`, the spelling of the structure
sheaf in which the integer tensor powers of [Stacks, Tag 01CU] and the nonvanishing open of
[Stacks, Tag 01CY] are available; it is definitionally the `RingCat`-valued structure sheaf
`AlgebraicGeometry.Scheme.ringCatSheaf` of the cohomology functors, and `implicit_reducible` is
what lets the two spellings meet.

## References

* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- Invertibility in the sense of Tag 01CS supplies the hypothesis under which the integer tensor
powers are defined; instance search does not cross the two spellings of the structure sheaf in
play, so the bridge is applied by hand. -/
local instance isEquivalence_tensorRightFunctor_structureSheafRing :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨X.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf) (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).flip.obj (L))).IsEquivalence :=
  TensorPower.isEquivalence_tensorRightFunctor X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L

/-- Every element of an abelian group that is a zero object is zero. -/
private theorem eq_zero_of_isZero_addCommGrpCat {G : AddCommGrpCat} (h : IsZero G) (ξ : G) :
    ξ = 0 :=
  have := AddCommGrpCat.isZero_iff_subsingleton.mp h
  Subsingleton.elim _ _

/-- A positive-degree cohomology class of a quasi-coherent module restricts to zero on the
nonvanishing open of a global section of an invertible module whenever that open is affine,
because the positive-degree cohomology of a quasi-coherent module on an affine open vanishes. -/
theorem hrestrict_eq_zero_of_isAffineOpen_nonvanishingOpen (s : L.sections)
    (hU : IsAffineOpen (nonvanishingOpen L s)) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : 0 < p) (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    Hrestrict X.ringCatSheaf (le_top (a := nonvanishingOpen L s)) p F ξ = 0 := by
  have h := Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F
    (nonvanishingOpen L s) hU p hp
  exact eq_zero_of_isZero_addCommGrpCat h _

/-- A cohomology class of a vanishing cohomology group is annihilated by the zeroth power of a
global section of an invertible module, that power acting as the zero map on a zero group. -/
theorem exists_sectionPowerAction_eq_zero_of_isZero (s : L.sections) (F : X.Modules) (p : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p F)) (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ (n : ℕ) (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n),
      IsSectionPowerHom X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L s n t ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L F n t) ξ = 0 := by
  refine ⟨0, sectionPowerHom X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L s 0,
    isSectionPowerHom_sectionPowerHom X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L s 0, ?_⟩
  rw [eq_zero_of_isZero_addCommGrpCat h ξ]
  exact map_zero _

/-- **The conclusion of [Stacks, Tag 01XR] for an affine ambient scheme.** On an affine scheme the
positive-degree cohomology of a quasi-coherent module vanishes, so every class is annihilated
already by the zeroth power of a global section of an invertible module. -/
@[stacks 01XR "the case of an affine ambient scheme"]
theorem exists_sectionPowerAction_eq_zero_of_isAffine [IsAffine X] (s : L.sections)
    [CompactSpace X] [QuasiSeparatedSpace X] (_hU : IsAffineOpen (nonvanishingOpen L s))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p)
    (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ (n : ℕ) (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n),
      IsSectionPowerHom X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L s n t ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L F n t) ξ = 0 :=
  exists_sectionPowerAction_eq_zero_of_isZero X L s F p
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤
      (isAffineOpen_top X) p hp) ξ

/-- **The conclusion of [Stacks, Tag 01XR] above the size of a finite affine cover.** On a scheme
with affine diagonal covered by `t` affine opens the cohomology of a quasi-coherent module
vanishes in every degree at least `t`, so in those degrees every class is annihilated already by
the zeroth power of a global section of an invertible module. -/
@[stacks 01XR "the degrees at least the size of a finite affine cover"]
theorem exists_sectionPowerAction_eq_zero_of_finite_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))] (s : L.sections)
    [CompactSpace X] [QuasiSeparatedSpace X] (_hU : IsAffineOpen (nonvanishingOpen L s))
    {t : ℕ} (U : Fin t → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : ⨆ i, U i = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (_hp : 0 < p) (ht : t ≤ p)
    (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ (n : ℕ) (t' : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n),
      IsSectionPowerHom X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L s n t' ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L F n t') ξ = 0 :=
  exists_sectionPowerAction_eq_zero_of_isZero X L s F p
    (Stacks.AlgebraicGeometry.AffineCoveringNumber.isZero_cohomology_of_finite_affine_cover X
      U hUaff hUcover F p ht) ξ

end Stacks.SheafOfModules

end
