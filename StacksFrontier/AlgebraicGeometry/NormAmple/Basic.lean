module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Map
public import StacksFrontier.AlgebraicGeometry.SectionExtension.FiniteSet
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# Norms of ample invertible sheaves

Let `f : X ⟶ Y` be a finite morphism of schemes admitting a norm of degree `d ≥ 1` on functions
(`Stacks.Norm.MorphismNorm`). If `X` carries an ample invertible sheaf, then so does `Y`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_of_le`: A nonvanishing locus
  contained in an affine open is affine.
* `Stacks.Divisors.surjective_of_morphismNorm`: A finite morphism admitting a norm of positive
  degree is surjective.
* `Stacks.Divisors.exists_isAmple_of_morphismNorm`: If `f` is finite and admits a norm of positive
  degree and `X` has an ample invertible sheaf, then so has `Y`.
* `Stacks.Divisors.exists_isAmple_of_isFiniteLocallyFreeOfRank`: If `f` is finite locally free of
  constant positive rank and `X` has an ample invertible sheaf, then so has `Y`.

## References

* [Stacks Project, Tag 0BD0](https://stacks.math.columbia.edu/tag/0BD0)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 0BD4](https://stacks.math.columbia.edu/tag/0BD4)
* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

universe u

/-- A nonvanishing locus contained in an affine open is affine. -/
theorem AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_of_le
    {X : Scheme.{u}} (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U)
    (hle : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s ≤ U) :
    IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s) :=
  inf_eq_right.2 hle ▸
    AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen L s U hU

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- A finite morphism of schemes admitting a norm of degree `d ≥ 1` is surjective. -/
theorem surjective_of_morphismNorm (f : X ⟶ Y) [IsFinite f] {d : ℕ} (hd : 1 ≤ d)
    (N : MorphismNorm f d) : Function.Surjective f.base := by
  intro y
  by_contra hy
  have hclosed : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  set V : Y.Opens := ⟨(Set.range f.base)ᶜ, hclosed.isOpen_compl⟩ with hV
  have hyV : y ∈ V := fun h => hy (Set.mem_range.1 h)
  have hpre : f ⁻¹ᵁ V = ⊥ :=
    TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun x hx => hx ⟨x, rfl⟩)
  have hsub : Subsingleton Γ(X, f ⁻¹ᵁ V) := hpre ▸ inferInstance
  have hzo : (0 : Γ(Y, V)) = 1 := by
    have h := (N.app_pullback V 0).symm.trans
      ((congrArg (N.app V) (Subsingleton.elim (f.app V 0) (f.app V 1))).trans (N.app_pullback V 1))
    rwa [zero_pow (by lia : d ≠ 0), one_pow] at h
  exact zero_ne_one
    ((map_zero _).symm.trans ((congrArg (Y.evaluation V y hyV).hom hzo).trans (map_one _)))

/-- The norm along a finite morphism of an invertible module is invertible. -/
private theorem isInvertible_normInvertible_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (N : MorphismNormMap f) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property (normInvertible f N L) :=
  isInvertible_normInvertible f N L (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)

/-- Let `f : X ⟶ Y` be a finite morphism of schemes admitting a norm of degree `d ≥ 1`. If `X`
has an ample invertible sheaf, then so has `Y`. -/
@[stacks 0BD0]
theorem exists_isAmple_of_morphismNorm (f : X ⟶ Y) [IsFinite f] {d : ℕ} (hd : 1 ≤ d)
    (N : MorphismNorm f d) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    ∃ (M : Y.Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property M),
      @AlgebraicGeometry.Scheme.Modules.IsAmple Y M hM := by
  classical
  have hsurj := surjective_of_morphismNorm f hd N
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  have hNLs : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (normInvertible f N.toMorphismNormMap L) :=
    isInvertible_normInvertible_of_isFinite f N.toMorphismNormMap L hLs
  have hNL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (normInvertible f N.toMorphismNormMap L) :=
    (isInvertible_iff_algebraicGeometry _ _ _).1 hNLs
  refine ⟨normInvertible f N.toMorphismNormMap L, hNL, ?_⟩
  have hcX : CompactSpace X := hL.compactSpace
  have hcpt : CompactSpace Y := ⟨hsurj.range_eq ▸ isCompact_range f.continuous⟩
  refine (AlgebraicGeometry.Scheme.Modules.isAmple_iff Y
    (normInvertible f N.toMorphismNormMap L)).2 ⟨hcpt, fun y => ?_⟩
  obtain ⟨V, hVaff, hyV, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (U := (⊤ : Y.Opens)) (Opens.mem_top y)
  have hEfin : (f.base ⁻¹' {y}).Finite := f.finite_preimage_singleton y
  have hEW : (f.base ⁻¹' {y}) ⊆ ((f ⁻¹ᵁ V : X.Opens) : Set X) := by
    rintro x (rfl : f.base x = y)
    exact hyV
  obtain ⟨m, hm, s, hsaff, hsE, hsW⟩ :=
    exists_sections_finite_subset_nonvanishingOpen_le_of_isAmple L hL hEfin (f ⁻¹ᵁ V) hEW
  have hunit : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
    Stacks.SheafOfModules.isInvertible_unit X.presheaf
      (structureSheafRing X.toRingedSpace).property
  have hone : ∀ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
      (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
      (unitSections X.toRingedSpace) :=
    fun x => (nonvanishingLocus_unitSections X.toRingedSpace).ge (Set.mem_univ x)
  have hLmAG : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) :=
    tensorPower_isInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L (m : ℤ)
  have hLms : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) := inferInstance
  obtain ⟨σ, hσ⟩ : ∃ σ : _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace) ⟶
      tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ),
      _root_.SheafOfModules.sectionsMap σ (unitSections X.toRingedSpace) = s :=
    ⟨_, sectionsMap_unitHomEquiv_symm_unitSections _ s⟩
  have hXs := nonvanishingLocus_sectionsMap_eq_setOf_not_zeroAt
    (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) σ (unitSections X.toRingedSpace) hone
  rw [hσ] at hXs
  have hNU := isInvertible_normInvertible_of_isFinite f N.toMorphismNormMap _ hunit
  have hNLm := isInvertible_normInvertible_of_isFinite f N.toMorphismNormMap _ hLms
  set tG := normGenerator f N.toMorphismNormMap
    (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f _ hunit) ⊤
    (generatorSectionsOfNonvanishing _ (unitSections X.toRingedSpace) hone _) with htG
  have hg' : ∀ y' : Y, y' ∈ nonvanishingLocus (X := Y.toRingedSpace)
      (normInvertible f N.toMorphismNormMap
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)))
      (sectionsOfTop _ tG.val) :=
    fun y' => (nonvanishingLocus_sectionsOfTop_generator _ tG).ge (Set.mem_univ y')
  set ψ := normMap f N (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) σ with hψ
  have hYt := nonvanishingLocus_sectionsMap_eq_setOf_not_zeroAt
    (normInvertible f N.toMorphismNormMap
      (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)))
    (normInvertible f N.toMorphismNormMap
      (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ))) ψ
    (sectionsOfTop _ tG.val) hg'
  obtain ⟨e⟩ := nonempty_normInvertible_tensorPowerModule'_iso f N L hNL m
  have hXs' : ∀ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
      (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) s ↔
      ¬ zeroAt (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
        (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) σ x :=
    fun x => Set.ext_iff.1 hXs x
  have hkey : ∀ y' : Y, y' ∈ nonvanishingLocus (X := Y.toRingedSpace)
      (@tensorPowerModule' Y.toRingedSpace
        (normInvertible f N.toMorphismNormMap L) hNL (m : ℤ))
      (_root_.SheafOfModules.sectionsMap e.hom
        (_root_.SheafOfModules.sectionsMap ψ (sectionsOfTop _ tG.val))) ↔
      ∀ x : X, f.base x = y' → x ∈ nonvanishingLocus (X := X.toRingedSpace)
        (tensorPowerModule' (X := X.toRingedSpace) L (m : ℤ)) s := by
    intro y'
    rw [Set.ext_iff.1 (nonvanishingLocus_sectionsMap Y.toRingedSpace e
        (_root_.SheafOfModules.sectionsMap ψ (sectionsOfTop _ tG.val))) y',
      Set.ext_iff.1 hYt y', Set.mem_ofPred_eq, hψ, normMap_zeroAt_iff f N _ _ σ y']
    exact ⟨fun h x hx => (hXs' x).2 fun hz => h ⟨x, hx, hz⟩,
      fun h hex => hex.elim fun x hx => (hXs' x).1 (h x hx.1) hx.2⟩
  refine ⟨m, hm, _root_.SheafOfModules.sectionsMap e.hom
    (_root_.SheafOfModules.sectionsMap ψ (sectionsOfTop _ tG.val)), ?_, ?_⟩
  · exact (hkey y).2 fun x hx => hsE hx
  · have hle : nonvanishingOpen (X := Y.toRingedSpace)
        (@tensorPowerModule' Y.toRingedSpace
          (normInvertible f N.toMorphismNormMap L) hNL (m : ℤ))
        (_root_.SheafOfModules.sectionsMap e.hom
          (_root_.SheafOfModules.sectionsMap ψ (sectionsOfTop _ tG.val))) ≤ V := by
      intro y' hy'
      obtain ⟨x, rfl⟩ := hsurj y'
      exact hsW ((hkey _).1 hy' x rfl)
    exact AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_of_le _ _ V hVaff hle

/- Tag 0BD4 case (1) asks only for `f` finite locally free, with surjectivity a separate
hypothesis; the statement below is that case for a morphism of constant positive rank, and
becomes case (1) in general only after `Y` is cut into the opens where the rank is constant. -/
/-- If `f : X ⟶ Y` is finite locally free of constant rank `d > 0` and `X` has an ample
invertible sheaf, then so has `Y`. -/
theorem exists_isAmple_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hd : 0 < d) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    ∃ (M : Y.Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property M),
      @AlgebraicGeometry.Scheme.Modules.IsAmple Y M hM :=
  have : IsFinite f :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d)).1
  exists_isAmple_of_morphismNorm f hd (finiteLocallyFreeNormOfRank f d hd).1 L hL

end Stacks.Divisors

end
