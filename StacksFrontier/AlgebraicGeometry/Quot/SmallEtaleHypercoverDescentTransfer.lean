module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleVertex
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechNerve
public import StacksFrontier.AlgebraicGeometry.Quot.HypercoverDerivedDescentTransfer
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedComparisonComp
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedDescent
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertyCovering

/-!
# Stacks 0DLA moves from the spaces-étale to the small étale sites

This file proves two statements:

* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDescentComparison`: the comparison
  `Φ_X = AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor` of the derived categories
  of the small étale site (modules in `Type u`) and of the spaces-étale site (modules in
  `Type (u + 1)`), with the comparisons `ε_f` of the derived pullbacks along fppf coverings,
  satisfies the five clauses of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.
* `AlgebraicGeometry.Space.smallEtaleHypercoverDescentOfSpacesEtale`: with any such comparison,
  Stacks 0DLA on the spaces-étale sites gives Stacks 0DLA on the small étale sites.

Along the way: on the small étale sites, complexes with quasi-coherent cohomology are stable under
shifts and under derived pullback along flat morphisms, and the augmentation, the faces and the
last vertices of an fppf hypercovering are fppf coverings (Stacks 0DER).

## Main results

* `isSpacesEtaleQuasicoherentComplex_smallEtaleSpacesEtaleDerivedFunctor_obj_iff`: `Φ_X K` has
  quasi-coherent cohomology exactly when `K` has.
* `AlgebraicGeometry.Space.isSmallEtaleQuasicoherentComplex_pull_of_isFlat`: flat derived
  pullback preserves quasi-coherent cohomology on the small étale sites.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDescentComparison`,
  `AlgebraicGeometry.Space.smallEtaleHypercoverDescentOfSpacesEtale` and
  `AlgebraicGeometry.Space.smallEtaleHypercoverDescent_of_spacesEtaleHypercoverDescent`.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory
  HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-coherent cohomology on the small étale sites -/

/-- `Φ_X` detects quasi-coherent cohomology: `Φ_X K` has quasi-coherent cohomology sheaves
exactly when `K` has. -/
theorem isSpacesEtaleQuasicoherentComplex_smallEtaleSpacesEtaleDerivedFunctor_obj_iff
    (X : AlgebraicSpaces B S hS) (K : derivedModules B S hS X) :
    IsSpacesEtaleQuasicoherentComplex B S hS X
        ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K) ↔
      IsSmallEtaleQuasicoherentComplex B S hS X K := by
  let : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
    HasDerivedCategory.standard _
  have := preservesFiniteLimits_toSpacesEtaleModules B S hS X
  have := preservesFiniteColimits_toSpacesEtaleModules B S hS X
  exact DerivedCategoryB.derivedCategoryB_mapDerivedCategory_obj_iff
    (toSpacesEtaleRingedToposModules B S hS X)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O))
    (fun M => ⟨fun hM => by
        have : M.IsQuasicoherentOnSite := hM
        exact isQuasicoherentOnSite_toSpacesEtaleModules B S hS X M,
      fun hM => by
        have : ((toSpacesEtaleModules B S hS X).obj M).IsQuasicoherentOnSite := hM
        exact isQuasicoherentOnSite_of_toSpacesEtaleModules B S hS X M⟩) K

/-- Quasi-coherent cohomology is stable under shifts on the small étale sites. -/
theorem isSmallEtaleQuasicoherentComplex_shift (X : AlgebraicSpaces B S hS)
    (K : derivedModules B S hS X) (i : ℤ) (hK : IsSmallEtaleQuasicoherentComplex B S hS X K) :
    IsSmallEtaleQuasicoherentComplex B S hS X (K⟦i⟧) := fun j =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor _ 0).shiftIso i j (i + j) rfl).app K).symm (hK (i + j))

/-- Flat derived pullback preserves quasi-coherent cohomology on the small étale sites. -/
theorem isSmallEtaleQuasicoherentComplex_pull_of_isFlat {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) (K : derivedModules B S hS Y)
    (hK : IsSmallEtaleQuasicoherentComplex B S hS Y K) :
    IsSmallEtaleQuasicoherentComplex B S hS X
      (((smallEtaleDerivedPullbackData B S hS).pull f).obj K) :=
  (isSpacesEtaleQuasicoherentComplex_smallEtaleSpacesEtaleDerivedFunctor_obj_iff B S hS X _).1
    (SimplicialSpacesEtaleSite.isSpacesEtaleQuasicoherentComplex_of_iso
      ((smallEtaleSpacesEtaleDerivedPullIso (T := B.bigEtaleSpaceSite S hS) f hf).app K).symm
      (SimplicialSpacesEtaleSite.isSpacesEtaleQuasicoherentComplex_spacesEtaleDerivedPull_of_isFlat
        f hf _
        ((isSpacesEtaleQuasicoherentComplex_smallEtaleSpacesEtaleDerivedFunctor_obj_iff
          B S hS Y K).2 hK)))

/-! ### The faces and vertices of an fppf hypercovering -/

/-- Fppf coverings are stable under base change. -/
instance fppfCoveringMorphisms_isStableUnderBaseChange :
    (fppfCoveringMorphisms B S hS).IsStableUnderBaseChange :=
  ⟨fun sq hg => fppfCoveringMorphisms_of_isPullback sq.flip hg⟩

/-- Fppf coverings are stable under composition. -/
instance fppfCoveringMorphisms_isStableUnderComposition :
    (fppfCoveringMorphisms B S hS).IsStableUnderComposition :=
  ⟨fun f g hf hg => fppfCoveringMorphisms_comp f g hf hg⟩

/-- Fppf coverings contain the identities and are stable under composition. -/
instance fppfCoveringMorphisms_isMultiplicative :
    (fppfCoveringMorphisms B S hS).IsMultiplicative where

variable {B S hS} in
/-- The last vertex `U_n ⟶ U_0` of an fppf hypercovering is an fppf covering (Stacks 0DER). -/
theorem fppfCoveringMorphisms_map_const_last
    {U : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}
    (hU : (fppfCoveringMorphisms B S hS).IsHypercovering U) (n : ℕ) :
    fppfCoveringMorphisms B S hS (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk n) (Fin.last n)).op) := by
  induction n with
  | zero =>
    rw [SimplicialSpacesEtaleSite.const_last_zero_eq_id, op_id, U.left.map_id]
    exact MorphismProperty.id_mem _ _
  | succ k ih =>
    rw [SimplicialSpacesEtaleSite.const_last_succ_eq_comp_δ_zero, op_comp, U.left.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.IsHypercovering.face_mem _ hU k 0) ih

/-! ### The transfer and the comparison -/

/-- With a comparison of the small étale and the spaces-étale
derived categories as in `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`,
Stacks 0DLA on the spaces-étale sites gives Stacks 0DLA on the small étale sites. -/
theorem smallEtaleHypercoverDescentOfSpacesEtale :
    SmallEtaleHypercoverDescentOfSpacesEtale B S hS := by
  rintro ⟨Φ, ε, h1, h2, h3, h4, h5⟩ h'
  let : ∀ a, Category.{u + 2} (spacesEtaleDerivedModules B S hS a) := fun _ => inferInstance
  let : ∀ a, HasShift (spacesEtaleDerivedModules B S hS a) ℤ := fun _ => inferInstance
  exact hypercoverDerivedDescent_of_comparison (D := derivedModules B S hS)
    (D' := spacesEtaleDerivedModules B S hS) (smallEtaleDerivedPullbackData B S hS).pull
    (smallEtaleDerivedPullbackData B S hS).compIso (fun f => spacesEtaleDerivedPull B S hS f)
    (fun f g => spacesEtaleDerivedPullComp B S hS f g) (fppfCoveringMorphisms B S hS) Φ ε
    (fun U => (fppfCoveringMorphisms B S hS).IsHypercovering U)
    (fun U => IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology U.left U.hom)
    (IsSmallEtaleQuasicoherentComplex B S hS) (IsSpacesEtaleQuasicoherentComplex B S hS) h'
    h1 h2 h3 h4 h5
    (fun f hf K hK => isSmallEtaleQuasicoherentComplex_pull_of_isFlat B S hS f (hf.flat ()) K hK)
    (isSmallEtaleQuasicoherentComplex_shift B S hS)
    (fun U hU => isHypercoveringAugmentation_bigFppf_of_isHypercovering B S hS U hU)
    (fun _ hU => hU.map_zero) (fun _ hU n i => MorphismProperty.IsHypercovering.face_mem _ hU n i)
    (fun _ hU n => fppfCoveringMorphisms_map_const_last hU n)

/-- The functors `Φ_X = AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor` with the
comparisons `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullIso` along fppf
coverings satisfy the five clauses of
`AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`: bijectivity on morphisms
(`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_map_bijective`), the shifts,
quasi-coherence, descent of the essential image
(`AlgebraicGeometry.Space.exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_fppfCovering`)
and the composition coherence
(`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullIso_comp_hom_app`). -/
theorem smallEtaleSpacesEtaleDescentComparison : SmallEtaleSpacesEtaleDescentComparison B S hS :=
  ⟨smallEtaleSpacesEtaleDerivedFunctor B S hS,
    fun f hf => smallEtaleSpacesEtaleDerivedPullIso (T := B.bigEtaleSpaceSite S hS) f (hf.flat ()),
    smallEtaleSpacesEtaleDerivedFunctor_map_bijective B S hS,
    nonempty_smallEtaleSpacesEtaleDerivedFunctor_shift_iso B S hS,
    fun X K hK => (isSpacesEtaleQuasicoherentComplex_smallEtaleSpacesEtaleDerivedFunctor_obj_iff
      B S hS X K).2 hK,
    fun f hf L hL K' hK' e =>
      exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_fppfCovering B S hS f hf L hL K' hK' e,
    fun f g hf hg hfg K => smallEtaleSpacesEtaleDerivedPullIso_comp_hom_app B hS f g hf hg hfg K⟩

/-- Stacks 0DLA on the spaces-étale sites gives Stacks 0DLA on the small étale sites. -/
theorem smallEtaleHypercoverDescent_of_spacesEtaleHypercoverDescent
    (h : SpacesEtaleHypercoverDescent B S hS) : SmallEtaleHypercoverDescent B S hS :=
  smallEtaleHypercoverDescentOfSpacesEtale B S hS (smallEtaleSpacesEtaleDescentComparison B S hS) h

end AlgebraicGeometry.Space
