module

public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleCohomologyInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UnitsShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift

/-!
# The cohomology of the ideal of `X₁ ⊂ Xₙ`

Let `i : T ⟶ T'` be a closed immersion of objects of the big fppf site with square-zero kernel,
and let `g : W ⟶ T'` be a flat morphism of algebraic spaces.  The inverse image
`Z = g⁻¹(T) ⊆ W` is a first order thickening, and its ideal sheaf `𝓘` is the first term of the
units sequence `0 ⟶ 𝓘 ⟶ 𝒪_W^* ⟶ 𝒪_Z^* ⟶ 0`.  This file identifies the étale cohomology of `𝓘`
on `W` with the étale cohomology, on `Z`, of the inverse image `f^*𝒞_{T/T'}` of the conormal
module along the projection `f : Z ⟶ T`:

`H^n(W, 𝓘) ≅ H^n(Z, f^*𝒞_{T/T'})`.

This is a step of the proof of [Stacks Project, Tag 0DPJ]: there `𝓘 = 𝒪_{X₁} ⊗ Iₙ` and the
obstruction group `H²(Xₙ, 𝓘)` is read on `X₁`.

## Main definitions and results

* `AlgebraicGeometry.Space.squareZeroPreimageSpace`: the algebraic space `Z = g⁻¹(T)`, the
  source of `AlgebraicGeometry.Space.preimageProjection` and of
  `AlgebraicGeometry.Space.subspaceInclusion`.
* `AlgebraicGeometry.Space.squareZeroPreimageIdealAddSheafIso`: the abelian sheaf `𝓘` is the
  restriction along the thickening of the abelian sheaf underlying `f^*𝒞_{T/T'}`.
* `AlgebraicGeometry.Space.squareZeroPreimageIdealCohomologyAddEquiv`: the comparison of
  cohomology groups, in every degree.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image `g⁻¹(T)` of a square-zero base extension, as an algebraic space.**  This
is the source of `AlgebraicGeometry.Space.preimageProjection` and of
`AlgebraicGeometry.Space.subspaceInclusion` at the closed subspace
`AlgebraicGeometry.Space.preimageSubspace` of `W`; the inverse image of
`AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso` is a module on it. -/
abbrev squareZeroPreimageSpace {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T') :
    AlgebraicSpaces B S hS :=
  ⟨(preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)).1.toFunctor,
    (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)).2.1⟩

/-- **The ideal of `g⁻¹(T) ⊆ W` is the restriction of `f^*𝒞_{T/T'}` along the thickening.**  The
first term of the units sequence of the first order thickening
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage_squareZeroSubspace` is isomorphic, as an
abelian sheaf on the small étale site of `W`, to the restriction along base change of étale
charts (`AlgebraicGeometry.Space.thickeningRestrictAddSheaf`) of the abelian sheaf underlying
the inverse image along the projection `f : g⁻¹(T) ⟶ T` of the conormal module `𝒞_{T/T'}`.

It is `AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso` (Tag 06BH and the flatness
of `g`) read on abelian sheaves, followed by
`AlgebraicGeometry.Space.modulePushforwardCompToSheafIso`: the abelian sheaf underlying a direct
image of modules along the inclusion of the subspace is the restriction along chart base change
of the underlying abelian sheaf. -/
def squareZeroPreimageIdealAddSheafIso {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T')
    (hg : IsFlat B S hS g.hom) :
    (thickeningUnitsShortComplex B S hS
        (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g)).X₁ ≅
      (thickeningRestrictAddSheaf B S hS
          (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g).1).obj
        ((SheafOfModules.toSheaf
            (structureRingSheaf B S hS (squareZeroPreimageSpace B S hS i hi g))).obj
          ((modulePullback B S hS
              (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
            (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
              (squareZeroSubspace B S hS i hi)))) :=
  (SheafOfModules.toSheaf (structureRingSheaf B S hS W)).mapIso
      (definingIdealSheafPullbackConormalIso B S hS i hi g hg) ≪≫
    (modulePushforwardCompToSheafIso B S hS
      (subspaceInclusion B S hS W (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)))
      (isClosedImmersion_inclusion_of_isThickening B S hS
        (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g).1).rep).app
      ((modulePullback B S hS
          (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
        (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
          (squareZeroSubspace B S hS i hi)))

/-- **The cohomology of the ideal of `X₁ ⊂ Xₙ` is the cohomology on `X₁` of `f^*𝒞_{T/T'}`.**  Let
`i : T ⟶ T'` be a closed immersion of objects of the site with square-zero kernel and let
`g : W ⟶ T'` be flat.  Then for every `n` the étale cohomology on `W` of the first term `𝓘` of
the units sequence of the first order thickening `g⁻¹(T) ⊆ W` is the étale cohomology, on the
small étale site of `g⁻¹(T)` (`AlgebraicGeometry.Space.squareZeroPreimageSpace`), of the
abelian sheaf underlying the inverse image along the projection `f : g⁻¹(T) ⟶ T` of the conormal
module `𝒞_{T/T'}`.

The isomorphism of sheaves is `AlgebraicGeometry.Space.squareZeroPreimageIdealAddSheafIso`, and
the passage from `W` to `g⁻¹(T)` is the invariance of étale cohomology under a thickening,
`AlgebraicGeometry.Space.thickeningCohomologyAddEquiv` ([Stacks Project, Tag 05ZM]). -/
def squareZeroPreimageIdealCohomologyAddEquiv {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T')
    (hg : IsFlat B S hS g.hom) (n : ℕ) :
    Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS
        (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g)).X₁ n ≃+
      Sheaf.H.{u + 1} ((SheafOfModules.toSheaf
            (structureRingSheaf B S hS (squareZeroPreimageSpace B S hS i hi g))).obj
          ((modulePullback B S hS
              (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
            (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
              (squareZeroSubspace B S hS i hi)))) n :=
  (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u, u + 1}
      (squareZeroPreimageIdealAddSheafIso B S hS i hi g hg) n).trans <|
    @AddEquiv.symm _ _ _ _ (thickeningCohomologyAddEquiv B S hS
      (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g).1
      ((SheafOfModules.toSheaf
            (structureRingSheaf B S hS (squareZeroPreimageSpace B S hS i hi g))).obj
          ((modulePullback B S hS
              (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
            (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
              (squareZeroSubspace B S hS i hi)))) n)

/-! ### The projection `g⁻¹(T) ⟶ T` and its cartesian square -/

/-- **The projection `g⁻¹(T) ⟶ T` into the algebraic space represented by `T`.**  It is
`AlgebraicGeometry.Space.preimageProjection`, whose target is the closed subspace
`AlgebraicGeometry.Space.squareZeroSubspace` of `T'`, followed by the identification
`AlgebraicGeometry.Space.rangeSpaceIso` of that subspace with the algebraic space
`⟨yoneda.obj T, _⟩` represented by `T`, which is `(schemeSpaceFunctor B S hS).obj T` by
definition. -/
def squareZeroPreimageProjection {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T') :
    squareZeroPreimageSpace B S hS i hi g ⟶
      (schemeSpace T : AlgebraicSpaces B S hS) :=
  preimageProjection B S hS g (squareZeroSubspace B S hS i hi) ≫
    (rangeSpaceIso B S hS i hi.1).inv

/-- **The square of `X₁ = Xₙ ×_{Spec(Rₙ)} Spec(R₁)` is cartesian.**  The square
```
g⁻¹(T) ──(inclusion)──▶ W
  │                     │
  f                     g
  ▼                     ▼
  T ──(schemeSpaceFunctor.map i)──▶ T'
```
with `f = AlgebraicGeometry.Space.squareZeroPreimageProjection`, is a pullback square of algebraic
spaces.  It is Stacks 083Q (`AlgebraicGeometry.Space.isPullback_fromPreimage`) for the closed
subspace cut out by `i`, transported along the identification of that subspace with `T`. -/
theorem isPullback_squareZeroPreimageProjection {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T') :
    IsPullback
      (subspaceInclusion B S hS W (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)))
      (squareZeroPreimageProjection B S hS i hi g) g ((schemeSpaceFunctor B S hS).map i) := by
  have h := (isPullback_fromPreimage B S hS g (squareZeroSubspace B S hS i hi).1
    (squareZeroSubspace B S hS i hi).2.1
    (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)).2.1).flip
  refine h.of_iso (Iso.refl _) (Iso.refl _) (rangeSpaceIso B S hS i hi.1).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    refine ObjectProperty.hom_ext _ ?_
    change (Subfunctor.range (yoneda.map i)).ι =
      (rangeIsoPresheaf B S hS i hi.1).inv ≫ yoneda.map i
    rw [eq_comm, Iso.inv_comp_eq, rangeIsoPresheaf_hom, Subfunctor.toRange_ι]

/-! ### Base change of the properties of `g` -/

/-- The projection `g⁻¹(T) ⟶ T` is flat when `g` is (Stacks 03MO, flatness is stable under base
change). -/
theorem isFlat_squareZeroPreimageProjection {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} {g : W ⟶ (schemeSpaceFunctor B S hS).obj T'}
    (hg : IsFlat B S hS g.hom) :
    IsFlat B S hS (squareZeroPreimageProjection B S hS i hi g).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_squareZeroPreimageProjection B S hS i hi g) hg

/-- The projection `g⁻¹(T) ⟶ T` is proper when `g` is (Stacks 04WP). -/
theorem isProper_squareZeroPreimageProjection {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} {g : W ⟶ (schemeSpaceFunctor B S hS).obj T'}
    (hg : IsProper B S hS g.hom) :
    IsProper B S hS (squareZeroPreimageProjection B S hS i hi g).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_squareZeroPreimageProjection B S hS i hi g) hg

/-- The projection `g⁻¹(T) ⟶ T` is of finite presentation when `g` is (Stacks 03XR). -/
theorem isFinitePresentation_squareZeroPreimageProjection {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} {g : W ⟶ (schemeSpaceFunctor B S hS).obj T'}
    (hg : IsFinitePresentation B S hS g.hom) :
    IsFinitePresentation B S hS (squareZeroPreimageProjection B S hS i hi g).hom :=
  (isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
    (isPullback_squareZeroPreimageProjection B S hS i hi g) hg

/-- The projection `g⁻¹(T) ⟶ T` has relative dimension `≤ d` when `g` is locally of finite type
of relative dimension `≤ d`: relative dimension is invariant under base change (Stacks 04NS,
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback`). -/
theorem hasRelativeDimensionLE_squareZeroPreimageProjection {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} {g : W ⟶ (schemeSpaceFunctor B S hS).obj T'} {d : ℕ}
    (hft : IsLocallyOfFiniteType B S hS g.hom) (hg : HasRelativeDimensionLE d B S hS g.hom) :
    HasRelativeDimensionLE d B S hS (squareZeroPreimageProjection B S hS i hi g).hom := by
  intro x
  obtain ⟨e, he, hrel⟩ := hg (pointsMap B S hS _
    (subspaceInclusion B S hS W
      (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))).hom x)
  exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_squareZeroPreimageProjection B S hS i hi g))
    W.property (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS T') hft x
    (e : ℕ∞)).1 hrel⟩

end AlgebraicGeometry.Space

end
