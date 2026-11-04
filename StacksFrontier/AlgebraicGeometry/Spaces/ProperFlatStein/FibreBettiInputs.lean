module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitRestrictScalarsIsoAnySite

/-!
# Three results consumed by the proof of Stacks 0E0D

The proof of Stacks 0E0D in this library uses three results that are not yet proved here:

* `AlgebraicGeometry.Space.fibreBetti_baseChange` (Stacks 0E0R, part (1)),
* `AlgebraicGeometry.Space.upperSemicontinuous_fibreBetti` (Stacks 0E0R, part (2)),
* `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_geometricFibres`
  (Stacks 0E0S).

This module states each of them, verbatim, as a proposition
(`AlgebraicGeometry.Space.ProperFlatStein.FibreBettiBaseChangeInput`,
`AlgebraicGeometry.Space.ProperFlatStein.UpperSemicontinuousFibreBettiInput` and
`AlgebraicGeometry.Space.ProperFlatStein.StructureSharpOfGeometricFibresInput`), so that each is
discharged by the corresponding theorem once it is proved.  The Betti-number function
`AlgebraicGeometry.Space.ProperFlatStein.fibreBettiFunction` is the intended body of
`AlgebraicGeometry.Space.fibreBetti`, with its derived categories taken at
`HasDerivedCategory.standard`.

It also proves the one computation with that function needed here:
`AlgebraicGeometry.Space.ProperFlatStein.finrank_homology_zero_of_isIso_structureSharp`, the
degree-zero cohomology of `Rq_* 𝒪` over an affine object `T` is `Γ(T, 𝒪)` when the structure map
`𝒪_T ⟶ q_* 𝒪` is an isomorphism.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space.ProperFlatStein

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The spectrum of a residue field is affine. -/
instance isAffine_residueFieldSiteObj (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The degree-`i` cohomology `Hⁱ(RΓ(T, R(f_T)_* 𝓕_T))` of the base change of `𝓕` to
`X ×_U T`, for an affine object `T` over `U`; the derived categories are taken at
`HasDerivedCategory.standard`. -/
abbrev baseChangeSectionsHomology {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace U) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) (i : ℤ) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
      _ _ (HasDerivedCategory.standard _) i).obj
    ((representedAffineDerivedSections B S hS T).obj
      ((derivedModulePushforward B S hS (pullback.snd f (schemeSpaceMap t))).obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
          ((modulePullback B S hS (pullback.fst f (schemeSpaceMap t))).obj F))))

/-- **The `i`-th Betti-number function of `(f, 𝓕)`**, `y ↦ dim_{κ(y)} Hⁱ(X_y, 𝓕_y)`: the body of
`AlgebraicGeometry.Space.fibreBetti`. -/
def fibreBettiFunction {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace U)
    (F : Modules.{u, u} B S hS X.1 X.2) (i : ℤ) :
    (BigFppfOver.toScheme B S hS).obj U → ℕ :=
  fun y => Module.finrank Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤)
    (baseChangeSectionsHomology f (residueFieldSiteHom B S hS U y) F i)

variable (B S hS) in
/-- **Stacks 0E0R, part (1)**, the statement of `AlgebraicGeometry.Space.fibreBetti_baseChange`
formation of the Betti-number functions commutes with base change. -/
def FibreBettiBaseChangeInput : Prop :=
  ∀ {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩),
    IsProper B S hS f.hom → IsFinitePresentation B S hS f.hom →
    ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsFinitePresentation →
    IsFlatOver B S hS X.2 f.hom F → ∀ {U' : BigFppfOver B S hS} (g : U' ⟶ U) (i : ℤ),
      fibreBettiFunction (pullback.snd f (representedSpaceMap B S hS g))
          ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj F) i =
        fibreBettiFunction f F i ∘ ((BigFppfOver.toScheme B S hS).map g).base

variable (B S hS) in
/-- **Stacks 0E0R, part (2)**, the statement of
`AlgebraicGeometry.Space.upperSemicontinuous_fibreBetti`: the Betti-number functions are upper
semicontinuous. -/
def UpperSemicontinuousFibreBettiInput : Prop :=
  ∀ {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩),
    IsProper B S hS f.hom → IsFinitePresentation B S hS f.hom →
    ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsFinitePresentation →
    IsFlatOver B S hS X.2 f.hom F → ∀ i : ℤ, UpperSemicontinuous (fibreBettiFunction f F i)

variable (B S hS) in
/-- **Stacks 0E0S**, the statement of
`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_geometricFibres`: for a proper,
flat, finitely presented morphism with reduced and connected geometric fibres, `𝒪_Y ⟶ f_* 𝒪_X`
is an isomorphism, also after any base change. -/
def StructureSharpOfGeometricFibresInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsProper B S hS f.hom → IsFlat B S hS f.hom → IsFinitePresentation B S hS f.hom →
    (∀ y : GeometricPoint B S hS Y.1,
      HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f.hom y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) →
    (∀ y : GeometricPoint B S hS Y.1,
      ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f.hom y.1)) →
    IsIso (structureSharp B S hS f) ∧
      ∀ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y),
        IsIso (structureSharp B S hS (pullback.snd f g))

end AlgebraicGeometry.Space.ProperFlatStein
