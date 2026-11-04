module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoof
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijective
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated

/-!
# The derived roof of [Stacks, Tag 0F8G] on classes of schemes

Let `E` and `F` be bounded complexes of finite locally free modules on a scheme `X`. Every
morphism `α : E ⟶ F` of the derived category is represented by a roof `E ← G → F` in which `G` is
a bounded complex of finite locally free modules and `G ⟶ E` is a quasi-isomorphism, when `X` is
quasi-compact and separated with the resolution property, Noetherian with the resolution property,
carries an ample invertible module, or is affine. The roof also exists for the identity of the
structure sheaf of `Spec R` and for the identity of `𝒪(1)` on `ℙⁿ_S` with `S` affine.

## Main results

* `exists_boundedFiniteLocallyFree_roof_of_isSeparated`: the roof on a quasi-compact separated
  scheme with the resolution property.
* `exists_boundedFiniteLocallyFree_roof_of_isNoetherian`: the roof on a Noetherian scheme with the
  resolution property.
* `exists_boundedFiniteLocallyFree_roof_of_isAmple`: the roof on a scheme carrying an ample
  invertible module.
* `exists_boundedFiniteLocallyFree_roof_of_isAffine`: the roof on an affine scheme.
* `exists_boundedFiniteLocallyFree_roof_unit_spec`: the roof for the identity of the structure
  sheaf of `Spec R` in degree zero.
* `exists_boundedFiniteLocallyFree_roof_twistingSheaf_projectiveSpace`: the roof for the identity
  of `𝒪(1)` in degree zero on `ℙⁿ_S`, `S` affine.

## References

* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.ProjectiveSpace

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0F8G] on a quasi-compact separated scheme with the resolution property.**
Every morphism `α : E ⟶ F` of the derived category between bounded complexes of finite locally
free modules is `inv p ≫ q` for a quasi-isomorphism `p : G ⟶ E` and a morphism `q : G ⟶ F` from a
bounded complex `G` of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_of_isSeparated (X : Scheme.{u})
    [CompactSpace X] [X.IsSeparated] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X E F hE hF α

/-- **[Stacks, Tag 0F8G] on a Noetherian scheme with the resolution property.** Every morphism
`α : E ⟶ F` of the derived category between bounded complexes of finite locally free modules is
`inv p ≫ q` for a quasi-isomorphism `p : G ⟶ E` and a morphism `q : G ⟶ F` from a bounded complex
`G` of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  have _ : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have _ := isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian X
  exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X E F hE hF α

/-- **[Stacks, Tag 0F8G] on a scheme carrying an ample invertible module.** Every morphism
`α : E ⟶ F` of the derived category between bounded complexes of finite locally free modules is
`inv p ≫ q` for a quasi-isomorphism `p : G ⟶ E` and a morphism `q : G ⟶ F` from a bounded complex
`G` of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  have _ : CompactSpace X := hL.1
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAmple L hL
  have _ : X.IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL).isSeparated
  exists_boundedFiniteLocallyFree_roof_of_isSeparated X E F hE hF α

/-- **[Stacks, Tag 0F8G] on an affine scheme.** Every morphism `α : E ⟶ F` of the derived
category between bounded complexes of finite locally free modules is `inv p ≫ q` for a
quasi-isomorphism `p : G ⟶ E` and a morphism `q : G ⟶ F` from a bounded complex `G` of finite
locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  exists_boundedFiniteLocallyFree_roof_of_isAmple X (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X) E F hE hF α

/-- **The roof of [Stacks, Tag 0F8G] for the identity of the structure sheaf of `Spec R`.** The
identity of `𝒪_{Spec R}` in degree zero is `inv p ≫ q` for a quasi-isomorphism `p` and a morphism
`q` from a bounded complex of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_unit_spec (R : CommRingCat.{u}) :
    ∃ (G : CochainComplex (Spec R).Modules ℤ)
      (p : G ⟶ (CochainComplex.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf)) (_ : QuasiIso p)
      (q : G ⟶ (CochainComplex.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf)),
      boundedFiniteLocallyFreeComplex (Spec R) G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = 𝟙 _ :=
  exists_boundedFiniteLocallyFree_roof_of_isAffine (Spec R) _ _
    (boundedFiniteLocallyFreeComplex_single (Spec R) _ (isFiniteLocallyFree_unit (Spec R)))
    (boundedFiniteLocallyFreeComplex_single (Spec R) _ (isFiniteLocallyFree_unit (Spec R)))
    (𝟙 _)

/-- **The roof of [Stacks, Tag 0F8G] for the identity of `𝒪(1)` on `ℙⁿ_S`, `S` affine.** The
identity of `𝒪(1)` in degree zero is `inv p ≫ q` for a quasi-isomorphism `p` and a morphism `q`
from a bounded complex of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_roof_twistingSheaf_projectiveSpace
    (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    ∃ (G : CochainComplex (projectiveSpaceOver n S).Modules ℤ)
      (p : G ⟶ (CochainComplex.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (projectiveSpaceTwistingSheaf n S)) (_ : QuasiIso p)
      (q : G ⟶ (CochainComplex.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (projectiveSpaceTwistingSheaf n S)),
      boundedFiniteLocallyFreeComplex (projectiveSpaceOver n S) G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = 𝟙 _ := by
  have hrk := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S)
  have hflf : IsFiniteLocallyFree.{u, u, u}
      (R := (projectiveSpaceOver n S).ringCatSheaf) (projectiveSpaceTwistingSheaf n S) :=
    ⟨(SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (M := projectiveSpaceTwistingSheaf n S) (r := 1) (hM := hrk)).exists_isFiniteLocallyFreeData⟩
  exact exists_boundedFiniteLocallyFree_roof_of_isAmple (projectiveSpaceOver n S)
    (projectiveSpaceTwistingSheaf n S) (isAmple_projectiveSpaceTwistingSheaf n S) _ _
    (boundedFiniteLocallyFreeComplex_single _ _ hflf)
    (boundedFiniteLocallyFreeComplex_single _ _ hflf) (𝟙 _)

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
