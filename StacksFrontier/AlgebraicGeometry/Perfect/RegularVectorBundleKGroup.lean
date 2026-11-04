module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularKGroupComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRegular
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering

/-!
# The three K-groups of a regular scheme agree

Let `X` be a quasi-compact regular scheme with affine diagonal. The Grothendieck group
`K₀(Vect(X))` of finite locally free `𝒪_X`-modules, the Grothendieck group
`K₀(X) = K₀(D_perf(𝒪_X))` of perfect complexes and the Grothendieck group `K'₀(X) = K₀(Coh(𝒪_X))`
of coherent sheaves are then all identified:

* `X` has the resolution property by [Stacks, Tag 0F8A], so `K₀(Vect(X)) ⟶ K₀(X)` is an
  isomorphism by [Stacks, Tag 0FDJ];
* `X` is Noetherian, being quasi-compact and regular, so `K₀(X) ⟶ K'₀(X)` is an isomorphism by
  [Stacks, Tag 0FDI].

The composite sends the class of a finite locally free module to its class as a coherent sheaf.
This is the first sentence of the proof of [Stacks, Tag 0FEY].

## Main definitions

* `AlgebraicGeometry.regularVectorBundleKZeroAddEquiv`: the additive isomorphism
  `K₀(Vect(X)) ≃+ K'₀(X)`.

## Main results

* `AlgebraicGeometry.isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian`: a finite locally
  free module on a locally Noetherian scheme is an object of `Coh(𝒪_X)`.
* `AlgebraicGeometry.regularVectorBundleKZeroAddEquiv_classOf`: the isomorphism sends the class of
  a finite locally free module to its class in `K'₀(X)`.

## Implementation notes

`K'₀(X)` is `AlgebraicGeometry.CoherentKZero X`, which is stated for a locally Noetherian scheme.
Local Noetherianity is not an additional hypothesis here: it is deduced from regularity by
`AlgebraicGeometry.isLocallyNoetherian_of_isRegular`, and the statements name that proof
explicitly. Since it is a proof of a proposition, the group so obtained is the group
`CoherentKZero X` for any other proof of local Noetherianity.

## References

* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 0FDI](https://stacks.math.columbia.edu/tag/0FDI)
* [Stacks Project, Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **A finite locally free module on a locally Noetherian scheme is coherent**, in the sense
that cuts out the category `Coh(𝒪_X)` whose Grothendieck group is `K'₀(X)`. -/
theorem isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    Stacks.SheafOfModules.coherentModules X.ringCatSheaf M :=
  (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' M).2
    (@Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _ M
      hM)

/-- **The isomorphism `K₀(Vect(X)) ≃+ K'₀(X)` of a quasi-compact regular scheme with affine
diagonal.**  It is the composite of the isomorphism `K₀(Vect(X)) ≃+ K₀(X)` of [Stacks, Tag 0FDJ]
(`Stacks.Perfect.BoundedLocallyFreeComplexes.vectorBundleKZeroAddEquiv`), which applies because
`X` has the resolution property by [Stacks, Tag 0F8A]
(`AlgebraicGeometry.hasResolutionProperty_of_isRegular`), with the isomorphism `K₀(X) ≃+ K'₀(X)`
of [Stacks, Tag 0FDI] (`AlgebraicGeometry.exists_addEquiv_K0_coherentKZero_of_isRegular`), which
applies because a quasi-compact regular scheme is Noetherian.

This is the first sentence of the proof of [Stacks, Tag 0FEY]: `K'₀(X) = K₀(X) = K₀(Vect(X))`. -/
def regularVectorBundleKZeroAddEquiv (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X) :
    VectorBundleKZero X ≃+ CoherentKZero X :=
  haveI := isLocallyNoetherian_of_isRegular hX
  haveI : IsNoetherian X := ⟨⟩
  haveI := AlgebraicGeometry.IsRegular.hasResolutionProperty X hX
  (vectorBundleKZeroAddEquiv X).trans
    (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose

/-- **The isomorphism `K₀(Vect(X)) ≃+ K'₀(X)` on classes.**  The class of a coherent sheaf which
is finite locally free goes to its class in `K'₀(X)`. -/
theorem regularVectorBundleKZeroAddEquiv_classOf (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F.obj) :
    regularVectorBundleKZeroAddEquiv X hX (VectorBundleKZero.classOf X F.obj) =
      @KZero.mk _ _ (coherentModulesAbelian X) F := by
  have := isLocallyNoetherian_of_isRegular hX
  have : IsNoetherian X := ⟨⟩
  have := AlgebraicGeometry.IsRegular.hasResolutionProperty X hX
  show (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose
    (vectorBundleKZeroAddEquiv X (VectorBundleKZero.classOf X F.obj)) = _
  rw [vectorBundleKZeroAddEquiv_classOf X F.obj hF]
  exact (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose_spec.2.1 F _ (Iso.refl _)

/-- **The isomorphism `K₀(Vect(X)) ≃+ K'₀(X)` on the class of a finite locally free module `ℰ`**:
the image is the class of `ℰ` as a coherent sheaf. -/
theorem regularVectorBundleKZeroAddEquiv_classOf' (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X) (E : X.Modules)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    regularVectorBundleKZeroAddEquiv X hX (VectorBundleKZero.classOf X E) =
      @KZero.mk _ _ (coherentModulesAbelian X)
        ⟨E, @isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian X
          (isLocallyNoetherian_of_isRegular hX) E hE⟩ :=
  regularVectorBundleKZeroAddEquiv_classOf X hX ⟨E, _⟩ hE

end AlgebraicGeometry

end
