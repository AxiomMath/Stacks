module

public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomologyDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.Homology.Perfect.MinimalComplexFreeCohomology
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# The de Rham complex of a proper smooth scheme over an affine base, as an object of `D(A)`

Let `A` be a commutative ring and `f : X ⟶ Spec A` a quasi-compact quasi-separated morphism. The
derived direct image `Rπ_*Ω^•_{X/A}` of the relative de Rham complex has quasi-coherent
cohomology sheaves ([Stacks, Tag 0FLX]), so by the derived Spec–Γ equivalence it is the complex
of sheaves associated to an object of `D(A)`, namely its derived global sections. This file names
that object, `affineDeRhamModel f`, and records the dictionary between it and the sheaves:

* its cohomology modules are the global sections of the de Rham cohomology sheaves
  `ℋ^n_dR(X/A)` of [Stacks, Tag 0FMN];
* for `f` proper and smooth it is perfect ([Stacks, Tag 0FM0]) and its formation commutes with
  arbitrary base change `A → B` ([Stacks, Tag 0FM0] together with [Stacks, Tag 08DW]);
* over a local ring, free cohomology modules make the de Rham cohomology sheaves finite locally
  free.

These are the inputs, on the side of `D(A)`, of the reduction of the finite local freeness of
`ℋ^n_dR(X/Y)` for a proper smooth `X ⟶ Y` over `ℚ` (the sentence of [Stacks, Tag 0FMN] the source
defers to a future reference) to the Artinian local case.

## Main definitions

* `Stacks.DeRhamSmooth.affineDeRhamDirectImageQCoh`: `Rπ_*Ω^•_{X/A}` as an object of
  `D_QCoh(𝒪_{Spec A})`.
* `Stacks.DeRhamSmooth.affineDeRhamModel`: `RΓ(Spec A, Rπ_*Ω^•_{X/A})`, an object of `D(A)`.

## Main results

* `Stacks.DeRhamSmooth.affineDeRhamModelHomologyIso`:
  `H^n(affineDeRhamModel f) ≅ Γ(Spec A, ℋ^n_dR(X/A))` as `A`-modules.
* `Stacks.DeRhamSmooth.affineDeRhamModelTildeIso`: the associated complex of sheaves of the model
  is `Rπ_*Ω^•_{X/A}`.
* `Stacks.DeRhamSmooth.isPerfect_affineDeRhamModel`: the model is perfect for `f` proper smooth.
* `Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback`: base change of the unbounded
  `Rπ_*Ω^•_{X/S}` along any cartesian square ([Stacks, Tag 0FM0]).
* `Stacks.DeRhamSmooth.affineDeRhamModelBaseChangeIsoOfIsPullback` and
  `Stacks.DeRhamSmooth.affineDeRhamModelBaseChangeIso`: the model of `X ×_A B` is the derived base
  change of the model of `X`.
* `Stacks.DeRhamSmooth.isFiniteLocallyFree_deRhamCohomologySheaf_of_free`: over a local ring,
  free global sections make the de Rham cohomology sheaves finite locally free.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, seated at
priority `10000` because the import closure carries the global locally small instances (see
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`): that is the
model at which `Stacks.DeRhamSmooth.deRhamCohomologySheaf` and the base change of
[Stacks, Tag 0FM0] are stated. No `@[stacks]` attribute is carried.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRhamDirectImage

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- **`Rπ_*Ω^•_{X/A}` as an object of `D_QCoh(𝒪_{Spec A})`**: the derived direct image of the
relative de Rham complex, read in the unbounded derived category, with the quasi-coherence of its
cohomology sheaves ([Stacks, Tag 0FLX]). -/
def affineDeRhamDirectImageQCoh [QuasiCompact f] [QuasiSeparated f] :
    (StandardModel.derivedQuasicoherent A).FullSubcategory :=
  ⟨DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f),
    fun n => isQuasicoherent_homology_derivedDeRhamDirectImage f n⟩

/-- **`RΓ(Spec A, Rπ_*Ω^•_{X/A})`**, the de Rham complex of `X` over `A` as an object of `D(A)`:
the derived global sections of the derived direct image of the relative de Rham complex. -/
def affineDeRhamModel [QuasiCompact f] [QuasiSeparated f] : DerivedCategory (ModuleCat.{u} A) :=
  (derivedGlobalSectionsQuasicoherent A).obj (affineDeRhamDirectImageQCoh f)

/-- **The cohomology of the model is the global sections of the de Rham cohomology sheaves**:
`H^n(RΓ(Spec A, Rπ_*Ω^•_{X/A})) ≅ Γ(Spec A, ℋ^n_dR(X/A))` as `A`-modules. -/
def affineDeRhamModelHomologyIso [QuasiCompact f] [QuasiSeparated f] (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (affineDeRhamModel f) ≅
      (moduleSpecΓFunctor (R := A)).obj (deRhamCohomologySheaf f n) :=
  (derivedGlobalSectionsQuasicoherentCompHomologyIso A n).app (affineDeRhamDirectImageQCoh f) ≪≫
    (moduleSpecΓIsoGlobalSectionsOver A).symm.app (deRhamCohomologySheaf f n)

/-- **The complex of sheaves associated to the model is `Rπ_*Ω^•_{X/A}`.** The counit of the
derived Spec–Γ adjunction is invertible on `D_QCoh(𝒪_{Spec A})`. -/
def affineDeRhamModelTildeIso [QuasiCompact f] [QuasiSeparated f] :
    (tilde.functor A).mapDerivedCategory.obj (affineDeRhamModel f) ≅
      DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f) :=
  ((derivedTildeCompι A).app (affineDeRhamModel f)).symm ≪≫
    (StandardModel.derivedQuasicoherent A).ι.mapIso
      (asIso ((StandardModel.derivedTildeQuasicoherentAdjunction A).counit.app
        (affineDeRhamDirectImageQCoh f)))

/-- **The model computes the unbounded `Rπ_*Ω^•_{X/A}`**, the object of [Stacks, Tag 0FM0]: the
complex of sheaves associated to the model is the unbounded derived direct image of the relative
de Rham complex. -/
def affineDeRhamModelTildeUnboundedIso [QuasiCompact f] [QuasiSeparated f] :
    (tilde.functor A).mapDerivedCategory.obj (affineDeRhamModel f) ≅
      DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded f :=
  affineDeRhamModelTildeIso f ≪≫ DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso f

/-- **The model of a proper smooth morphism is perfect** ([Stacks, Tag 0FM0] read through
[Stacks, Tag 08EB]). -/
theorem isPerfect_affineDeRhamModel [IsProper f] [Smooth f] :
    StacksDraft.Perfect.IsPerfect (affineDeRhamModel f) :=
  (isPerfect_tilde_iff_of_model (affineDeRhamModel f)).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      (affineDeRhamModelTildeUnboundedIso f).symm
      (ProperSmoothDeRham.isPerfect_derivedPushforward_deRhamComplex f))

/-- **The de Rham cohomology modules of a proper smooth scheme over a Noetherian ring are
finite**: they are the cohomology modules of the perfect model. -/
theorem module_finite_homology_affineDeRhamModel [IsNoetherianRing A] [IsProper f] [Smooth f]
    (n : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (affineDeRhamModel f)) :=
  StacksDraft.Perfect.module_finite_homology_of_isPerfect _ (isPerfect_affineDeRhamModel f) n

/-- **The converter: over a local ring, free global sections make the de Rham cohomology sheaves
finite locally free.** Let `A` be a local ring and `f : X ⟶ Spec A` proper and smooth. If every
`Γ(Spec A, ℋ^n_dR(X/A))` is a free `A`-module, then every `ℋ^n_dR(X/A)` is a finite locally free
`𝒪_{Spec A}`-module.

The modules are the cohomology modules of the perfect model, so they are finite as well
(`StacksDraft.Perfect.free_finite_homology_of_projective`), and a quasi-coherent module on
`Spec A` whose global sections are finite projective is finite locally free
([Stacks, Tag 05JM]). -/
theorem isFiniteLocallyFree_deRhamCohomologySheaf_of_free [IsLocalRing A] [IsProper f] [Smooth f]
    (h : ∀ n : ℤ, Module.Free A ((moduleSpecΓFunctor (R := A)).obj (deRhamCohomologySheaf f n)))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f n) := by
  have hH : ∀ i, Module.Projective A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (affineDeRhamModel f)) :=
    fun i => by
      have := h i
      exact Module.Projective.of_equiv (affineDeRhamModelHomologyIso f i).toLinearEquiv.symm
  obtain ⟨-, hfin⟩ := StacksDraft.Perfect.free_finite_homology_of_projective _
    (isPerfect_affineDeRhamModel f) hH n
  let N := (moduleSpecΓFunctor (R := A)).obj (deRhamCohomologySheaf f n)
  have : Module.Finite A N := Module.Finite.equiv (affineDeRhamModelHomologyIso f n).toLinearEquiv
  have := h n
  have : (deRhamCohomologySheaf f n).IsQuasicoherent :=
    isQuasicoherent_homology_derivedDeRhamDirectImage f n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (tilde ((modulesSpecToSheaf.obj (deRhamCohomologySheaf f n)).presheaf.obj (Opposite.op ⊤))) :=
    (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module A N).2
      ((Module.isFiniteLocallyFree_iff_finite_projective A N).2 ⟨inferInstance, inferInstance⟩)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (asIso (deRhamCohomologySheaf f n).fromTildeΓ)

section GeneralBaseChange

variable {S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange in
/-- **Base change for the unbounded `Rπ_*Ω^•_{X/S}`**, for `p` proper and smooth and any cartesian
square `X' = X ×_S S'`: `Lg^*Rπ_*Ω^•_{X/S} ≅ Rπ'_*Ω^•_{X'/S'}` ([Stacks, Tag 0FM0]). -/
def deRhamUnboundedBaseChangeIsoOfIsPullback [IsProper p] [Smooth p] {X' : Scheme.{u}}
    (g' : X' ⟶ X) (p' : X' ⟶ S') (hsq : IsPullback g' p' p g) :
    (derivedPullback g.toLRSHom.toShHom).obj
        (DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded p) ≅
      DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded p' :=
  have := ProperSmoothDeRham.isIso_derivedBaseChangeMap_deRhamComplex hsq
  (derivedPullback g.toLRSHom.toShHom).mapIso
      ((derivedPushforward (inverseImageBaseProjection p)).mapIso
        ((DerivedCategory.quotientCompQhIso _).app _).symm) ≪≫
    @asIso _ _ _ _ _ this ≪≫
    (derivedPushforward (inverseImageBaseProjection p')).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _)

end GeneralBaseChange

section BaseChange

variable {B : CommRingCat.{u}} (φ : A ⟶ B)

/-- **Base change for the unbounded `Rπ_*Ω^•_{X/A}`** along `Spec B ⟶ Spec A`, for `f` proper and
smooth and any cartesian square: [Stacks, Tag 0FM0]. -/
def affineDeRhamUnboundedBaseChangeIsoOfIsPullback [IsProper f] [Smooth f] {X' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Spec B) (hsq : IsPullback g' f' f (Spec.map φ)) :
    (StandardModel.specDerivedPullback φ).obj
        (DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded f) ≅
      DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded f' :=
  deRhamUnboundedBaseChangeIsoOfIsPullback f (Spec.map φ) g' f' hsq

/-- **Base change for the unbounded `Rπ_*Ω^•_{X/A}`** along `Spec B ⟶ Spec A`, for `f` proper and
smooth: [Stacks, Tag 0FM0] at the cartesian square of `pullback f (Spec.map φ)`. -/
def affineDeRhamUnboundedBaseChangeIso [IsProper f] [Smooth f] :
    (StandardModel.specDerivedPullback φ).obj
        (DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded f) ≅
      DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded
        (pullback.snd f (Spec.map φ)) :=
  affineDeRhamUnboundedBaseChangeIsoOfIsPullback f φ _ _ (IsPullback.of_hasPullback f (Spec.map φ))

/-- **Base change for the model along any cartesian square**, for `f` proper and smooth: if
`X' = X ×_{Spec A} Spec B` then `RΓ(X', Ω^•_{X'/B}) ≅ RΓ(X, Ω^•_{X/A}) ⊗ᴸ_A B`. This is
[Stacks, Tag 0FM0] read through the affine comparison square of [Stacks, Tag 08DW] and the full
faithfulness of derived sheafification. -/
def affineDeRhamModelBaseChangeIsoOfIsPullback [IsProper f] [Smooth f] {X' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Spec B) [QuasiCompact f'] [QuasiSeparated f']
    (hsq : IsPullback g' f' f (Spec.map φ)) :
    affineDeRhamModel f' ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ.hom).functor.obj (affineDeRhamModel f) :=
  (StandardModel.mapDerivedCategoryFullyFaithful B).preimageIso
    (affineDeRhamModelTildeUnboundedIso f' ≪≫
      (affineDeRhamUnboundedBaseChangeIsoOfIsPullback f φ g' f' hsq).symm ≪≫
      (StandardModel.specDerivedPullback φ).mapIso (affineDeRhamModelTildeUnboundedIso f).symm ≪≫
      (StandardModel.affinePullbackComparison A B φ).app (affineDeRhamModel f))

/-- **Base change for the model**, for `f` proper and smooth: the model of the base change
`X ×_{Spec A} Spec B ⟶ Spec B` is the derived base change of the model,
`RΓ(X_B, Ω^•_{X_B/B}) ≅ RΓ(X, Ω^•_{X/A}) ⊗ᴸ_A B`. -/
def affineDeRhamModelBaseChangeIso [IsProper f] [Smooth f] :
    affineDeRhamModel (pullback.snd f (Spec.map φ)) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ.hom).functor.obj (affineDeRhamModel f) :=
  affineDeRhamModelBaseChangeIsoOfIsPullback f φ _ _ (IsPullback.of_hasPullback f (Spec.map φ))

end BaseChange

end Stacks.DeRhamSmooth

end
