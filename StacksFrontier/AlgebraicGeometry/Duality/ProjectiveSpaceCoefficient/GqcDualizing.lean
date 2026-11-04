module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ComparisonIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Picard.Group.TensorConstraints
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# `(𝒪(-n-1) ⊗ p^*ω~)[n]` is a dualizing complex on `ℙⁿ_R`

Let `R` be a Noetherian ring, `ω` a dualizing module over `R`, and `p : ℙⁿ_R ⟶ Spec R`. Then
`(𝒪(-n-1) ⊗ p^*ω~)[n]` is a dualizing complex on `ℙⁿ_R` ([Stacks, Tag 0A87]).

The proof is chart by chart, through [Stacks, Tag 0A86]. Every point of `ℙⁿ_R` has an affine
open neighbourhood `W` on which `𝒪(-n-1)` is trivial. Over such a `W` the sheaf
`𝒪(-n-1) ⊗ p^*ω~` is `p^*ω~`, and since `W ⟶ Spec R` is, read on `W ≅ Spec Γ(W)`, the spectrum
of a smooth ring map `ψ : R ⟶ Γ(W)`, the sheaf `p^*ω~` restricted to `W` is the sheaf associated
to `ω ⊗_R Γ(W)` ([Stacks, Tag 01I9]). A smooth ring map is a local complete intersection, so
derived extension of scalars along `ψ` carries the dualizing complex `ω[k]` of `R` to a
dualizing complex of `Γ(W)` ([Stacks, Tag 0BZL] with [Stacks, Tag 0E4B]); as `ψ` is flat that
extension is `(ω ⊗_R Γ(W))[k]`, and a shift of a dualizing complex is dualizing.

## Main results

* `Stacks.Duality.ProjCoeff.isDualizingComplex_Gqc`: `(𝒪(-n-1) ⊗ p^*ω~)[n]` is a dualizing
  complex on `ℙⁿ_R`.

## Implementation notes

`(𝒪(-n-1) ⊗ p^*ω~)[n]` lives in the locally small model of `D(𝒪_{ℙⁿ_R})`
(`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`), where the rest of
`StacksFrontier/AlgebraicGeometry/Duality/ProjectiveSpaceCoefficient/` works.
`Stacks.Duality.HasDualizingModelOn` reads it after restriction to an affine open, in the standard
model of `D(𝒪_W)`; restriction commutes with shifts and with placing a module in degree `0`
whatever the two models, so only the module `𝒪(-n-1) ⊗ p^*ω~` itself has to be restricted.

## References

* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

/-! ### The ring-level input -/

section RingLevel

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Shifted extension of a dualizing module along a smooth ring map.** Let `ψ : R ⟶ B` be a
smooth map of Noetherian rings and `ω` an `R`-module with `ω[k]` dualizing. For every `m`, the
complex `(ω ⊗_R B)[0]⟦m⟧` is isomorphic to a dualizing complex over `B`. -/
theorem exists_isDualizingComplex_iso_extendScalars_shift {R B : Type u} [CommRing R]
    [CommRing B] [IsNoetherianRing R] [IsNoetherianRing B] (ψ : R →+* B) (hψ : ψ.Smooth)
    (ω : ModuleCat.{u} R) (k : ℤ)
    (hk : Dualizing.IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} R) k).obj ω))
    (m : ℤ) :
    ∃ M : DerivedCategory (ModuleCat.{u} B), Dualizing.IsDualizingComplex M ∧
      Nonempty (((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} ψ).obj ω))⟦m⟧ ≅ M) := by
  let : Algebra R B := ψ.toAlgebra
  have : Algebra.Smooth R B := hψ.toAlgebra
  have hsyn := (RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection ψ).mp
    (Algebra.Smooth.syntomic R B)
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation ψ hsyn.2.1
  have hD := Dualizing.isDualizingComplex_derivedExtensionScalars_of_upperShriek ψ p _ hk
    (Dualizing.isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection p hsyn.2)
    (Dualizing.nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci
      ψ p hsyn.2 _)
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ψ) :=
    extendScalars_preservesFiniteLimits_of_flat' ψ hsyn.1
  let F := ModuleCat.extendScalars.{u, u, u} ψ
  let D :=
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} ψ).functor
  let e₁ : D.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) k).obj ω) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) k).obj (F.obj ω) :=
    (Stacks.LocalCohomology.derivedExtensionScalarsIsoMapDerivedCategory.{u, u, u} ψ).app _ ≪≫
      (F.mapDerivedCategorySingleFunctor k).app ω
  let e₂ : ((DerivedCategory.singleFunctor (ModuleCat.{u} B) k).obj (F.obj ω))⟦k⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (F.obj ω) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso k 0 k (by simp)).app (F.obj ω)
  refine ⟨((D.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) k).obj ω))⟦k⟧)⟦m⟧,
    Dualizing.isDualizingComplex_shift _ (Dualizing.isDualizingComplex_shift _ hD k) m, ⟨?_⟩⟩
  exact (shiftFunctor _ m).mapIso (e₂.symm ≪≫ (shiftFunctor _ k).mapIso e₁.symm)

end RingLevel

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The twisting sheaves are trivial on small affine opens -/

/-- Every point of `ℙⁿ_R` has an affine open neighbourhood on which `𝒪(d)` is trivial. -/
theorem exists_isAffineOpen_restrict_O_iso_unit (d : ℤ) (x : P R n) :
    ∃ W : (P R n).Opens, IsAffineOpen W ∧ x ∈ W ∧
      Nonempty ((Scheme.Modules.restrictFunctor W.ι).obj (O R n d) ≅
        SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  obtain ⟨V, hxV, ⟨eV⟩⟩ :=
    Stacks.AlgebraicGeometry.TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
      (polyGrading R n) (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading R n) d x
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    (P R n).isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  refine ⟨W, hW, hxW, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorCongr ((P R n).homOfLE_ι hle).symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ((P R n).homOfLE hle) V.ι).app _) ≪≫
    (Scheme.Modules.restrictFunctor ((P R n).homOfLE hle)).mapIso eV ≪≫
    Scheme.Modules.restrictUnitIso _

/-! ### `𝒪(d) ⊗ p^*M~` restricted to a chart -/

/-- Restricting `𝒪(d) ⊗ p^*M~` to an open on which `𝒪(d)` is trivial gives the restriction of
`p^*M~`. -/
def restrictTIso (d : ℤ) (M : ModuleCat.{u} R) (W : (P R n).Opens)
    (e : (Scheme.Modules.restrictFunctor W.ι).obj (O R n d) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((T R n d).obj M) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj
        ((Scheme.Modules.pullback (projToSpecCoeff R n)).obj ((tilde.functor (.of R)).obj M)) :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso W.ι (O R n d)
      ((Scheme.Modules.pullback (projToSpecCoeff R n)).obj ((tilde.functor (.of R)).obj M)) ≪≫
    Stacks.SheafOfModules.tensorSheafMapIso _ _
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm ≪≫ e)
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm ≪≫
    Stacks.SheafOfModules.tensorSheafLeftUnitor _ _ _

/-! ### `p^*M~` restricted to an affine open -/

/-- **`W ⟶ Spec R` is the spectrum of a smooth ring map.** For an affine open `W` of `ℙⁿ_R`, the
composite `W ⟶ ℙⁿ_R ⟶ Spec R`, read on `W ≅ Spec Γ(W)`, is `Spec ψ` for a smooth ring map
`ψ : R ⟶ Γ(W)`. -/
theorem exists_smooth_specMap_eq (W : (P R n).Opens) (hW : IsAffineOpen W) :
    ∃ ψ : CommRingCat.of R ⟶ Γ(P R n, W), ψ.hom.Smooth ∧
      W.ι ≫ projToSpecCoeff R n = hW.isoSpec.hom ≫ Spec.map ψ := by
  have : Smooth (projToSpecCoeff R n) := smooth_projToSpecCoeff R n
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hW.isoSpec.inv ≫ W.ι ≫ projToSpecCoeff R n)
  refine ⟨ψ, ?_, ?_⟩
  · have : Smooth (Spec.map ψ) := by
      rw [hψ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · rw [hψ, Iso.hom_inv_id_assoc]

/-- **`p^*M~` restricted to an affine open `W` is associated to `M ⊗_R Γ(W)`**, given the ring
map `ψ : R ⟶ Γ(W)` of which `W ⟶ Spec R` is the spectrum. This is [Stacks, Tag 01I9] read
through `W ≅ Spec Γ(W)`. -/
def restrictPullbackTildeIso (M : ModuleCat.{u} R) (W : (P R n).Opens) (hW : IsAffineOpen W)
    (ψ : CommRingCat.of R ⟶ Γ(P R n, W))
    (h : W.ι ≫ projToSpecCoeff R n = hW.isoSpec.hom ≫ Spec.map ψ) :
    (Scheme.Modules.restrictFunctor W.ι).obj
        ((Scheme.Modules.pullback (projToSpecCoeff R n)).obj ((tilde.functor (.of R)).obj M)) ≅
      (Scheme.Modules.restrictFunctor hW.isoSpec.hom).obj
        ((tilde.functor Γ(P R n, W)).obj ((ModuleCat.extendScalars.{u, u, u} ψ.hom).obj M)) :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp W.ι (projToSpecCoeff R n)).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫
    ((Scheme.Modules.pullbackComp hW.isoSpec.hom (Spec.map ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback hW.isoSpec.hom).mapIso
      ((AlgebraicGeometry.pullbackTildeIso (.of R) Γ(P R n, W) ψ).app M) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback hW.isoSpec.hom).app _).symm

/-! ### The dualizing model on a chart -/

/-- **`(𝒪(-n-1) ⊗ p^*ω~)[n]` carries a dualizing model on every affine open on which `𝒪(-n-1)` is
trivial.** -/
theorem hasDualizingModelOn_Gqc [IsNoetherianRing R] [IsLocallyNoetherian (P R n)]
    (ω : ModuleCat.{u} R) (hω : Stacks.Duality.IsDualizingRingModule R ω)
    (W : (P R n).Opens) (hW : IsAffineOpen W)
    (eO : (Scheme.Modules.restrictFunctor W.ι).obj (O R n (-(n : ℤ) - 1)) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf) :
    Stacks.Duality.HasDualizingModelOn (Gqc R n ω).obj W hW := by
  obtain ⟨-, k, hk⟩ := hω
  let : IsNoetherianRing Γ(P R n, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let := HasDerivedCategory.standard W.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(P R n, W))
  obtain ⟨ψ, hψ, hsq⟩ := exists_smooth_specMap_eq R n W hW
  obtain ⟨M, hM, ⟨eM⟩⟩ :=
    exists_isDualizingComplex_iso_extendScalars_shift ψ.hom hψ ω k hk (n : ℤ)
  refine ⟨M, hM, ⟨?_⟩⟩
  let Fr := Scheme.Modules.restrictFunctor W.ι
  let G := tilde.functor Γ(P R n, W) ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.hom
  let N := (ModuleCat.extendScalars.{u, u, u} ψ.hom).obj ω
  let eS : Fr.obj ((T R n (-(n : ℤ) - 1)).obj ω) ≅ G.obj N :=
    restrictTIso R n _ ω W eO ≪≫ restrictPullbackTildeIso R n ω W hW ψ hsq
  exact (Fr.mapDerivedCategory.commShiftIso (n : ℤ)).app (Gsingle R n ω) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso
      ((Fr.mapDerivedCategorySingleFunctor 0).app ((T R n (-(n : ℤ) - 1)).obj ω) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eS ≪≫
        ((G.mapDerivedCategorySingleFunctor 0).app N).symm) ≪≫
    ((G.mapDerivedCategory.commShiftIso (n : ℤ)).app _).symm ≪≫
    G.mapDerivedCategory.mapIso eM

/-! ### The theorem -/

/-- **`(𝒪(-n-1) ⊗ p^*ω~)[n]` is a dualizing complex on `ℙⁿ_R`** for every dualizing module `ω`
over a Noetherian ring `R`. -/
theorem isDualizingComplex_Gqc [IsNoetherianRing R] (ω : ModuleCat.{u} R)
    (hω : Stacks.Duality.IsDualizingRingModule R ω) :
    letI : IsLocallyNoetherian (P R n) := inferInstance
    Stacks.Duality.IsDualizingComplex (Gqc R n ω).obj := by
  choose W hW hxW eW using exists_isAffineOpen_restrict_O_iso_unit R n (-(n : ℤ) - 1)
  refine Stacks.Duality.isDualizingComplex_of_hasDualizingModelOn_cover W hW ?_
    fun x => hasDualizingModelOn_Gqc R n ω hω (W x) (hW x) (eW x).some
  exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩

end Stacks.Duality.ProjCoeff
