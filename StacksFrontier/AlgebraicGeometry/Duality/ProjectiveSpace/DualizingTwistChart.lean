module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulaySchemeOfDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict
public import StacksFrontier.AlgebraicGeometry.TwistPullbackChart.Chart
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# The twisted dualizing module of projective space is a dualizing complex

Let `A` be a Noetherian ring with a dualizing module `ω_A`, let `p : ℙⁿ_A ⟶ Spec A` be projective
`n`-space over `A`, and let `d` be an integer. Then the `𝒪_{ℙⁿ_A}`-module
`p^*(ω̃_A) ⊗ 𝒪(d)` placed in any single degree is a dualizing complex on `ℙⁿ_A`
([Stacks, Tag 0A87]). For `d = -n-1` and the degree `-n` this is the statement that
`p^*ω_A(-n-1)[n]` is a dualizing complex, which is what the projective route to
[Stacks, Tag 0AA3] needs once [Stacks, Tag 0A9W] identifies `p^!` there.

## The argument

Being a dualizing complex is local ([Stacks, Tag 0A86]), and:

* `ω̃_A`, in any degree, is a dualizing complex on `Spec A`
  (`Stacks.Duality.isDualizingComplex_singleFunctor_tilde`): the single affine open `⊤` of
  `Spec A` carries the dualizing model `ω_A ⊗_A Γ(Spec A, ⊤)`, the extension of scalars along
  the ring isomorphism `A ≅ Γ(Spec A, ⊤)`, which is dualizing by [Stacks, Tag 0A7G].
* `p` is smooth ([Stacks, Tag 0B2P]), hence syntomic, so the derived pullback of a dualizing
  complex along it is dualizing by the ascent half of [Stacks, Tag 0E4N]
  (`Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic`); on each affine chart this is
  [Stacks, Tag 0A7J] for the polynomial ring. `p` is flat, so `Lp^*(ω̃_A[k]) = (p^*ω̃_A)[k]`.
* on each of the `n + 1` standard affine charts `D₊(Tᵢ)` the twist `𝒪(d)` is trivial
  (`Stacks.TwistPullbackChart.degreeOnePullbackTwistIsoUnit`), so `p^*ω̃_A ⊗ 𝒪(d)` and
  `p^*ω̃_A` have isomorphic restrictions there, and two modules whose restrictions to the members
  of an affine open cover agree are dualizing in a given degree together
  (`Stacks.Duality.isDualizingComplex_singleFunctor_of_restrict_iso`).

## Main results

* `Stacks.Duality.isDualizingComplex_singleFunctor_of_restrict_iso` — a module is dualizing in
  degree `k` once it is locally isomorphic, on an affine open cover, to one that is.
* `Stacks.Duality.isDualizingComplex_singleFunctor_tilde` — `ω̃[k]` is dualizing on `Spec R`
  when `ω[k]` is dualizing over `R`.
* `Stacks.Duality.ProjectiveSpace.isDualizingComplex_singleFunctor_pullback_tensor_twistOver` —
  **`(p^*ω̃_A ⊗ 𝒪(d))[k]` is a dualizing complex on `ℙⁿ_A`**, at every model of `D(𝒪_{ℙⁿ_A})`.

## Implementation notes

The tensor product in the statement is `Stacks.SheafOfModules.Tensor.sheafTensor` over
`X.toRingedSpace.sheaf`, the spelling of the derived-to-underived comparison
`Lf^*(H[0]) ⊗ᴸ L[n] ≅ (f^*H ⊗ L)[n]` through which `p^!(ω̃_A)` is computed; it is the same object
as `Stacks.RelativeVeryAmple.tensorModules`, which the proof uses, up to unfolding.

The ring-level and chart-level derived categories are read at `HasDerivedCategory.standard`,
the model sealed inside `Stacks.Duality.HasDualizingModelOn`; the final statement holds at an
arbitrary model of `D(𝒪_{ℙⁿ_A})`, in particular at the locally small model of the twisted inverse
image, by `Stacks.Duality.isDualizingComplex_singleFunctor_model_iff`.

## References

* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7J](https://stacks.math.columbia.edu/tag/0A7J)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
* [Stacks Project, Tag 0E4N](https://stacks.math.columbia.edu/tag/0E4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

/-- An isomorphism `R F ≅ R' G` induces one between the images of `F[-k]` and `G[-k]` under the
derived functors of `R` and `R'`. -/
private def mapDerivedCategorySingleFunctorIso {C₁ C₁' C₂ : Type*} [Category C₁] [Category C₁']
    [Category C₂] [Abelian C₁] [Abelian C₁'] [Abelian C₂] [HasDerivedCategory C₁]
    [HasDerivedCategory C₁'] [HasDerivedCategory C₂] (R : C₁ ⥤ C₂) (R' : C₁' ⥤ C₂)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] [R'.Additive]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R'] (k : ℤ) {F : C₁} {G : C₁'}
    (e : R.obj F ≅ R'.obj G) :
    R.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C₁ k).obj F) ≅
      R'.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C₁' k).obj G) :=
  (R.mapDerivedCategorySingleFunctor k).app F ≪≫ (DerivedCategory.singleFunctor _ k).mapIso e ≪≫
    ((R'.mapDerivedCategorySingleFunctor k).app G).symm

section LocalTransfer

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **A module is dualizing in a degree once it is so locally.** If `F` and `G` have isomorphic
restrictions to the members of an affine open cover of `X`, and `F[-k]` is a dualizing complex,
then so is `G[-k]`: the condition [Stacks, Tag 0A87] reads each affine open through the
restriction functor, which commutes with placing a module in a degree, and by
[Stacks, Tag 0A86] one cover suffices. -/
theorem isDualizingComplex_singleFunctor_of_restrict_iso {F G : X.Modules} (k : ℤ)
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (e : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).obj F ≅
      (Scheme.Modules.restrictFunctor (U i).ι).obj G)
    (hF : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules k).obj F)) :
    IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules k).obj G) := by
  refine isDualizingComplex_of_hasDualizingModelOn_cover U hU hcov fun i => ?_
  let := HasDerivedCategory.standard (U i).toScheme.Modules
  obtain ⟨ω, hω, ⟨a⟩⟩ := hF (U i) (hU i)
  exact ⟨ω, hω, ⟨mapDerivedCategorySingleFunctorIso _ _ k (e i).symm ≪≫ a⟩⟩

end LocalTransfer

section Affine

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- On `Spec R`, the canonical isomorphism of the affine open `⊤` with `Spec Γ(Spec R, ⊤)`,
followed by `Spec` of the ring isomorphism `R ≅ Γ(Spec R, ⊤)`, is the inclusion of `⊤`. -/
theorem isoSpec_hom_specMap_ΓSpecIso_inv :
    (isAffineOpen_top (Spec R)).isoSpec.hom ≫ Spec.map (Scheme.ΓSpecIso R).inv =
      (⊤ : (Spec R).Opens).ι := by
  rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top, ← IsAffineOpen.isoSpec_inv_ι,
    Iso.hom_inv_id_assoc]

/-- **The associated sheaf of a module, restricted to `⊤ ⊆ Spec R`, is the associated sheaf of
its extension to `Γ(Spec R, ⊤)`**, transported along `⊤ ≅ Spec Γ(Spec R, ⊤)`. -/
def restrictTopTildeIso (ω : ModuleCat.{u} R) :
    (Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι).obj ((tilde.functor R).obj ω) ≅
      (tilde.functor Γ(Spec R, ⊤) ⋙ Scheme.Modules.restrictFunctor
        (isAffineOpen_top (Spec R)).isoSpec.hom).obj
          ((ModuleCat.extendScalars (Scheme.ΓSpecIso R).inv.hom).obj ω) :=
  (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (isoSpec_hom_specMap_ΓSpecIso_inv R).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      ((pullbackTildeIso R Γ(Spec R, ⊤) (Scheme.ΓSpecIso R).inv).app ω) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm

/-- **`ω̃[-k]` is a dualizing complex on `Spec R` when `ω[-k]` is one over `R`.** The single
affine open `⊤` carries the dualizing model `(ω ⊗_R Γ(Spec R, ⊤))[-k]`, the extension of scalars
along the ring isomorphism `R ≅ Γ(Spec R, ⊤)`, which is dualizing by [Stacks, Tag 0A7G]
(`Dualizing.isDualizingComplex_of_ringEquiv`); and by [Stacks, Tag 0A86] one affine open cover
suffices. -/
theorem isDualizingComplex_singleFunctor_tilde (ω : ModuleCat.{u} R) (k : ℤ)
    (hω : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) k).obj ω)) :
    IsDualizingComplex
      ((DerivedCategory.singleFunctor (Spec R).Modules k).obj ((tilde.functor R).obj ω)) := by
  let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (e : R →+* Γ(Spec R, ⊤))) :=
    extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.Flat.of_bijective e.bijective)
  refine isDualizingComplex_of_hasDualizingModelOn_cover (ι := PUnit.{1})
    (fun _ => ⊤) (fun _ => isAffineOpen_top _) (by simp) fun _ => ?_
  let : IsNoetherianRing Γ(Spec R, ⊤) := isNoetherianRing_of_ringEquiv R e
  let E := ModuleCat.extendScalars.{u, u, u} (e : R →+* Γ(Spec R, ⊤))
  refine ⟨(DerivedCategory.singleFunctor _ k).obj (E.obj ω),
    ringIsDualizingComplex_of_iso ((E.mapDerivedCategorySingleFunctor k).app ω)
      (Dualizing.isDualizingComplex_of_ringEquiv e _ hω),
    ⟨mapDerivedCategorySingleFunctorIso _ _ k (restrictTopTildeIso R ω)⟩⟩

/-- **A dualizing module is dualizing in every degree.** If `ω[-m]` is a dualizing complex over
`A` for one `m` then `ω[-k]` is one for every `k`, being a shift of it
(`Dualizing.isDualizingComplex_shift`). -/
theorem IsDualizingRingModule.isDualizingComplex_singleFunctor {A : Type u} [CommRing A]
    [IsNoetherianRing A] {ω : ModuleCat.{u} A} (h : IsDualizingRingModule A ω) (k : ℤ) :
    Dualizing.IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) k).obj ω) := by
  obtain ⟨-, m, hm⟩ := h
  exact ringIsDualizingComplex_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (m - k) k m
      (by ring)).app ω) (Dualizing.isDualizingComplex_shift _ hm (m - k))

end Affine

/-- A quasi-coherent module placed in degree `k` has quasi-coherent cohomology sheaves: the module
itself in degree `k` and zero elsewhere. -/
theorem isQuasicoherent_homology_singleFunctor_obj_of_degree {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] (F : X.Modules) (hF : F.IsQuasicoherent) (k i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules k).obj F)).IsQuasicoherent := by
  rcases lt_trichotomy i k with h | h | h
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules k).obj F) k i h)
  · subst h
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules i).app F).symm hF
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules k).obj F) k i h)

end Stacks.Duality

namespace Stacks.Duality.ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.RelativeVeryAmple (tensorModules pullbackTensorModulesIso tensorModulesMapIso)
open AlgebraicGeometry.ProjectiveSpace (standardOpen iSup_standardOpen_eq_top
  isAffineOpen_standardOpen)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Tensoring with a module that is trivial on an open does not change the restriction to
it**: if `L|_U ≅ 𝒪_U` then `(F ⊗ L)|_U ≅ F|_U`. Restriction is pullback along the open
immersion, which commutes with tensor products ([Stacks, Tag 01CD]). -/
def restrictTensorIsoOfRestrictIsoUnit {X : Scheme.{u}} (U : X.Opens) (F L : X.Modules)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor U.ι).obj (tensorModules X F L) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj F :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    pullbackTensorModulesIso U.ι F L ≪≫
    tensorModulesMapIso U.toScheme ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e) ≪≫
    Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor U.toScheme _

variable (n : ℕ) (S : Scheme.{u})

/-- **Every twist `𝒪(d)` of `ℙⁿ_S` is trivial on each standard chart `D₊(Tᵢ)`.** The twist is
pulled back from the integral model, where `𝒪(d)` is trivialized on `D₊(Tᵢ)` by `Tᵢᵈ`
(`Stacks.TwistPullbackChart.degreeOnePullbackTwistIsoUnit`), and the standard chart of `ℙⁿ_S` is
the preimage of `D₊(Tᵢ)`. -/
def twistOverRestrictStandardOpenIso (d : ℤ) (i : Fin (n + 1)) :
    (Scheme.Modules.restrictFunctor (standardOpen n S i).ι).obj (twistOver n S d) ≅
      SheafOfModules.unit (standardOpen n S i).toScheme.ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjTwistMono.restrictPullbackIsoUnit
    (projectiveSpaceOver.toIntegralAtUniverse n S) (standardOpen n S i) _
    (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))
    (projectiveSpaceOver.toIntegralAtUniverse n S ∣_ _) (morphismRestrict_ι _ _)
    (Stacks.TwistPullbackChart.degreeOnePullbackTwistIsoUnit _
      (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one i) d)

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

section Standard

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback AlgebraicGeometry.pullback_additive
attribute [local instance] projectiveSpaceOver_isLocallyNoetherian

/-- **`(p^*ω̃_A)[-k]` is a dualizing complex on `ℙⁿ_A`**, at the standard model, when `ω_A[-k]`
is one over `A`. The structure morphism `p` is smooth, hence syntomic, so this is the ascent
half of [Stacks, Tag 0E4N] applied to `ω̃_A[-k]`; `p` is flat, so `Lp^*` is degreewise
pullback. -/
theorem isDualizingComplex_singleFunctor_pullback_tilde_standard (ωA : ModuleCat.{u} A) (k : ℤ)
    (hω : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) k).obj ωA)) :
    IsDualizingComplex ((DerivedCategory.singleFunctor _ k).obj
      ((Scheme.Modules.pullback (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tilde.functor (.of A)).obj ωA))) := by
  let p := projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)
  exact isDualizingComplex_of_iso
    ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory p).app _ ≪≫
      ((Scheme.Modules.pullback p).mapDerivedCategorySingleFunctor k).app _)
    (isDualizingComplex_derivedPullback_of_syntomic p (syntomic_of_smooth p) _
      (isQuasicoherent_homology_singleFunctor_obj_of_degree _ inferInstance k)
      (isDualizingComplex_singleFunctor_tilde (.of A) ωA k hω))

/-- `(p^*ω̃_A ⊗ 𝒪(d))[-k]` is a dualizing complex on `ℙⁿ_A`, at the standard model. -/
theorem isDualizingComplex_singleFunctor_pullback_tensor_twistOver_standard
    (ωA : ModuleCat.{u} A) (d k : ℤ)
    (hω : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) k).obj ωA)) :
    IsDualizingComplex ((DerivedCategory.singleFunctor _ k).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (projectiveSpaceOver n (Spec (.of A))).toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
          ((tilde.functor (.of A)).obj ωA))).obj
        (twistOver n (Spec (.of A)) d))) :=
  isDualizingComplex_singleFunctor_of_restrict_iso k (standardOpen n (Spec (.of A)))
    (isAffineOpen_standardOpen n (Spec (.of A))) (iSup_standardOpen_eq_top n (Spec (.of A)))
    (fun i => (restrictTensorIsoOfRestrictIsoUnit _ _ _
      (twistOverRestrictStandardOpenIso n (Spec (.of A)) d i)).symm)
    (isDualizingComplex_singleFunctor_pullback_tilde_standard n ωA k hω)

end Standard

attribute [local instance] projectiveSpaceOver_isLocallyNoetherian

/-- **The twisted dualizing module of projective space is a dualizing complex.** Let `A` be a
Noetherian ring with a dualizing module `ω_A` ([Stacks, Tag 0B4R]), let
`p : ℙⁿ_A ⟶ Spec A` be projective `n`-space over `A`, and let `d` and `k` be integers. Then
`p^*(ω̃_A) ⊗ 𝒪(d)`, placed in degree `k`, is a dualizing complex on `ℙⁿ_A`
([Stacks, Tag 0A87]), in every model of `D(𝒪_{ℙⁿ_A})`.

For `d = -n-1` and `k = -n` this says that `p^*ω_A(-n-1)[n]` is a dualizing complex on `ℙⁿ_A`,
the chart computation of the projective route to [Stacks, Tag 0AA3]: on the standard affine chart
`Spec A[t₁, …, tₙ]` the twist is trivial and the module is `ω_A ⊗_A A[t₁, …, tₙ]`, which is
dualizing by [Stacks, Tag 0A7J]. -/
theorem isDualizingComplex_singleFunctor_pullback_tensor_twistOver (ωA : ModuleCat.{u} A)
    (hωA : IsDualizingRingModule A ωA) (d k : ℤ)
    [h : HasDerivedCategory.{w} (projectiveSpaceOver n (Spec (.of A))).Modules] :
    IsDualizingComplex ((DerivedCategory.singleFunctor _ k).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (projectiveSpaceOver n (Spec (.of A))).toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
          ((tilde.functor (.of A)).obj ωA))).obj
        (twistOver n (Spec (.of A)) d))) :=
  (isDualizingComplex_singleFunctor_model_iff (HasDerivedCategory.standard _) h k _).2
    (isDualizingComplex_singleFunctor_pullback_tensor_twistOver_standard n ωA d k
      (IsDualizingRingModule.isDualizingComplex_singleFunctor hωA k))

end Stacks.Duality.ProjectiveSpace

end
