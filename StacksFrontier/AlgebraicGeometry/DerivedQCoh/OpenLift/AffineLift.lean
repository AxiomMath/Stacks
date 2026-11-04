module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.SupportedLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectLift
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel

/-!
# Tags 08EH and 08EI on an arbitrary affine scheme

Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. For `E` perfect and `E'` in
`D_QCoh(𝒪_X)`, every morphism `E|_U ⟶ E'|_U` lifts, up to a perfect modification of `E` that is
an isomorphism over `U`, to a morphism over `X`; and for every perfect object `F` of `D(𝒪_U)` the
object `F ⊕ F[1]` is the restriction of a perfect complex on `X`. Both are deduced from the case
`X = Spec A` through the isomorphism `X ≅ Spec Γ(X, 𝒪_X)`.

## Main results

* `Stacks.DerivedQCoh.exists_isPerfect_lift_of_structureSheaf_of_isAffine`: the lifting
  statement for `E = 𝒪_X`.
* `Stacks.DerivedQCoh.isQuasicoherent_homology_derivedSheafHom_of_isAffine`: `R𝓗om(E, E')` has
  quasi-coherent cohomology for `E` perfect and `E'` in `D_QCoh(𝒪_X)`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_derivedTensor_lift_of_isAffine`: the lifting
  statement for a perfect `E`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_restrict_iso_biprod_shift_of_isAffine`:
  `F ⊕ F[1]` is the restriction of a perfect complex on `X`.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Functor

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']

/-- Let `Φ : C ⥤ C'` and `Θ : D ⥤ D'` be fully faithful, `Φ` essentially surjective, with
`R ⋙ Θ ≅ Φ ⋙ R'`. If every morphism `R' O' ⟶ R' (Φ H)` is, after precomposition with `R' b'` for
a suitable `b' : I' ⟶ O'`, the image of a morphism `I' ⟶ Φ H`, then the same holds for
`R O ⟶ R H` for any `O` with `Φ O ≅ O'`. -/
theorem exists_map_comp_eq_map_of_equivalence (Φ : C ⥤ C') [Φ.Full] [Φ.Faithful] [Φ.EssSurj]
    (R : C ⥤ D) (R' : C' ⥤ D') (Θ : D ⥤ D') [Θ.Full] [Θ.Faithful] (κ : R ⋙ Θ ≅ Φ ⋙ R')
    (O : C) (O' : C') (ω : Φ.obj O ≅ O') (P : C → Prop) (P' : C' → Prop)
    (hP : ∀ I, P' (Φ.obj I) → P I) (hP' : ∀ {I J : C'}, (I ≅ J) → P' I → P' J) (H : C)
    (hlift : ∀ a' : R'.obj O' ⟶ R'.obj (Φ.obj H), ∃ (I' : C') (b' : I' ⟶ O')
      (c' : I' ⟶ Φ.obj H), P' I' ∧ IsIso (R'.map b') ∧ R'.map b' ≫ a' = R'.map c')
    (a : R.obj O ⟶ R.obj H) :
    ∃ (I : C) (b : I ⟶ O) (c : I ⟶ H), P I ∧ IsIso (R.map b) ∧ R.map b ≫ a = R.map c := by
  have hΘ : ∀ {X Y : C} (g : X ⟶ Y),
      Θ.map (R.map g) = κ.hom.app X ≫ R'.map (Φ.map g) ≫ κ.inv.app Y := fun g => by
    have h := κ.hom.naturality g
    simp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  obtain ⟨I', b', c', hI', hb', hc'⟩ :=
    hlift (R'.map ω.inv ≫ κ.inv.app O ≫ Θ.map a ≫ κ.hom.app H)
  let e := Φ.objObjPreimageIso I'
  refine ⟨Φ.objPreimage I', Φ.preimage (e.hom ≫ b' ≫ ω.inv), Φ.preimage (e.hom ≫ c'),
    hP _ (hP' e.symm hI'), ?_, ?_⟩
  · have h1 : IsIso (Θ.map (R.map (Φ.preimage (e.hom ≫ b' ≫ ω.inv)))) := by
      rw [hΘ, Functor.map_preimage, Functor.map_comp, Functor.map_comp]
      infer_instance
    exact (FullyFaithful.ofFullyFaithful Θ).isIso_of_isIso_map _
  · apply Θ.map_injective
    rw [Θ.map_comp, hΘ, hΘ, Functor.map_preimage, Functor.map_preimage]
    simp [← hc']

end CategoryTheory.Functor

namespace Stacks.DerivedQCoh

open Stacks.DerivedQCoh.OpenLift
open Stacks.Duality.OpenImmersion (derivedRestrict)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictFunctor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Restriction along an isomorphism of schemes, as an equivalence of derived categories. -/
def derivedRestrictEquivalence {A B : Scheme.{u}} (e : A ≅ B) :
    DerivedCategory A.Modules ≌ DerivedCategory B.Modules :=
  CategoryTheory.Equivalence.mk (derivedRestrict e.inv) (derivedRestrict e.hom)
    (derivedRestrictCompIso e).symm (derivedRestrictCompIso e.symm)

/-- Restriction along a composite of open immersions is the composite of the restrictions. -/
def derivedRestrictComp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) [IsOpenImmersion f]
    [IsOpenImmersion g] : derivedRestrict (f ≫ g) ≅ derivedRestrict g ⋙ derivedRestrict f :=
  mapDerivedCategoryCongr _ _ (Scheme.Modules.restrictFunctorComp f g) ≪≫
    mapDerivedCategoryComp _ _

/-- Restriction along two equal open immersions. -/
def derivedRestrictEq {A B : Scheme.{u}} {f g : A ⟶ B} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : derivedRestrict f ≅ derivedRestrict g :=
  mapDerivedCategoryCongr _ _ (Scheme.Modules.restrictFunctorCongr h)

/-- The structure sheaf in degree zero restricts to the structure sheaf in degree zero. -/
def derivedRestrictStructureSheafIso {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f] :
    (derivedRestrict f).obj ((DerivedCategory.singleFunctor B.Modules 0).obj
        (SheafOfModules.unit B.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor A.Modules 0).obj (SheafOfModules.unit A.ringCatSheaf) :=
  ((Scheme.Modules.restrictFunctor f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor A.Modules 0).mapIso (Scheme.Modules.restrictUnitIso f)

/-- Perfectness is reflected by restriction along an isomorphism of schemes. -/
theorem isPerfect_of_isPerfect_derivedRestrict_iso {A B : Scheme.{u}} (e : A ≅ B)
    (I : DerivedCategory A.Modules)
    (hI : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := B.toRingedSpace)
      ((derivedRestrict e.inv).obj I)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := A.toRingedSpace) I :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((derivedRestrictCompIso e).app I) (isPerfect_derivedRestrict_of_isIso e.hom _ hI)

/-- Let `U ⊆ Spec A` be a quasi-compact open and `H` an object of `D_QCoh(𝒪_{Spec A})`. Every
morphism `𝒪_U ⟶ H|_U` is `c|_U ∘ (b|_U)⁻¹` for a perfect object `I` and morphisms `b : I ⟶ 𝒪`,
`c : I ⟶ H` with `b|_U` invertible. -/
theorem exists_isPerfect_lift_of_structureSheaf_spec {A : CommRingCat.{u}} (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (H : DerivedCategory (Spec A).Modules)
    (hH : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec A).Modules i).obj H).IsQuasicoherent)
    (a : (derivedRestrict U.ι).obj ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj
        (SheafOfModules.unit (Spec A).ringCatSheaf)) ⟶ (derivedRestrict U.ι).obj H) :
    ∃ (I : DerivedCategory (Spec A).Modules)
      (b : I ⟶ (DerivedCategory.singleFunctor (Spec A).Modules 0).obj
        (SheafOfModules.unit (Spec A).ringCatSheaf))
      (c : I ⟶ H),
        Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := (Spec A).toRingedSpace) I ∧
        IsIso ((derivedRestrict U.ι).map b) ∧
        (derivedRestrict U.ι).map b ≫ a = (derivedRestrict U.ι).map c := by
  let ψ := derivedRestrictionIsoDerivedRestrictModules U ≪≫
    AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor (Spec A) U
  obtain ⟨I, hI, β, γ, hβ, hγ⟩ := exists_isPerfect_lift_of_structureSheaf U hU H hH
    (ψ.hom.app _ ≫ a ≫ ψ.inv.app _)
  exact ⟨I, β, γ, hI, (NatIso.isIso_map_iff ψ β).mp hβ,
    Functor.map_comp_eq_map_of_iso _ _ ψ β a γ (by simpa only [Category.assoc] using hγ)⟩

/-- Let `X` be an affine scheme, `U ⊆ X` a quasi-compact open and `H` an object of
`D_QCoh(𝒪_X)`. Every morphism `𝒪_U ⟶ H|_U` is `c|_U ∘ (b|_U)⁻¹` for a perfect object `I` and
morphisms `b : I ⟶ 𝒪_X`, `c : I ⟶ H` with `b|_U` invertible. -/
theorem exists_isPerfect_lift_of_structureSheaf_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (H : DerivedCategory X.Modules)
    (hH : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj H).IsQuasicoherent)
    (a : (derivedRestrict U.ι).obj ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) ⟶ (derivedRestrict U.ι).obj H) :
    ∃ (I : DerivedCategory X.Modules)
      (b : I ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
      (c : I ⟶ H),
        Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) I ∧
        IsIso ((derivedRestrict U.ι).map b) ∧
        (derivedRestrict U.ι).map b ≫ a = (derivedRestrict U.ι).map c := by
  let e := X.isoSpec
  let Φ := derivedRestrict e.inv
  have : Φ.IsEquivalence := (derivedRestrictEquivalence e).isEquivalence_functor
  let U' := e.hom ''ᵁ U
  let j := e.hom.isoImage U
  have hj : U'.ι ≫ e.inv = j.inv ≫ U.ι := by
    rw [← cancel_epi j.hom, Scheme.Hom.isoImage_hom_ι_assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  let Θ := derivedRestrict j.inv
  have : Θ.IsEquivalence := (derivedRestrictEquivalence j).isEquivalence_functor
  let κ : derivedRestrict U.ι ⋙ Θ ≅ Φ ⋙ derivedRestrict U'.ι :=
    (derivedRestrictComp j.inv U.ι).symm ≪≫ derivedRestrictEq hj.symm ≪≫
      derivedRestrictComp U'.ι e.inv
  have hU' : IsCompact (U' : Set (Spec Γ(X, ⊤))) := by
    show IsCompact (e.hom.base '' (U : Set X))
    exact hU.image e.hom.base.hom.continuous
  exact Functor.exists_map_comp_eq_map_of_equivalence Φ (derivedRestrict U.ι)
    (derivedRestrict U'.ι) Θ κ _ _ (derivedRestrictStructureSheafIso e.inv)
    (fun I => Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) I)
    (fun I => Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := (Spec Γ(X, ⊤)).toRingedSpace) I)
    (isPerfect_of_isPerfect_derivedRestrict_iso e)
    (fun i hI => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} i hI) H
    (exists_isPerfect_lift_of_structureSheaf_spec U' hU' (Φ.obj H)
      (fun i => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory e.inv hH i)) a

/-- Quasi-coherence of the `i`-th cohomology transports along an isomorphism in the derived
category. -/
private theorem isQuasicoherent_homology_of_iso {X : Scheme.{u}} {A B : DerivedCategory X.Modules}
    (e : B ≅ A) {i : ℤ}
    (h : ((DerivedCategory.homologyFunctor X.Modules i).obj B).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso e) h

/-- Quasi-coherence of the cohomology is reflected by restriction along an isomorphism of
schemes. -/
theorem isQuasicoherent_homology_of_derivedRestrict_iso {A B : Scheme.{u}} (e : A ≅ B)
    (H : DerivedCategory A.Modules)
    (hH : ∀ i : ℤ, ((DerivedCategory.homologyFunctor B.Modules i).obj
      ((derivedRestrict e.inv).obj H)).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor A.Modules i).obj H).IsQuasicoherent :=
  isQuasicoherent_homology_of_iso ((derivedRestrictCompIso e).app H)
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory e.hom hH i)

/-- On an affine scheme, the derived internal Hom `R𝓗om(E, E')` out of a perfect object `E` into
an object `E'` with quasi-coherent cohomology has quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_derivedSheafHom_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (E E' : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E)
    (hE' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E').IsQuasicoherent)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (Opposite.op E)).obj
        E')).IsQuasicoherent := by
  let e := X.isoSpec
  refine isQuasicoherent_homology_of_derivedRestrict_iso e _ (fun i => ?_) n
  refine isQuasicoherent_homology_of_iso
    (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso e.inv E E').symm ?_
  exact Stacks.DerivedQCoh.OpenLift.isQuasicoherent_homology_derivedSheafHom_of_isPerfect
    Γ(X, ⊤) _ _ (isPerfect_derivedRestrict_of_isIso e.inv E hE)
    (fun j => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory e.inv hE' j) i

end Stacks.DerivedQCoh

namespace Stacks.DerivedQCoh.OpenLift

open CategoryTheory.MonoidalCategory Stacks.SheafOfModules Stacks.DerivedQCoh
open Stacks.DerivedTensor.ExtensionByZero (restriction)
open Stacks.Duality.OpenImmersion (derivedRestrict)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. Let `E, E'` be objects of
`D_QCoh(𝒪_X)` with `E` perfect. For every morphism `α : E|_U ⟶ E'|_U` there are a perfect object
`I` of `D(𝒪_X)`, a morphism `b : I ⟶ 𝒪_X` whose restriction to `U` is an isomorphism, and a
morphism `γ : E ⊗^L I ⟶ E'`, such that, writing `β : E ⊗^L I ⟶ E ⊗^L 𝒪_X ≅ E` for the morphism
induced by `b`, the object `E₁ = E ⊗^L I` is perfect, `β|_U` is an isomorphism and
`α = γ|_U ∘ (β|_U)⁻¹`. -/
@[stacks 08EH]
theorem exists_isPerfect_derivedTensor_lift_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (E E' : DerivedCategory (SheafOfModules X.ringCatSheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E)
    (hE' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E').IsQuasicoherent)
    (α : (derivedRestrict U.ι).obj E ⟶ (derivedRestrict U.ι).obj E') :
    letI := derivedMonoidalStructure X.sheaf
    ∃ (I : DerivedCategory (SheafOfModules X.ringCatSheaf))
      (b : I ⟶ 𝟙_ (DerivedCategory (SheafOfModules X.ringCatSheaf))) (γ : E ⊗ I ⟶ E'),
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) I ∧
      IsIso ((derivedRestrict U.ι).map b) ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)
        (E ⊗ I : DerivedCategory (SheafOfModules X.ringCatSheaf)) ∧
      IsIso ((derivedRestrict U.ι).map (E ◁ b ≫ (ρ_ E).hom)) ∧
      (derivedRestrict U.ι).map (E ◁ b ≫ (ρ_ E).hom) ≫ α = (derivedRestrict U.ι).map γ := by
  let := derivedMonoidalStructure X.sheaf
  let := derivedSymmetricStructure X.sheaf
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal ((ringedSite X.sheaf).O.over U)
  let := Stacks.DerivedTensor.ExtensionByZero.additive_restriction (ringedSite X.sheaf) U
  let := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteLimits_restriction
    (ringedSite X.sheaf) U
  let := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteColimits_restriction
    (ringedSite X.sheaf) U
  let := sliceRestrictionMonoidal X.sheaf U
  have hEs : (ringedSite X.sheaf).IsPerfect E :=
    Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect _ E hE
  let := exactPairingDerivedDual X.sheaf E hEs
  let R := derivedRestrict U.ι
  let F := 𝟭 (DerivedCategory (SheafOfModules X.ringCatSheaf)) ⋙
    (restriction (ringedSite X.sheaf) U).mapDerivedCategory
  let Φ := ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory
  let ri : F ⋙ Φ ≅ R := derivedOverFunctorEquiv U
  have hΦ : Φ.IsEquivalence := inferInstance
  let H : DerivedCategory (SheafOfModules X.ringCatSheaf) := E' ⊗ derivedDual X.sheaf E
  have hH : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj H).IsQuasicoherent := by
    have hiso := isIso_derivedTensorDualToSheafHom_of_isPerfectSpace X.toRingedSpace E E' hE
    intro i
    exact isQuasicoherent_homology_of_iso (asIso (derivedTensorDualToSheafHom X.sheaf E E')).symm
      (isQuasicoherent_homology_derivedSheafHom_of_isAffine X E E' hE hE' i)
  obtain ⟨I, b, γ₀, ⟨hI, hb⟩, hγ₀⟩ := exists_map_whiskerRight_leftUnitor_comp_eq_map F E
    (derivedDual X.sheaf E) E'
    (fun I b => Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace) I ∧ IsIso (R.map b))
    (Φ.preimage (ri.hom.app E ≫ α ≫ ri.inv.app E')) (fun a => by
      obtain ⟨I, β, c, hI, hβ, hc⟩ := exists_isPerfect_lift_of_structureSheaf_of_isAffine X U hU
        H hH (ri.inv.app (𝟙_ _) ≫ Φ.map a ≫ ri.hom.app H)
      exact ⟨I, β, c, ⟨hI, hβ⟩, Functor.map_comp_eq_map_of_natIso F Φ hΦ.faithful R ri β a c hc⟩)
  have hβ : E ◁ b ≫ (ρ_ E).hom = (β_ E I).hom ≫ b ▷ E ≫ (λ_ E).hom := by
    rw [← braiding_leftUnitor, BraidedCategory.braiding_naturality_right_assoc]
  have hFb : IsIso (F.map b) := Functor.isIso_map_of_natIso F Φ hΦ.full hΦ.faithful R ri b hb
  have hFβ : IsIso (F.map (E ◁ b ≫ (ρ_ E).hom)) := by
    rw [Functor.map_comp, Functor.Monoidal.map_whiskerLeft]
    infer_instance
  have hRβ : IsIso (R.map (E ◁ b ≫ (ρ_ E).hom)) := Functor.isIso_map_of_natIso' F Φ R ri _ hFβ
  refine ⟨I, b, (β_ E I).hom ≫ γ₀, hI, hb,
    AlgebraicGeometry.RingedSpace.isPerfect_derivedTensor (X := X.toRingedSpace) E I hE hI,
    hRβ, ?_⟩
  refine Functor.map_comp_eq_map_of_natIso' F Φ hΦ.full R ri _ α _ ?_
  refine (congrArg (fun t => F.map t ≫ Φ.preimage (ri.hom.app E ≫ α ≫ ri.inv.app E')) hβ).trans ?_
  refine ((congrArg (· ≫ Φ.preimage (ri.hom.app E ≫ α ≫ ri.inv.app E'))
    (F.map_comp _ _)).trans (Category.assoc _ _ _)).trans ?_
  exact (congrArg (fun t => F.map (β_ E I).hom ≫ t) hγ₀).trans (F.map_comp _ _).symm

open CategoryTheory.Pretriangulated in
/-- Let `X` be an affine scheme, `U ⊆ X` a quasi-compact open and `E` a perfect object of
`D(𝒪_X)`. For every decomposition `b : A ⊞ B ≅ E|_U` there are a perfect object `E₁ ≅ E ⊗^L I`
of `D(𝒪_X)`, a morphism `γ : E₁ ⟶ E` and an identification `a : A ⊞ B ≅ E₁|_U` in which `γ|_U`
is the partial identity `diag(𝟙_A, 0)`. -/
theorem exists_isPerfect_derivedTensor_restrict_eq_biprod_map_id_zero_of_isAffine
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (E : DerivedCategory (SheafOfModules X.ringCatSheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E)
    (A' B : DerivedCategory U.toScheme.Modules)
    (b : A' ⊞ B ≅ (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) :
    ∃ (E₁ : DerivedCategory (SheafOfModules X.ringCatSheaf)) (γ : E₁ ⟶ E)
      (a : A' ⊞ B ≅
        (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E₁),
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E₁ ∧
      (∃ I : DerivedCategory (SheafOfModules X.ringCatSheaf),
        Nonempty (E₁ ≅ ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj E).obj I)) ∧
      a.hom ≫ (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).map γ =
        biprod.map (𝟙 A') (0 : B ⟶ B) ≫ b.hom := by
  let R' := AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U
  let ψ := (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U).symm
  let α' := b.inv ≫ biprod.map (𝟙 A') (0 : B ⟶ B) ≫ b.hom
  suffices key : ∀ (E₁ : DerivedCategory (SheafOfModules X.ringCatSheaf))
      (_ : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E₁)
      (_ : ∃ I : DerivedCategory (SheafOfModules X.ringCatSheaf),
        Nonempty (E₁ ≅ ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj E).obj I))
      (β γ : E₁ ⟶ E), IsIso ((derivedRestrict U.ι).map β) →
      (derivedRestrict U.ι).map β ≫ ψ.hom.app E ≫ α' ≫ ψ.inv.app E =
        (derivedRestrict U.ι).map γ →
      ∃ (E₁ : DerivedCategory (SheafOfModules X.ringCatSheaf)) (γ : E₁ ⟶ E)
        (a : A' ⊞ B ≅ R'.obj E₁),
        Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E₁ ∧
        (∃ I : DerivedCategory (SheafOfModules X.ringCatSheaf),
          Nonempty (E₁ ≅ ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj E).obj I)) ∧
        a.hom ≫ R'.map γ = biprod.map (𝟙 A') (0 : B ⟶ B) ≫ b.hom by
    let := Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf
    obtain ⟨I, b₀, γ, -, -, hEI, hβ, hγ⟩ :=
      exists_isPerfect_derivedTensor_lift_of_isAffine X U hU E E hE
        (fun i => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE i)
        (ψ.hom.app E ≫ α' ≫ ψ.inv.app E)
    exact key _ hEI ⟨I, ⟨Iso.refl _⟩⟩ _ γ hβ hγ
  intro E₁ hE₁ hE₁I β γ hβ hγ
  have hβ' : IsIso (R'.map β) := (NatIso.isIso_map_iff ψ β).mp hβ
  have hγ' : R'.map β ≫ α' = R'.map γ := Functor.map_comp_eq_map_of_iso _ R' ψ β α' γ hγ
  refine ⟨E₁, γ, b ≪≫ (asIso (R'.map β)).symm, hE₁, hE₁I, ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (b.hom ≫ ·)
    ((congrArg ((asIso (R'.map β)).inv ≫ ·) hγ'.symm).trans
      ((asIso (R'.map β)).inv_hom_id_assoc α'))).trans (Iso.hom_inv_id_assoc b _))

/-- Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. For every perfect object `F` of
`D(𝒪_U)` the object `F ⊕ F[1]` is the restriction of a perfect object of `D(𝒪_X)`: there is a
perfect complex `P` of `𝒪_X`-modules whose degreewise restriction to `U` represents `F ⊕ F[1]`. -/
@[stacks 08EI]
theorem exists_isPerfectComplex_restrict_iso_biprod_shift_of_isAffine (X : Scheme.{u})
    [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : DerivedCategory U.toScheme.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) F) :
    ∃ P : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ,
      Stacks.Cohomology.PerfectComplexes.IsPerfectComplex P ∧
      Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj
        (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
          U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  exists_isPerfectComplex_restrict_iso_biprod_shift_of_lift X U hU
    (fun E hE A' B b => by
      obtain ⟨E₁, γ, a, hE₁, -, h⟩ :=
        exists_isPerfect_derivedTensor_restrict_eq_biprod_map_id_zero_of_isAffine X U hU E hE A' B b
      exact ⟨E₁, γ, a, hE₁, h⟩) F hF

end Stacks.DerivedQCoh.OpenLift

end
