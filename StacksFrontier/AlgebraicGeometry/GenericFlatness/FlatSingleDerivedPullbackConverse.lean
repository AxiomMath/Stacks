module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitStalk
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.Homology.PseudoCoherent.Relative.TowerModule
public import StacksFrontier.RingTheory.Flat.DerivedFlat.NoetherianInduction
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Flatness in degree zero is detected after a surjective derived pullback of finite presentation

Let `f : X ⟶ S` be a surjective morphism of finite presentation and let `M` be an object of
`D_QCoh(𝒪_S)` with `H^i(M) = 0` for `i > 0`. Stacks 0H89 (Longke Tang) says that `M` is isomorphic
to a flat `𝒪_S`-module placed in degree `0` if and only if `Lf^*M` is isomorphic to a flat
`𝒪_X`-module placed in degree `0`. The implication (1) ⇒ (2) holds for any morphism of ringed
spaces and is `AlgebraicGeometry.exists_isFlat_derivedPullback_of_exists_isFlat`; this file proves
the converse and registers the equivalence.

## Main results

In the namespace `Stacks.Cohomology`:

* `FlatSingleDerivedPullbackConverse.exists_affine_model`: over an affine open `U ⊆ S` an object
  of `D_QCoh(𝒪_S)` has a model `ω ∈ D(Γ(S, U))` whose derived base change along the germ map
  `Γ(S, U) → 𝒪_{S,s}` is the derived stalk at `s`, for every `s ∈ U`.
* `FlatSingleDerivedPullbackConverse.exists_isFlat_of_exists_isFlat_derivedPullback`: the
  implication (2) ⇒ (1).

In the namespace `AlgebraicGeometry`:

* `exists_isFlat_iff_exists_isFlat_derivedPullback`: **Stacks 0H89.** For `f` surjective of finite
  presentation, `M` is a flat module in degree zero if and only if `Lf^*M` is.

## The argument

Being a flat module in degree zero is a stalkwise condition (cohomology sheaves vanish and flatness
of a sheaf of modules are both detected on stalks, Stacks 05NE), so it suffices to treat the
derived stalk of `M` at a point `s`. Pick an affine open `U ∋ s`. The derived pullback of `M` to
`Spec Γ(S, U)` has quasi-coherent cohomology, so it is the derived sheafification of an object `ω`
of `D(Γ(S, U))` (Stacks 06Z0); computing stalks on both sides identifies the derived stalk of `M`
at every point `s' ∈ U` with `ω ⊗ᴸ 𝒪_{S,s'}`. Cover `f⁻¹ U` by finitely many affine opens `V_j`
and put `B_j = Γ(X, V_j)`, a finitely presented `Γ(S, U)`-algebra; the maps
`Spec B_j → Spec Γ(S, U)` are jointly surjective because `f` is surjective. The derived stalk of
`Lf^*M` at `x ∈ V_j` is `ω ⊗ᴸ 𝒪_{X,x}` (Stacks 0DJ7 in the form of
`AlgebraicGeometry.derivedPullbackStalkIso`), and `𝒪_{X,x}` is the localization of `B_j` at the
prime of `x`, so `ω ⊗ᴸ B_j` is a flat module in degree zero at every maximal ideal, hence flat in
degree zero. The algebraic statement
`StacksDraft.DerivedFlat.isFlatInDegreeZero_of_finitePresentation_family` then makes `ω` itself a
flat module in degree zero; that is where the flat stratification and Stacks 0H85 of the source's
proof enter, as a Noetherian induction. Hence so is every derived stalk of `M` over `U`.

## Implementation notes

The derived categories are taken at `HasDerivedCategory.standard`, the model of
`AlgebraicGeometry.exists_isFlat_derivedPullback_of_exists_isFlat`. The import closure contains
the locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` as a global
instance, which is why the standard model is installed at priority `10000`: at the default
priority the global instance would win and the statements would be read at the other model.
`D_QCoh(𝒪_S)` is written as the condition that every cohomology sheaf be quasi-coherent, as in the
statement of the implication (1) ⇒ (2).

## References

* [The Stacks Project, Lemma 37.54.3 (0H89)](https://stacks.math.columbia.edu/tag/0H89)
* [The Stacks Project, Tag 0H85](https://stacks.math.columbia.edu/tag/0H85)
* [The Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [The Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StacksDraft.DerivedFlat
open scoped ZeroObject

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.FlatSingleDerivedPullbackConverse

/-- The cohomology of an object placed in degree zero vanishes in every other degree. -/
lemma isZero_homology_singleFunctor (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (X : C) {i : ℤ} (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj X)) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact DerivedCategory.isZero_of_isLE _ 0 i h

variable {S : Scheme.{u}}

/-- The derived stalk commutes with cohomology. -/
def homologyDerivedStalkIso (M : DerivedCategory S.Modules) (s : S) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((derivedStalkFunctor s).obj M) ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor S s).obj
        ((DerivedCategory.homologyFunctor S.Modules i).obj M) :=
  ((Stacks.ModuleSkyscraper.modulesStalkFunctor S s).mapDerivedCategoryHomologyIso i).app M

/-- A sheaf of `𝒪_S`-modules all of whose stalks vanish is zero. -/
lemma isZero_of_forall_stalk (F : S.Modules)
    (h : ∀ s, IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor S s).obj F)) : IsZero F := by
  have : IsIso (0 : F ⟶ 0) :=
    Stacks.ModuleSkyscraper.isIso_of_forall_isIso_modulesStalkFunctor_map _ fun s =>
      ⟨⟨0, (h s).eq_of_src _ _,
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor S s).map_isZero
          (isZero_zero _)).eq_of_src _ _⟩⟩
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : F ⟶ 0))

/-- A sheaf of `𝒪_S`-modules is flat if and only if each of its stalks is a flat module over the
local ring at that point. -/
lemma isFlat_iff_forall_stalk (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ↔
      ∀ s : S, Module.Flat (S.presheaf.stalk s)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor S s).obj F) :=
  AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat S.toRingedSpace.sheaf F

/-- If `M ≅ F[0]`, then the degree zero cohomology of the derived stalk of `M` is flat exactly
when the stalk of `F` is. -/
private lemma flat_homology_derivedStalk_iff
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (e : M ≅ (DerivedCategory.singleFunctor _ 0).obj F) (s : S) :
    Module.Flat (S.presheaf.stalk s)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S.presheaf.stalk s)) 0).obj
        ((derivedStalkFunctor s).obj M)) ↔
      Module.Flat (S.presheaf.stalk s) ((Stacks.ModuleSkyscraper.modulesStalkFunctor S s).obj F) :=
  Module.Flat.equiv_iff ((homologyDerivedStalkIso M s 0) ≪≫
    (Stacks.ModuleSkyscraper.modulesStalkFunctor S s).mapIso
      ((DerivedCategory.homologyFunctor S.Modules 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules 0).app F)).toLinearEquiv

/-- An object of `D(𝒪_S)` all of whose derived stalks are flat modules in degree zero is
isomorphic to a flat `𝒪_S`-module placed in degree zero. -/
lemma exists_isFlat_of_forall_stalk
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (h : ∀ s : S, IsFlatInDegreeZero ((derivedStalkFunctor s).obj M)) :
    ∃ F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ∧
        Nonempty (M ≅ (DerivedCategory.singleFunctor _ 0).obj F) := by
  have hz : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor S.Modules i).obj M) :=
    fun i hi => isZero_of_forall_stalk _ fun s =>
      (((isFlatInDegreeZero_iff_homology _).1 (h s)).1 i hi).of_iso
        (homologyDerivedStalkIso M s i).symm
  have hGE : M.IsGE 0 := (DerivedCategory.isGE_iff M 0).2 (fun i hi => hz i (by omega))
  have hLE : M.IsLE 0 := (DerivedCategory.isLE_iff M 0).2 (fun i hi => hz i (by omega))
  obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M 0
  refine ⟨F, (isFlat_iff_forall_stalk F).2 fun s => ?_, ⟨e⟩⟩
  exact (flat_homology_derivedStalk_iff M F e s).1 ((isFlatInDegreeZero_iff_homology _).1 (h s)).2

/-- The derived stalks of a flat module placed in degree zero are flat modules in degree zero. -/
lemma isFlatInDegreeZero_derivedStalk
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hM : ∃ F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ∧
        Nonempty (M ≅ (DerivedCategory.singleFunctor _ 0).obj F)) (s : S) :
    IsFlatInDegreeZero ((derivedStalkFunctor s).obj M) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := hM
  rw [isFlatInDegreeZero_iff_homology]
  refine ⟨fun i hi => ?_, ?_⟩
  · refine IsZero.of_iso ?_ (homologyDerivedStalkIso M s i)
    refine Functor.map_isZero _ (IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctor S.Modules i).mapIso e))
    exact isZero_homology_singleFunctor _ F hi
  · exact (flat_homology_derivedStalk_iff M F e s).2 ((isFlat_iff_forall_stalk F).1 hF s)

section Tilde

variable (R : CommRingCat.{u}) (q : Spec R)

/-- The two stalk functors on `𝒪_{Spec R}`-modules over the local ring agree. -/
def stalkFunctorBridge :
    Stacks.Duality.modulesStalkFunctor q ≅ Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) q :=
  NatIso.ofComponents (fun M => AlgebraicGeometry.restrictScalarsStalkObjIso q M) (fun _ => rfl)

/-- The stalk of an associated sheaf is the base change along the germ map. -/
def tildeStalkNatIso :
    tilde.functor R ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) q ≅
      ModuleCat.extendScalars.{u, u, u} (Stacks.Duality.specGermRingHom R q) :=
  Functor.isoWhiskerLeft _ (stalkFunctorBridge R q).symm ≪≫ Stacks.Duality.tildeSchemeStalkIso R q

/-- The germ map `R → 𝒪_{Spec R, q}` is flat. -/
lemma flat_specGermRingHom : (Stacks.Duality.specGermRingHom R q).Flat := by
  have : (q : PrimeSpectrum R).asIdeal.IsPrime := (q : PrimeSpectrum R).isPrime
  let : Algebra R ((Spec R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  rw [Stacks.Duality.specGermRingHom_eq]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ q.asIdeal.primeCompl)

/-- The derived stalk of the derived associated sheaf is the derived base change along the germ
map. -/
def tildeDerivedStalkIso (N : DerivedCategory (ModuleCat.{u} R)) :
    (derivedStalkFunctor q).obj ((tilde.functor R).mapDerivedCategory.obj N) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (Stacks.Duality.specGermRingHom R q)).functor.obj N := by
  have : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (Stacks.Duality.specGermRingHom R q)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_specGermRingHom R q)
  have : PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u} (Stacks.Duality.specGermRingHom R q)) :=
    have : PreservesColimitsOfSize.{0, 0}
        (ModuleCat.extendScalars.{u, u, u} (Stacks.Duality.specGermRingHom R q)) :=
      (ModuleCat.extendRestrictScalarsAdj
        (Stacks.Duality.specGermRingHom R q)).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (tilde.functor R)
        (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) q)).symm.app N ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (tildeStalkNatIso R q)).app N ≪≫
    (PseudoCoherence.derivedExtensionIsoOfExact (Stacks.Duality.specGermRingHom R q)).symm.app N

end Tilde

/-- Every prime ideal of the sections over an affine open is the prime ideal of a point of it. -/
lemma exists_primeIdealOf_eq {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Ideal Γ(Y, W)) [P.IsPrime] : ∃ y : W, (hW.primeIdealOf y).asIdeal = P :=
  ⟨hW.isoSpec.inv ⟨P, inferInstance⟩, congrArg PrimeSpectrum.asIdeal
    ((Scheme.homeoOfIso hW.isoSpec).apply_symm_apply (⟨P, inferInstance⟩ : PrimeSpectrum _))⟩

section Affine

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The germ map of `Spec Γ(S, U)` at `q`, read in `S` through the open immersion
`Spec Γ(S, U) ⟶ S`, is the germ of `S` at the image of `q`. -/
lemma stalkMap_fromSpec_comp_germ (q : Spec Γ(S, U)) (hq : hU.fromSpec q ∈ U) :
    (hU.fromSpec.stalkMap q).hom.comp (S.presheaf.germ U (hU.fromSpec q) hq).hom =
      Stacks.Duality.specGermRingHom Γ(S, U) q := by
  ext r
  change hU.fromSpec.stalkMap q (S.presheaf.germ U (hU.fromSpec q) hq r) = _
  rw [Scheme.Hom.germ_stalkMap_apply, IsAffineOpen.fromSpec_app_self_apply]
  exact (TopCat.Presheaf.germ_res_apply (Spec Γ(S, U)).presheaf
    (homOfLE (le_top : hU.fromSpec ⁻¹ᵁ U ≤ ⊤)) q hq ((Scheme.ΓSpecIso Γ(S, U)).inv r)).trans
    (SemilinearStalk.commStalkRingEquiv_germ (Spec Γ(S, U)).presheaf q ⊤ trivial _).symm

/-- **An affine model.** An object of `D(𝒪_S)` with quasi-coherent cohomology has, over an affine
open `U`, a model `ω ∈ D(Γ(S, U))`: at every point `s ∈ U` its derived stalk is the derived base
change of `ω` along the germ map `Γ(S, U) → 𝒪_{S,s}`. -/
theorem exists_affine_model (hU : IsAffineOpen U)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hQ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M).IsQuasicoherent) :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(S, U)), ∀ (s : S) (hs : s ∈ U),
      Nonempty ((derivedStalkFunctor s).obj M ≅
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (S.presheaf.germ U s hs).hom).functor.obj ω) := by
  let ι := hU.fromSpec
  let E := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    ι.toLRSHom.toShHom).obj M
  have hE := Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel ι M hQ
  obtain ⟨ω, ⟨eω⟩⟩ := StandardModel.exists_iso_mapDerivedCategory Γ(S, U) E hE
  refine ⟨ω, fun s hs => ?_⟩
  obtain ⟨q, rfl⟩ : s ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  let σ : S.presheaf.stalk (ι q) ≃+* (Spec Γ(S, U)).presheaf.stalk q :=
    (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let e₁ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        σ.toRingHom).functor.obj ((derivedStalkFunctor (ι q)).obj M) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (Stacks.Duality.specGermRingHom Γ(S, U) q)).functor.obj ω :=
    ((derivedPullbackStalkIso ι q).app M).symm ≪≫
      (derivedStalkFunctor q).mapIso eω.symm ≪≫ tildeDerivedStalkIso Γ(S, U) q ω
  have hid : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id _ :=
    RingHom.ext σ.symm_apply_apply
  have hgerm : σ.symm.toRingHom.comp (Stacks.Duality.specGermRingHom Γ(S, U) q) =
      (S.presheaf.germ U (ι q) hs).hom := by
    rw [← stalkMap_fromSpec_comp_germ hU q hs]
    ext r
    exact σ.symm_apply_apply _
  exact ⟨((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u}
      (S.presheaf.stalk (ι q))).app _) ≪≫ eqToIso (by rw [hid]) ≪≫
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      σ.toRingHom σ.symm.toRingHom).app _).symm ≪≫
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      σ.symm.toRingHom).functor.mapIso e₁ ≪≫
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      _ σ.symm.toRingHom).app _ ≪≫ eqToIso (by rw [hgerm])⟩

/-- An affine model of an object of `D(𝒪_S)` without cohomology in positive degrees has no
cohomology in positive degrees. -/
lemma isZero_homology_of_affine_model (hU : IsAffineOpen U)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hM : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M))
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, U)))
    (hω : ∀ (s : S) (hs : s ∈ U), Nonempty ((derivedStalkFunctor s).obj M ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (S.presheaf.germ U s hs).hom).functor.obj ω)) :
    ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, U)) i).obj ω) := by
  rw [← baseChangeLE_id_iff]
  refine BaseChangeLE.of_forall_maximal _ fun P _ => ?_
  obtain ⟨y, rfl⟩ := exists_primeIdealOf_eq hU P
  let := (S.presheaf.germ U y.1 y.2).hom.toAlgebra
  have := hU.isLocalization_stalk y
  let e := IsLocalization.algEquiv (hU.primeIdealOf y).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf y).asIdeal) (S.presheaf.stalk y.1)
  refine BaseChangeLE.of_comp_ringEquiv e.toRingEquiv ?_
  refine (show BaseChangeLE ω (S.presheaf.germ U y.1 y.2).hom from fun i hi => ?_).of_eq ?_
  · obtain ⟨e₁⟩ := hω y.1 y.2
    exact (Functor.map_isZero (Stacks.ModuleSkyscraper.modulesStalkFunctor S y.1)
      (hM i hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e₁.symm ≪≫ homologyDerivedStalkIso M y.1 i)
  · ext r
    exact (e.commutes r).symm

end Affine

section Main

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- If `Lf^*M` is a flat module in degree zero, then the derived base change of an affine model
`ω` of `M` over `U` along `Γ(S, U) → Γ(X, V)` is flat in degree zero, for every affine `V` over
`U`. -/
lemma baseChangeFlat_appLE {U : S.Opens}
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (h₂ : ∃ G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) G ∧
        Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj M ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj G))
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, U)))
    (hω : ∀ (s : S) (hs : s ∈ U), Nonempty ((derivedStalkFunctor s).obj M ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (S.presheaf.germ U s hs).hom).functor.obj ω))
    {V : X.Opens} (hV : IsAffineOpen V) (hle : V ≤ f ⁻¹ᵁ U) :
    BaseChangeFlat ω (f.appLE U V hle).hom := by
  refine BaseChangeFlat.of_forall_maximal _ fun Q _ => ?_
  obtain ⟨x, rfl⟩ := exists_primeIdealOf_eq hV Q
  let := (X.presheaf.germ V x.1 x.2).hom.toAlgebra
  have := hV.isLocalization_stalk x
  let e := IsLocalization.algEquiv (hV.primeIdealOf x).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf x).asIdeal) (X.presheaf.stalk x.1)
  refine BaseChangeFlat.of_comp_ringEquiv e.toRingEquiv ?_
  have hfx : f x.1 ∈ U := hle x.2
  refine (show BaseChangeFlat ω ((f.stalkMap x.1).hom.comp
      (S.presheaf.germ U (f x.1) hfx).hom) from ?_).of_eq ?_
  · obtain ⟨e₁⟩ := hω (f x.1) hfx
    exact (isFlatInDegreeZero_derivedStalk _ h₂ x.1).of_iso
      ((derivedPullbackStalkIso f x.1).app M ≪≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (f.stalkMap x.1).hom).functor.mapIso e₁ ≪≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          _ _).app ω)
  · ext r
    refine Eq.trans ?_ (e.commutes ((f.appLE U V hle).hom r)).symm
    change f.stalkMap x.1 (S.presheaf.germ U (f x.1) hfx r) =
      X.presheaf.germ V x.1 x.2 (f.appLE U V hle r)
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]

/-- **The implication (2) ⇒ (1) of Stacks 0H89.** Let `f : X ⟶ S` be a surjective morphism of
finite presentation and let `M` be an object of `D_QCoh(𝒪_S)` with `H^i(M) = 0` for `i > 0`. If
`Lf^*M` is isomorphic to a flat `𝒪_X`-module placed in degree `0`, then `M` is isomorphic to a flat
`𝒪_S`-module placed in degree `0`. -/
theorem exists_isFlat_of_exists_isFlat_derivedPullback [Surjective f]
    (hf : FinitePresentation f)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hQCoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M).IsQuasicoherent)
    (hM : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M))
    (h₂ : ∃ G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) G ∧
        Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj M ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj G)) :
    ∃ F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ∧
        Nonempty (M ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj F) := by
  obtain ⟨hlfp, hqc, -⟩ := hf
  refine exists_isFlat_of_forall_stalk M fun s => ?_
  obtain ⟨_, ⟨U, (hU : IsAffineOpen U), rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  obtain ⟨ω, hω⟩ := exists_affine_model hU M hQCoh
  obtain ⟨t, htfin, htU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := f ⁻¹ᵁ U)).1 (f.isCompact_preimage hU.isCompact)
  have : Finite t := htfin.to_subtype
  have hVle : ∀ V : t, (V : X.affineOpens).1 ≤ f ⁻¹ᵁ U := fun V => by
    rw [htU]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ t) => (i : X.Opens)) V.1 V.2
  let B : t → Type u := fun V => Γ(X, (V : X.affineOpens).1)
  let : ∀ V : t, Algebra Γ(S, U) (B V) := fun V => (f.appLE U V.1.1 (hVle V)).hom.toAlgebra
  have : ∀ V : t, Algebra.FinitePresentation Γ(S, U) (B V) := fun V =>
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f hlfp ⟨U, hU⟩ V.1 (hVle V)
  have hωflat : IsFlatInDegreeZero ω := by
    refine isFlatInDegreeZero_of_finitePresentation_family B
      (isZero_homology_of_affine_model hU M hM ω hω) (fun P => ?_)
      fun V => baseChangeFlat_appLE f M h₂ ω hω V.1.2 (hVle V)
    let y : U := hU.isoSpec.inv P
    obtain ⟨x, hx⟩ := f.surjective y.1
    have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from hx ▸ y.2
    rw [htU] at hxU
    obtain ⟨V, hVt, hxV⟩ : ∃ V ∈ t, x ∈ (V : X.Opens) := by simpa using hxU
    refine ⟨⟨V, hVt⟩, V.2.primeIdealOf ⟨x, hxV⟩, ?_⟩
    refine (IsAffineOpen.comap_primeIdealOf_appLE U hU V.1 V.2 (hVle ⟨V, hVt⟩) hxV).trans ?_
    rw [show (⟨f x, hVle ⟨V, hVt⟩ hxV⟩ : U) = y from Subtype.ext hx]
    exact (Scheme.homeoOfIso hU.isoSpec).apply_symm_apply P
  exact (hωflat.baseChange (S.presheaf.germ U s hsU).hom).of_iso (hω s hsU).some.symm

end Main

end Stacks.Cohomology.FlatSingleDerivedPullbackConverse

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 0H89** (Longke Tang). Let `f : X ⟶ S` be a surjective morphism of finite presentation
and let `M` be an object of `D_QCoh(𝒪_S)` such that `H^i(M) = 0` for `i > 0`. Then `M` is
isomorphic to a flat `𝒪_S`-module placed in degree `0` if and only if `Lf^*M` is isomorphic to a
flat `𝒪_X`-module placed in degree `0`. -/
@[stacks 0H89]
theorem exists_isFlat_iff_exists_isFlat_derivedPullback [Surjective f]
    (hf : FinitePresentation f)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hQCoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M).IsQuasicoherent)
    (hM : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M)) :
    (∃ F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ∧
        Nonempty (M ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj F)) ↔
      ∃ G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
        SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) G ∧
          Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              f.toLRSHom.toShHom).obj M ≅
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj G) :=
  ⟨exists_isFlat_derivedPullback_of_exists_isFlat f hf M hQCoh hM,
    open Stacks.Cohomology.FlatSingleDerivedPullbackConverse in
      exists_isFlat_of_exists_isFlat_derivedPullback f hf M hQCoh hM⟩

end AlgebraicGeometry

end
