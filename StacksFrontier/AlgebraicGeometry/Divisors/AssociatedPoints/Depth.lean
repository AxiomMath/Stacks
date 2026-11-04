module

public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# An isomorphism criterion from depth and associated points

Let `f : F ⟶ G` be a map of quasi-coherent modules on a locally Noetherian scheme, with `F`
coherent. If at every point the induced map on stalks is an isomorphism, or else the stalk of
`F` has depth at least two and the point is not associated to `G`, then `f` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated` is the criterion.

## Implementation notes

The stalk map is the morphism of additive groups induced by the map of sheaves of modules; its
source carries the canonical module structure over the local ring at the point. Both sides are
read on an affine open: the stalk is the localization of the module of sections, so the
hypothesis becomes the corresponding module-theoretic alternative at each prime, and
`bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes` applies. A map of
sheaves whose stalk maps are all bijective is an isomorphism.

## References

* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The map on sections over an open induced by a map of `𝒪_X`-modules, as a linear map. -/
private noncomputable def affineSectionsMapLinear {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (U : X.Opens) :
    letI : Module Γ(X, U) Γ(F, U) := (F.val.obj (op U)).isModule
    letI : Module Γ(X, U) Γ(G, U) := (G.val.obj (op U)).isModule
    Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) where
  toFun := ConcreteCategory.hom (f.val.app (op U))
  map_add' := map_add _
  map_smul' := fun r s => map_smul _ r s

/-- The map on stalks induced by a map of `𝒪_X`-modules, as a linear map over the local ring. -/
public noncomputable def schemeStalkLinearMap {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x := by
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
  refine
    { toFun := ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)
      map_add' := map_add _
      map_smul' := ?_ }
  intro a m
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq m
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op r
  let sW : Γ(F, W) := F.presheaf.map (homOfLE inf_le_right).op s
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxW r,
    ← F.presheaf.germ_res_apply (homOfLE inf_le_right) x hxW s]
  have hF : X.presheaf.germ W x hxW rW • F.presheaf.germ W x hxW sW =
      F.presheaf.germ W x hxW (rW • sW) :=
    (PresheafOfModules.germ_smul F.val x W hxW rW sW).symm
  rw [hF]
  have hnat (t : Γ(F, W)) :
      ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)
          (F.presheaf.germ W x hxW t) =
        G.presheaf.germ W x hxW (f.app W t) := by
    simpa only [TopCat.Presheaf.stalkFunctor_obj, Scheme.Modules.mapPresheaf_app] using
      TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW f.mapPresheaf t
  rw [hnat, f.app_smul]
  have hG : G.presheaf.germ W x hxW (rW • f.app W sW) =
      X.presheaf.germ W x hxW rW • G.presheaf.germ W x hxW (f.app W sW) :=
    PresheafOfModules.germ_smul G.val x W hxW rW (f.app W sW)
  rw [hG, hnat]
  have hr : X.presheaf.germ W x hxW rW = X.presheaf.germ U x hxU r := by
    dsimp [rW]
    exact X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxW r
  rw [hr]
  rfl

/-- **The stalk map of an isomorphism of `𝒪_X`-modules, as a linear equivalence** over the local
ring at the point. The stalk functor is a functor, so it takes the isomorphism to an isomorphism
of abelian groups, which is a bijection; `AlgebraicGeometry.schemeStalkLinearMap` supplies the
linearity. -/
public noncomputable def schemeStalkLinearEquiv {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (x : X) :
    F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x :=
  haveI : IsIso e.hom.mapPresheaf := by
    change IsIso ((Scheme.Modules.toPresheaf X).map e.hom)
    infer_instance
  LinearEquiv.ofBijective (schemeStalkLinearMap e.hom x)
    (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map e.hom.mapPresheaf))

/-- The stalk map sends the germ of a section to the germ of its image. -/
private lemma schemeStalkLinearMap_germ {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)) :
    (schemeStalkLinearMap f x).toFun (F.presheaf.germ U x hx s) =
      G.presheaf.germ U x hx (ConcreteCategory.hom (f.val.app (op U)) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf s

/-- The germ map intertwines the map on sections with the map on stalks. -/
private lemma affineGerm_map {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) (U : X.Opens)
    (s : Γ(F, U)) (x : X) (hx : x ∈ U) :
    letI : Module Γ(X, U) Γ(F, U) := (F.val.obj (op U)).isModule
    letI : Module Γ(X, U) Γ(G, U) := (G.val.obj (op U)).isModule
    affineGerm G U x hx ((affineSectionsMapLinear f U).toFun s) =
      (schemeStalkLinearMap f x).toFun (affineGerm F U x hx s) := by
  show G.presheaf.germ U x hx (ConcreteCategory.hom (f.val.app (op U)) s) =
    (schemeStalkLinearMap f x).toFun (F.presheaf.germ U x hx s)
  rw [schemeStalkLinearMap_germ]

/-- The stalk map of a map of `𝒪_X`-modules is bijective iff it is an isomorphism of abelian
groups. -/
private lemma isIso_stalkFunctor_map_iff_bijective_schemeStalkLinearMap {X : Scheme.{u}}
    {F G : X.Modules} (f : F ⟶ G) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ↔
      Function.Bijective (schemeStalkLinearMap f x).toFun := by
  dsimp only [schemeStalkLinearMap]
  exact ConcreteCategory.isIso_iff_bijective _

/-- On an affine open, bijectivity of the localized map on sections at the prime of `x` is
bijectivity of the map on stalks at `x`. -/
private lemma localized_section_map_bijective_of_stalk_map_bijective {X : Scheme.{u}}
    {F G : X.Modules} (f : F ⟶ G) [F.IsQuasicoherent] [G.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI : Module Γ(X, U) Γ(F, U) := (F.val.obj (op U)).isModule
    letI : Module Γ(X, U) Γ(G, U) := (G.val.obj (op U)).isModule
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    letI : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hx
    letI : Module Γ(X, U) (G.presheaf.stalk x) := affineStalkModule G U x hx
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (G.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Bijective (LocalizedModule.map
        (↑(hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (affineSectionsMapLinear f U)) ↔
      Function.Bijective (schemeStalkLinearMap f x).toFun := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let R := Γ(X, U)
  let M := Γ(F, U)
  let N := Γ(G, U)
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
  let : Module R (F.presheaf.stalk x) := affineStalkModule F U x hx
  let : Module R (G.presheaf.stalk x) := affineStalkModule G U x hx
  let : Algebra R (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsScalarTower R (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let gF := affineGerm F U x hx
  let gG := affineGerm G U x hx
  have hlocF : IsLocalizedModule p.primeCompl gF := affineGerm_isLocalized F U hU x hx
  have hlocG : IsLocalizedModule p.primeCompl gG := affineGerm_isLocalized G U hU x hx
  let eF := IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) gF
  let eG := IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl N) gG
  let φ := affineSectionsMapLinear f U
  let locf := LocalizedModule.map p.primeCompl φ
  let locfR := locf.restrictScalars R
  let stalkf : F.presheaf.stalk x →ₗ[R] G.presheaf.stalk x :=
    { toFun := (schemeStalkLinearMap f x).toFun
      map_add' := (schemeStalkLinearMap f x).map_add
      map_smul' := by
        intro r z
        show (schemeStalkLinearMap f x).toFun ((X.presheaf.germ U x hx).hom r • z) =
          (X.presheaf.germ U x hx).hom r • (schemeStalkLinearMap f x).toFun z
        exact (schemeStalkLinearMap f x).map_smul ((X.presheaf.germ U x hx).hom r) z }
  have hjk : eG.toLinearMap ∘ₗ locfR = stalkf ∘ₗ eF.toLinearMap := by
    refine IsLocalizedModule.ext p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
      (map_unit := affineGerm_map_units G U hU x hx) ?_
    ext m
    show eG (locf ((LocalizedModule.mkLinearMap p.primeCompl M) m)) =
      stalkf (eF ((LocalizedModule.mkLinearMap p.primeCompl M) m))
    dsimp [eG, eF]
    have hmap : locf ((LocalizedModule.mkLinearMap p.primeCompl M) m) =
        (LocalizedModule.mkLinearMap p.primeCompl N) (φ.toFun m) :=
      IsLocalizedModule.map_apply p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl M)
        (LocalizedModule.mkLinearMap p.primeCompl N) φ m
    rw [hmap, IsLocalizedModule.linearEquiv_apply, IsLocalizedModule.linearEquiv_apply]
    exact affineGerm_map f U m x hx
  have heq : (fun z => eG (locf (eF.symm z))) = (schemeStalkLinearMap f x).toFun := by
    funext z
    have hz := LinearMap.congr_fun hjk (eF.symm z)
    change eG (locf (eF.symm z)) = (schemeStalkLinearMap f x).toFun (eF (eF.symm z)) at hz
    simpa only [LinearEquiv.apply_symm_apply] using hz
  rw [← heq]
  exact (Function.Bijective.of_comp_iff' eG.bijective locf).symm.trans
    ((Function.Bijective.of_comp_iff _ eF.symm.bijective).symm)

/-- On an affine open, depth at least two of the stalk at `x` is depth at least two of the
localization of the module of sections at the prime of `x`. -/
private lemma affine_depth_two_iff_localized {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ↔
      (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (IsLocalRing.maximalIdeal
          (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let R := Γ(X, U)
  let M := Γ(F, U)
  let T := X.presheaf.stalk x
  let N := F.presheaf.stalk x
  let S := Localization.AtPrime p
  let : Module T N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module R N := affineStalkModule F U x hx
  let : Algebra R T := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsScalarTower R T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsLocalization.AtPrime T p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  let e : S ≃ₐ[R] T := IsLocalization.algEquiv p.primeCompl S T
  let : Algebra S T := e.toAlgHom.toAlgebra
  let : Module S N := Module.compHom N (algebraMap S T)
  let : IsScalarTower S T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp (r : R) : algebraMap S T (algebraMap R S r) = algebraMap R T r := e.commutes r
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun r t => by
    show algebraMap S T (algebraMap R S r) * t = algebraMap R T r * t
    rw [hcomp]
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r n => by
    show algebraMap S T (algebraMap R S r) • n = algebraMap R T r • n
    rw [hcomp]
  have hlocM : IsLocalizedModule p.primeCompl (affineGerm F U x hx) :=
    affineGerm_isLocalized F U hU x hx
  let eM : LocalizedModule p.primeCompl M ≃ₗ[R] N :=
    IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
      (affineGerm F U x hx)
  let eM' : LocalizedModule p.primeCompl M ≃ₗ[S] N :=
    eM.extendScalarsOfIsLocalization p.primeCompl S
  have hdepthM : Module.depth S (IsLocalRing.maximalIdeal S)
      (LocalizedModule p.primeCompl M) = Module.depth S (IsLocalRing.maximalIdeal S) N :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) eM'
  have hmax : Ideal.map (algebraMap S T) (IsLocalRing.maximalIdeal S) =
      IsLocalRing.maximalIdeal T :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hdepthST := Module.depth_eq_depth_map_algebraMap e.surjective
    (IsLocalRing.maximalIdeal S) N
  rw [hmax] at hdepthST
  show (2 : ℕ∞) ≤ Module.depth T (IsLocalRing.maximalIdeal T) N ↔
    (2 : ℕ∞) ≤ Module.depth S (IsLocalRing.maximalIdeal S) (LocalizedModule p.primeCompl M)
  rw [← hdepthST, ← hdepthM]

/-- On an affine open `U`, the hypothesis of
`AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated` gives, at every prime of
`Γ(X, U)`, the module-theoretic alternative for the map on sections. -/
private lemma bijective_localized_or_depth_two_of_affine {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : F ⟶ G)
    (hf : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
      ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ∧
        x ∉ Stacks.Divisors.associatedPoints G))
    (U : X.Opens) (hU : IsAffineOpen U) (q : Ideal Γ(X, U)) (hq : q.IsPrime) :
    Function.Bijective (LocalizedModule.map q.primeCompl (affineSectionsMapLinear f U)) ∨
      2 ≤ Module.depth (Localization.AtPrime q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl Γ(F, U)) ∧ q ∉ associatedPrimes Γ(X, U) Γ(G, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let qs : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  let y : X := hU.fromSpec qs
  have hyU : y ∈ U := by
    show hU.fromSpec qs ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨qs, rfl⟩
  have hyq : hU.primeIdealOf ⟨y, hyU⟩ = qs := by
    apply hU.fromSpec.isOpenEmbedding.injective
    simpa [y] using hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hprimeEq : (⟨(hU.primeIdealOf ⟨y, hyU⟩).asIdeal, inferInstance⟩ :
      {I : Ideal Γ(X, U) // I.IsPrime}) = ⟨q, hq⟩ :=
    Subtype.ext (congrArg PrimeSpectrum.asIdeal hyq)
  let : Module (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  rcases hf y with hIso | ⟨hdepth, hnotassoc⟩
  · left
    let primeComplOf (I : {J : Ideal Γ(X, U) // J.IsPrime}) : Submonoid Γ(X, U) := by
      let : I.1.IsPrime := I.2
      exact I.1.primeCompl
    have hprimeComplEq : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl = q.primeCompl :=
      congrArg primeComplOf hprimeEq
    rw [← hprimeComplEq]
    exact (localized_section_map_bijective_of_stalk_map_bijective f U hU y hyU).2
      ((isIso_stalkFunctor_map_iff_bijective_schemeStalkLinearMap f y).1 hIso)
  · right
    have hdepth' := (affine_depth_two_iff_localized F U hU y hyU).1 hdepth
    let depthAt : {I : Ideal Γ(X, U) // I.IsPrime} → Prop := fun I => by
      let : I.1.IsPrime := I.2
      exact (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime I.1)
        (IsLocalRing.maximalIdeal (Localization.AtPrime I.1))
        (LocalizedModule I.1.primeCompl Γ(F, U))
    have hdepthSub : depthAt ⟨(hU.primeIdealOf ⟨y, hyU⟩).asIdeal, inferInstance⟩ := hdepth'
    refine ⟨(congrArg depthAt hprimeEq).mp hdepthSub, fun hmem => ?_⟩
    have hmem' : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(G, U) := by
      simpa [hyq] using hmem
    exact hnotassoc
      ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
        G U hU hyU).mp ((isAssociatedPrimeStacks_iff_mem_associatedPrimes _).2 hmem'))

/-- A map of `𝒪_X`-modules whose maps on stalks are all bijective is an isomorphism. -/
private theorem isIso_of_bijective_schemeStalkLinearMap {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G)
    (h : ∀ x : X, Function.Bijective (schemeStalkLinearMap f x).toFun) : IsIso f := by
  have hstalkIso : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map f)) := fun x =>
    (isIso_stalkFunctor_map_iff_bijective_schemeStalkLinearMap f x).2 (h x)
  let Fs : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.presheaf, F.isSheaf⟩
  let Gs : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G.presheaf, G.isSheaf⟩
  let fs : Fs ⟶ Gs := ⟨f.mapPresheaf⟩
  have hstalks : ∀ x : X,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map fs.1) := by
    intro x
    simpa [fs] using hstalkIso x
  have hfs : IsIso fs := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fs
  have hmap : IsIso f.mapPresheaf := by
    show IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map fs)
    infer_instance
  exact (isIso_iff_of_reflects_iso f (Scheme.Modules.toPresheaf X)).mp (by
    simpa only [Scheme.Modules.toPresheaf_map, Scheme.Modules.toPresheaf_obj] using hmap)

/-- **Stacks Project, Tag 0AVM.** A map from a coherent sheaf to a quasi-coherent sheaf is an
isomorphism if, at every point, it is an isomorphism on stalks, or the source stalk has depth at
least two and the point is not associated to the target.

The clause on associated points is what settles the degenerate case, and it cannot be dropped:
Tag 00LI sets `depth_I(M) = ∞` when `IM = M`, hence `⊤` for `M = 0`
(`Module.depth_eq_top_of_subsingleton`), so for `F = 0` and `G` nonzero the alternative
`depth(F_x) ≥ 2` holds at every point on its own while `0 ⟶ G` is not an isomorphism. See
`AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree`, which
is the integral, torsion-free case of Tag 0AVS, and the counterexample recorded alongside it. -/
@[stacks 0AVM]
theorem isIso_of_stalk_isIso_or_depth_two_and_not_associated {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsCoherent] (f : F ⟶ G)
    (hf : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
      ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ∧
        x ∉ Stacks.Divisors.associatedPoints G)) :
    IsIso f := by
  have hftF : F.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).2
  refine isIso_of_bijective_schemeStalkLinearMap f fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  let R : Type u := Γ(X, U)
  let M : Type u := Γ(F, U)
  let N : Type u := Γ(G, U)
  let φ : M →ₗ[R] N := affineSectionsMapLinear f U
  have hnoeth : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfinM : Module.Finite R M := moduleFinite_sections_on_affine F U hU
  have hφbij : Function.Bijective φ :=
    bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes φ
      (bijective_localized_or_depth_two_of_affine f hf U hU)
  exact (localized_section_map_bijective_of_stalk_map_bijective f U hU x hxU).1
    ⟨LocalizedModule.map_injective _ φ hφbij.1, LocalizedModule.map_surjective _ φ hφbij.2⟩

end AlgebraicGeometry
