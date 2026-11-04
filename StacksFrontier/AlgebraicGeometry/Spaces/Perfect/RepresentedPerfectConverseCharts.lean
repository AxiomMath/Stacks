module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineKoszulGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartStrictlyPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.Homology.Perfect.FiniteFlatFamilyDescent

/-!
# Perfectness of `ε^*E` on `h_{Spec A}` gives perfectness on an étale affine covering

Let `A` be a ring, `T` the object `Spec A` of the big fppf site and `E` an object of
`D(𝒪_{Spec A})` with quasi-coherent cohomology. If `ε^*E` is a perfect object of `D(𝒪_{h_T})`
(perfectness on the small étale site, Stacks 08G5), then there are finitely many rings `A_i` and
flat morphisms `g_i : Spec A_i ⟶ Spec A`, jointly surjective, with every derived pullback
`Lg_i^*E` perfect on `Spec A_i`.

This is the étale-local half of the converse of Stacks 08HG for an affine scheme: the local
strictly perfect models of `ε^*E` live over the members of an étale covering of `T`, which may be
refined to finitely many affine members `Spec A_i`; over each the model is a strictly perfect
complex on `h_{Spec A_i}` representing `ε^*(Lg_i^*E)`, which forces `Lg_i^*E` to be perfect
(`AlgebraicGeometry.Space.exists_isPerfect_tilde_iso_of_isStrictlyPerfect`). Descending
perfectness along the faithfully flat family `{g_i}` is the remaining, purely scheme-theoretic,
step.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedPullback_of_representedDerivedPullback_iso`: one
  chart: if `(ε^*E)|_{h_{Spec A'}}` is a strictly perfect complex, then `Lg^*E` is perfect.
* `AlgebraicGeometry.Space.exists_finite_affine_isPerfect_derivedPullback`: the finite étale
  affine covering.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- Perfectness of `E` is equivalent to perfectness of `M` when `E ≅ M̃`. -/
private theorem isPerfect_iff_of_tilde_iso {R : CommRingCat.{u}}
    {M : DerivedCategory (ModuleCat.{u} R)} {E : DerivedCategory (Spec R).Modules}
    (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E ↔
      StacksDraft.Perfect.IsPerfect M :=
  ⟨fun h => (isPerfect_tilde_iff M).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
        e.symm h),
    fun h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) e ((isPerfect_tilde_iff M).2 h)⟩

/-- **One affine chart.** Let `g : Spec A' ⟶ Spec A` be a flat morphism of the big fppf site whose
represented morphism is étale, and `E` an object of `D(𝒪_{Spec A})` with quasi-coherent
cohomology. If the restriction of `ε^*E` to `h_{Spec A'}` is represented by a strictly perfect
complex, then the derived pullback `Lg^*E` is perfect on `Spec A'`. -/
theorem isPerfect_derivedPullback_of_representedDerivedPullback_iso
    {A' : Type u} [CommRing A'] (hA' : B.Contains (Spec (CommRingCat.of A')))
    (p' : Spec (CommRingCat.of A') ⟶ S)
    (g : BigFppfOver.mk B S hS hA' p' ⟶ BigFppfOver.mk B S hS hA p)
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    (hφ : IsEtale B S hS (representedSpaceMap B S hS g).hom)
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsQuasicoherent)
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA' p'))
      (isAlgebraicSpace_yoneda B S hS _)) ℤ)
    (hP : IsStrictlyPerfect _ P)
    (e : (representedDerivedPullback B S hS g hφ).obj
        ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj E) ≅
      DerivedCategory.Q.obj P) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec (CommRingCat.of A')).toRingedSpace)
      ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj E) := by
  let f := (BigFppfOver.toScheme B S hS).map g
  have := preservesFiniteLimits_modulesPullback_of_flat f
  have : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  have hE' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback f.toLRSHom.toShHom).obj E)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      ((((Scheme.Modules.pullback f).mapDerivedCategoryHomologyIso i).app E).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso
          ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory f).app E).symm)
      (Stacks.Modules.isQuasicoherent_pullback f _ (hE i))
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isPerfect_tilde_iso_of_isStrictlyPerfect B S hS hA' p' _ hE' P hP
    (((representedDerivedAssociatedModulePullbackIso B S hS g hφ).app E).symm ≪≫ e)
  exact (isPerfect_iff_of_tilde_iso eM).2 hM

/-- **A finite étale affine covering on whose members `E` becomes perfect.** Let `E` be an object
of `D(𝒪_{Spec A})` with quasi-coherent cohomology such that `ε^*E` is perfect on the small étale
site of `h_{Spec A}`. Then there are finitely many rings `A_i` and flat morphisms
`g_i : Spec A_i ⟶ Spec A`, jointly surjective, such that every `Lg_i^*E` is perfect.

The local strictly perfect models of `ε^*E` over the identity chart live on a covering sieve,
which is refined to finitely many affine étale charts (Stacks 03ED); each is isomorphic to some
`Spec A_i`, the model over it is a strictly perfect complex on `h_{Spec A_i}` representing
`(ε^*E)|_{h_{Spec A_i}} = ε^*(Lg_i^*E)`, and
`AlgebraicGeometry.Space.isPerfect_derivedPullback_of_representedDerivedPullback_iso` applies. -/
theorem exists_finite_affine_isPerfect_derivedPullback
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsQuasicoherent)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj E)) :
    ∃ (ι : Type) (_ : Finite ι) (A' : ι → Type u) (_ : ∀ i, CommRing (A' i))
      (g : ∀ i, Spec (CommRingCat.of (A' i)) ⟶ Spec (CommRingCat.of A)),
      (∀ i, Flat (g i)) ∧ (∀ x : Spec (CommRingCat.of A), ∃ i y, (g i).base y = x) ∧
      ∀ i, Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (Spec (CommRingCat.of (A' i))).toRingedSpace)
        ((derivedPullback (g i).toLRSHom.toShHom).obj E) := by
  classical
  let T := BigFppfOver.mk B S hS hA p
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  obtain ⟨F, hF, ⟨eF⟩⟩ := h
  let t := idEtaleChart B S hS T
  obtain ⟨Sp, hSp, hmod⟩ := hF t
  obtain ⟨ι, hι, V, f, haff, hle, hmem⟩ := SmallEtale.exists_finite_affine_refinement B S hS X.1 t
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))) (Sieve.generate Sp) hSp
  have hloc : ∀ i, (smallEtaleRingedSite B S hS X.1 X.2).HasStrictlyPerfectQuasiIso F (V i) := by
    intro i
    obtain ⟨W, a, s, hs, -⟩ := hle _ (Sieve.ofArrows_mk V f i)
    exact RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ F a (hmod s hs)
  choose A' instA' hA' p' e using fun i => exists_iso_mk_spec B S hS
    ((SmallEtale.toOver B S hS X.1).obj (V i)) (haff i)
  let g' : ∀ i, BigFppfOver.mk B S hS (hA' i) (p' i) ⟶ T := fun i =>
    (e i).some.inv ≫ (SmallEtale.toOver B S hS X.1).map (f i)
  have h1 : ∀ i, yoneda.map (g' i) = yoneda.map (e i).some.inv ≫ (V i).1.hom := fun i => by
    rw [← CostructuredArrow.w (f i).hom]
    simp [g', t, idEtaleChart]
    rfl
  have hφ : ∀ i, IsEtale B S hS (yoneda.map (g' i)) := fun i => by
    rw [h1]
    exact isEtale_yoneda_map_comp B S hS _ _ inferInstance
      (isEtale_of_presheaf_etale B S hS (V i).2)
  have hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (g' i)) := fun i => by
    have : Etale ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (f i))) :=
      etale_of_comp_etale_chart B S hS (V i).property t.property (CostructuredArrow.w (f i).hom)
    change Flat ((BigFppfOver.toScheme B S hS).map
      ((e i).some.inv ≫ (SmallEtale.toOver B S hS X.1).map (f i)))
    rw [Functor.map_comp]
    infer_instance
  have h2 : ∀ i, (BigFppfOver.toScheme B S hS).map (e i).some.hom ≫
      (BigFppfOver.toScheme B S hS).map (g' i) =
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (f i)) := fun i => by
    rw [← Functor.map_comp]
    exact congrArg (BigFppfOver.toScheme B S hS).map (Iso.hom_inv_id_assoc (e i).some _)
  refine ⟨ι, hι, A', instA', fun i => (BigFppfOver.toScheme B S hS).map (g' i), hflat, ?_, ?_⟩
  · intro x
    obtain ⟨W, k, ⟨Y, a, _, ⟨i⟩, rfl⟩, y, hy⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).1 hmem x
    refine ⟨i, ((BigFppfOver.toScheme B S hS).map (e i).some.hom).base
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a)).base y), ?_⟩
    rw [← hy]
    have h3 : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) ≫
        (BigFppfOver.toScheme B S hS).map (e i).some.hom ≫
          (BigFppfOver.toScheme B S hS).map (g' i) =
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (a ≫ f i)) := by
      rw [h2, Functor.map_comp (SmallEtale.toOver B S hS X.1), Functor.map_comp]
      rfl
    exact congrArg (fun φ => φ.base y) h3
  · intro i
    let V' : SmallEtale B S hS X.1 :=
      ⟨CostructuredArrow.mk (yoneda.map (g' i)), presheaf_etale_of_isEtale B S hS (hφ i)⟩
    let k : V' ⟶ V i := ObjectProperty.homMk (CostructuredArrow.homMk (e i).some.inv (h1 i).symm)
    obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isStrictlyPerfect_iso_chartRestriction B S hS F V'
      (RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ F k (hloc i))
    exact isPerfect_derivedPullback_of_representedDerivedPullback_iso B S hS hA p (hA' i) (p' i)
      (g' i) (hφ i) E hE P hP
      ((representedDerivedPullback B S hS (g' i) (hφ i)).mapIso eF.symm ≪≫ eP.symm)

/-- **Derived pullback of `K̃` along a flat `Spec A' ⟶ Spec A` is `(K ⊗_A A')~`.** -/
def derivedPullbackSpecMapTildeIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') [Flat (Spec.map φ)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedPullback (Spec.map φ).toLRSHom.toShHom).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      (tilde.functor R').mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} φ.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) :=
  haveI : PreservesFiniteColimits (tilde.functor R) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  haveI : PreservesFiniteColimits (tilde.functor R') :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R'
  haveI : (tilde.functor R).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  haveI : (tilde.functor R').Additive := ⟨by intros; exact tilde.map_add _ _⟩
  haveI : PreservesFiniteLimits (tilde.functor R) := AlgebraicGeometry.tilde.preservesFiniteLimits _
  haveI : PreservesFiniteLimits (tilde.functor R') :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
    StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars φ.hom
  haveI : (ModuleCat.extendScalars.{u, u, u} φ.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI := preservesFiniteLimits_modulesPullback_of_flat (Spec.map φ)
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback (Spec.map φ)) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback _
  haveI : (Scheme.Modules.pullback (Spec.map φ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Scheme.Modules.derivedPullbackIsoMapDerivedCategory (Spec.map φ)).app _ ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapDerivedCategory.mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app K) ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := tilde.functor R)
          (G := Scheme.Modules.pullback (Spec.map φ))
          (Stacks.Descent.extendScalarsCompTildeIso φ).symm (ComplexShape.up ℤ)).app K ≪≫
        ((Functor.mapHomologicalComplexCompIso (F := ModuleCat.extendScalars.{u, u, u} φ.hom)
          (G := tilde.functor R') (Iso.refl _) (ComplexShape.up ℤ)).app K).symm) ≪≫
    ((tilde.functor R').mapDerivedCategoryFactors.app _).symm

/-- **The converse of Stacks 08HG on an affine scheme, for quasi-coherent cohomology.** Let `E`
be an object of `D(𝒪_{Spec A})` with quasi-coherent cohomology sheaves. If `ε^*E` is a perfect
object of `D(𝒪_{h_{Spec A}})` (perfectness on the small étale site of the represented algebraic
space, Stacks 08G5), then `E` is perfect.

The local models of `ε^*E` give a finite flat jointly surjective family `Spec A_i ⟶ Spec A` on
which `E` becomes perfect
(`AlgebraicGeometry.Space.exists_finite_affine_isPerfect_derivedPullback`); writing `E = K̃`
(Stacks 06Z0), the pullbacks are `(K ⊗_A A_i)~`, so every `K ⊗_A A_i` is perfect (Stacks 08EB),
and perfectness descends along the faithfully flat `A → ∏ A_i`
(`StacksDraft.Perfect.isPerfect_of_finite_flat_family`). -/
theorem isPerfect_spec_of_isPerfect_representedDerivedAssociatedModule
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsQuasicoherent)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace) E := by
  obtain ⟨ι, hι, A', instA', g, hflat, hsurj, hP⟩ :=
    exists_finite_affine_isPerfect_derivedPullback B S hS hA p E hE h
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory
    (CommRingCat.of A) E hE
  let K := DerivedCategory.Q.objPreimage M
  let eE : (tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
      E :=
    (tilde.functor _).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M) ≪≫ eM
  let φ : ∀ i, CommRingCat.of A ⟶ CommRingCat.of (A' i) := fun i => Spec.preimage (g i)
  have hg : ∀ i, Spec.map (φ i) = g i := fun i => Spec.map_preimage (g i)
  have hflat' : ∀ i, Flat (Spec.map (φ i)) := fun i => (hg i).symm ▸ hflat i
  have hK : ∀ i, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (φ i).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) := fun i => by
    have hPi := hP i
    rw [← hg i] at hPi
    exact (isPerfect_iff_of_tilde_iso ((derivedPullbackSpecMapTildeIso (φ i) K).symm ≪≫
      (derivedPullback (Spec.map (φ i)).toLRSHom.toShHom).mapIso eE)).1 hPi
  exact (isPerfect_iff_of_tilde_iso eE).2
    (StacksDraft.Perfect.isPerfect_of_finite_flat_family A' (fun i => (φ i).hom)
      (fun i => (HasRingHomProperty.Spec_iff (P := @Flat)).1 (hflat' i))
      (fun x => by
        obtain ⟨i, y, rfl⟩ := hsurj x
        exact ⟨i, y, by rw [← hg i]; rfl⟩) K hK)

end AlgebraicGeometry.Space
