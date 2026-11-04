module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoherentTorAmplitudePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSingleUnit
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Morphisms from a perfect object of high Tor amplitude to the structure sheaf

Let `Y` be an affine algebraic space and `P` a perfect object of `D(𝒪_Y)` with Tor amplitude in
`[a, b]`. Then every morphism `P ⟶ 𝒪_Y[-n]` vanishes for `n < a`. Over `Y = Spec A` the object
`P` is represented by a complex of finite projective `A`-modules sitting in degrees `[a, b]`
(Stacks 0658), which has no term in degree `n`.

## Main results

* `DerivedCategory.Q_obj_hom_singleFunctor_obj_eq_zero`: a morphism from a bounded above complex
  of projectives to an object placed in a degree where the complex vanishes is zero.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIdentityIso`: `L(𝟙_X)^* ≅ 𝟭`.
* `AlgebraicGeometry.Space.faithful_smallEtaleDerivedModulePullback_of_iso`: derived pullback
  along an isomorphism of algebraic spaces is faithful.
* `AlgebraicGeometry.Space.hom_singleFunctor_structureModule_eq_zero_of_hasTorAmplitude`: the
  vanishing above, for an affine algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A morphism in `D(C)` from a bounded above complex of projectives `E` to an object `A` placed in
a degree `n` with `E^n = 0` is zero. -/
theorem Q_obj_hom_singleFunctor_obj_eq_zero (E : CochainComplex C ℤ) (b : ℤ) [E.IsStrictlyLE b]
    [∀ i, Projective (E.X i)] (n : ℤ) (hn : IsZero (E.X n)) (A : C)
    (φ : Q.obj E ⟶ (singleFunctor C n).obj A) : φ = 0 := by
  have := CochainComplex.isKProjective_of_projective E b
  obtain ⟨c, rfl⟩ := StacksDraft.Perfect.map_surjective_of_isKProjective E
    ((CochainComplex.singleFunctor C n).obj A) φ
  have hc : c = 0 := by
    ext i
    by_cases hi : i = n
    · subst hi
      exact hn.eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ n A i hi).eq_of_tgt _ _
  rw [hc, Functor.map_zero]

end DerivedCategory

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck modules_abelian

-- `SheafOfModules.hasBinBiprod`, universe-polymorphic in the module universe, gives a second
-- route to the biproducts of sheaves of modules, and the derived tensor product of the small étale
-- site no longer elaborates against it: the two routes leave the module universe stuck at
-- `max ?v ?w =?= u`.
attribute [-instance] SheafOfModules.hasBinBiprod

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Derived pullback along an identity and along an isomorphism -/

/-- **The derived pullback along the identity is the identity**: `L(𝟙_X)^* ≅ 𝟭`. -/
def smallEtaleDerivedModulePullbackIdentityIso (X : AlgebraicSpaces B S hS) :
    smallEtaleDerivedModulePullback B S hS (𝟙 X) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  let h : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS (𝟙 X : X ⟶ X).hom
  smallEtaleDerivedModulePullbackIsoEtale B S hS (𝟙 X) h ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackIdIso B S hS h) ≪≫
    StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso

/-- **Derived pullback along an isomorphism of algebraic spaces is faithful.** Composed with the
derived pullback along the inverse it is the derived pullback along the identity. -/
theorem faithful_smallEtaleDerivedModulePullback_of_iso {X Y : AlgebraicSpaces B S hS}
    (e : X ≅ Y) : (smallEtaleDerivedModulePullback B S hS e.hom).Faithful :=
  have : (smallEtaleDerivedModulePullback B S hS e.hom ⋙
      smallEtaleDerivedModulePullback B S hS e.inv).Faithful :=
    Functor.Faithful.of_iso ((smallEtaleDerivedModulePullbackIdentityIso B S hS Y).symm ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS e.inv_hom_id.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS e.inv e.hom).symm)
  Functor.Faithful.of_comp _ (smallEtaleDerivedModulePullback B S hS e.inv)

/-! ### The vanishing on an affine algebraic space -/

/-- On a represented affine algebraic space `Spec A`, a morphism from a perfect object with Tor
amplitude in `[a, b]` to `𝒪[-n]` vanishes for `n < a`. -/
theorem hom_singleFunctor_structureModule_eq_zero_of_hasTorAmplitude_yoneda
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (P : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hP : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPerfect P) (a b : ℤ)
    (hamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      P a b) (n : ℤ) (hn : n < a)
    (t : P ⟶ (DerivedCategory.singleFunctor _ n).obj
      (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) : t = 0 := by
  let Φ := representedAffineDerivedAssociated B S hS U
  let T := smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  have hQ := qcohDerived_of_isPerfect B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ P hP
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U P hQ
  set M := (representedAffineDerivedSections B S hS U).obj P
  let ε : Φ.obj M ≅ P := asIso ((representedAffineDerivedAdjunction B S hS U).counit.app P)
  have hMperf : StacksDraft.Perfect.IsPerfect M :=
    isPerfect_representedAffineDerivedSections_obj B S hS U P hP
  have hamp' : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T (Φ.obj M) a b :=
    fun F i hi => (hamp F i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((T.tensor.mapIso ε).app _))
  have hcan := (hasTorAmplitude_representedAffineDerivedAssociated_iff B S hS U M a b).1 hamp'
  obtain ⟨E₀, hE₀, hGE₀, hLE₀, ⟨e₀⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ M a b).1 hcan
  have hchar := StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} M
  obtain ⟨E, hE, hGE, hLE, ⟨e⟩⟩ := hchar.2 a b (hchar.1.1 hMperf).1 ⟨E₀, hE₀, hGE₀, hLE₀, ⟨e₀⟩⟩
  have : ∀ i, Projective (E.X i) := fun i =>
    have := (hE i).2
    (E.X i).projective_of_categoryTheory_projective
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let ι := representedAffineDerivedAssociatedSingleUnitIso B S hS U n
  let s : DerivedCategory.Q.obj E ⟶ (DerivedCategory.singleFunctor _ n).obj R₀ :=
    (representedAffineDerivedAssociatedFullyFaithful B S hS U).preimage
      (Φ.map e.inv ≫ ε.hom ≫ t ≫ ι.inv)
  have hs : s = 0 := DerivedCategory.Q_obj_hom_singleFunctor_obj_eq_zero E b n
    (E.isZero_of_isStrictlyGE a n hn) R₀ s
  have h0 : Φ.map e.inv ≫ ε.hom ≫ t ≫ ι.inv = 0 := by
    rw [← (representedAffineDerivedAssociatedFullyFaithful B S hS U).map_preimage
      (Φ.map e.inv ≫ ε.hom ≫ t ≫ ι.inv)]
    show Φ.map s = 0
    rw [hs, Functor.map_zero]
  rw [← cancel_mono ι.inv, Limits.zero_comp, ← cancel_epi (Φ.mapIso e.symm ≪≫ ε).hom,
    Limits.comp_zero]
  simpa using h0

/-- **On an affine algebraic space `Y`, a morphism from a perfect object `P` with Tor amplitude in
`[a, b]` to `𝒪_Y[-n]` vanishes for `n < a`.** Over `Y ≅ Spec A` the object `P` is represented by a
complex of finite projective `A`-modules in degrees `[a, b]` (Stacks 0658). -/
theorem hom_singleFunctor_structureModule_eq_zero_of_hasTorAmplitude
    (Y : AlgebraicSpaces B S hS) (hY : IsAffineSpace B S hS Y.1)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hP : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P) (a b : ℤ)
    (hamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS Y) P a b) (n : ℤ) (hn : n < a)
    (t : P ⟶ (DerivedCategory.singleFunctor _ n).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) : t = 0 := by
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hY
  have := hT₀
  let Y₀ : AlgebraicSpaces B S hS := ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
  let e : Y₀ ≅ Y := (ObjectProperty.isoMk _ i).symm
  let L := smallEtaleDerivedModulePullback B S hS e.hom
  have := faithful_smallEtaleDerivedModulePullback_of_iso B S hS e
  have : IsIso e.hom.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map e.hom))
  have het : IsEtale B S hS e.hom.hom := isEtale_of_isIso B S hS e.hom.hom
  have hsep : IsSeparated B S hS e.hom.hom := isSeparated_of_isIso B S hS e.hom.hom
  let u : L.obj ((DerivedCategory.singleFunctor _ n).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) ≅
      (DerivedCategory.singleFunctor _ n).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y₀)) :=
    L.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ n).app _) ≪≫
      Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
        (smallEtaleRingedToposHom B S hS e.hom) n ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ n).app _).symm
  have h := hom_singleFunctor_structureModule_eq_zero_of_hasTorAmplitude_yoneda B S hS T₀
    (L.obj P) (isPerfect_smallEtaleDerivedModulePullback e.hom P hP) a b
    (hasTorAmplitude_smallEtaleDerivedModulePullback_of_isEtale B S hS e.hom het hsep P a b hamp)
    n hn (L.map t ≫ u.hom)
  have : (smallEtaleDerivedModulePullback B S hS e.hom).IsLeftAdjoint :=
    (smallEtaleDerivedModuleAdjunction B S hS e.hom).isLeftAdjoint
  apply (smallEtaleDerivedModulePullback B S hS e.hom).map_injective
  rw [Functor.map_zero, ← Iso.cancel_iso_hom_right _ _ u, Limits.zero_comp]
  exact h

end AlgebraicGeometry.Space

end
