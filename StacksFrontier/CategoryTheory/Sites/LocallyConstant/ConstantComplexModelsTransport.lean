module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexInduction

/-!
# Local models by constant complexes on a site of arbitrary size

This file states Tag 094G for a site whose objects, morphisms and coefficient ring lie in three
unrelated universes `u`, `v` and `r`, with the sections taken in the universe `max u v r`
containing all three, sheafification assumed outright and the covering family indexed in the
universe of the sections.

## Main results

* `Stacks.ConstantSheaf.exists_cover_constantComplex_representation'`: **Stacks 094G** for a site
  of arbitrary size.

## Implementation notes

The statement is reached from the *small* instance of
`Stacks.ConstantSheaf.exists_cover_constantComplex_representation`, proved in
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/BoundedComplexInduction.lean`, the one in which
the site and the ring already live in the universe of the sections. So the work here is the
transport of the conclusion along a small model of the site and a small model of the ring. Both
models are free of hypotheses, which is why
the general statement carries no smallness binder: a category with objects in `Type u` and
morphisms in `Type v` is `Small.{max u v r}` and `LocallySmall.{max u v r}`, hence
`EssentiallySmall.{max u v r}`, and a ring in `Type r` is `Small.{max u v r}`. So
`CategoryTheory.SmallModel` of the site and `Shrink` of the ring are a small site and a ring in
the single universe `max u v r`, which is exactly the diagonal the small-site statement needs.

The two models are transported separately: the ring along `CategoryTheory.sheafCompose` for the
restriction of scalars of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`, which is an
equivalence of coefficient categories, and the site along
`CategoryTheory.Equivalence.sheafCongr`, which needs no hypothesis on the coefficients at all.
Their composite is an additive equivalence of the sheaf categories, so it induces an equivalence
of derived categories, carries bounded objects to bounded objects, and commutes with cohomology;
the only computations are the comparison of the constant sheaf functors across each of the two
equivalences, and the same comparison on the slices, where the slice of the site equivalence is
again an equivalence of sites.

Pullbacks in the site are used only to move a local trivialization of a sheaf along a morphism of
the base while transporting local constancy across the site equivalence; the two consumers of
Tag 094G in `ConnectedConstantModels.lean` already assume them.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe m v u r v₂ u₂

attribute [local instance] HasDerivedCategory.standard

-- Restricting a sheaf to a slice, reindexing it along an equivalence of sites, and composing it
-- with an equivalence of coefficient categories are all precomposition with a functor on
-- presheaves, so the two ways of restricting a transported sheaf to a transported object agree
-- definitionally; the identifications go through these names, which are made transparent to
-- unification here.
attribute [local implicit_reducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.sheafPushforwardContinuous
  CategoryTheory.Equivalence.sheafCongr CategoryTheory.Equivalence.sheafCongr.functor

/-! ### Sheafification of module-valued presheaves -/

/-- The forgetful functor of modules preserves filtered colimits as soon as the ring fits in the
module universe. -/
private lemma forgetModule_preservesFilteredColimits (R : Type r) [Ring R] [Small.{m} R] :
    PreservesFilteredColimits (forget (ModuleCat.{m} R)) := by
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (Shrink.ringEquiv R : Shrink.{m} R ≃+* R)
  change PreservesFilteredColimits (e.functor ⋙ forget (ModuleCat.{m} (Shrink.{m} R)))
  infer_instance

/-- Module-valued presheaves on a site can be sheafified in any module universe containing both
the site and the ring: both the site and the ring have a small model there. -/
public lemma hasSheafifyModuleCatOfSmall {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type r) [Ring R] [UnivLE.{max u v, m}] [Small.{m} R] :
    HasSheafify J (ModuleCat.{m} R) := by
  let := forgetModule_preservesFilteredColimits.{m} R
  have : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget (ModuleCat.{m} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{m, m} _
  infer_instance

/-! ### Transport along an equivalence of coefficient categories -/

/-- Composing with an equivalence of coefficient categories is an equivalence of sheaf
categories. -/
private lemma isEquivalence_sheafCompose {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A D : Type*} [Category* A] [Category* D] (F : A ⥤ D) [F.IsEquivalence]
    [J.HasSheafCompose F] [J.HasSheafCompose F.inv] :
    (sheafCompose J F).IsEquivalence := by
  have : (sheafCompose J F).EssSurj := by
    refine ⟨fun G => ⟨(sheafCompose J F.inv).obj G, ?_⟩⟩
    exact ⟨ObjectProperty.isoMk _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G.obj F.asEquivalence.counitIso ≪≫
      Functor.rightUnitor G.obj)⟩
  exact { }

/-! ### Exact functors on derived categories -/

/-- An exact functor commutes with the cohomology of an object of the derived category. -/
private noncomputable def exactFunctorDerivedHomologyIso {A D : Type*} [Category* A] [Category* D]
    [Abelian A] [Abelian D] (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor A n).obj K) :=
  let T := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj T ≅ K := DerivedCategory.Q.objObjPreimageIso K
  (DerivedCategory.homologyFunctor D n).mapIso
      (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app T) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app _ ≪≫
    (T.sc n).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors A n).app T).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor A n).mapIso e)

/-- An exact functor carries a bounded object of the derived category to a bounded object. -/
private lemma isGE_isLE_mapDerivedCategory {A D : Type*} [Category* A] [Category* D]
    [Abelian A] [Abelian D] (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory.Bounded A) :
    (∃ a : ℤ, (F.mapDerivedCategory.obj K.obj).IsGE a) ∧
      (∃ b : ℤ, (F.mapDerivedCategory.obj K.obj).IsLE b) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property
  refine ⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr (fun n hn => ?_)⟩,
    ⟨b, (DerivedCategory.isLE_iff _ b).mpr (fun n hn => ?_)⟩⟩
  · exact (F.map_isZero ((DerivedCategory.isGE_iff K.obj a).mp ha n hn)).of_iso
      (exactFunctorDerivedHomologyIso F K.obj n)
  · exact (F.map_isZero ((DerivedCategory.isLE_iff K.obj b).mp hb n hn)).of_iso
      (exactFunctorDerivedHomologyIso F K.obj n)

/-- An additive equivalence of abelian categories induces an equivalence of derived
categories. -/
private lemma isEquivalence_mapDerivedCategoryOfEquivalence {A D : Type*} [Category* A]
    [Abelian A] [HasDerivedCategory A] [Category* D] [Abelian D] [HasDerivedCategory D]
    (e : A ≌ D) [e.functor.Additive] : e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let : Φ.functor.IsEquivalence :=
    (e.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : Φ.IsInduced := ⟨by
    ext X Y f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f e.functor⟩
  let : Φ.IsLocalizedEquivalence := Φ.isLocalizedEquivalence_of_isInduced
  let : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q
      e.functor.mapDerivedCategory := ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory

/-! ### Transport along an equivalence of sites -/

/-- The localization of an equivalence of sites at an object is again an equivalence of sites. -/
private lemma overPostIsDenseSubsite {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (L : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsDenseSubsite J L] (X : C) :
    (Over.post (X := X) e.functor).IsDenseSubsite (J.over X) (L.over (e.functor.obj X)) := by
  let : (Over.post (X := X) e.functor).IsEquivalence :=
    (Over.postEquiv (X := X) e).isEquivalence_functor
  refine { functorPushforward_mem_iff := ?_ }
  intro Z S
  constructor
  · intro hS
    have hh := (Over.post e.functor).cover_lift (J.over X) (L.over _) hS
    rwa [(Sieve.fullyFaithfulFunctorGaloisCoinsertion (Over.post e.functor) Z).u_l_eq] at hh
  · exact (Functor.IsDenseSubsite.coverPreserving J L e.functor).overPost X |>.cover_preserve

attribute [local instance] overPostIsDenseSubsite

/-- The constant sheaf functor commutes with the pushforward along a continuous left adjoint
whose right adjoint is continuous as well. -/
private noncomputable def pushforwardConstantSheafIso {C : Type*} [Category* C] {D : Type*}
    [Category* D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.IsContinuous J K] [G.IsContinuous K J]
    {T : D} (hT : IsTerminal T) :
    constantSheaf K A ⋙ F.sheafPushforwardContinuous A J K ≅ constantSheaf J A := by
  let := adj.isRightAdjoint
  exact ((constantSheafAdj K A hT).comp (adj.sheafPushforwardContinuous J K)).leftAdjointUniq
    (constantSheafAdj J A (hT.isTerminalObj G T))

/-- Restricting a constant sheaf on a slice along a morphism of the base gives the constant sheaf
with the same value. -/
private noncomputable def constantSheafOverMapPullbackIso {C : Type*} [Category* C]
    [HasPullbacks C] (J : GrothendieckTopology C) (A : Type*) [Category* A] {U V : C}
    [HasWeakSheafify (J.over U) A] [HasWeakSheafify (J.over V) A] (f : V ⟶ U) (M : A) :
    (J.overMapPullback A f).obj ((constantSheaf (J.over U) A).obj M) ≅
      (constantSheaf (J.over V) A).obj M :=
  (pushforwardConstantSheafIso (J.over V) (J.over U) A (Over.mapPullbackAdj f)
    (Over.mkIdTerminal (X := U))).app M

/-- The constant sheaf functor on the slices of an equivalence of sites commutes with the
pushforward along the localized equivalence. -/
private noncomputable def overPostConstantSheafIso {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (L : GrothendieckTopology D) (e : C ≌ D)
    [e.functor.IsDenseSubsite J L] (A : Type*) [Category* A] (X : C)
    [HasWeakSheafify (J.over X) A] [HasWeakSheafify (L.over (e.functor.obj X)) A] :
    constantSheaf (L.over (e.functor.obj X)) A ⋙
      (Over.post (X := X) e.functor).sheafPushforwardContinuous A (J.over X)
        (L.over (e.functor.obj X)) ≅ constantSheaf (J.over X) A :=
  let ep := Over.postEquiv (X := X) e
  let : ep.functor.IsDenseSubsite (J.over X) (L.over _) := overPostIsDenseSubsite J L e X
  let : ep.symm.inverse.IsDenseSubsite (J.over X) (L.over _) :=
    inferInstanceAs (ep.functor.IsDenseSubsite _ _)
  let : ep.inverse.IsDenseSubsite (L.over _) (J.over X) :=
    inferInstanceAs (ep.symm.functor.IsDenseSubsite _ _)
  pushforwardConstantSheafIso (J.over X) (L.over _) A ep.toAdjunction
    (Over.mkIdTerminal (X := e.functor.obj X))

/-! ### Transport of local constancy of finite type -/

/-- Local constancy of finite type is invariant under isomorphism of sheaves. -/
private lemma finiteTypeLocallyConstantModuleSheaf_of_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type*) [CommRing R]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v m} R)]
    {F G : Sheaf J (ModuleCat.{max u v m} R)} (e : F ≅ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, m} J R F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, m} J R G := by
  intro X
  obtain ⟨I, V, f, hcov, h⟩ := hF X
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h i
  exact ⟨M, hM, ⟨eM ≪≫ (J.overPullback (ModuleCat.{max u v m} R) (V i)).mapIso e⟩⟩

/-- Restriction of scalars along an isomorphism of rings preserves finite generation. -/
private lemma isFG_restrictScalars {R S : Type*} [CommRing R] [CommRing S] (ε : R ≃+* S)
    (M : ModuleCat.{m} S) (hM : ModuleCat.isFG S M) :
    ModuleCat.isFG R ((ModuleCat.restrictScalars ε.toRingHom).obj M) := by
  let : Module.Finite S M := hM
  let g : (ModuleCat.restrictScalars ε.toRingHom).obj M →ₛₗ[ε.toRingHom] M :=
    { toFun := id, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  let : RingHomSurjective ε.toRingHom := ⟨ε.surjective⟩
  exact (g.finite_iff_of_bijective Function.bijective_id).mpr hM

/-- Local constancy of finite type is carried along the restriction of scalars of an isomorphism
of coefficient rings. -/
private lemma finiteTypeLocallyConstantModuleSheaf_restrictScalars {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {S : Type r} [CommRing S] {R : Type (max u v r)} [CommRing R]
    (ε : R ≃+* S)
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v r} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v r} S)]
    (F : Sheaf J (ModuleCat.{max u v r} S))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J S F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J R
      ((sheafCompose J (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε :
        ModuleCat.{max u v r} S ≌ ModuleCat.{max u v r} R).functor).obj F) := by
  intro X
  obtain ⟨I, V, f, hcov, h⟩ := hF X
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨M, hM, ⟨a⟩⟩ := h i
  let E : ModuleCat.{max u v r} S ≌ ModuleCat.{max u v r} R :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε
  let : (J.over (V i)).PreservesSheafification E.functor :=
    Sheaf.preservesSheafification_of_adjunction _ E.toAdjunction
  exact ⟨E.functor.obj M, isFG_restrictScalars ε M hM,
    ⟨((constantCommuteCompose (J.over (V i)) E.functor).app M).symm ≪≫
      (sheafCompose (J.over (V i)) E.functor).mapIso a⟩⟩

/-- Local constancy of finite type is carried from a site to a small model of it, along the
pushforward of the equivalence. -/
private lemma finiteTypeLocallyConstantModuleSheaf_pushforward_smallModel {C : Type u}
    [Category.{v} C] [HasPullbacks C] (J : GrothendieckTopology C) {D : Type (max u v r)}
    [SmallCategory D] (L : GrothendieckTopology D) (e : D ≌ C)
    [e.functor.IsDenseSubsite L J] (R : Type (max u v r)) [CommRing R]
    [HasSheafify J (ModuleCat.{max u v r} R)]
    [HasSheafify L (ModuleCat.{max u v r} R)]
    [∀ V : D, HasWeakSheafify (L.over V) (ModuleCat.{max u v r} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v r} R)]
    (F : Sheaf J (ModuleCat.{max u v r} R))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J R F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{max u v r, max u v r, max u v r} L R
      ((e.functor.sheafPushforwardContinuous (ModuleCat.{max u v r} R) L J).obj F) := by
  intro Y
  obtain ⟨I, V, f, hf, hV⟩ := hF (e.functor.obj Y)
  let S := (Sieve.ofArrows V f).functorPullback e.functor
  have hS : S ∈ L Y := e.functor.cover_lift L J hf
  refine ⟨S.arrows.category, fun g => g.obj.left, fun g => g.obj.hom,
    by simpa only [Sieve.ofArrows_category] using hS, fun g => ?_⟩
  obtain ⟨i, k, hk⟩ := Sieve.ofArrows.exists g.property
  obtain ⟨M, hM, ⟨a⟩⟩ := hV i
  let b := (constantSheafOverMapPullbackIso J (ModuleCat.{max u v r} R) k M).symm ≪≫
    (J.overMapPullback (ModuleCat.{max u v r} R) k).mapIso a ≪≫ F.pushforwardOverMapIso k
  let G := (Over.post (X := g.obj.left) e.functor).sheafPushforwardContinuous
    (ModuleCat.{max u v r} R) (L.over g.obj.left) (J.over (e.functor.obj g.obj.left))
  let c := overPostConstantSheafIso L J e (ModuleCat.{max u v r} R) g.obj.left
  exact ⟨M, hM, ⟨(c.app M).symm ≪≫ G.mapIso b ≪≫ Iso.refl _⟩⟩

/-! ### Tag 094G on a site of arbitrary size -/

/-- **Stacks 094G, the general case on a site of arbitrary size.** A bounded object of the derived
category of sheaves of `Λ`-modules whose cohomology sheaves are locally constant of finite type is,
over the members of a covering family, the constant complex attached to a bounded complex of
finite `Λ`-modules. The sections are taken in the universe containing the site and `Λ`. -/
theorem exists_cover_constantComplex_representation'
    {C : Type u} [Category.{v} C] [HasPullbacks C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify J (ModuleCat.{max u v r} Λ)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{max u v r} Λ)]
    (X : C)
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{max u v r} Λ)))
    (hK : ∀ n : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, r} J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v r} Λ)) n).obj K.obj)) :
    ∃ (T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T)
      (I : Type (max u v r)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
        ∀ i, ∃ (P : CochainComplex (ModuleCat.{max u v r} Λ) ℤ) (a b : ℤ),
          (∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) ∧
          (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
          Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v r} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
            DerivedCategory.Q.obj
              (((constantSheaf (J.over (U i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
  classical
  have hsC : Small.{max u v r} C := small_max.{max u v r} C
  have hlC : LocallySmall.{max u v r} C := CategoryTheory.locallySmall_max.{max u v r, v, u}
  have hsΛ : Small.{max u v r} Λ := small_max.{max u v r} Λ
  have hle : UnivLE.{max u v, max u v r} := univLE_max.{max u v, r}
  let D := SmallModel.{max u v r} C
  let e : C ≌ D := equivSmallModel.{max u v r} C
  let L : GrothendieckTopology D := e.inverse.inducedTopology J
  have hds : e.symm.functor.IsDenseSubsite L J :=
    inferInstanceAs (e.inverse.IsDenseSubsite L J)
  let Λ' := Shrink.{max u v r} Λ
  let er : Λ' ≃+* Λ := Shrink.ringEquiv Λ
  let E : ModuleCat.{max u v r} Λ ≌ ModuleCat.{max u v r} Λ' :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv er
  have hNoeth : IsNoetherianRing Λ' := isNoetherianRing_of_ringEquiv Λ er.symm
  have hJΛ' : HasSheafify J (ModuleCat.{max u v r} Λ') :=
    hasSheafifyModuleCatOfSmall.{max u v r} J Λ'
  have hJoΛ' : ∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v r} Λ') := fun U =>
    (hasSheafifyModuleCatOfSmall.{max u v r} (J.over U) Λ').isRightAdjoint
  have hLΛ' : HasSheafify L (ModuleCat.{max u v r} Λ') :=
    hasSheafifyModuleCatOfSmall.{max u v r} L Λ'
  have hLoΛ' : ∀ V : D, HasWeakSheafify (L.over V) (ModuleCat.{max u v r} Λ') := fun V =>
    (hasSheafifyModuleCatOfSmall.{max u v r} (L.over V) Λ').isRightAdjoint
  let Hc := sheafCompose J E.functor
  let Es := e.sheafCongr J L (ModuleCat.{max u v r} Λ')
  let H := Hc ⋙ Es.functor
  have hHcEq : Hc.IsEquivalence := isEquivalence_sheafCompose J E.functor
  have hHadd : H.Additive := { map_add := by intros; rfl }
  have hHeq : H.IsEquivalence := inferInstance
  have hHlim : PreservesFiniteLimits H := inferInstance
  have hHcolim : PreservesFiniteColimits H := inferInstance
  have hHK : ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModuleSheaf.{max u v r, max u v r, max u v r} L Λ'
        ((DerivedCategory.homologyFunctor (Sheaf L (ModuleCat.{max u v r} Λ')) n).obj
          (H.mapDerivedCategory.obj K.obj)) := fun n =>
    finiteTypeLocallyConstantModuleSheaf_of_iso L Λ'
      (exactFunctorDerivedHomologyIso H K.obj n).symm
      (finiteTypeLocallyConstantModuleSheaf_pushforward_smallModel J L e.symm Λ' _
        (finiteTypeLocallyConstantModuleSheaf_restrictScalars J er _ (hK n)))
  let K' : DerivedCategory.Bounded (Sheaf L (ModuleCat.{max u v r} Λ')) :=
    ⟨H.mapDerivedCategory.obj K.obj, isGE_isLE_mapDerivedCategory H K⟩
  obtain ⟨T', ⟨a'⟩, I, U, f, hf, hU⟩ :=
    exists_cover_constantComplex_representation.{max u v r, max u v r, max u v r}
      L Λ' (e.functor.obj X) K' hHK
  let T : CochainComplex (Sheaf J (ModuleCat.{max u v r} Λ)) ℤ :=
    (DerivedCategory.Q (C := Sheaf J (ModuleCat.{max u v r} Λ))).objPreimage K.obj
  let a : K.obj ≅ DerivedCategory.Q.obj T :=
    ((DerivedCategory.Q (C := Sheaf J (ModuleCat.{max u v r} Λ))).objObjPreimageIso K.obj).symm
  let t : DerivedCategory.Q.obj ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj T' :=
    (H.mapDerivedCategoryFactors.app T).symm ≪≫ H.mapDerivedCategory.mapIso a.symm ≪≫ a'
  let U' (i : I) := e.inverse.obj (U i)
  let f' (i : I) : U' i ⟶ X := e.inverse.map (f i) ≫ e.unitInv.app X
  refine ⟨T, a, I, U', f', ?_, ?_⟩
  · have hcov := (Functor.IsDenseSubsite.coverPreserving L J e.inverse).cover_preserve hf
    rw [Sieve.functorPushforward_ofArrows] at hcov
    apply J.superset_covering ?_ (J.pullback_stable (e.unit.app X) hcov)
    intro Y g hg
    obtain ⟨i, k, hk⟩ := Sieve.ofArrows.exists hg
    convert (Sieve.ofArrows U' f').downward_closed (Sieve.ofArrows_mk U' f' i) k using 1
    · dsimp [f']
    · rw [← Category.assoc, ← hk]
      simp
  · intro i
    obtain ⟨P, lo, hi, hvan, hfg, ⟨hp⟩⟩ := hU i
    let ep := Over.postEquiv (X := U i) e.symm
    have : ep.symm.inverse.IsDenseSubsite (L.over (U i)) (J.over (U' i)) :=
      overPostIsDenseSubsite L J e.symm _
    let El := ep.symm.sheafCongr (J.over (U' i)) (L.over (U i)) (ModuleCat.{max u v r} Λ')
    let Hcl := sheafCompose (J.over (U' i)) E.functor
    let Hl := Hcl ⋙ El.functor
    have hHclEq : Hcl.IsEquivalence := isEquivalence_sheafCompose (J.over (U' i)) E.functor
    have hHlAdd : Hl.Additive := { map_add := by intros; rfl }
    have hHlZero : Hl.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive Hl
    have hHlEq : Hl.IsEquivalence := inferInstance
    have hHlAdd' : Hl.asEquivalence.functor.Additive := hHlAdd
    have hHlDer : Hl.mapDerivedCategory.IsEquivalence :=
      isEquivalence_mapDerivedCategoryOfEquivalence Hl.asEquivalence
    let G := L.overPullback (ModuleCat.{max u v r} Λ') (U i)
    have hGadd : G.Additive := { map_add := by intros; rfl }
    have hGzero : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
    have hGadj : G.IsLeftAdjoint :=
      ((Over.forget (U i)).sheafAdjunctionCocontinuous _ _ _).isLeftAdjoint
    let isoLocal := (G.mapDerivedCategoryFactors.app _).symm ≪≫
      G.mapDerivedCategory.mapIso t ≪≫ G.mapDerivedCategoryFactors.app T' ≪≫ hp
    have hps : (J.over (U' i)).PreservesSheafification E.functor :=
      Sheaf.preservesSheafification_of_adjunction _ E.toAdjunction
    let c := constantCommuteCompose (J.over (U' i)) E.functor
    let cs := overPostConstantSheafIso L J e.symm (ModuleCat.{max u v r} Λ') (U i)
    let ctot : constantSheaf (J.over (U' i)) (ModuleCat.{max u v r} Λ) ⋙ Hl ≅
        E.functor ⋙ constantSheaf (L.over (U i)) (ModuleCat.{max u v r} Λ') :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight c El.functor ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft E.functor cs
    let Pc := (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
    let pc := (NatIso.mapHomologicalComplex E.counitIso (ComplexShape.up ℤ)).app P
    let targetIso := Hl.mapDerivedCategoryFactors.app
        (((constantSheaf (J.over (U' i)) (ModuleCat.{max u v r} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Pc) ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex ctot (ComplexShape.up ℤ)).app Pc) ≪≫
      DerivedCategory.Q.mapIso
        (((constantSheaf (L.over (U i)) (ModuleCat.{max u v r} Λ')).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso pc)
    refine ⟨Pc, lo, hi, fun n hn => E.inverse.map_isZero (hvan n hn),
      fun n => isFG_restrictScalars er.symm (P.X n) (hfg n), ?_⟩
    refine ⟨Hl.mapDerivedCategory.preimageIso (?_ ≪≫ isoLocal ≪≫ targetIso.symm)⟩
    exact Hl.mapDerivedCategoryFactors.app _

end Stacks.ConstantSheaf

end
