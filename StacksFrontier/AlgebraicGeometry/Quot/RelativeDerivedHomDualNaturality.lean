module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualStable
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomBaseChangeBijective
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomFunctorConeComparison
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance

/-!
# The naturality step of the proof of Stacks 0DKY

This file proves `AlgebraicGeometry.Space.RelativeDerivedHomDualNaturality`, the naturality in
the test scheme of the identification `Hom(K_T, E_T) = Hom(L_T, 𝒪_T)` of the proof of
Stacks 0DKY, granted the invertibility of the map of Stacks 08JF for perfect sources
(`AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`).

Fix an index `N` large for both the window `a` and the bound `b` of the dual system.  At a test
scheme `T` over `Y`, with `p : X_T ⟶ X`, `f' : X_T ⟶ T` and `q : T ⟶ Y`, write
`R = R𝓗om(K_N, E)` and `D = R𝓗om(L_N, 𝒪_Y) ≅ Rf_* R` (the given isomorphism of systems at `N`).
Each of the following maps is natural in `T` and bijective:

1. `Hom(K_T, E_T) ⟶ Hom(K_{N,T}, E_T)`, composition with `Lp^* c_N` (the window, through the
   Milnor sequence: `AlgebraicGeometry.Space.bijective_pull_coprojection_comp`);
2. `Hom(Lp^*𝒪_X, Lp^*R) ⟶ Hom(K_{N,T}, E_T)` (Stacks 08JF at the perfect `K_N`);
3. `Hom(Lq^*𝒪_Y, Lq^*Rf_*R) ⟶ Hom(Lp^*𝒪_X, Lp^*R)`, pulling back along `f'` and applying the
   counit (Stacks 07A7 at `R`, which is the base change hypothesis);
4. `Hom(Lq^*𝒪_Y, Lq^*D) ⟶ Hom(Lq^*𝒪_Y, Lq^*Rf_*R)`, composition with the isomorphism;
5. `Hom(Lq^*𝒪_Y, Lq^*D) ⟶ Hom(L_{N,T}, 𝒪_T)` (Stacks 08JF at the perfect `L_N`);
6. `Hom(L_T, 𝒪_T) ⟶ Hom(L_{N,T}, 𝒪_T)`, composition with `Lq^* c'_N`
   (`AlgebraicGeometry.Space.bijective_pull_coprojection_comp_structureObject`).

Each is a morphism of relative Hom functors (`CategoryTheory.PullbackData.relHomNatTrans`,
`CategoryTheory.PullbackData.relHomFunctorConeMap`,
`CategoryTheory.PullbackData.relHomPostcompIso`), so the composite of these isomorphisms and their
inverses is the required isomorphism.

## Main results

* `AlgebraicGeometry.Space.relativeDerivedHomDualNaturality_of_pullSheafHom`.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- A morphism of presheaves of sets whose components are bijective is an isomorphism. -/
theorem NatTrans.isIso_of_bijective_app_types.{w} {J : Type*} [Category* J] {F G : J ⥤ Type w}
    (τ : F ⟶ G) (h : ∀ j, Function.Bijective (τ.app j)) : IsIso τ := by
  have : ∀ j, IsIso (τ.app j) := fun j => (isIso_iff_bijective _).2 (h j)
  exact NatIso.isIso_of_isIso_app τ

/-- Conjugating by a comparison, transporting back along a second one and composing with the
images of two fixed morphisms. -/
theorem Functor.comp_transportHom_conjHom_comp {C D₁ D₂ D₃ : Type*} [Category* C] [Category* D₁]
    [Category* D₂] [Category* D₃] {P₁ : C ⥤ D₁} {L : D₁ ⥤ D₂} {P₂ : C ⥤ D₂} {Q : C ⥤ D₃}
    {Lp : D₃ ⥤ D₂} (e₁ : P₂ ≅ P₁ ⋙ L) (e₂ : P₂ ≅ Q ⋙ Lp) {M N : C} {O' R' : D₃}
    (u : O' ⟶ Q.obj M) (v : Q.obj N ⟶ R') (β : P₁.obj M ⟶ P₁.obj N) :
    Lp.map u ≫ Functor.transportHom e₂.symm (Functor.conjHom e₁ β) ≫ Lp.map v =
      (Lp.map u ≫ e₂.inv.app M ≫ e₁.hom.app M) ≫ L.map β ≫
        (e₁.inv.app N ≫ e₂.hom.app N) ≫ Lp.map v := by
  simp only [Functor.transportHom, Functor.conjHom, Iso.symm_hom, Iso.symm_inv, Functor.id_map,
    Category.assoc]

/-- Composing with the image of an identity on the right does not change bijectivity. -/
theorem Functor.bijective_map_comp_comp_map_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A A' B : C} (u : A ⟶ A')
    (h : Function.Bijective (fun x : F.obj A' ⟶ F.obj B => F.map u ≫ x)) :
    Function.Bijective (fun x : F.obj A' ⟶ F.obj B => F.map u ≫ x ≫ F.map (𝟙 B)) := by
  simpa using h

/-- Composing with the image of an identity on the left and an isomorphism on the right is
bijective. -/
theorem Functor.bijective_map_id_comp_comp_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B B' : C} (v : B ≅ B') :
    Function.Bijective (fun x : F.obj A ⟶ F.obj B => F.map (𝟙 A) ≫ x ≫ F.map v.hom) := by
  simp only [Functor.map_id, Category.id_comp]
  exact Functor.bijective_comp_isIso _ _

end CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The projections `X_T ⟶ T` of the base changes, as a morphism from the diagram of the cone of
projections to `X` to that of the test schemes over `Y`. -/
def baseChangeInclusionNatTrans {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (schemesOverToOver Y ⋙ overBaseChangeFunctor f ⋙ Over.forget X) ⟶
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y ⋙ schemeSpaceFunctor B S hS) where
  app T := baseChangeInclusion f T
  naturality _ _ g := baseChangeMap_comp_inclusion f g

/-- Composing with the inverse images of fixed morphisms `u` and `v` gives an isomorphism of
relative Hom functors as soon as it is bijective at each leg of the cone. -/
private theorem nonempty_relHomFunctor_iso_of_bijective_comp {I : Type*} [Category* I]
    {π : I ⥤ AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS} (κ : PullbackData.ConeTo π Y)
    {M' M N N' : derivedModules B S hS Y} (u : M' ⟶ M) (v : N ⟶ N')
    (h : ∀ i, Function.Bijective (fun x : ((smallEtaleDerivedPullbackData B S hS).pull
      (κ.leg i)).obj M ⟶ ((smallEtaleDerivedPullbackData B S hS).pull (κ.leg i)).obj N =>
        ((smallEtaleDerivedPullbackData B S hS).pull (κ.leg i)).map u ≫ x ≫
          ((smallEtaleDerivedPullbackData B S hS).pull (κ.leg i)).map v)) :
    Nonempty (((smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) κ M N) ≅
      (smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) κ M' N') :=
  let τ := (smallEtaleDerivedPullbackData B S hS).relHomNatTrans
      (smallEtaleDerivedPullbackData_isCoherent B S hS) κ
      (fun q α => ((smallEtaleDerivedPullbackData B S hS).pull q).map u ≫ α ≫
        ((smallEtaleDerivedPullbackData B S hS).pull q).map v)
      ((smallEtaleDerivedPullbackData B S hS).isTriangleNatural_comp u v)
  have := NatTrans.isIso_of_bijective_app_types τ (fun i => h i.unop)
  ⟨asIso τ⟩

/-- Stacks 08JF for a perfect source gives an isomorphism of relative Hom functors. -/
private theorem nonempty_relHomFunctor_iso_pullHomOfSections
    (hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS) {I : Type*} [Category* I]
    {π : I ⥤ AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS} (κ : PullbackData.ConeTo π Z)
    (P M : derivedModules B S hS Z) (hP : ∀ {T : AlgebraicSpaces B S hS} (q : T ⟶ Z),
      IsIso (pullSheafHomComparison q P M)) :
    Nonempty (((smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) κ (structureObject B S hS Z)
        (((smallEtaleDerivedSheafHom B S hS Z).obj (op P)).obj M)) ≅
      (smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) κ P M) :=
  let τ := (smallEtaleDerivedPullbackData B S hS).relHomNatTrans
    (smallEtaleDerivedPullbackData_isCoherent B S hS) κ
    (fun q γ => pullHomOfSections q P M γ) (isTriangleNatural_pullHomOfSections hc P M)
  have := NatTrans.isIso_of_bijective_app_types τ
    (fun _ => bijective_pullHomOfSections _ P M (hP _))
  ⟨asIso τ⟩

variable (B S hS) in
/-- **The naturality step of the proof of Stacks 0DKY**,
`AlgebraicGeometry.Space.RelativeDerivedHomDualNaturality`, granted Stacks 08JF for perfect
sources (`AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`, not yet proved here).

The isomorphism is the composite, at one index `N` large for both the window and the bound of
the dual system, of six bijective morphisms of relative Hom functors: the two stabilizations
(`AlgebraicGeometry.Space.bijective_pull_coprojection_comp` and
`AlgebraicGeometry.Space.bijective_pull_coprojection_comp_structureObject`), Stacks 08JF at
`K_N` and at `L_N` (`AlgebraicGeometry.Space.bijective_pullHomOfSections`), the base change of
Stacks 07A7 at `R𝓗om(K_N, E)` (`AlgebraicGeometry.Space.bijective_pullBaseChangeRelHom`) and
the given isomorphism `R𝓗om(L_N, 𝒪_Y) ≅ Rf_* R𝓗om(K_N, E)`. -/
theorem relativeDerivedHomDualNaturality_of_pullSheafHom
    (hH : PullSheafHomComparisonIsIso B S hS) : RelativeDerivedHomDualNaturality B S hS := by
  intro hZ X Y f _ _ _ hflat hfp K E _ _ F c hF _ hFK G L c' hG hb _ θ hbc hwin
  obtain ⟨b, hb⟩ := hb
  obtain ⟨a, hwin⟩ := hwin
  have := hasColimitsOfShape_discrete_nat_derivedModules B S hS X
  have hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS :=
    fun f g => smallEtaleDerivedPullbackData_compIso_eq B S hS f g
  -- the index
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, 1 ≤ a + (N : ℤ) ∧ (b - (N : ℤ)) + 2 ≤ 0 := by
    refine ⟨(max (b + 2) (1 - a)).toNat, ?_, ?_⟩ <;>
    · have h1 := Int.self_le_toNat (max (b + 2) (1 - a))
      have h2 := le_max_left (b + 2) (1 - a)
      have h3 := le_max_right (b + 2) (1 - a)
      omega
  let R := ((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj N))).obj E
  let ι : ((smallEtaleDerivedSheafHom B S hS Y).obj (op (G.obj N))).obj
      (structureObject B S hS Y) ≅ (derivedModulesPushforward f).obj R :=
    θ.app (op N) ≪≫ eqToIso (congrArg (fun Φ => Φ.obj R)
      (derivedPushforward_eq_spaceDerivedPushforward B S hS f).symm)
  -- (1) the stabilization of `Hom(K_T, E_T)`
  obtain ⟨e₁⟩ := nonempty_relHomFunctor_iso_of_bijective_comp
    ((overBaseChangeCone f).restrict (schemesOverToOver Y)) (c N) (𝟙 E) (fun T =>
    Functor.bijective_map_comp_comp_map_id
      ((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)) (c N)
      (bijective_pull_coprojection_comp (baseChangeProjection f T) (baseChangeInclusion f T)
        F K c hFK _ a (fun n i hi => hwin n _ _ _ (isPullback_baseChangeSpace f T) i hi) N hN1))
  -- (2) Stacks 08JF at `K_N`
  obtain ⟨e₂⟩ := nonempty_relHomFunctor_iso_pullHomOfSections hc
    ((overBaseChangeCone f).restrict (schemesOverToOver Y)) (F.obj N) E
    (fun q => hH q _ _ (hF N))
  -- (3) the base change at `R𝓗om(K_N, E)`
  let τ₃ := (smallEtaleDerivedPullbackData B S hS).relHomFunctorConeMap
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (((overBaseChangeCone f).restrict (schemesOverToOver Y)).postcomp f) (schemesOverCone Y)
      (baseChangeInclusionNatTrans f) (fun T => (isPullback_baseChangeSpace f T).w.symm)
      (structureObject B S hS Y) ((derivedModulesPushforward f).obj R) ≫
    ((smallEtaleDerivedPullbackData B S hS).relHomPostcompIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      ((overBaseChangeCone f).restrict (schemesOverToOver Y)) f (structureObject B S hS Y)
      ((derivedModulesPushforward f).obj R)).inv ≫
    (smallEtaleDerivedPullbackData B S hS).relHomNatTrans
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      ((overBaseChangeCone f).restrict (schemesOverToOver Y))
      (fun q α => ((smallEtaleDerivedPullbackData B S hS).pull q).map
          (smallEtaleDerivedPullStructureIso B S hS f).inv ≫ α ≫
        ((smallEtaleDerivedPullbackData B S hS).pull q).map
          ((derivedModulesAdjunction f).counit.app R))
      ((smallEtaleDerivedPullbackData B S hS).isTriangleNatural_comp
        (smallEtaleDerivedPullStructureIso B S hS f).inv
        ((derivedModulesAdjunction f).counit.app R))
  have i₃ : IsIso τ₃ := NatTrans.isIso_of_bijective_app_types τ₃ (fun ⟨T⟩ => by
    have key := bijective_pullBaseChangeRelHom hc f T.hom (baseChangeInclusion f T)
      (baseChangeProjection f T) (isPullback_baseChangeSpace f T).w R
      (hbc N _ _ _ (isPullback_baseChangeSpace f T))
      (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)).mapIso
          (smallEtaleDerivedPullStructureIso B S hS f).symm ≪≫
        ((smallEtaleDerivedPullbackData B S hS).triangle
          (rfl : baseChangeProjection f T ≫ f = baseChangeProjection f T ≫ f)).symm.app
            (structureObject B S hS Y) ≪≫
        ((smallEtaleDerivedPullbackData B S hS).triangle
          (isPullback_baseChangeSpace f T).w.symm).app (structureObject B S hS Y))
    exact (congrArg Function.Bijective (funext fun β =>
      Functor.comp_transportHom_conjHom_comp
        ((smallEtaleDerivedPullbackData B S hS).triangle (isPullback_baseChangeSpace f T).w.symm)
        ((smallEtaleDerivedPullbackData B S hS).triangle
          (rfl : baseChangeProjection f T ≫ f = baseChangeProjection f T ≫ f))
        (smallEtaleDerivedPullStructureIso B S hS f).inv
        ((derivedModulesAdjunction f).counit.app R) β)).mpr key)
  -- (4) the given isomorphism `R𝓗om(L_N, 𝒪_Y) ≅ Rf_* R𝓗om(K_N, E)`
  obtain ⟨e₄⟩ := nonempty_relHomFunctor_iso_of_bijective_comp (schemesOverCone Y)
    (𝟙 (structureObject B S hS Y)) ι.hom (fun T =>
    Functor.bijective_map_id_comp_comp_map
      ((smallEtaleDerivedPullbackData B S hS).pull T.hom) ι)
  -- (5) Stacks 08JF at `L_N`
  obtain ⟨e₅⟩ := nonempty_relHomFunctor_iso_pullHomOfSections hc (schemesOverCone Y)
    (G.obj N) (structureObject B S hS Y) (fun q => hH q _ _ (hG N))
  -- (6) the stabilization of `Hom(L_T, 𝒪_T)`
  obtain ⟨e₆⟩ := nonempty_relHomFunctor_iso_of_bijective_comp (schemesOverCone Y) (c' N)
    (𝟙 (structureObject B S hS Y)) (fun T =>
    Functor.bijective_map_comp_comp_map_id ((smallEtaleDerivedPullbackData B S hS).pull T.hom)
      (c' N) (bijective_pull_coprojection_comp_structureObject T.hom (c' N) (b - N) hN2
        (fun i hi => hb N i hi)))
  exact ⟨(PullbackData.relHomFunctorRestrictIso (smallEtaleDerivedPullbackData B S hS)
      (smallEtaleDerivedPullbackData_isCoherent B S hS) (overBaseChangeCone f)
      (schemesOverToOver Y) K E).symm ≪≫ e₁ ≪≫ e₂.symm ≪≫ (asIso τ₃).symm ≪≫
    e₄.symm ≪≫ e₅ ≪≫ e₆.symm⟩

end AlgebraicGeometry.Space

end
