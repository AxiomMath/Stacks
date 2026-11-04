module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPullbackSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorMonoidalOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualLeftDual
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable
public import StacksFrontier.CategoryTheory.Functor.BifunctorEvaluationTransport

/-!
# Stacks 08JF for algebraic spaces: the comparison is invertible out of a perfect object

Let `g : X ⟶ Y` be a morphism of algebraic spaces, `P` a perfect and `M` an arbitrary object of
`D(𝒪_Y)`. The canonical map `Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` of Stacks 08JF
(`AlgebraicGeometry.Space.pullSheafHomComparison`) is an isomorphism.

The proof is the source's: a perfect object is dualizable (Stacks 0FPU), a monoidal functor
carries an internal Hom out of a dualizable object to an internal Hom
(`CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map`), and the map of Stacks 08JF
is the comparison of the two evaluations. It is run on the equi-universe models of the small
étale ringed sites, where the derived pullback along the morphism of models `g_m`
(`AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom`) is a monoidal functor
(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorMonoidal`), with the derived
tensor product of `Stacks.SheafOfModules` for its tensor product on the nose and the inverse of
the comparison of Stacks 07A4 for its tensorator: the derived internal Homs and the evaluations of
`X` and `Y` are carried to the models by the derived equivalences, and the comparison of
Stacks 07A4 along `g` to the one along `g_m`
(`AlgebraicGeometry.Space.smallEtaleModelDerivedPullbackSquareIso_tensor`).

## Main results

* `AlgebraicGeometry.Space.pullSheafHomComparisonIsIso`: **Stacks 08JF, the invertibility for a
  perfect source**, `AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification `smallEtaleModelDerivedTensorIso` of the derived tensor products of `Z`
and of its model, with the derived tensor product of the model spelled at the ringed site of its
ringed topos, which is the spelling of the comparisons of Stacks 07A4 along morphisms of models. -/
def smallEtaleModelDerivedTensorIsoTopos (Z : AlgebraicSpaces B S hS) :
    Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z) ⋙
        (smallEtaleModelDerivedEquivalence B S hS Z).functor ≅
      (smallEtaleModelDerivedEquivalence B S hS Z).functor.prod
          (smallEtaleModelDerivedEquivalence B S hS Z).functor ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS Z.1 Z.2).toRingedTopos.toRingedSite) :=
  smallEtaleModelDerivedTensorIso B S hS Z

/-- **The derived internal Hom of an algebraic space, read on its model, is an internal Hom**
for the derived tensor product of `Stacks.SheafOfModules` on the model: the evaluation
`R𝓗om(P, M) ⊗^L P ⟶ M` of Stacks 08J8, carried along the derived equivalence and the
identification of the derived tensor products. -/
theorem bijective_smallEtaleModelEvaluation (Z : AlgebraicSpaces B S hS)
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (W : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS Z.1 Z.2).O))) :
    Function.Bijective fun x : W ⟶ (smallEtaleModelDerivedEquivalence B S hS Z).functor.obj
        (((smallEtaleDerivedSheafHom B S hS Z).obj (op P)).obj M) =>
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS Z.1 Z.2).toRingedTopos.toRingedSite).map x).app
          ((smallEtaleModelDerivedEquivalence B S hS Z).functor.obj P) ≫
        (smallEtaleModelDerivedTensorIsoTopos Z).inv.app
          (((smallEtaleDerivedSheafHom B S hS Z).obj (op P)).obj M, P) ≫
        (smallEtaleModelDerivedEquivalence B S hS Z).functor.map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Z P).counit.app M) := by
  refine bijective_map_app_comp_transport_equivalence _ (smallEtaleDerivedTensor B S hS Z) _
    (smallEtaleModelDerivedTensorIsoTopos Z) _ (fun V => ?_) W
  have key : (fun x : V ⟶ ((smallEtaleDerivedSheafHom B S hS Z).obj (op P)).obj M =>
      ((smallEtaleDerivedTensor B S hS Z).map x).app P ≫
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS Z P).counit.app M) =
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Z P).homEquiv V M).symm := by
    funext x
    rw [Adjunction.homEquiv_counit]
    rfl
  rw [key]
  exact Equiv.bijective _

/-- **The arrow algebra of Stacks 08JF on the models.** With the comparison `c` of the two
derived pullbacks, the identifications `τ` of derived tensor products downstairs and upstairs, a
transpose `ψ` of `α_g⁻¹ ≫ Lg^*(ev)` and the square `hC` of Stacks 07A4 along `g` and `g_m`:
whiskering `c ≫ e_X ψ` and evaluating on the model of `X` is the inverse of the comparison of
Stacks 07A4 along `g_m` followed by `g_m` of the evaluation on the model of `Y`. -/
theorem whiskerRight_comp_evaluation_chase {𝒟Y 𝒟 ℳY ℳ : Type*} [Category 𝒟Y] [Category 𝒟]
    [Category ℳY] [Category ℳ] {eY : 𝒟Y ⥤ ℳY} {eX : 𝒟 ⥤ ℳ} {Lg : 𝒟Y ⥤ 𝒟} {G : ℳY ⥤ ℳ}
    {TY : 𝒟Y ⥤ 𝒟Y ⥤ 𝒟Y} {T : 𝒟 ⥤ 𝒟 ⥤ 𝒟} {T1Y : ℳY ⥤ ℳY ⥤ ℳY} {T1 : ℳ ⥤ ℳ ⥤ ℳ}
    (τY : Functor.uncurry.obj TY ⋙ eY ≅ eY.prod eY ⋙ Functor.uncurry.obj T1Y)
    (τ : Functor.uncurry.obj T ⋙ eX ≅ eX.prod eX ⋙ Functor.uncurry.obj T1)
    (c : eY ⋙ G ≅ Lg ⋙ eX)
    (αg : Functor.uncurry.obj TY ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj T)
    (gen : Functor.uncurry.obj T1Y ⋙ G ≅ G.prod G ⋙ Functor.uncurry.obj T1)
    {R P M : 𝒟Y} {R' : 𝒟} (ψ : Lg.obj R ⟶ R') (evX : (T.obj R').obj (Lg.obj P) ⟶ Lg.obj M)
    (evY : (TY.obj R).obj P ⟶ M)
    (ht : (T.map ψ).app (Lg.obj P) ≫ evX = αg.inv.app (R, P) ≫ Lg.map evY)
    (hC : G.map (τY.hom.app (R, P)) ≫ gen.hom.app (eY.obj R, eY.obj P) ≫
        (Functor.uncurry.obj T1).map (c.hom.app R ×ₘ c.hom.app P) =
      c.hom.app ((Functor.uncurry.obj TY).obj (R, P)) ≫ eX.map (αg.hom.app (R, P)) ≫
        τ.hom.app (Lg.obj R, Lg.obj P)) :
    (T1.map (c.hom.app R ≫ eX.map ψ)).app (G.obj (eY.obj P)) ≫
        (T1.obj (eX.obj R')).map (c.hom.app P) ≫
        (τ.inv.app (R', Lg.obj P) ≫ eX.map evX) ≫ c.inv.app M =
      gen.inv.app (eY.obj R, eY.obj P) ≫ G.map (τY.inv.app (R, P) ≫ eY.map evY) := by
  have nτ := τ.inv.naturality (ψ ×ₘ 𝟙 (Lg.obj P))
  have hT : (Functor.uncurry.obj T).map (ψ ×ₘ 𝟙 (Lg.obj P)) = (T.map ψ).app (Lg.obj P) := by simp
  have hT1 : (Functor.uncurry.obj T1).map (eX.map ψ ×ₘ 𝟙 (eX.obj (Lg.obj P))) =
      (T1.map (eX.map ψ)).app (eX.obj (Lg.obj P)) := by simp
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at nτ
  rw [hT, hT1] at nτ
  have nc := c.inv.naturality evY
  simp only [Functor.comp_map, Functor.comp_obj] at nc
  have nT := (T1.map (eX.map ψ)).naturality (c.hom.app P)
  simp only [Functor.comp_obj] at nT
  have ht' := congrArg eX.map ht
  simp only [Functor.map_comp] at ht'
  have hC' : (Functor.uncurry.obj T1).map (c.hom.app R ×ₘ c.hom.app P) ≫
      τ.inv.app (Lg.obj R, Lg.obj P) ≫ eX.map (αg.inv.app (R, P)) ≫
        c.inv.app ((Functor.uncurry.obj TY).obj (R, P)) =
      gen.inv.app (eY.obj R, eY.obj P) ≫ G.map (τY.inv.app (R, P)) := by
    rw [← cancel_epi (G.map (τY.hom.app (R, P)) ≫ gen.hom.app (eY.obj R, eY.obj P))]
    simp only [Category.assoc]
    rw [reassoc_of% hC]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  simp only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj] at hC'
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, ← reassoc_of% nT]
  simp only [Category.assoc]
  rw [reassoc_of% nτ, reassoc_of% ht', nc, reassoc_of% hC']
  simp only [Functor.map_comp]

/-- Transporting a bijective family along the identification of the tensor product with a
bifunctor `T` makes the whiskering family bijective. -/
private theorem bijective_whiskerRight_comp {C : Type*} [Category C] [MonoidalCategory C]
    {T : C ⥤ C ⥤ C} (ht : ∀ A A' : C, A ⊗ A' = (T.obj A).obj A')
    (hw : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      f ▷ B = eqToHom (ht A B) ≫ (T.map f).app B ≫ eqToHom (ht A' B).symm)
    {K I L : C} {e : (T.obj I).obj K ⟶ L}
    (h : ∀ W : C, Function.Bijective fun g : W ⟶ I => (T.map g).app K ≫ e) (W : C) :
    Function.Bijective fun g : W ⟶ I => g ▷ K ≫ eqToHom (ht I K) ≫ e := by
  have key : (fun g : W ⟶ I => g ▷ K ≫ eqToHom (ht I K) ≫ e) =
      (fun x => eqToHom (ht W K) ≫ x) ∘ (fun g : W ⟶ I => (T.map g).app K ≫ e) := by
    funext g
    simp [hw]
  rw [key]
  exact Function.Bijective.comp ⟨fun a b hab => (cancel_epi _).1 hab,
    fun y => ⟨eqToHom (ht W K).symm ≫ y, by simp⟩⟩ (h W)

/-- `CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map` for monoidal structures
whose tensor product is a prescribed bifunctor on the nose, stated with that bifunctor in place of
the tensor product, and with the tensorator of the functor named by `hμ`. -/
theorem isIso_of_bijective_map_app {C D : Type*} [Category C] [Category D]
    [MC : MonoidalCategory C] [MD : MonoidalCategory D] {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
    (htC : ∀ A A' : C, A ⊗ A' = (TC.obj A).obj A')
    (hwC : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      f ▷ B = eqToHom (htC A B) ≫ (TC.map f).app B ≫ eqToHom (htC A' B).symm)
    (htD : ∀ A A' : D, A ⊗ A' = (TD.obj A).obj A')
    (hwD : ∀ {A A' : D} (f : A ⟶ A') (B : D),
      f ▷ B = eqToHom (htD A B) ≫ (TD.map f).app B ≫ eqToHom (htD A' B).symm)
    (F : C ⥤ D) [hF : F.Monoidal] (K K' : C) [hK : ExactPairing K K'] {L I : C}
    {e : (TC.obj I).obj K ⟶ L}
    (h : ∀ W : C, Function.Bijective fun g : W ⟶ I => (TC.map g).app K ≫ e)
    {J : D} {e' : (TD.obj J).obj (F.obj K) ⟶ F.obj L}
    (h' : ∀ W : D, Function.Bijective fun g : W ⟶ J => (TD.map g).app (F.obj K) ≫ e')
    (m : (TD.obj (F.obj I)).obj (F.obj K) ⟶ F.obj ((TC.obj I).obj K))
    (hμ : Functor.LaxMonoidal.μ F I K =
      eqToHom (htD _ _) ≫ m ≫ F.map (eqToHom (htC I K).symm))
    (φ : F.obj I ⟶ J) (hφ : (TD.map φ).app (F.obj K) ≫ e' = m ≫ F.map e) : IsIso φ := by
  refine isIso_of_tensorHomBijective_map F K K' (e := eqToHom (htC I K) ≫ e) (fun W => ?_)
    (e' := eqToHom (htD J (F.obj K)) ≫ e') (fun W => ?_) φ ?_
  · exact bijective_whiskerRight_comp htC hwC h W
  · exact bijective_whiskerRight_comp htD hwD h' W
  · rw [hwD, hμ]
    simp [hφ]

/-- **The argument of Stacks 08JF, abstractly.** Let `G : ℳY ⥤ ℳ` be monoidal for structures
re-seated onto bifunctors `T1Y` and `T1`, with tensorator the inverse of `gen`, and let `eY P` be
dualizable. If `eY R` with `τY⁻¹ ≫ eY evY` is an internal Hom from `eY P` to `eY M` and `eX R'`
with `τ⁻¹ ≫ eX evX` one from `eX (Lg P)` to `eX (Lg M)`, then for a transpose `ψ` of
`αg⁻¹ ≫ Lg evY`, and given the square `hC` relating `gen`, `αg`, `τY`, `τ` and `c`, the morphism
`c ≫ eX ψ` is an isomorphism. -/
theorem isIso_comp_map_of_evaluation_chase {𝒟Y 𝒟 ℳY ℳ : Type*} [Category 𝒟Y] [Category 𝒟]
    [Category ℳY] [Category ℳ] {MY : MonoidalCategory ℳY} {MX : MonoidalCategory ℳ}
    {eY : 𝒟Y ⥤ ℳY} {eX : 𝒟 ⥤ ℳ} {Lg : 𝒟Y ⥤ 𝒟} {G : ℳY ⥤ ℳ}
    {TY : 𝒟Y ⥤ 𝒟Y ⥤ 𝒟Y} {T : 𝒟 ⥤ 𝒟 ⥤ 𝒟} {T1Y : ℳY ⥤ ℳY ⥤ ℳY} {T1 : ℳ ⥤ ℳ ⥤ ℳ}
    {UY : ℳY} {UX : ℳ} (iY : @curriedTensor ℳY _ MY ≅ T1Y)
        (εY : @tensorUnit ℳY _ MY.toMonoidalCategoryStruct ≅ UY)
    (iX : @curriedTensor ℳ _ MX ≅ T1) (εX : @tensorUnit ℳ _ MX.toMonoidalCategoryStruct ≅ UX)
    (hG : @Functor.Monoidal ℳY _ (@reseat ℳY _ MY T1Y UY iY εY) ℳ _
      (@reseat ℳ _ MX T1 UX iX εX) G)
    (τY : Functor.uncurry.obj TY ⋙ eY ≅ eY.prod eY ⋙ Functor.uncurry.obj T1Y)
    (τ : Functor.uncurry.obj T ⋙ eX ≅ eX.prod eX ⋙ Functor.uncurry.obj T1)
    (c : eY ⋙ G ≅ Lg ⋙ eX)
    (αg : Functor.uncurry.obj TY ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj T)
    (gen : Functor.uncurry.obj T1Y ⋙ G ≅ G.prod G ⋙ Functor.uncurry.obj T1)
    (hμ : ∀ A B : ℳY, @Functor.LaxMonoidal.μ ℳY _ (@reseat ℳY _ MY T1Y UY iY εY) ℳ _
      (@reseat ℳ _ MX T1 UX iX εX) G hG.toLaxMonoidal A B = gen.inv.app (A, B))
    {R P M : 𝒟Y} {R' : 𝒟} (ψ : Lg.obj R ⟶ R') (evX : (T.obj R').obj (Lg.obj P) ⟶ Lg.obj M)
    (evY : (TY.obj R).obj P ⟶ M)
    (ht : (T.map ψ).app (Lg.obj P) ≫ evX = αg.inv.app (R, P) ≫ Lg.map evY)
    (hC : G.map (τY.hom.app (R, P)) ≫ gen.hom.app (eY.obj R, eY.obj P) ≫
        (Functor.uncurry.obj T1).map (c.hom.app R ×ₘ c.hom.app P) =
      c.hom.app ((Functor.uncurry.obj TY).obj (R, P)) ≫ eX.map (αg.hom.app (R, P)) ≫
        τ.hom.app (Lg.obj R, Lg.obj P))
    (K' : ℳY) (hK : @ExactPairing ℳY _ (@reseat ℳY _ MY T1Y UY iY εY) (eY.obj P) K')
    (hY : ∀ W : ℳY, Function.Bijective fun x : W ⟶ eY.obj R =>
      (T1Y.map x).app (eY.obj P) ≫ τY.inv.app (R, P) ≫ eY.map evY)
    (hX : ∀ W : ℳ, Function.Bijective fun x : W ⟶ eX.obj R' =>
      (T1.map x).app (eX.obj (Lg.obj P)) ≫ τ.inv.app (R', Lg.obj P) ≫ eX.map evX) :
    IsIso (c.hom.app R ≫ eX.map ψ) :=
  @isIso_of_bijective_map_app ℳY ℳ _ _ (@reseat ℳY _ MY T1Y UY iY εY)
    (@reseat ℳ _ MX T1 UX iX εX) T1Y T1 (fun _ _ => rfl)
    (fun _ _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    (fun _ _ => rfl)
    (fun _ _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    G hG (eY.obj P) K' hK _ _ _ hY _ _
    (fun W => bijective_map_app_comp_congr T1 (c.app P) (c.app M).symm _ hX W)
    (gen.inv.app (eY.obj R, eY.obj P))
    (by rw [hμ]; simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.map_id])
    _ (whiskerRight_comp_evaluation_chase τY τ c αg gen ψ evX evY ht hC)

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-- The square of Stacks 07A4 along `g` and `g_m`, at the spelling of the comparisons along
morphisms of models. -/
theorem smallEtaleModelPullbackSquare_tensor {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
      (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
      (smallEtaleModelPullbackRingedToposHom g)).map
          ((smallEtaleModelDerivedTensorIsoTopos Y).hom.app (A, A')) ≫
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso
        (smallEtaleModelPullbackRingedToposHom g)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)).hom.app
            ((smallEtaleModelDerivedEquivalence B S hS Y).functor.obj A,
            (smallEtaleModelDerivedEquivalence B S hS Y).functor.obj A') ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)).map
        ((smallEtaleModelDerivedPullbackSquareIso g).hom.app A ×ₘ
            (smallEtaleModelDerivedPullbackSquareIso g).hom.app A') =
    (smallEtaleModelDerivedPullbackSquareIso g).hom.app
        ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y)).obj (A, A')) ≫
      (smallEtaleModelDerivedEquivalence B S hS X).functor.map
          ((smallEtaleDerivedPullbackTensorIso g).hom.app (A, A')) ≫
      (smallEtaleModelDerivedTensorIsoTopos X).hom.app
          ((smallEtaleDerivedModulePullback B S hS g).obj A,
          (smallEtaleDerivedModulePullback B S hS g).obj A') := by
  exact smallEtaleModelDerivedPullbackSquareIso_tensor g A A'

/-- The transpose of `ψ` under Stacks 08J8, written with the evaluation. -/
theorem smallEtaleDerivedTensor_map_app_comp_counit {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ψ : (smallEtaleDerivedModulePullback B S hS g).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M) ⟶
        (((smallEtaleDerivedSheafHom B S hS X).obj
        (op ((smallEtaleDerivedModulePullback B S hS g).obj P))).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj M)))
    (hψ : ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        ((smallEtaleDerivedModulePullback B S hS g).obj P)).homEquiv _ _).symm ψ =
      (smallEtaleDerivedPullbackTensorIso g).inv.app
          ((((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M), P) ≫
          (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)) :
    ((smallEtaleDerivedTensor B S hS X).map ψ).app
        ((smallEtaleDerivedModulePullback B S hS g).obj P) ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        ((smallEtaleDerivedModulePullback B S hS g).obj P)).counit.app
        ((smallEtaleDerivedModulePullback B S hS g).obj M)) =
      (smallEtaleDerivedPullbackTensorIso g).inv.app
          ((((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M), P) ≫
          (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M) :=
  (Adjunction.homEquiv_counit _ _ _ _).symm.trans hψ

/-- The derived pullback along `g_m`, the morphism of models of `g`. -/
def smallEtaleModelPullbackFunctor {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS Y.1 Y.2).O)) ⥤
          DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)) :=
  (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
      (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
      (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
      (smallEtaleModelPullbackRingedToposHom g))

/-- The derived tensor product of `Stacks.SheafOfModules` on the model of `Z`. -/
def smallEtaleModelTensorOne (Z : AlgebraicSpaces B S hS) : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS Z.1 Z.2).O)) ⥤
          DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS Z.1 Z.2).O)) ⥤
          DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS Z.1 Z.2).O)) :=
  Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleModelRingedSite B S hS Z.1 Z.2).toRingedTopos.toRingedSite

/-- The identification of the derived tensor products of `Z` and of its model. -/
def smallEtaleModelTensorTransport (Z : AlgebraicSpaces B S hS) :
    Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z) ⋙
        (smallEtaleModelDerivedEquivalence B S hS Z).functor ≅
      (smallEtaleModelDerivedEquivalence B S hS Z).functor.prod
          (smallEtaleModelDerivedEquivalence B S hS Z).functor ⋙
        Functor.uncurry.obj (smallEtaleModelTensorOne Z) :=
  smallEtaleModelDerivedTensorIsoTopos Z

/-- Stacks 07A4 along `g_m`, at the derived tensor products of `Stacks.SheafOfModules`. -/
def smallEtaleModelPullbackTensorOne {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    Functor.uncurry.obj (smallEtaleModelTensorOne Y) ⋙ smallEtaleModelPullbackFunctor g ≅
      (smallEtaleModelPullbackFunctor g).prod (smallEtaleModelPullbackFunctor g) ⋙
        Functor.uncurry.obj (smallEtaleModelTensorOne X) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso
    (smallEtaleModelPullbackRingedToposHom g)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)

/-- The comparison of the derived pullbacks along `g_m` and `g` across the models. -/
def smallEtaleModelPullbackComparison {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (smallEtaleModelDerivedEquivalence B S hS Y).functor ⋙ smallEtaleModelPullbackFunctor g ≅
      smallEtaleDerivedModulePullback B S hS g ⋙
          (smallEtaleModelDerivedEquivalence B S hS X).functor :=
  smallEtaleModelDerivedPullbackSquareIso g

/-- The arrow algebra of Stacks 08JF on the models, at a transpose `ψ`. -/
theorem smallEtaleModelPullbackSheafHom_chase {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ψ : (smallEtaleDerivedModulePullback B S hS g).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M) ⟶
        (((smallEtaleDerivedSheafHom B S hS X).obj
        (op ((smallEtaleDerivedModulePullback B S hS g).obj P))).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj M)))
    (hψ : ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        ((smallEtaleDerivedModulePullback B S hS g).obj P)).homEquiv _ _).symm ψ =
      (smallEtaleDerivedPullbackTensorIso g).inv.app
          ((((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M), P) ≫
        (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)) :
    ((smallEtaleModelTensorOne X).map ((smallEtaleModelPullbackComparison g).hom.app
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M) ≫
        (smallEtaleModelDerivedEquivalence B S hS X).functor.map ψ)).app
            ((smallEtaleModelPullbackFunctor g).obj
            ((smallEtaleModelDerivedEquivalence B S hS Y).functor.obj P)) ≫
      ((smallEtaleModelTensorOne X).obj ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
          (((smallEtaleDerivedSheafHom B S hS X).obj
          (op ((smallEtaleDerivedModulePullback B S hS g).obj P))).obj
          ((smallEtaleDerivedModulePullback B S hS g).obj M)))).map
        ((smallEtaleModelPullbackComparison g).hom.app P) ≫
      ((smallEtaleModelTensorTransport X).inv.app ((((smallEtaleDerivedSheafHom B S hS X).obj
          (op ((smallEtaleDerivedModulePullback B S hS g).obj P))).obj
          ((smallEtaleDerivedModulePullback B S hS g).obj M)),
          ((smallEtaleDerivedModulePullback B S hS g).obj P)) ≫
        (smallEtaleModelDerivedEquivalence B S hS X).functor.map
            ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
            ((smallEtaleDerivedModulePullback B S hS g).obj P)).counit.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M))) ≫
      (smallEtaleModelPullbackComparison g).inv.app M =
    (smallEtaleModelPullbackTensorOne g).inv.app ((smallEtaleModelDerivedEquivalence B S hS
        Y).functor.obj (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M),
        (smallEtaleModelDerivedEquivalence B S hS Y).functor.obj P) ≫
      (smallEtaleModelPullbackFunctor g).map ((smallEtaleModelTensorTransport Y).inv.app
          ((((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M), P) ≫
        (smallEtaleModelDerivedEquivalence B S hS Y).functor.map
            ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)) :=
  whiskerRight_comp_evaluation_chase (smallEtaleModelTensorTransport Y)
    (smallEtaleModelTensorTransport X) (smallEtaleModelPullbackComparison g)
    (smallEtaleDerivedPullbackTensorIso g) (smallEtaleModelPullbackTensorOne g) ψ
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        ((smallEtaleDerivedModulePullback B S hS g).obj P)).counit.app
        ((smallEtaleDerivedModulePullback B S hS g).obj M))
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)
    (smallEtaleDerivedTensor_map_app_comp_counit g P M ψ hψ)
    (smallEtaleModelPullbackSquare_tensor g _ P)

/-- **Stacks 08JF for algebraic spaces, at a transpose.** Let `g : X ⟶ Y` be a morphism of
algebraic spaces, `P` a perfect and `M` an arbitrary object of `D(𝒪_Y)`. A morphism
`ψ : Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` whose transpose under Stacks 08J8 is the inverse of
the comparison of Stacks 07A4 followed by `Lg^*` of the evaluation is an isomorphism. -/
theorem isIso_of_homEquiv_symm_eq_pullbackTensorIso {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hP : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P)
    (ψ : (smallEtaleDerivedModulePullback B S hS g).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M) ⟶
        (((smallEtaleDerivedSheafHom B S hS X).obj
        (op ((smallEtaleDerivedModulePullback B S hS g).obj P))).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj M)))
    (hψ : ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        ((smallEtaleDerivedModulePullback B S hS g).obj P)).homEquiv _ _).symm ψ =
      (smallEtaleDerivedPullbackTensorIso g).inv.app
          ((((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M), P) ≫
        (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)) :
    IsIso ψ := by
  obtain ⟨pair, -, -⟩ := RingedSite.exists_exactPairing_derivedDual
    (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite
        ((smallEtaleModelDerivedEquivalence B S hS Y).functor.obj P)
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS Y P hP)
  have hφ := isIso_comp_map_of_evaluation_chase
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso
      (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.O
      (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso
      (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.O)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso
      (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O
      (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso
      (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorMonoidal
      (smallEtaleModelPullbackRingedToposHom g))
    (smallEtaleModelTensorTransport Y) (smallEtaleModelTensorTransport X)
    (smallEtaleModelPullbackComparison g) (smallEtaleDerivedPullbackTensorIso g)
    (smallEtaleModelPullbackTensorOne g)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorMonoidal_μ
      (smallEtaleModelPullbackRingedToposHom g)) ψ
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
      ((smallEtaleDerivedModulePullback B S hS g).obj P)).counit.app
        ((smallEtaleDerivedModulePullback B S hS g).obj M))
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)
    (smallEtaleDerivedTensor_map_app_comp_counit g P M ψ hψ)
    (smallEtaleModelPullbackSquare_tensor g _ P) _ pair
    (bijective_smallEtaleModelEvaluation Y P M) (bijective_smallEtaleModelEvaluation X _ _)
  have hc : IsIso ((smallEtaleModelPullbackComparison g).hom.app
      (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M)) :=
    Iso.isIso_hom ((smallEtaleModelPullbackComparison g).app _)
  have h2 := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hc hφ
  exact @isIso_of_reflects_iso _ _ _ _ _ _ ψ (smallEtaleModelDerivedEquivalence B S hS X).functor h2
      _

/-- **Stacks 08JF for algebraic spaces, at a transpose, for any spelling of the derived
pullback.** `AlgebraicGeometry.Space.isIso_of_homEquiv_symm_eq_pullbackTensorIso` for a functor `F`
equal to `Lg^*` and an isomorphism `α` equal to the comparison of Stacks 07A4, so that a caller
whose derived pullback is spelled differently converts only the functor and the isomorphism. -/
theorem isIso_of_homEquiv_symm_eq_pullbackTensorIso_of_eq {X Y : AlgebraicSpaces B S hS}
    (g : X ⟶ Y)
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hF : F = smallEtaleDerivedModulePullback B S hS g)
    (α : Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (hα : HEq α (smallEtaleDerivedPullbackTensorIso g))
    (P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hP : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P)
    (ψ : F.obj (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M) ⟶
      ((smallEtaleDerivedSheafHom B S hS X).obj (op (F.obj P))).obj (F.obj M))
    (hψ : ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X (F.obj P)).homEquiv _ _).symm ψ =
      α.inv.app (((smallEtaleDerivedSheafHom B S hS Y).obj (op P)).obj M, P) ≫
        F.map ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)) :
    IsIso ψ := by
  subst hF
  obtain rfl := eq_of_heq hα
  exact isIso_of_homEquiv_symm_eq_pullbackTensorIso g P M hP ψ hψ

end AlgebraicGeometry.Space

end
