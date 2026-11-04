module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeCoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquareUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositeAdjunctionUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CoefficientChangeProjectionFormula

/-!
# The projection formula of the change of coefficients `ℤ/nℤ ⟶ ℤ/ℓℤ`, and Tag 0F1J over `ℤ/nℤ`

Let `φ : Λ ⟶ Λ'` be a map of coefficient rings and `c : (Z_étale, Λ̲') ⟶ (Z_étale, Λ̲)` the change
of coefficients (`coefficientHom`). Its projection map

`K ⊗^L_Λ Rc_*N ⟶ Rc_*(Lc^*K ⊗^L_{Λ'} N)`

(`coefficientProjectionMap`) is the adjoint of the comparison of Stacks 07A4 followed by the
counit in the second factor. The step
`p⁻¹E ⊗^L_{ℤ/n} (f')⁻¹Rg_*𝒢 = p⁻¹(E ⊗^L_{ℤ/n} 𝔽_ℓ) ⊗^L_{𝔽_ℓ} (f')⁻¹Rg_*𝒢` of the proof of
[Stacks, Tag 0F1J] is that this map is invertible for `ℤ/nℤ ⟶ ℤ/ℓℤ`; this file proves it, with
no hypothesis, and feeds it into Tag 0F1J for `ℤ/nℤ`-coefficients.

## The argument

Write `K = Q P` for a K-flat complex `P` with flat terms (Stacks 06YS) and `N = Q F`.
Restriction of scalars `c_*` is exact, so `Rc_*N = Q(c_*F)`
(`Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedPushforwardUnit_app_of_exact`). Then

* the derived tensor products are total tensor complexes: `K ⊗^L Rc_*N = Q Tot(P ⊗ c_*F)` because
  `P` is K-flat, and `Lc^*K ⊗^L N = Q Tot(c^*P ⊗ F)` because `c^*P` is (Stacks 06YY, 0G7E);
* the comparison of Stacks 07A4 at `(P, c_*F)` is read through the comparison of complexes
  `c^*Tot(P ⊗ c_*F) ≅ Tot(c^*P ⊗ c^*c_*F)` by Stacks 0FPH
  (`Stacks.Sheaves.DerivedPullback.derivedPullback_toTensor_square_unconditional`), with no
  flatness asked of `c_*F`;
* the derived counit at `Q F` is the ordinary counit `c^*c_*F ⟶ F` by Stacks 0FPI, and the
  derived unit at `Q Tot(P ⊗ c_*F)` is the ordinary unit by the unit factorization of Stacks
  07A6.

So, up to isomorphisms on both sides, the projection map is the class of the map of complexes

`Tot(P ⊗ c_*F) ⟶ c_*c^*Tot(P ⊗ c_*F) ≅ c_*Tot(c^*P ⊗ c^*c_*F) ⟶ c_*Tot(c^*P ⊗ F)`

(`isIso_coefficientProjectionMap_of_isIso_unit`), and it is invertible as soon as the ordinary
counit is invertible and the ordinary unit is invertible at the terms of `Tot(P ⊗ c_*F)`. For
`ℤ/nℤ ⟶ ℤ/ℓℤ` with `ℓ ∣ n` both hold: restriction of scalars is fully faithful
(`coefficientPushforwardZModFullyFaithful`), so the counit is invertible, and the terms of
`Tot(P ⊗ c_*F)` are annihilated by `ℓ`, hence restrictions of scalars, where the unit is inverse
to the restriction of the counit.

## Main results

* `isIso_coefficientProjectionMap_zmodULiftRingHom` — the projection formula of the change of
  coefficients `ℤ/nℤ ⟶ ℤ/ℓℤ`, for every `K` and `N`.
* `isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds` — Tag 0F1J for
  `ℤ/nℤ`-coefficients, from derived base change.

Not registered: derived base change over `X` and over the finite schemes over its affine opens
(Tag 0F1I for `S = Spec K`) are explicit arguments of
`isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds`.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.AbstractKunnethMap

section Transpose

variable {C D : Type*} [Category* C] [Category* D] (TC : C × C ⥤ C) (TD : D × D ⥤ D)
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (μ : TC ⋙ L ⟶ L.prod L ⋙ TD)

/-- **The projection map read on models.** Let `v : B₀ ⟶ R B`, `b : A ⊗ B₀ ⟶ M` and
`d : L A ⊗ B ⟶ W` be isomorphisms, and `x : L M ⟶ W` a map which, precomposed with `L b`, is the
comparison `μ` followed by `L v` and the counit in the second factor and by `d`. Then the
projection map `A ⊗ R B ⟶ R(L A ⊗ B)` is invertible as soon as the transpose `M ⟶ R W` of `x`
is: the two agree up to `v`, `b` and `d`. -/
theorem isIso_projectionMap_of_isIso_homEquiv {A B₀ M : C} {B W : D}
    (v : B₀ ⟶ R.obj B) (hv : IsIso v) (b : TC.obj (A, B₀) ⟶ M) (hb : IsIso b)
    (d : TD.obj (L.obj A, B) ⟶ W) (hd : IsIso d) (x : L.obj M ⟶ W)
    (hx : L.map b ≫ x =
      μ.app (A, B₀) ≫ TD.map (𝟙 (L.obj A) ×ₘ (L.map v ≫ a.counit.app B)) ≫ d)
    (hiso : IsIso (a.homEquiv _ _ x)) :
    IsIso (projectionMap TC TD a μ A B) := by
  have key : TC.map (𝟙 A ×ₘ v) ≫ projectionMap TC TD a μ A B ≫ R.map d =
      b ≫ a.homEquiv _ _ x := by
    have hp : projectionMap TC TD a μ A B =
        a.homEquiv _ _ (μ.app (A, R.obj B) ≫ TD.map (𝟙 (L.obj A) ×ₘ a.counit.app B)) := rfl
    rw [hp, ← a.homEquiv_naturality_right, ← a.homEquiv_naturality_left,
      ← a.homEquiv_naturality_left, hx]
    congr 1
    have hn := μ.naturality (𝟙 A ×ₘ v : (A, B₀) ⟶ (A, R.obj B))
    simp only [Functor.comp_map, Functor.prod_map] at hn
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← TD.map_comp_assoc]
    simp
  have := hv
  have := hb
  have := hd
  have : IsIso (𝟙 A ×ₘ v) :=
    (isIso_prod_iff (f := (𝟙 A ×ₘ v))).2 ⟨inferInstance, inferInstance⟩
  have h2 : IsIso (TC.map (𝟙 A ×ₘ v) ≫ projectionMap TC TD a μ A B ≫ R.map d) := by
    rw [key]
    infer_instance
  have : IsIso (projectionMap TC TD a μ A B ≫ R.map d) :=
    IsIso.of_isIso_comp_left (TC.map (𝟙 A ×ₘ v)) _
  exact IsIso.of_isIso_comp_right _ (R.map d)

/-- Cancelling `G e` against `G e⁻¹` in front of a composite. -/
theorem map_hom_comp_map_inv_comp_assoc (G : C ⥤ D) {X Y : C} (e : X ≅ Y) {P Q R : D}
    (f : G.obj X ⟶ P) (g : P ⟶ Q) (k : Q ⟶ R) :
    G.map e.hom ≫ (G.map e.inv ≫ (f ≫ g)) ≫ k = f ≫ g ≫ k := by
  simp only [Category.assoc, ← G.map_comp_assoc, e.hom_inv_id, G.map_id, Category.id_comp]

/-- **The transpose of a map out of `L M`, read on a model `M' ≅ M`**: if `L e ≫ x` is `c ≫ r`
with `r` invertible and the composite of the unit at `M'` with `R c` invertible, then the
transpose of `x` is invertible. -/
theorem isIso_homEquiv_of_fac {M M' : C} {V W : D} (e : M' ≅ M) (x : L.obj M ⟶ W)
    (c : L.obj M' ⟶ V) (r : V ⟶ W) (hx : L.map e.hom ≫ x = c ≫ r)
    (h₁ : IsIso (a.unit.app M' ≫ R.map c)) (h₂ : IsIso r) :
    IsIso (a.homEquiv M W x) := by
  have h := a.homEquiv_naturality_left e.hom x
  rw [hx, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc] at h
  have h' : a.homEquiv M W x = e.inv ≫ (a.unit.app M' ≫ R.map c) ≫ R.map r := by
    rw [h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

end Transpose

section Representatives

open Stacks.Sheaves.DerivedPullback (bifunctorMap)

variable {C D : Type*} [Category* C] [Category* D] (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (L : C ⥤ D) (μ : Functor.uncurry.obj T ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj T')

/-- The arrow algebra of `isIso_coefficientProjectionMap_of_isIso_unit`, in bare categories: a
square through the comparison `μ` (`h₀`, Stacks 0FPH), the naturality of the map to the total
tensor complex in the second factor (`hnat`) and the identification of the counit (`hcounit`,
Stacks 0FPI) give the equation `isIso_projectionMap_of_isIso_homEquiv` asks for. -/
theorem map_comp_eq_of_toTensor_square {A B₀ B₀' M : C} {LA' Bρ' F' V V' W B : D}
    (e : B₀ ⟶ B₀') (t : (T.obj A).obj B₀' ⟶ M) (cmpA : L.obj A ⟶ LA')
    (cmpB : L.obj B₀' ⟶ Bρ') (tt : (T'.obj LA').obj Bρ' ⟶ V') (cmpM : L.obj M ⟶ V)
    (qτ : V ⟶ V') (qε : Bρ' ⟶ F') (qtε : V' ⟶ W) (t' : (T'.obj LA').obj F' ⟶ W)
    (g : L.obj B₀ ⟶ B) (eF : B ⟶ F')
    (h₀ : L.map t ≫ cmpM ≫ qτ = μ.app (A, B₀') ≫ bifunctorMap T' cmpA cmpB ≫ tt)
    (hnat : tt ≫ qtε = (T'.obj LA').map qε ≫ t')
    (hcounit : L.map e ≫ cmpB ≫ qε = g ≫ eF) :
    L.map ((T.obj A).map e ≫ t) ≫ cmpM ≫ qτ ≫ qtε =
      μ.app (A, B₀) ≫ (Functor.uncurry.obj T').map (𝟙 (L.obj A) ×ₘ g) ≫
        (bifunctorMap T' cmpA eF ≫ t') := by
  have hn := μ.naturality ((𝟙 A, e) : (A, B₀) ⟶ (A, B₀'))
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.prod_obj] at hn
  rw [L.map_comp, Category.assoc, reassoc_of% h₀, reassoc_of% hn, hnat]
  congr 1
  dsimp only [bifunctorMap, Functor.uncurry_obj_map, Functor.prod_obj]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc,
    NatTrans.naturality_assoc]
  congr 1
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f => (T'.obj LA').map f ≫ t') hcounit

end Representatives

end Stacks.Cohomology.AbstractKunnethMap

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `coefficientProjectionMap` (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Kunneth/
-- EtaleCoefficientsCoefficientChange.lean:111`) is stated for the standard model of the derived
-- category, through `derivedPullback`.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

-- The imports bring `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

open Stacks.Cohomology.AbstractKunnethMap
open Stacks.Sheaves.DerivedPullback
open Stacks.Sheaves.DerivedPullback.KFlatPullback

section General

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (Z : Scheme.{u})

/-- **The projection map of a change of coefficients from the ordinary unit and counit.** If the
counit `c^*c_*G ⟶ G` of the change of coefficients is invertible at every sheaf of
`Λ'`-modules, and the unit `M ⟶ c_*c^*M` at every term of every total tensor complex
`Tot(P ⊗_Λ c_*F)`, then the projection map `K ⊗^L_Λ Rc_*N ⟶ Rc_*(Lc^*K ⊗^L_{Λ'} N)` is invertible
for all `K` and `N`. At `K = Q P` with `P` K-flat with flat terms and `N = Q F` it is, up to
isomorphisms, the class of
`Tot(P ⊗ c_*F) ⟶ c_*c^*Tot(P ⊗ c_*F) ≅ c_*Tot(c^*P ⊗ c^*c_*F) ⟶ c_*Tot(c^*P ⊗ F)`, by Stacks
0FPH, 0FPI and the unit factorization of Stacks 07A6. -/
theorem isIso_coefficientProjectionMap_of_isIso_unit
    (hε : ∀ G, IsIso ((coefficientHom φ Z).pullbackPushforwardAdjunctionTopos.counit.app G))
    (hη : ∀ (P : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Z).O)) ℤ)
      (F : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ' Z).O)) ℤ) (k : ℤ),
      IsIso ((coefficientHom φ Z).pullbackPushforwardAdjunctionTopos.unit.app
        ((((Stacks.SheafOfModules.Tensor.tensorComplex (ringedTopos Λ Z).O).obj P).obj
          (((coefficientHom φ Z).pushforwardTopos.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)).X k)))
    (K : DerivedModules Λ Z) (N : DerivedModules Λ' Z) :
    IsIso (coefficientProjectionMap φ Z K N) := by
  have hmos := isMorphismOfSites_coefficientHom φ Z
  obtain ⟨P, hP, hflat, ⟨eK⟩⟩ :=
    Stacks.Cohomology.CoefficientChange.exists_flatKFlatModel (ringedTopos Λ Z).O K
  let F := DerivedCategory.Q.objPreimage N
  let eN : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F) ≅ N :=
    (DerivedCategory.quotientCompQhIso _).app F ≪≫ DerivedCategory.Q.objObjPreimageIso N
  refine (isIso_projectionMap_iff_of_iso_objects (Functor.uncurry.obj (tensor Λ Z))
    (Functor.uncurry.obj (tensor Λ' Z)) (coefficientAdjunction φ Z)
    (coefficientTensorIso φ Z).hom eK eN).1 ?_
  let c := coefficientHom φ Z
  let adjC := Adjunction.mapHomologicalComplexAdjunction c.pullbackPushforwardAdjunctionTopos
    (ComplexShape.up ℤ)
  let ρF := (c.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let Tot := ((Stacks.SheafOfModules.Tensor.tensorComplex (ringedTopos Λ Z).O).obj P).obj ρF
  let εF : (pullbackComplex c).obj ρF ⟶ F := adjC.counit.app F
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ Z).O
  let T' := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ' Z).O
  let qΛ := DerivedCategory.quotientCompQhIso (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Z).O))
  let qΛ' := DerivedCategory.quotientCompQhIso (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ' Z).O))
  let v := (derivedPushforwardUnit c).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)
  have hv : IsIso v :=
    Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedPushforwardUnit_app_of_exact c _
  let b : (T.tensor.obj (DerivedCategory.Q.obj P)).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ρF)) ⟶
      DerivedCategory.Q.obj Tot :=
    (T.tensor.obj (DerivedCategory.Q.obj P)).map (qΛ.hom.app ρF) ≫ T.toTensor P ρF
  have hb : IsIso b := by
    have : IsIso (T.toTensor P ρF) := by
      rw [T.toTensor_eq_comparisonLeft P ρF hP]
      infer_instance
    infer_instance
  let d := bifunctorMap T'.tensor (pullbackComparisonQ c P) (qΛ'.hom.app F) ≫
    T'.toTensor ((pullbackComplex c).obj P) F
  have hd : IsIso d := by
    have h₁ : IsIso (pullbackComparisonQ c P) := by
      rw [← flatPullbackIso_hom_eq_pullbackComparisonQ c hmos P hP hflat]
      infer_instance
    have h₂ : IsIso (T'.toTensor ((pullbackComplex c).obj P) F) := by
      rw [T'.toTensor_eq_comparisonLeft _ F (kFlat_pullbackComplex' c hmos P hP hflat)]
      infer_instance
    have h₃ : IsIso (bifunctorMap T'.tensor (pullbackComparisonQ c P) (qΛ'.hom.app F)) := by
      unfold bifunctorMap
      infer_instance
    infer_instance
  let x := pullbackComparisonQ c Tot ≫
    DerivedCategory.Q.map (pullbackTensorComplexIso c hmos P ρF).hom ≫
      DerivedCategory.Q.map (tensorComplexMap (ringedTopos Λ' Z) (𝟙 _) εF)
  refine isIso_projectionMap_of_isIso_homEquiv _ _ _ _ v hv b hb d hd x ?_ ?_
  · have h₀ := derivedPullback_toTensor_square_unconditional c hmos P ρF
    have hnat := T'.toTensor_naturality (𝟙 ((pullbackComplex c).obj P)) εF
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hnat
    have hfac := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac c
      hmos ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)
    have hcounit : (coefficientPullback φ Z).map (qΛ.hom.app ρF) ≫ pullbackComparisonQ c ρF ≫
        DerivedCategory.Q.map εF =
        ((coefficientPullback φ Z).map v ≫ (coefficientAdjunction φ Z).counit.app _) ≫
          qΛ'.hom.app F := by
      have e₁ : (coefficientPullback φ Z).map (qΛ.hom.app ρF) ≫ pullbackComparisonQ c ρF ≫
          DerivedCategory.Q.map εF = (derivedPullbackComparison c).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ρF) ≫
            qΛ'.hom.app ((pullbackComplex c).obj ρF) ≫ DerivedCategory.Q.map εF := by
        show (derivedPullback c).map (qΛ.hom.app ρF) ≫ ((derivedPullback c).map (qΛ.inv.app ρF) ≫
          ((derivedPullbackComparison c).app _ ≫ qΛ'.hom.app _)) ≫ DerivedCategory.Q.map εF = _
        exact map_hom_comp_map_inv_comp_assoc (derivedPullback c) (qΛ.app ρF) _ _ _
      have h₂ : (derivedPullbackComparison c).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ρF) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map εF) =
          (coefficientPullback φ Z).map v ≫ (coefficientAdjunction φ Z).counit.app _ :=
        hfac.symm
      exact e₁.trans ((congrArg ((derivedPullbackComparison c).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ρF) ≫ ·)
          (DerivedCategory.quotientCompQhIso_hom_naturality εF).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ qΛ'.hom.app F) h₂)))
    exact map_comp_eq_of_toTensor_square T.tensor T'.tensor _ (coefficientTensorIso φ Z).hom
      (qΛ.hom.app ρF) (T.toTensor P ρF) (pullbackComparisonQ c P) (pullbackComparisonQ c ρF)
      (T'.toTensor _ _) (pullbackComparisonQ c Tot) _ _ _ (T'.toTensor _ F) _ (qΛ'.hom.app F)
      h₀ hnat.symm hcounit
  · have hεF : IsIso εF := by
      have : ∀ k, IsIso (εF.f k) := fun k => hε (F.X k)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hηT : IsIso (adjC.unit.app Tot) := by
      have : ∀ k, IsIso ((adjC.unit.app Tot).f k) := fun k => hη P F k
      exact HomologicalComplex.Hom.isIso_of_components _
    have htcm : IsIso (tensorComplexMap (ringedTopos Λ' Z) (𝟙 ((pullbackComplex c).obj P)) εF) :=
      (inferInstance : IsIso (((Stacks.SheafOfModules.Tensor.tensorComplex
        (ringedTopos Λ' Z).O).obj ((pullbackComplex c).obj P)).map εF))
    let rest := qΛ'.hom.app ((pullbackComplex c).obj Tot) ≫
      DerivedCategory.Q.map (pullbackTensorComplexIso c hmos P ρF).hom ≫
        DerivedCategory.Q.map (tensorComplexMap (ringedTopos Λ' Z) (𝟙 _) εF)
    have hrest : IsIso rest := inferInstance
    have hx' : (coefficientPullback φ Z).map (qΛ.hom.app Tot) ≫ x =
        (derivedPullbackComparison c).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot) ≫ rest := by
      show (derivedPullback c).map (qΛ.hom.app Tot) ≫ ((derivedPullback c).map (qΛ.inv.app Tot) ≫
        ((derivedPullbackComparison c).app _ ≫ qΛ'.hom.app _)) ≫ _ = _
      exact map_hom_comp_map_inv_comp_assoc (derivedPullback c) (qΛ.app Tot) _ _ _
    have hu : (coefficientAdjunction φ Z).unit.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) ≫
        (coefficientPushforward φ Z).map ((derivedPullbackComparison c).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) =
        DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction c).unit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) ≫
          (derivedPushforwardUnit c).app ((c.pullbackTopos.mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) :=
      derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac c hmos
        (fun h ↦ Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat c h)
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)
    have h₁ : IsIso ((coefficientAdjunction φ Z).unit.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) ≫
        (coefficientPushforward φ Z).map ((derivedPullbackComparison c).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot))) := by
      rw [hu]
      have : IsIso ((homotopyPullbackPushforwardAdjunction c).unit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot)) :=
        (inferInstance : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (adjC.unit.app Tot)))
      have := Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedPushforwardUnit_app_of_exact
        c ((c.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Tot))
      infer_instance
    exact isIso_homEquiv_of_fac (coefficientAdjunction φ Z) (qΛ.app Tot) x _ rest hx' h₁ hrest
end General

section ZMod

variable {n ℓ : ℕ} (hℓ : ℓ ∣ n) (Z : Scheme.{u})

/-- **Restriction of scalars along `ℤ/nℤ ⟶ ℤ/ℓℤ` is fully faithful**: its composite with the
underlying abelian sheaf is the underlying abelian sheaf, which is fully faithful for
`ℤ/ℓℤ`-coefficients, and the underlying abelian sheaf is faithful for `ℤ/nℤ`-coefficients. -/
def coefficientPushforwardZModFullyFaithful :
    (coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.FullyFaithful :=
  haveI := (etaleToSheafZModFullyFaithful n Z).faithful
  Functor.FullyFaithful.ofCompFaithful (G := etaleToSheaf (ULift.{u + 1} (ZMod n)) Z)
    (etaleToSheafZModFullyFaithful ℓ Z)

/-- **The counit `Λ' ⊗_Λ M ⟶ M` of the change of coefficients `ℤ/nℤ ⟶ ℤ/ℓℤ` is invertible**,
restriction of scalars being fully faithful. -/
theorem isIso_coefficientHom_zmod_counit_app
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Z).O)) :
    IsIso ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pullbackPushforwardAdjunctionTopos.counit
      |>.app G) :=
  have := (coefficientPushforwardZModFullyFaithful hℓ Z).full
  have := (coefficientPushforwardZModFullyFaithful hℓ Z).faithful
  inferInstance

/-- **The unit `M ⟶ Λ' ⊗_Λ M` of the change of coefficients `ℤ/nℤ ⟶ ℤ/ℓℤ` is invertible at a
sheaf annihilated by `ℓ`**: such a sheaf is a restriction of scalars
(`exists_coefficientPushforward_iso`), and at a restriction of scalars the unit is inverse to
the restriction of scalars of the counit (the triangle identity), which is invertible. -/
theorem isIso_coefficientHom_zmod_unit_app
    (A : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) Z).O)) (hA : ℓ • 𝟙 A = 0) :
    IsIso ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pullbackPushforwardAdjunctionTopos.unit
      |>.app A) := by
  obtain ⟨G, ⟨e⟩⟩ := exists_coefficientPushforward_iso hℓ A hA
  let adj := (coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pullbackPushforwardAdjunctionTopos
  have := isIso_coefficientHom_zmod_counit_app hℓ Z G
  have h₁ : IsIso (adj.unit.app ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.obj
      G)) := by
    have : IsIso (adj.unit.app ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.obj
        G) ≫ (coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.map
          (adj.counit.app G)) := by
      rw [adj.right_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.map (adj.counit.app G))
  exact (NatTrans.isIso_app_iff_of_iso adj.unit e).1 h₁

/-- **A total tensor complex `Tot(P ⊗_{ℤ/n} Rc_*F)` is annihilated by `ℓ` in each degree**: each
summand `P^i ⊗ Rc_*F^j` is, `Rc_*F^j` being annihilated by `ℓ`. -/
theorem nsmul_id_tensorComplex_coefficientPushforward_X_eq_zero
    (P : CochainComplex (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) Z).O)) ℤ)
    (F : CochainComplex (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Z).O)) ℤ) (k : ℤ) :
    ℓ • 𝟙 ((((Stacks.SheafOfModules.Tensor.tensorComplex
      (ringedTopos (ULift.{u + 1} (ZMod n)) Z).O).obj P).obj
        (((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)).X k) = 0 := by
  have hT : ∀ i j, ℓ • 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor
      (ringedTopos (ULift.{u + 1} (ZMod n)) Z).O).obj (P.X i)).obj
        ((coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos.obj (F.X j))) = 0 :=
    fun i j => nsmul_id_map_eq_zero ℓ _
      (nsmul_id_map_eq_zero ℓ (coefficientHom (zmodULiftRingHom.{u} hℓ) Z).pushforwardTopos
        (nsmul_id_eq_zero_zmod ℓ (F.X j)))
  have hc : ∀ {A B : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) Z).O)} (f : A ⟶ B), f ≫ (ℓ • 𝟙 B) = (ℓ • 𝟙 A) ≫ f :=
    fun f => by rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
      Category.id_comp]
  refine HomologicalComplex.mapBifunctor.hom_ext (fun i₁ i₂ h => ?_)
  exact ((hc _).trans ((congrArg (· ≫ HomologicalComplex.ιMapBifunctor _ _ _ _ i₁ i₂ k h)
    (hT i₁ i₂)).trans zero_comp)).trans comp_zero.symm

/-- **The projection formula of the change of coefficients `ℤ/nℤ ⟶ ℤ/ℓℤ`**: for `ℓ ∣ n`,
`K ∈ D(Z_étale, ℤ/n)` and `N ∈ D(Z_étale, ℤ/ℓ)` the projection map
`K ⊗^L_{ℤ/n} Rc_*N ⟶ Rc_*(Lc^*K ⊗^L_{ℤ/ℓ} N)` is an isomorphism. This is the step
`p⁻¹E ⊗^L_{ℤ/n} (f')⁻¹Rg_*𝒢 = p⁻¹(E ⊗^L_{ℤ/n} 𝔽_ℓ) ⊗^L_{𝔽_ℓ} (f')⁻¹Rg_*𝒢` of the proof of
[Stacks, Tag 0F1J]. -/
theorem isIso_coefficientProjectionMap_zmodULiftRingHom
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Z)
    (N : DerivedModules (ULift.{u + 1} (ZMod ℓ)) Z) :
    IsIso (coefficientProjectionMap (zmodULiftRingHom.{u} hℓ) Z K N) :=
  isIso_coefficientProjectionMap_of_isIso_unit _ Z (isIso_coefficientHom_zmod_counit_app hℓ Z)
    (fun P F k => isIso_coefficientHom_zmod_unit_app hℓ Z _
      (nsmul_id_tensorComplex_coefficientPushforward_X_eq_zero hℓ Z P F k)) K N

end ZMod

section Assembly


open Stacks.EtaleCohomology.BaseChangeOverField

variable {S X X' S' T Y : Scheme.{u}} (πX : X ⟶ S) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
  (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]


include s hX' in
/-- **The canonical map of Tag 0F1J over `ℤ/nℤ` at a sheaf annihilated by a prime `ℓ ∣ n`**,
placed in any degree, from the case of `𝔽_ℓ`-coefficients. The base change map is invertible by
derived base change over `X` (`hBC`), and the projection map of `h` over `ℤ/nℤ` at
`(p⁻¹E, e⁻¹G[j])` is read, through `G = Rc_*G'`, on the projection map of `h` over `𝔽_ℓ` at
`(Lc^*p⁻¹E, e⁻¹G'[j]) = (p⁻¹Lc^*E, e⁻¹G'[j])`
(`isIso_projectionMap_coefficientPushforward_of_isIso`), which is Tag 0F1J for `ℓ`
(`isIso_tensorBaseChangeMap_of_derivedBaseChangeHolds`), `Lc^*E` having the Tor amplitude of `E`.
The projection maps of the change of coefficients are invertible by
`isIso_coefficientProjectionMap_zmodULiftRingHom`. -/
theorem isIso_tensorBaseChangeMap_singleFunctor_of_nsmul_prime (n ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ∣ n) (hBC : DerivedBaseChangeHolds πX n)
    (hBCaff : ∀ {U Z : Scheme.{u}} (ιU : U ⟶ X) [IsOpenImmersion ιU] [IsAffine U] (π : Z ⟶ U)
      [IsFinite π], DerivedBaseChangeHolds (π ≫ ιU ≫ πX) n)
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (a : ℤ)
    (hE : HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a)
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) T).O)) (hG : ℓ • 𝟙 G = 0) (j : ℤ) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E)
        ((DerivedCategory.singleFunctor _ j).obj G)) := by
  have hdvd : (ℓ : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hℓ
  have hbc := isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds n πX hBC s p f' hX'
    g h e hY G j
  rw [isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _ hbc]
  obtain ⟨G', ⟨eG⟩⟩ := exists_coefficientPushforward_iso hℓ G hG
  let φ := zmodULiftRingHom.{u} hℓ
  let N := (pullback (ULift.{u + 1} (ZMod ℓ)) e).obj ((DerivedCategory.singleFunctor _ j).obj G')
  let eN : (coefficientPushforward φ Y).obj N ≅
      (pullback (ULift.{u + 1} (ZMod n)) e).obj ((DerivedCategory.singleFunctor _ j).obj G) :=
    (coefficientPushforward φ Y).mapIso (pullbackObjSingleFunctorObjIsoOfExact _ e j G') ≪≫
      coefficientPushforwardSingleIso φ Y j _ ≪≫
      (DerivedCategory.singleFunctor _ j).mapIso (coefficientPushforwardPullbackToposIso hℓ e G' ≪≫
        (ringedToposHom (ULift.{u + 1} (ZMod n)) e).pullbackTopos.mapIso eG) ≪≫
      (pullbackObjSingleFunctorObjIsoOfExact _ e j G).symm
  refine (isIso_projectionMap_iff_of_iso_right n h _ eN).1 ?_
  refine isIso_projectionMap_coefficientPushforward_of_isIso φ h _ N
    (isIso_coefficientProjectionMap_zmodULiftRingHom hℓ _ _ _)
    (isIso_coefficientProjectionMap_zmodULiftRingHom hℓ _ _ _) ?_
  refine (isIso_projectionMap_iff_of_iso _ h ((coefficientPullbackSquareIso φ p).app E).symm N).1 ?_
  have hBCℓ : DerivedBaseChangeHolds πX ℓ := hBC.of_dvd hdvd
  have hT := isIso_tensorBaseChangeMap_of_derivedBaseChangeHolds ℓ πX s p f' hX' g h e hY hBCℓ
    (fun ιU _ _ π _ => (hBCaff ιU π).of_dvd hdvd) ((coefficientPullback φ X).obj E) a
    (hasTorAmplitudeGE_coefficientPullback_obj φ E a hE)
    ((DerivedCategory.singleFunctor _ j).obj G') j
    inferInstance
  have hbc' := isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds ℓ πX hBCℓ s p f'
    hX' g h e hY G' j
  exact (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _ hbc').1 hT

include s hX' in
/-- **[Stacks, Tag 0F1J] for `ℤ/nℤ`-coefficients, from derived base change.** In the setting of
Tag 0F1J (`X' = X ×_S S'`, `Y = X' ×_{S'} T`, `g` quasi-compact and quasi-separated), the
canonical map

`p⁻¹E ⊗^L_{ℤ/n} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/n} e⁻¹F)`

is invertible for `E ∈ D(X_étale, ℤ/n)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, ℤ/n)`.
The source's proof: reduce `F` to a single sheaf `G`
(`isIso_tensorBaseChangeMap_of_isIso_singleFunctor_right`), and `G`, annihilated by `n`, through
`0 → G[ℓ] → G → G/G[ℓ] → 0` to sheaves annihilated by a prime `ℓ ∣ n`
(`forall_of_nsmul_id_eq_zero`; both sides are exact functors of `F`), where it is
`isIso_tensorBaseChangeMap_singleFunctor_of_nsmul_prime`.

Not registered: derived base change along `X ⟶ S` (`hBC`) and along the finite schemes over the
affine opens of `X` (`hBCaff`), for sheaves annihilated by `n`, are explicit arguments (for
`S = Spec K` with `n` invertible in `K` they are [Stacks, Tag 0F1I]). The projection formula of
the change of coefficients `ℤ/n ⟶ ℤ/ℓ` is `isIso_coefficientProjectionMap_zmodULiftRingHom`. -/
theorem isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds (n : ℕ)
    [NeZero n] (hBC : DerivedBaseChangeHolds πX n)
    (hBCaff : ∀ {U Z : Scheme.{u}} (ιU : U ⟶ X) [IsOpenImmersion ιU] [IsAffine U] (π : Z ⟶ U)
      [IsFinite π], DerivedBaseChangeHolds (π ≫ ιU ≫ πX) n)
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (a : ℤ)
    (hE : HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (b : ℤ) (hF : F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  let η := tensorBaseChangeNatTransRight (ULift.{u + 1} (ZMod n)) f' g h e hY.w
    ((pullback (ULift.{u + 1} (ZMod n)) p).obj E)
  let P : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) T).O) → Prop := fun G =>
    NatTrans.isoLocusAtShifts η ((DerivedCategory.singleFunctor _ 0).obj G)
  have key : ∀ G, P G := fun G => by
    refine forall_of_nsmul_id_eq_zero P (fun G hG m => ?_) (fun S hS h₁ h₃ => ?_) n
      (NeZero.ne n) (fun ℓ hℓ hℓn G hG m => ?_) n dvd_rfl G (nsmul_id_eq_zero_zmod n G)
    · have hz : IsZero (((DerivedCategory.singleFunctor _ 0).obj G)⟦m⟧) :=
        Functor.map_isZero _ (Functor.map_isZero _ hG)
      exact isIso_of_source_target_iso_zero _ (Functor.map_isZero _ hz).isoZero
        (Functor.map_isZero _ hz).isoZero
    · exact (NatTrans.isoLocusAtShifts η).ext_of_isTriangulatedClosed₂ hS.singleTriangle
        hS.singleTriangle_distinguished h₁ h₃
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      refine (η.isIso_app_iff_of_iso
        (((DerivedCategory.singleFunctors _).shiftIso m (-m) 0 (by omega)).app G).symm).1 ?_
      exact isIso_tensorBaseChangeMap_singleFunctor_of_nsmul_prime πX s p f' hX' g h e hY n ℓ
        hℓn hBC hBCaff E a hE G hG (-m)
  refine isIso_tensorBaseChangeMap_of_isIso_singleFunctor_right _ f' g h e hY.w _ a
    (hasTorAmplitudeGE_pullback_obj _ p E a hE) (fun G j => ?_) F b hF
  exact (η.isIso_app_iff_of_iso
    (((DerivedCategory.singleFunctors _).shiftIso (-j) j 0 (by omega)).app G)).1 (key G (-j))

end Assembly

end Stacks.EtaleCohomology.EtaleCoefficients

end
