module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliMap
public import StacksFrontier.AlgebraicGeometry.Stacks.CategoricalModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Base change of the chart of a well-nigh affine stack

Let `𝒳` be a well-nigh affine algebraic stack with chart `x : U ⟶ 𝒳` and moduli morphism
`f : 𝒳 ⟶ M` (`AlgebraicGeometry.Stack.WellNighAffineChart.moduliMap`), and let `a : T ⟶ M` be a
morphism from an affine object of the site. The proof of Stacks 0DUP studies the base change
`f' : T ×_M 𝒳 ⟶ T` through the base change `U' = T ×_M U` of the chart and the base change
`R' ⟶ U'` of the relation. This file provides the stack-theoretic part of that study:

* the base-changed chart `x' : U' ⟶ T ×_M 𝒳` into the canonical 2-fibre product
  (`AlgebraicGeometry.Stack.WellNighAffineChart.baseChart`);
* the two composites `R' ⟶ U' ⟶ T ×_M 𝒳` are joined by a vertical morphism;
* every object of `T ×_M 𝒳` comes, after restriction to a covering sieve, from `x'`.

From these, `f'` is a categorical moduli space in the category of affine schemes as soon as
`U' ⟶ T` is a categorical quotient of `R' ⇉ U'` in the category of affine schemes
(`AlgebraicGeometry.Stack.WellNighAffineChart.isCategoricalModuliSpaceIn_baseChange`).

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Generalities -/

/-- **Being a categorical moduli space in a full subcategory does not depend on the chosen
2-fibre product.** This is `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_isTwoFibreProduct`
against the test objects selected by a predicate. -/
theorem isCategoricalModuliSpaceIn_of_isTwoFibreProduct
    {𝒳 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Pr : AlgebraicSpaces B S hS → Prop) {Y : AlgebraicSpaces B S hS}
    {a : fibredCategory B S hS Y.obj ⟶ 𝒵} {f : 𝒳 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq a f}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hc : IsCategoricalModuliSpaceIn B S hS Pr Y Q.fst) :
    IsCategoricalModuliSpaceIn B S hS Pr Y P.fst := by
  classical
  let L := Bicategory.twoFibreProductPreHom hQ P
  let N := Bicategory.twoFibreProductPreHom hP Q
  obtain ⟨e, -⟩ := Bicategory.twoFibreProductPreHom_rel hP (L.comp N) (.id P)
  refine ⟨hc.1, fun W hW g => ?_⟩
  obtain ⟨k, ⟨hk⟩, hu⟩ := hc.2 W hW (N.hom ≫ g)
  refine ⟨k, ⟨?_⟩, ?_⟩
  · exact Bicategory.whiskerRightIso L.isoFst (associatedMap B S hS k.hom).1 ≪≫
      Bicategory.whiskerLeftIso L.hom hk ≪≫
      Bicategory.whiskerRightIso e g ≪≫ Bicategory.leftUnitor g
  · rintro k' ⟨hk'⟩
    exact hu k' ⟨Bicategory.whiskerRightIso N.isoFst (associatedMap B S hS k'.hom).1 ≪≫
      Bicategory.whiskerLeftIso N.hom hk'⟩

/-- A morphism of the category of elements of a presheaf lying over `k : V ⟶ U`, from the
restriction of an element along `k` to the element itself. -/
def elementsRestrictionHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {V U : BigFppfOver B S hS}
    (k : V ⟶ U) (y : F.obj (op U)) :
    (⟨V, Discrete.mk (F.map k.op y)⟩ : (fibredCategory B S hS F).val.obj) ⟶ ⟨U, Discrete.mk y⟩ :=
  ⟨k, Discrete.eqToHom rfl⟩

/-- The morphism `elementsRestrictionHom F k y` lies over `k`. -/
theorem isHomLift_elementsRestrictionHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {V U : BigFppfOver B S hS} (k : V ⟶ U) (y : F.obj (op U)) :
    (fibredCategory B S hS F).val.p.IsHomLift k (elementsRestrictionHom F k y) :=
  IsHomLift.of_fac' _ _ _ rfl rfl (by rfl)

/-- The section named by an object of a fibre of a category of elements which is equal to an
explicit pair is the second component of that pair. -/
theorem discreteFiberEquiv_of_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {V : BigFppfOver B S hS}
    (X : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (h : (PresheafOfCategories.discreteProjection F).obj X = V) (x : F.obj (op V))
    (hX : X = ⟨V, Discrete.mk x⟩) :
    PresheafOfCategories.discreteFiberEquiv F V ⟨X, h⟩ = x := by
  subst hX; rfl

/-- A morphism of the category of elements of a presheaf lying over `k : V ⟶ X.base`, from the
restriction along `k` of the element named by `X` to `X` itself. -/
def elementsRestrictionHom' (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (X : (fibredCategory B S hS F).val.obj) {V : BigFppfOver B S hS} (k : V ⟶ X.base) :
    (⟨V, Discrete.mk (F.map k.op X.fiber.as)⟩ : (fibredCategory B S hS F).val.obj) ⟶ X :=
  ⟨k, Discrete.eqToHom rfl⟩

/-- The morphism `elementsRestrictionHom' F X k` lies over `k`. -/
theorem isHomLift_elementsRestrictionHom' (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (X : (fibredCategory B S hS F).val.obj) {V : BigFppfOver B S hS} (k : V ⟶ X.base) :
    (fibredCategory B S hS F).val.p.IsHomLift k (elementsRestrictionHom' F X k) :=
  IsHomLift.of_fac' _ _ _ rfl rfl (by rfl)

/-- The structure functor of a category of elements of a presheaf is fibred in sets. -/
private instance isFiberedInSets_fibredCategory_p (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory B S hS F).val.p.IsFiberedInSets :=
  inferInstanceAs (PresheafOfCategories.discreteProjection F).IsFiberedInSets

/-- **Composites in a category of elements lying over one morphism agree**: a morphism over `k`
followed by a vertical one equals a vertical one followed by a morphism over `k`, between the
same objects. -/
theorem elements_comp_eq_comp_of_isHomLift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {A X Y Z : (fibredCategory B S hS F).val.obj} {V W : BigFppfOver B S hS} (k : V ⟶ W)
    (u₁ : A ⟶ X) (u₂ : X ⟶ Z) (v₁ : A ⟶ Y) (v₂ : Y ⟶ Z)
    (hu₁ : (fibredCategory B S hS F).val.p.IsHomLift k u₁)
    (hu₂ : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 W) u₂)
    (hv₁ : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 V) v₁)
    (hv₂ : (fibredCategory B S hS F).val.p.IsHomLift k v₂) : u₁ ≫ u₂ = v₁ ≫ v₂ := by
  exact @Functor.IsFiberedInSets.hom_ext_of_isHomLift _ _ _ _
    (fibredCategory B S hS F).val.p _ _ _ k _ _ _ _
    (@IsHomLift.comp_lift_id_right' _ _ _ _ _ _ _ _ _ _ k _ hu₁ W _ hu₂)
    (@IsHomLift.comp_lift_id_left' _ _ _ _ _ _ _ _ V _ hv₁ _ _ k _ hv₂)

namespace WellNighAffineChart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- **Every object of `𝒳` comes from the chart after restriction to a covering sieve**: the chart
is surjective, flat and locally of finite presentation. -/
theorem exists_sieve_lift (V : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber V) :
    ∃ R ∈ BigFppfOver.topology B S hS V,
      ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃k : V' ⟶ V⦄, R.arrows k →
        ∃ (z : (schemeFibredCategory B S hS K.U).val.obj)
          (φ : K.chart.hom.hom.obj z ⟶ y.1), 𝒳.val.val.p.IsHomLift k φ := by
  obtain ⟨hrep, hfin⟩ := K.isFinite_chart
  obtain ⟨-, hfp⟩ := K.isRelativelyFinitePresentation_chart
  have hflatP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) K.chart.hom hrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (schemeStack.{u, w} B S hS K.U).property 𝒳.property K.chart.hom hrep).1 K.isFlat_chart
  have hsurjP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) K.chart.hom hrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS K.chart hrep).1
      K.isSurjective_chart
  exact localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS K.chart.hom hrep
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      (hfp T y hy G hG he).1⟩) V y

/-! ### The base change square -/

section BaseChange

variable {T : BigFppfOver B S hS} {a₀ : T ⟶ K.moduliObject}
  {U' : BigFppfOver B S hS} (pr₁ : U' ⟶ T) (pr₂ : U' ⟶ K.U)
  {Y' : AlgebraicSpaces B S hS} (e : Y'.obj ≅ yoneda.obj T) (a : Y' ⟶ K.moduliSpace)

/-- The first leg `U' ⟶ T ≅ Y'` of the square of the base-changed chart. -/
noncomputable def baseFst :
    (schemeFibredCategory B S hS U').val ⥤ᵇ (fibredCategory B S hS Y'.obj).val :=
  BasedFunctor.comp (sliceElementsComparison B S hS U')
    (associatedMap B S hS (yoneda.map pr₁ ≫ e.inv)).1.hom

/-- The second leg `U' ⟶ U ⟶ 𝒳` of the square of the base-changed chart. -/
noncomputable def baseSnd : (schemeFibredCategory B S hS U').val ⥤ᵇ 𝒳.val.val :=
  BasedFunctor.comp (schemeFibredCategoryMap B S hS pr₂).hom K.chart.hom.hom

variable {pr₁ pr₂ e a}

/-- The square of the base-changed chart commutes on the nose. -/
theorem baseFst_comp_eq (ha : e.inv ≫ a.hom = yoneda.map a₀)
    (hcomm : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀) :
    BasedFunctor.comp (baseFst pr₁ e) (associatedMap B S hS a.hom).1.hom =
      BasedFunctor.comp (K.baseSnd pr₂) K.moduliMap.hom.hom := by
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _
    (BasedFunctor.comp (baseFst pr₁ e) (associatedMap B S hS a.hom).1.hom).w
    (BasedFunctor.comp (K.baseSnd pr₂) K.moduliMap.hom.hom).w (fun z => ?_)
  have hR := congrArg (fun L : (schemeFibredCategory B S hS K.U).val ⥤ᵇ
      (fibredCategory B S hS K.moduliSpace.obj).val =>
        L.obj ((schemeFibredCategoryMap B S hS pr₂).hom.obj z)) K.chart_comp_moduliMap
  refine Eq.trans ?_ hR.symm
  let z' : Over U' := z
  show (associatedMap B S hS a.hom).1.hom.obj
      ((associatedMap B S hS (yoneda.map pr₁ ≫ e.inv)).1.hom.obj
      ((sliceElementsComparison B S hS U').obj z)) =
    (associatedMap B S hS (yoneda.map K.quotientMap)).1.hom.obj
      ((sliceElementsComparison B S hS K.U).obj ((schemeFibredCategoryMap B S hS pr₂).hom.obj z))
  rw [associatedMap_obj, associatedMap_obj, associatedMap_obj]
  have h₁ := congrArg (fun φ => φ.app (op z'.left) (z'.hom ≫ pr₁)) ha
  have hval : a.hom.app (op z'.left) (e.inv.app (op z'.left) (z'.hom ≫ pr₁)) =
      (z'.hom ≫ pr₂) ≫ K.quotientMap := by
    refine h₁.trans ?_
    show (z'.hom ≫ pr₁) ≫ a₀ = _
    rw [Category.assoc, Category.assoc, hcomm]
  exact congrArg (fun x => (⟨z'.left, Discrete.mk x⟩ :
    (fibredCategory B S hS K.moduliSpace.obj).val.obj)) hval

/-- **The square of the base-changed chart**: `U' ⟶ T ≅ Y'` and `U' ⟶ U ⟶ 𝒳` over `M`. -/
noncomputable def baseSquare (ha : e.inv ≫ a.hom = yoneda.map a₀)
    (hcomm : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀) :
    Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 K.moduliMap.hom where
  pt := schemeFibredCategory B S hS U'
  fst := Bicategory.InducedBicategory.mkHom (baseFst pr₁ e)
  snd := Bicategory.InducedBicategory.mkHom (K.baseSnd pr₂)
  iso := eqToIso (Bicategory.InducedBicategory.hom_ext (K.baseFst_comp_eq ha hcomm))

/-- **The base-changed chart `x' : U' ⟶ T ×_M 𝒳`**, into the canonical 2-fibre product. -/
noncomputable def baseChart (ha : e.inv ≫ a.hom = yoneda.map a₀)
    (hcomm : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀) :
    schemeFibredCategory B S hS U' ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt :=
  CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
    (K.baseSquare ha hcomm)

end BaseChange

section BaseChartObj

variable {T : BigFppfOver B S hS} {a₀ : T ⟶ K.moduliObject}
  {U' : BigFppfOver B S hS} {pr₁ : U' ⟶ T} {pr₂ : U' ⟶ K.U}
  {Y' : AlgebraicSpaces B S hS} {e : Y'.obj ≅ yoneda.obj T} {a : Y' ⟶ K.moduliSpace}
  (ha : e.inv ≫ a.hom = yoneda.map a₀) (hcomm : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀)

/-- The base of the image under the base-changed chart of `z : Over U'` is `z.left`. -/
theorem baseChart_obj_base (z : Over U') :
    ((K.baseChart ha hcomm).hom.obj z).base = z.left := rfl

/-- The `Y'`-component of the image under the base-changed chart of `z` is its image under
`baseFst`. -/
theorem baseChart_obj_x (z : Over U') :
    ((K.baseChart ha hcomm).hom.obj z).x = (baseFst pr₁ e).obj z := rfl

/-- The `𝒳`-component of the image under the base-changed chart of `z` is its image under
`baseSnd`. -/
theorem baseChart_obj_y (z : Over U') :
    ((K.baseChart ha hcomm).hom.obj z).y = (K.baseSnd pr₂).obj z := rfl

/-- The structure functor of the 2-fibre product sends the image under the base-changed chart of
`z : Over U'` to `z.left`. -/
theorem baseChart_p_obj (z : Over U') :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.obj
      ((K.baseChart ha hcomm).hom.obj z) = z.left := rfl

/-- `baseFst` sends `z : Over U'` to the element `e⁻¹ (z.hom ≫ pr₁)` of `Y'` over `z.left`. -/
theorem baseFst_obj (z : Over U') :
    (baseFst pr₁ e).obj z =
      ⟨z.left, Discrete.mk (e.inv.app (op z.left) (z.hom ≫ pr₁))⟩ :=
  associatedMap_obj B S hS (yoneda.map pr₁ ≫ e.inv) ((sliceElementsComparison B S hS U').obj z)

/-- `baseSnd` sends `z : Over U'` to the image under the chart of `z.hom ≫ pr₂`. -/
theorem baseSnd_obj (z : Over U') :
    (K.baseSnd pr₂).obj z = K.chart.hom.hom.obj (Over.mk (z.hom ≫ pr₂)) := rfl

end BaseChartObj

/-- The structure functor of the canonical 2-fibre product sends a morphism to its base
morphism. -/
theorem twoFibreProductSquare_p_map {Y' : AlgebraicSpaces B S hS} {a : Y' ⟶ K.moduliSpace}
    {ζ ξ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.obj} (m : ζ ⟶ ξ) :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.map m = m.hbase := rfl

/-- The structure functor of the canonical 2-fibre product sends an object to its base. -/
theorem twoFibreProductSquare_p_obj {Y' : AlgebraicSpaces B S hS} {a : Y' ⟶ K.moduliSpace}
    (ζ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.obj) :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.obj ζ = ζ.base := rfl


section BaseChartProperties

variable {T : BigFppfOver B S hS} {a₀ : T ⟶ K.moduliObject}
  {U' : BigFppfOver B S hS} {pr₁ : U' ⟶ T} {pr₂ : U' ⟶ K.U}
  {Y' : AlgebraicSpaces B S hS} {e : Y'.obj ≅ yoneda.obj T} {a : Y' ⟶ K.moduliSpace}
  (ha : e.inv ≫ a.hom = yoneda.map a₀) (hcomm : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀)

/-- The comparison isomorphism of the image under the base-changed chart of `u` is vertical. -/
private theorem isHomLift_baseChart_obj_iso_hom (u : Over U') :
    (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 u.left)
      ((K.baseChart ha hcomm).hom.obj u).iso.hom := by
  have := ((K.baseChart ha hcomm).hom.obj u).vertical
  rwa [baseChart_obj_base] at this

/-- Restricting an element of `Y'` along `k` agrees with transporting its restriction through
`e`. -/
private theorem map_op_eq_inv_app_comp_hom_app {xb : BigFppfOver B S hS} (xe : Y'.obj.obj (op xb))
    {z : BigFppfOver B S hS} (k : z ⟶ xb) :
    Y'.obj.map k.op xe = e.inv.app (op z) (k ≫ e.hom.app (op xb) xe) := by
  have := NatTrans.naturality_apply e.inv k.op (e.hom.app (op xb) xe)
  change e.inv.app (op z) (k ≫ e.hom.app (op xb) xe) =
    Y'.obj.map k.op (e.inv.app (op xb) (e.hom.app (op xb) xe)) at this
  rw [this]
  exact congrArg (Y'.obj.map k.op) (congrFun (congrArg (fun φ => (φ.app (op xb) : _ → _))
    e.hom_inv_id) xe).symm

/-- **The two composites `R' ⟶ U' ⟶ T ×_M 𝒳` are joined by a vertical morphism**, for a pair
`s', t' : R' ⟶ U'` over the relation `s, t : R ⟶ U` along `ρ : R' ⟶ R` with
`pr₁ ∘ s' = pr₁ ∘ t'`. -/
theorem exists_vertical_baseChart {V' : BigFppfOver B S hS} (s' t' : V' ⟶ U') (ρ : V' ⟶ K.V)
    (hs : s' ≫ pr₂ = ρ ≫ K.s) (ht : t' ≫ pr₂ = ρ ≫ K.t) (hpr : s' ≫ pr₁ = t' ≫ pr₁) :
    ∃ φ : (K.baseChart ha hcomm).hom.obj (Over.mk s') ⟶
        (K.baseChart ha hcomm).hom.obj (Over.mk t'),
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.IsHomLift (𝟙 V') φ := by
  have hxeq : (baseFst pr₁ e).obj (Over.mk s') = (baseFst pr₁ e).obj (Over.mk t') :=
    (baseFst_obj (Over.mk s')).trans ((congrArg (fun v : V' ⟶ T =>
      (⟨V', Discrete.mk (e.inv.app (op V') v)⟩ : (fibredCategory B S hS Y'.obj).val.obj)) hpr).trans
        (baseFst_obj (Over.mk t')).symm)
  have hy₁ : (K.baseSnd pr₂).obj (Over.mk s') =
      K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.s).hom.obj (Over.mk ρ)) :=
    (K.baseSnd_obj (Over.mk s')).trans (congrArg (fun v => K.chart.hom.hom.obj (Over.mk v)) hs)
  have hy₂ : K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.t).hom.obj (Over.mk ρ)) =
      (K.baseSnd pr₂).obj (Over.mk t') :=
    (congrArg (fun v => K.chart.hom.hom.obj (Over.mk v)) ht.symm).trans
      (K.baseSnd_obj (Over.mk t')).symm
  obtain ⟨ψ, hψ⟩ := K.vertical (Over.mk ρ)
  -- the same facts, read on the components of the two objects of the 2-fibre product
  have hx' : ((K.baseChart ha hcomm).hom.obj (Over.mk s')).x =
      ((K.baseChart ha hcomm).hom.obj (Over.mk t')).x :=
    (K.baseChart_obj_x ha hcomm (Over.mk s')).trans
      (hxeq.trans (K.baseChart_obj_x ha hcomm (Over.mk t')).symm)
  have hy₁' : ((K.baseChart ha hcomm).hom.obj (Over.mk s')).y =
      K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.s).hom.obj (Over.mk ρ)) :=
    (K.baseChart_obj_y ha hcomm (Over.mk s')).trans hy₁
  have hy₂' : K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.t).hom.obj (Over.mk ρ)) =
      ((K.baseChart ha hcomm).hom.obj (Over.mk t')).y :=
    hy₂.trans (K.baseChart_obj_y ha hcomm (Over.mk t')).symm
  have ha' : (fibredCategory B S hS Y'.obj).val.p.IsHomLift (𝟙 V') (eqToHom hx') :=
    IsHomLift.eqToHom_domain_lift_id hx'
      (((K.baseChart ha hcomm).hom.obj (Over.mk s')).hx.trans
        (K.baseChart_obj_base ha hcomm (Over.mk s')))
  have hb' : 𝒳.val.val.p.IsHomLift (𝟙 V') (eqToHom hy₁' ≫ ψ ≫ eqToHom hy₂') := by
    rwa [IsHomLift.comp_eqToHom_lift_iff, IsHomLift.eqToHom_comp_lift_iff]
  refine ⟨⟨𝟙 V', eqToHom hx', eqToHom hy₁' ≫ ψ ≫ eqToHom hy₂', ha', hb', ?_⟩, ?_⟩
  · exact elements_comp_eq_comp_of_isHomLift K.moduliSpace.obj (𝟙 V') _ _ _ _
      (Functor.isHomLift_map_of_comp_eq (associatedMap B S hS a.hom).1.hom.w (𝟙 V') _)
      (K.isHomLift_baseChart_obj_iso_hom ha hcomm (Over.mk t'))
      (K.isHomLift_baseChart_obj_iso_hom ha hcomm (Over.mk s'))
      (Functor.isHomLift_map_of_comp_eq K.moduliMap.hom.hom.w (𝟙 V') _)
  · refine IsHomLift.of_fac' _ (𝟙 V') _ (K.baseChart_p_obj ha hcomm (Over.mk s'))
      (K.baseChart_p_obj ha hcomm (Over.mk t')) ?_
    refine (K.twoFibreProductSquare_p_map _).trans ?_
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_refl V' rfl).symm
include ha in
/-- **A lift of the `𝒳`-component of an object of `T ×_M 𝒳` to the chart is compatible with its
`T`-component in `M`.** -/
theorem quotientMap_eq_of_isHomLift {xb : BigFppfOver B S hS} (xe : Y'.obj.obj (op xb))
    (y : 𝒳.val.val.obj)
    (iso : (associatedMap B S hS a.hom).1.hom.obj ⟨xb, Discrete.mk xe⟩ ≅ K.moduliMap.hom.hom.obj y)
    (vert : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 xb) iso.hom)
    (hy : 𝒳.val.val.p.obj y = xb) (z : Over K.U) (k : z.left ⟶ xb)
    (φ : K.chart.hom.hom.obj z ⟶ y) (hφ : 𝒳.val.val.p.IsHomLift k φ) :
    z.hom ≫ K.quotientMap = (k ≫ e.hom.app (op xb) xe) ≫ a₀ := by
  have h₂ : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 xb)
      (𝟙 (K.moduliMap.hom.hom.obj y)) :=
    IsHomLift.id (p := (fibredCategory B S hS K.moduliSpace.obj).val.p)
      ((Functor.congr_obj K.moduliMap.hom.hom.w y).trans hy)
  have hFG : (associatedMap B S hS a.hom).1.hom.obj ⟨xb, Discrete.mk xe⟩ =
      K.moduliMap.hom.hom.obj y :=
    (@Functor.IsFiberedInSets.eq_of_isHomLift _ _ _ _
      (fibredCategory B S hS K.moduliSpace.obj).val.p _ _ _ (𝟙 xb) _ _ _ iso.hom
      (𝟙 (K.moduliMap.hom.hom.obj y)) vert h₂).1
  have hF : (associatedMap B S hS a.hom).1.hom.obj ⟨xb, Discrete.mk xe⟩ =
      ⟨xb, Discrete.mk (a.hom.app (op xb) xe)⟩ := associatedMap_obj B S hS a.hom _
  have hG : K.moduliMap.hom.hom.obj (K.chart.hom.hom.obj z) =
      ⟨z.left, Discrete.mk (z.hom ≫ K.quotientMap)⟩ :=
    (congrArg (fun L : (schemeFibredCategory B S hS K.U).val ⥤ᵇ
        (fibredCategory B S hS K.moduliSpace.obj).val => L.obj z) K.chart_comp_moduliMap).trans
      (associatedMap_obj B S hS (yoneda.map K.quotientMap) _)
  have hsec₀ := PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift K.moduliSpace.obj k
    ⟨K.moduliMap.hom.hom.obj y, (Functor.congr_obj K.moduliMap.hom.hom.w y).trans hy⟩
    ⟨K.moduliMap.hom.hom.obj (K.chart.hom.hom.obj z),
      (Functor.congr_obj K.moduliMap.hom.hom.w _).trans (Functor.congr_obj K.chart.hom.hom.w z)⟩
    (K.moduliMap.hom.hom.toFunctor.map φ)
    (Functor.isHomLift_map_of_comp_eq K.moduliMap.hom.hom.w k φ)
  have hsec : z.hom ≫ K.quotientMap = K.moduliSpace.obj.map k.op (a.hom.app (op xb) xe) :=
    (discreteFiberEquiv_of_eq K.moduliSpace.obj _ _ _ hG).symm.trans (hsec₀.trans
      (congrArg (K.moduliSpace.obj.map k.op)
        (discreteFiberEquiv_of_eq K.moduliSpace.obj _ _ _ (hFG.symm.trans hF))))
  rw [hsec, ← NatTrans.naturality_apply a.hom k.op xe,
    map_op_eq_inv_app_comp_hom_app (e := e) xe k]
  exact congrFun (congrArg (fun φ => (φ.app (op z.left) : _ → _)) ha) (k ≫ e.hom.app (op xb) xe)

include ha in
/-- The point of `U' = T ×_M U` determined by a lift to the chart of the `𝒳`-component of an object
of `T ×_M 𝒳` together with its `T`-component. -/
theorem exists_point_baseChart (hpb : IsPullback pr₂ pr₁ K.quotientMap a₀)
    (ζ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.obj)
    (z : Over K.U) (k : z.left ⟶ ζ.base) (φ : K.chart.hom.hom.obj z ⟶ ζ.y)
    (hφ : 𝒳.val.val.p.IsHomLift k φ) :
    ∃ u₀ : z.left ⟶ U', u₀ ≫ pr₂ = z.hom ∧
      u₀ ≫ pr₁ = (k ≫ eqToHom ζ.hx.symm) ≫ e.hom.app (op ζ.x.base) ζ.x.fiber.as := by
  have hX : ζ.x.base = ζ.base := ζ.hx
  have hφX : 𝒳.val.val.p.IsHomLift (k ≫ eqToHom hX.symm) φ :=
    (IsHomLift.lift_comp_eqToHom_iff _ _ _ _).2 hφ
  have hvertX : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 ζ.x.base)
      ζ.iso.hom := by
    have := ζ.vertical
    rwa [← hX] at this
  exact ⟨hpb.lift z.hom _ (K.quotientMap_eq_of_isHomLift ha ζ.x.fiber.as ζ.y ζ.iso hvertX
    (ζ.hy.trans hX.symm) z (k ≫ eqToHom hX.symm) φ hφX), hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩

/-- **The morphism from the base-changed chart to an object of `T ×_M 𝒳` along a lift of its
`𝒳`-component**, given the corresponding point of `U'`. -/
theorem exists_hom_baseChart (hpb : IsPullback pr₂ pr₁ K.quotientMap a₀)
    (ζ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.obj)
    (z : Over K.U) (k : z.left ⟶ ζ.base) (φ : K.chart.hom.hom.obj z ⟶ ζ.y)
    (hφ : 𝒳.val.val.p.IsHomLift k φ) (u₀ : z.left ⟶ U') (h₂ : u₀ ≫ pr₂ = z.hom)
    (h₁ : u₀ ≫ pr₁ = (k ≫ eqToHom ζ.hx.symm) ≫ e.hom.app (op ζ.x.base) ζ.x.fiber.as) :
    ∃ m : (K.baseChart ha hpb.w).hom.obj (Over.mk u₀) ⟶ ζ,
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.IsHomLift k m := by
  have hX : ζ.x.base = ζ.base := ζ.hx
  let kX : z.left ⟶ ζ.x.base := k ≫ eqToHom hX.symm
  have hA : ((K.baseChart ha hpb.w).hom.obj (Over.mk u₀)).x =
      ⟨z.left, Discrete.mk (Y'.obj.map kX.op ζ.x.fiber.as)⟩ :=
    (K.baseChart_obj_x ha hpb.w (Over.mk u₀)).trans ((baseFst_obj (Over.mk u₀)).trans
      ((congrArg (fun v => (⟨z.left, Discrete.mk (e.inv.app (op z.left) v)⟩ :
        (fibredCategory B S hS Y'.obj).val.obj)) h₁).trans
        (congrArg (fun v => (⟨z.left, Discrete.mk v⟩ : (fibredCategory B S hS Y'.obj).val.obj))
          (map_op_eq_inv_app_comp_hom_app (e := e) ζ.x.fiber.as kX).symm)))
  have hB : ((K.baseChart ha hpb.w).hom.obj (Over.mk u₀)).y = K.chart.hom.hom.obj z :=
    (K.baseChart_obj_y ha hpb.w (Over.mk u₀)).trans ((K.baseSnd_obj (Over.mk u₀)).trans
      (congrArg (fun v => K.chart.hom.hom.obj (Over.mk v)) h₂))
  have hma : (fibredCategory B S hS Y'.obj).val.p.IsHomLift k
      (eqToHom hA ≫ elementsRestrictionHom' Y'.obj ζ.x kX) :=
    (IsHomLift.comp_eqToHom_lift_iff _ _ _ _).2 ((IsHomLift.lift_comp_eqToHom_iff _ _ _ _).1
      (isHomLift_elementsRestrictionHom' Y'.obj ζ.x kX))
  have hmb : 𝒳.val.val.p.IsHomLift k (eqToHom hB ≫ φ) :=
    (IsHomLift.comp_eqToHom_lift_iff _ _ _ _).2 hφ
  refine ⟨⟨k, eqToHom hA ≫ elementsRestrictionHom' Y'.obj ζ.x kX, eqToHom hB ≫ φ, hma, hmb,
    elements_comp_eq_comp_of_isHomLift K.moduliSpace.obj k _ _ _ _
      (Functor.isHomLift_map_of_comp_eq (associatedMap B S hS a.hom).1.hom.w k _) ζ.vertical
      (K.isHomLift_baseChart_obj_iso_hom ha hpb.w (Over.mk u₀))
      (Functor.isHomLift_map_of_comp_eq K.moduliMap.hom.hom.w k _)⟩, ?_⟩
  refine IsHomLift.of_fac' _ k _ (K.baseChart_p_obj ha hpb.w (Over.mk u₀))
    (K.twoFibreProductSquare_p_obj ζ) ?_
  refine (K.twoFibreProductSquare_p_map _).trans ?_
  show k = eqToHom rfl ≫ k ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **Every object of `T ×_M 𝒳` comes from the base-changed chart after restriction to a
covering sieve.** The `𝒳`-component lifts to the chart along a covering sieve (the chart is
surjective, flat and locally of finite presentation), and the lift together with the
`T`-component meets in `U' = T ×_M U`. -/
theorem exists_sieve_lift_baseChart (hpb : IsPullback pr₂ pr₁ K.quotientMap a₀)
    (ζ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.obj) :
    ∃ R ∈ BigFppfOver.topology B S hS ζ.base,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ ζ.base⦄, R.arrows k →
        ∃ (u : Over U') (m : (K.baseChart ha hpb.w).hom.obj u ⟶ ζ),
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p.IsHomLift k m := by
  obtain ⟨R, hR, hr⟩ := K.exists_sieve_lift ζ.base ⟨ζ.y, ζ.hy⟩
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hr hk
  have hzV : (z : Over K.U).left = V := by
    have : 𝒳.val.val.p.IsHomLift k φ := hφ
    exact (Functor.congr_obj K.chart.hom.hom.w z).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p k φ)
  subst hzV
  obtain ⟨u₀, h₂, h₁⟩ := K.exists_point_baseChart ha hpb ζ z k φ hφ
  obtain ⟨m, hm⟩ := K.exists_hom_baseChart ha hpb ζ z k φ hφ u₀ h₂ h₁
  exact ⟨Over.mk u₀, m, hm⟩

/-- **1-morphisms from `T ×_M 𝒳` to an algebraic space are determined by their restriction to
the base-changed chart.** -/
theorem baseChart_ext (hpb : IsPullback pr₂ pr₁ K.quotientMap a₀) {W : AlgebraicSpaces B S hS}
    (g₁ g₂ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val ⥤ᵇ (fibredCategory B S hS W.obj).val)
    (h : BasedFunctor.comp (K.baseChart ha hpb.w).hom g₁ =
      BasedFunctor.comp (K.baseChart ha hpb.w).hom g₂) : g₁ = g₂ := by
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _ g₁.w g₂.w (fun ζ => ?_)
  obtain ⟨R, hR, hr⟩ := K.exists_sieve_lift_baseChart ha hpb ζ
  have key : PresheafOfCategories.discreteFiberEquiv W.obj ζ.base
        ⟨g₁.obj ζ, Functor.congr_obj g₁.w ζ⟩ =
      PresheafOfCategories.discreteFiberEquiv W.obj ζ.base
        ⟨g₂.obj ζ, Functor.congr_obj g₂.w ζ⟩ := by
    refine ((isSheaf_iff_isSheaf_of_type _ _).mp W.property.isSheaf R hR).isSeparatedFor.ext ?_
    intro V k hk
    obtain ⟨u, m, hm⟩ := hr hk
    have hu : ((K.baseChart ha hpb.w).hom.obj u).base = V :=
      (K.baseChart_obj_base ha hpb.w u).trans
        (IsHomLift.domain_eq (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val.p k m)
    have hg (g : type_of% g₁) := PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift
      W.obj k ⟨g.obj ζ, Functor.congr_obj g.w ζ⟩
      ⟨g.obj ((K.baseChart ha hpb.w).hom.obj u), (Functor.congr_obj g.w _).trans hu⟩
      (g.toFunctor.map m) (Functor.isHomLift_map_of_comp_eq g.w k m)
    rw [← hg g₁, ← hg g₂]
    have hobj := congrArg (fun L : (schemeFibredCategory B S hS U').val ⥤ᵇ
      (fibredCategory B S hS W.obj).val => L.obj u) h
    exact congrArg (PresheafOfCategories.discreteFiberEquiv W.obj V)
      (Subtype.ext hobj)
  exact congrArg Subtype.val ((PresheafOfCategories.discreteFiberEquiv W.obj ζ.base).injective key)

end BaseChartProperties

end WellNighAffineChart

end AlgebraicGeometry.Stack

end
