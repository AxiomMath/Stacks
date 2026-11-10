module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeRectangle
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCellStage
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullbackConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer

/-!
# Stacks 0CMT: the base change of a limit preserving 1-morphism

Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the big
fppf category of a scheme `S`. **Stacks 0CMT** says that if `p` is limit preserving then so is the
base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵`.

Both conditions are properties of the single square `AlgebraicGeometry.Stack.canonicalSquare` of
Stacks 0CMR -- of `p'` for the conclusion and of `p` for the hypothesis -- by
`AlgebraicGeometry.Stack.isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare`. The two squares
are compared by the two pastings of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeRectangle`, which produce two
rectangles with the same apex `colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}`, the same left leg `colim (p')_{Uᵢ}` and the
same right leg `p_U`, whose horizontal legs factor the two ways round the squares of Stacks 0CMR
for the two projections and for `q`. This file supplies the one remaining input: that the two
fillers agree through those 2-cells.

Since the lower right corner of both rectangles is the plain fibre `𝒴_U`, and not a 2-fibre
product, the coherence is a single identity rather than a pair of components. It is checked at an
object of a stage of the colimit, every object of the colimit being of that form, and there it
says that the chosen pullback of the comparison isomorphism of Stacks 02XI is the comparison
isomorphism of the chosen pullback -- which is
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_inv_comp_pullbackFiberHom_proj`, the
base-change comparisons of the two projections and of `p` and `q` cancelling in pairs.

## Main results

* `AlgebraicGeometry.Stack.baseChangeFillerCoherence`: the coherence of the two fillers, the
  hypothesis `hα` of
  `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
  for the two rectangles.
* `AlgebraicGeometry.Stack.isEquivalence_squareComparison_canonicalSquare_twoFibreProductSnd`:
  the square of Stacks 0CMR for `p'` is 2-cartesian as soon as the square of `p` is.
* `AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProductSnd`: **Stacks 0CMT**.

## Implementation notes

The stagewise coherence is split over four declarations because `maxHeartbeats` is per
declaration: the normalization of the two sides, the identity they reduce to in the fibre at the
cone point, the restriction of the stagewise comparison to the cone point, and the reading of the
stagewise comparison's structural isomorphism down the universe lift.

Every transport in sight mediates between two spellings of one object that differ by an unfolding
of `CategoryTheory.Functor.comp`, and such a composite is type-correct only at default
transparency. Two devices keep `simp` able to work: the bridging lemmas state the endpoints of
their transports in the spelling the neighbouring morphism has
(`CategoryTheory.Cat.twoFibreProductStage_obj_iso_hom_aligned` and
`CategoryTheory.Limits.CategoricalPullback.projFillerOfEq_hom_app`), which is why their proofs are
chains of named equalities rather than `rfl` -- a type ascription on `rfl` is discarded, and the
type of a transport is read off its proof; and the two steps that no rewriting tactic can take are
term-mode lemmas applied with `exact`
(`AlgebraicGeometry.Stack.up_map_plumb` and `…comp₄_eq_comp₄_comp_map_id`).

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Bicategory.InducedBicategory Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor
  Deformation.Artin.colimitComparison Deformation.Artin.evaluateSplitFiber
  BigFppfOver.twoFibreProduct BasedCategory.ofFunctor Functor.fiberMap
  Functor.SplitFiber.evaluation splitFiberTwoFibreProductComparisonApp
  splitFiberTwoFibreProductComparisonStage fiberDiagramMap
  CategoryTheory.Limits.CategoricalPullback.map Cat.twoFibreProductStage
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]


/-- **Two chains of transports and images that agree because their images do.** The transports
of both chains are between one and the same pair of objects, so they collapse; what is left is
the functor applied to the two composites, which the hypothesis identifies.

Stated in term mode, and applied with `exact`, because the chains it closes are type-correct only
at default transparency: their transports mediate between spellings of one object that differ by
an unfolding. -/
private lemma up_map_plumb {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a₁ a₂ a₃ b₂ b₃ b₄ : C} (m : a₁ ⟶ a₂) (n : a₂ ⟶ a₃)
    (m' : a₁ ⟶ b₂) (n' : b₂ ⟶ b₃) (r : b₃ ⟶ b₄) (t : b₄ ⟶ a₃)
    (h : m ≫ n = m' ≫ n' ≫ r ≫ t)
    {X Y : D} (e₁ : X = F.obj a₁) (e₂ : F.obj a₂ = F.obj a₂) (e₃ : F.obj a₃ = Y)
    (f₁ : X = F.obj a₁) (f₂ : F.obj b₂ = F.obj b₂) (f₃ : F.obj b₃ = F.obj b₃)
    (f₄ : F.obj a₃ = Y) :
    eqToHom e₁ ≫ F.map m ≫ eqToHom e₂ ≫ F.map n ≫ eqToHom e₃ =
      eqToHom f₁ ≫ F.map m' ≫ eqToHom f₂ ≫ F.map n' ≫ eqToHom f₃ ≫ F.map r ≫ F.map t ≫
        eqToHom f₄ := by
  subst e₁
  subst e₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, h]
  simp only [CategoryTheory.Functor.map_comp]

/-- A chain of four morphisms, followed by the image of an identity. Stated in term mode, and
applied with `exact`, because the identity's image sits at the end of a right-associated chain,
where a rewriting tactic cannot reach it: the chain is type-correct only at default
transparency. -/
private lemma comp₄_eq_comp₄_comp_map_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {Y₁ Y₂ Y₃ Y₄ : D} {Z : C} (f₁ : Y₁ ⟶ Y₂) (f₂ : Y₂ ⟶ Y₃) (f₃ : Y₃ ⟶ Y₄)
    (f₄ : Y₄ ⟶ F.obj Z) :
    f₁ ≫ f₂ ≫ f₃ ≫ f₄ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ F.map (𝟙 Z) := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The universe lift of a morphism, read back down. -/
private lemma down_map_up_map {C : Type*} [Category C] {a b : C} (f : a ⟶ b) :
    AsSmall.down.map (AsSmall.up.map f) = f := rfl

/-- The universe lift of an object, read back down. -/
private lemma down_obj_up_obj {C : Type*} [Category C] (a : C) :
    AsSmall.down.obj (AsSmall.up.obj a) = a := rfl

/-- An equality of objects of an explicit 2-fibre product, read on their structural
isomorphisms. -/
private lemma iso_hom_of_obj_eq {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    (F : 𝒜 ⥤ 𝒞) (G : ℬ ⥤ 𝒞) {P Q : CategoricalPullback F G} (h : P = Q) :
    P.iso.hom = eqToHom (congrArg (fun R => F.obj R.fst) h) ≫ Q.iso.hom ≫
      eqToHom (congrArg (fun R => G.obj R.snd) h).symm := by
  subst h
  simp

/-- Evaluating the restriction of a morphism of split fibres at the cone point is base change of
the underlying morphism of the fibre. -/
private lemma evaluateSplitFiber_map_restrict_map {C : Type*} [Category C] {X : Type*}
    [Category X] (P : X ⥤ C) [P.IsFibered] {V V' : C} (g : V' ⟶ V)
    {o o' : P.SplitFiber V} (m : o ⟶ o') :
    (Deformation.Artin.evaluateSplitFiber P V').map ((Functor.SplitFiber.restrict P g).map m) =
      Functor.SplitFiber.restrictHom g (Functor.SplitFiber.toFiberHom m) := rfl

/-- **The structural isomorphism of the componentwise reading of an object of the split fibre of
a base change**: the chosen pullback of the structural isomorphism of the object's image under
the comparison of Stacks 02XI. -/
lemma splitFiberTwoFibreProductComparisonApp_obj_iso_hom (V : BigFppfOver B S hS)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    ((splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V).obj o).iso.hom =
      Functor.SplitFiber.ofFiberHom (Functor.pullbackFiberHom
        ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) o.base).obj o.obj).iso.hom o.hom) := rfl

/-- **The structural isomorphism of the stagewise comparison** is the universe lift of that of
the componentwise reading: the two changes of cospan the lift inserts are identities. -/
lemma splitFiberTwoFibreProductComparisonStage_obj_iso_hom (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber
        (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    ((splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).obj o).iso.hom =
      AsSmall.up.map ((splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q
        (E.obj j.unop)).obj o).iso.hom := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  change 𝟙 _ ≫ AsSmall.up.map _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- **The structural isomorphism of the lifted comparison of Stacks 02XI** is the lift of that of
the unlifted one, the two changes of cospan the lift inserts being identities. -/
lemma baseChangeFiberPullback_obj_iso_hom (V : BigFppfOver B S hS)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      AsSmall.{max (u + 1) v w}
        ((BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.Fiber V)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    ((baseChangeFiberPullback.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V).obj o).iso.hom =
      AsSmall.up.map (((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
        (CatFiberedInGroupoids.homFunctor_comp_p p)
        (CatFiberedInGroupoids.homFunctor_comp_p q) V).obj (AsSmall.down.obj o)).iso.hom) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  change 𝟙 _ ≫ AsSmall.up.map _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- **The structural isomorphism of the stagewise comparison, read down the universe lift**: the
chosen pullback along the structure morphism of the object's own structural isomorphism under the
comparison of Stacks 02XI. -/
lemma down_map_comparisonStage_obj_iso_hom (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber
        (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    AsSmall.down.map
        (((splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).obj o).iso.hom) =
      Functor.SplitFiber.ofFiberHom (Functor.pullbackFiberHom
        ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) o.base).obj o.obj).iso.hom o.hom) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  rw [splitFiberTwoFibreProductComparisonStage_obj_iso_hom]
  rfl

/-- **The structural isomorphism of the stagewise comparison, restricted to the cone point.**
Reading it down the universe lift and restricting along the cone projection gives the chosen
pullback of the comparison isomorphism of Stacks 02XI along the composite morphism, which is
`CategoryTheory.TwoFibreProductOver.restrictHom_pullbackFiberHom`. It is applied with `exact`
rather than used as a rewrite: that lemma pins the two objects of the split fibre as explicit
triples, and the triples agree with the objects here only definitionally. -/
lemma restrictHom_down_map_comparisonStage (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber
        (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Functor.SplitFiber.restrictHom (d.π.app j.unop)
        (Functor.SplitFiber.toFiberHom (AsSmall.down.map
          ((splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).obj y₀).iso.hom)) =
      Functor.pullbackFiberHom
        ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) y₀.base).obj y₀.obj).iso.hom
        (d.π.app j.unop ≫ y₀.hom) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  rw [down_map_comparisonStage_obj_iso_hom]
  exact TwoFibreProductOver.restrictHom_pullbackFiberHom _ _ _

/-- **The core of the coherence of the two fillers, in the fibre at the cone point.** On the left
the base-change comparison of `p` and the chosen pullback of the comparison isomorphism of
Stacks 02XI; on the right the base-change comparisons of the two projections of the base change
and of `q`, around the comparison isomorphism of the chosen pullback. The two agree by
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_inv_comp_pullbackFiberHom_proj`, the
chosen pullback of a comparison isomorphism being the comparison isomorphism of the chosen
pullback. -/
lemma baseChangeFillerCoherence_core (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber
        (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    ((isFibredOneMorphism B S hS p).mapPullbackFiberIso
          ((splitFiberMap B S hS (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
            (E.obj j.unop)).obj y₀).obj
          (d.π.app j.unop ≫
            ((splitFiberMap B S hS
              (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
              (E.obj j.unop)).obj y₀).hom)).inv ≫
        Functor.SplitFiber.restrictHom (d.π.app j.unop)
          (Functor.SplitFiber.toFiberHom (AsSmall.down.map
            ((splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).obj y₀).iso.hom)) =
      (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt).map
          ((isFibredOneMorphism B S hS
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)).mapPullbackFiberIso
            y₀.obj (d.π.app j.unop ≫ y₀.hom)).hom ≫
        ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
            (CatFiberedInGroupoids.homFunctor_comp_p p)
            (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt).obj
          ((Deformation.Artin.evaluateSplitFiber
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p d.pt).obj
            ((Functor.SplitFiber.restrict
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p
              (d.π.app j.unop)).obj y₀))).iso.hom ≫
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt).map
            ((isFibredOneMorphism B S hS
              (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)).mapPullbackFiberIso
              y₀.obj (d.π.app j.unop ≫ y₀.hom)).inv ≫
          ((isFibredOneMorphism B S hS q).mapPullbackFiberIso
            ((splitFiberMap B S hS
              (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
              (E.obj j.unop)).obj y₀).obj
            (d.π.app j.unop ≫
              ((splitFiberMap B S hS
                (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
                (E.obj j.unop)).obj y₀).hom)).inv := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  rw [restrictHom_down_map_comparisonStage]
  exact TwoFibreProductOver.mapPullbackFiberIso_inv_comp_pullbackFiberHom_proj 𝒳.val.p 𝒵.val.p
    𝒴.val.p (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
    (isFibredOneMorphism B S hS p) (isFibredOneMorphism B S hS q)
    𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q))
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q))
    y₀.obj (d.π.app j.unop ≫ y₀.hom)

/-- **The coherence of the two fillers at an object of a stage.** Both sides are read at the
image of an object `y₀` of a stage: the 2-cells of the four squares of Stacks 0CMR become the
base-change comparisons of `p`, `q` and the two projections at the restriction of `y₀` to the cone
point, the comparison of the colimits becomes the stagewise comparison, and the comparison of
Stacks 02XI becomes the comparison isomorphism of the chosen pullback. What is left is
`AlgebraicGeometry.Stack.baseChangeFillerCoherence_core`. -/
lemma baseChangeFillerCoherence_ι (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber
        (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS p E d).hom.app
          ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor.obj
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up).map
          ((CategoricalPullback.projFillerOfEq _ _ _ _
            (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)
            (BigFppfOver.colimMap_twoFibreProductFst_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 𝒵 p q E)
            (BigFppfOver.colimMap_twoFibreProductSnd_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 𝒵 p q E)).hom.app
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) =
      (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
            AsSmall.up).map
          ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d).inv.app
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
        (baseChangeFiberFiller.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q d.pt).hom.app
          ((Deformation.Artin.colimitComparison
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙
            AsSmall.up).obj
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
        (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
            AsSmall.up).map
          ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d).hom.app
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS q E d).hom.app
          ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor.obj
            ((colimit.ι (Deformation.Artin.fiberDiagram
                (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
              j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  have hι : ∀ (𝒜 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
        (BigFppfOver B S hS))
      (f : BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q ⟶ 𝒜),
      letI : 𝒜.val.p.IsFibered := 𝒜.2.isFibered
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor.obj
          ((colimit.ι (Deformation.Artin.fiberDiagram
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
            j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) =
        (colimit.ι (Deformation.Artin.fiberDiagram 𝒜.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj
            ((splitFiberMap B S hS f (E.obj j.unop)).obj y₀)) := fun 𝒜 f => by
    let : 𝒜.val.p.IsFibered := 𝒜.2.isFibered
    exact Functor.congr_obj (Cat.ι_colimMap_toFunctor
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j)
      (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)
  have hρ := hι 𝒳 (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
  have hσ := hι 𝒵 (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)
  have hW : (Deformation.Artin.colimitComparison
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}).obj
        ((colimit.ι (Deformation.Artin.fiberDiagram
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
          j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) =
      AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}.obj
        ((Deformation.Artin.evaluateSplitFiber
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p d.pt).obj
          ((Functor.SplitFiber.restrict
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p
            (d.π.app j.unop)).obj y₀)) :=
    Functor.congr_obj (Deformation.Artin.ι_comp_colimitComparison_comp_up.{max (u + 1) v w}
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d j)
      (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)
  have hK : (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).obj
        ((colimit.ι (Deformation.Artin.fiberDiagram
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)
          j).toFunctor.obj (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) =
      (Cat.twoFibreProductStage
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) j).obj
        ((splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).obj y₀) :=
    Functor.congr_obj (ι_comp_colimitSplitFiberTwoFibreProductComparison
      B S hS 𝒳 𝒴 𝒵 p q E j) (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)
  rw [natTrans_app_eq_of_obj_eq
    (baseChangeFiberFiller.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q d.pt).hom hW]
  simp only [natTrans_app_eq_of_obj_eq
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS p E d).hom hρ,
    natTrans_app_eq_of_obj_eq
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS q E d).hom hσ,
    down_map_up_map, down_obj_up_obj,
    canonicalTwoCellUp_hom_app_ι, canonicalTwoCellUp_inv_app_ι,
    splitEvaluationIso_hom_app, splitEvaluationIso_inv_app,
    Functor.SplitFiber.restrict_obj_base, Functor.SplitFiber.restrict_obj_obj,
    Functor.SplitFiber.restrict_obj_hom,
    baseChangeFiberFiller, CategoricalPullback.projFillerOfEq_hom_app,
    iso_hom_of_obj_eq _ _ hK,
    Cat.twoFibreProductStage_obj_iso_hom_aligned,
    CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map,
    CategoryTheory.Functor.comp_map,
    Deformation.Artin.up_map_colimitComparison_map_ι_map,
    evaluateSplitFiber_map_restrict_map,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simp only [baseChangeFiberPullback_obj_iso_hom, down_obj_up_obj]
  refine up_map_plumb AsSmall.up _ _ _ _ _ _ ?_ _ _ _ _ _ _ _
  exact baseChangeFillerCoherence_core B S hS 𝒳 𝒴 𝒵 p q E d j y₀

/-- **The coherence hypothesis `hα` of the transfer lemma for the two rectangles of Stacks
0CMT.** The filler of the rectangle built from the colimit 2-fibre product and the square of `p`
is the filler of the rectangle built from the square of `p'` and Stacks 02XI, read through the
2-cells of the two projections and of `q`.

It is checked at an object of a stage of the colimit, every object of the colimit being of that
form by `CategoryTheory.Cat.exists_stage_obj_of_colimit`; no filteredness is needed. -/
lemma baseChangeFillerCoherence (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    ∀ x : ↑(colimit (Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E)),
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS p E d).hom.app
          ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor.obj
            x) ≫
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up).map
          ((CategoricalPullback.projFillerOfEq _ _ _ _
            (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)
            (BigFppfOver.colimMap_twoFibreProductFst_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 𝒵 p q E)
            (BigFppfOver.colimMap_twoFibreProductSnd_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 𝒵 p q E)).hom.app x) =
      (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
            AsSmall.up).map
          ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d).inv.app x) ≫
        (baseChangeFiberFiller.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q d.pt).hom.app
          ((Deformation.Artin.colimitComparison
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙
            AsSmall.up).obj x) ≫
        (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
            AsSmall.up).map
          ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d).hom.app x) ≫
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS q E d).hom.app
          ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor.obj
            x) :=
  fun x => by
    let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
    obtain ⟨j, y, rfl⟩ := Cat.exists_stage_obj_of_colimit.{u + 1, v, w} _ x
    obtain ⟨y₀, rfl⟩ :
        ∃ y₀, AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀ = y :=
      ⟨AsSmall.down.{max u v, max (u + 1) v w, max v w}.obj y, rfl⟩
    exact baseChangeFillerCoherence_ι B S hS 𝒳 𝒴 𝒵 p q E d j y₀

/-- **The square of Stacks 0CMR for the base change `p'` is 2-cartesian as soon as the square of
`p` is.** The first pasting replaces `p'`'s square by a rectangle whose cospan is the fibres of
`p` and `q` at the cone point; the second builds, from the square of the colimits and the square
of `p`, a rectangle with the same apex and the same two vertical legs; and the two rectangles
differ only by the 2-cells of the two projections and of `q` on their horizontal legs, which is
`AlgebraicGeometry.Stack.baseChangeFillerCoherence`. So
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_congr_top` and
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
identify them, the comparisons of the lower corners being identity functors. -/
lemma isEquivalence_squareComparison_canonicalSquare_twoFibreProductSnd
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) [IsFiltered Iᵒᵖ]
    (hp : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
      (CategoricalPullback.squareComparison
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)).toFunctor
        (AsSmall.down ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
          AsSmall.up)
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v}
          B S hS p E d)).IsEquivalence) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.squareComparison
      (Deformation.Artin.colimitComparison
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
        (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d)).IsEquivalence := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  refine (isEquivalence_squareComparison_baseChangeRectangle_iff.{u, v, w}
    B S hS 𝒳 𝒴 𝒵 p q E d).mp ?_
  refine (CategoricalPullback.isEquivalence_squareComparison_congr_top _ _ _ _ _ _
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d)).mpr ?_
  refine (@CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up) ⋙
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
        AsSmall.up))
    _ _ _
    ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).toFunctor ⋙
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up))
    _ (𝟭 _) (𝟭 _) (Iso.refl _) (Iso.refl _)
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS q E d).symm
    inferInstance inferInstance inferInstance (fun x => ?_)).mpr
    (isEquivalence_squareComparison_baseChangeColimitRectangle.{u, v, w}
      B S hS 𝒳 𝒴 𝒵 p q E d hp)
  simp only [CategoricalPullback.pasteFiller_hom_app, CategoricalPullback.topIsoFiller_hom_app,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Functor.id_map,
    CategoryTheory.Functor.comp_map, Iso.symm_inv,
    Category.assoc, Category.id_comp]
  refine (baseChangeFillerCoherence B S hS 𝒳 𝒴 𝒵 p q E d x).trans ?_
  exact comp₄_eq_comp₄_comp_map_id _ _ _ _ _

/-- **Stacks 0CMT.** The base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a limit preserving 1-morphism `p` of
categories fibred in groupoids over the big fppf category of a scheme `S` is limit preserving.

Both conditions are properties of `AlgebraicGeometry.Stack.canonicalSquare` -- of `p'` for the
conclusion and of `p` for the hypothesis -- by
`AlgebraicGeometry.Stack.isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare`, and the two
squares are 2-cartesian together by
`AlgebraicGeometry.Stack.isEquivalence_squareComparison_canonicalSquare_twoFibreProductSnd`. The
input the source leaves implicit is that filtered colimits of categories commute with 2-fibre
products, which is what identifies `colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}` with
`colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`. -/
@[stacks 0CMT]
theorem isLimitPreserving_twoFibreProductSnd
    (hp : IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS p) :
    IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) := by
  rw [isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare]
  intro J _ _ D c hc
  have : IsFiltered Jᵒᵖ := (isFiltered_op_iff_isCofiltered J).2 inferInstance
  refine Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor _ ?_
  exact isEquivalence_squareComparison_canonicalSquare_twoFibreProductSnd.{u, v, w}
    B S hS 𝒳 𝒴 𝒵 p q (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c)
    (Cat.isEquivalence_toCategoricalPullbackFunctor
      ((isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare B S hS p).mp hp
        J D c hc).some)

end AlgebraicGeometry.Stack

end
