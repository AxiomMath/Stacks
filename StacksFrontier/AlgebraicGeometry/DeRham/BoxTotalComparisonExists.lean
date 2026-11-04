module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonNaturality

/-!
# Step (5) of [Stacks, Tag 0G4A] exists

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a`. For `𝓕^•` and `𝓖^•` complexes of quasi-coherent modules whose
differentials are finite-order differential operators on `X/S` and on `Y/S`, both strictly
bounded below, the degreewise comparisons
`p^{-1}𝓕^i ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j` of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` assemble into a
morphism of complexes

`Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)`.

This is step (5) of the construction of the Künneth maps of [Stacks, Tag 0G4A], which
`StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison` carried as the parameter
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison`. It is a parameter no longer: the datum is
constructed here, and being unique by
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison.hom_unique` it is canonical.

What the construction needs, and what was missing until the naturality of
`relativeBoxComparison` in the two differential operators was proved in
`StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonNaturality`, is exactly the commutation
of the degreewise comparisons with the two differentials of the two double complexes: the
differential of a total complex acts on the summand of degree `(i, j)` by
`d ⊗ 1 + (-1)^i (1 ⊗ d)` on the source and by `d ⊠ 1 + (-1)^i (1 ⊠ d)` on the target, and a
differential of `𝓕^•` is a differential operator, not an `𝒪_W`-linear map.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.boxTotalComparisonMap`: the degreewise step-(5) comparison,
  defined on the summand of degree `(i, j)` as `relativeBoxComparison` followed by the inclusion
  of the summand.
* `Stacks.Cohomology.BoxKunneth.boxTotalComparisonHom`: **step (5), the morphism of complexes.**
* `Stacks.Cohomology.BoxKunneth.boxTotalComparison`: **the step-(5) datum**, inhabiting
  `Stacks.Cohomology.BoxKunneth.BoxTotalComparison`.

## Main results

* `Stacks.Cohomology.BoxKunneth.ι_boxTotalComparisonMap`: its component on a summand is the
  degreewise comparison, which is the field `BoxTotalComparison.ι_hom` asks for.
* `Stacks.Cohomology.BoxKunneth.boxTotalComparisonMap_comm`: **it commutes with the two
  differentials**, which is what the naturality of `relativeBoxComparison` in the two operators
  supplies.
* `HomologicalComplex.ιMapBifunctor_d_up_ℤ`: [Stacks, Tag 012Z] for the total complex of
  `F(K^p, L^q)`, for any bifunctor additive in each variable — the generic form of
  `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.ιMapBifunctor_d_up_ℤ`.

## Implementation notes

*Everything is split as far as it will go, and nothing is rewritten in a concrete goal.* The two
total complexes are spelled differently — the source through the curried tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` applied to the two inverse-image complexes, the target
through the bifunctor `(𝓕, 𝓖) ↦ p^{-1}𝓕 ⊗ q^{-1}𝓖` on the product category, and the target of
step (5) through restriction of scalars applied *after* the total complex rather than degreewise
— so the commutation crosses three definitional seams. Each crossing is affordable once, and the
budget is per declaration: the associativity rearrangement, the crossing proper and the
assembly are therefore separate declarations per leg (`..._comp_ι`, `..._assoc₁`, `..._whisk`,
`..._cross`, `boxTotalLeg..`), and the algebra of `d₁ + (-1)^i d₂` is
`CategoryTheory.summand_comm`, stated over variables and applied by unification. A single
declaration doing two crossings exhausts the heartbeat limit; the same work split takes a few
seconds.

*Whiskering a naturality square by the inclusion of a summand has to be done as a rewrite, not
as a term.* `CategoryTheory.eq_whisker` applied to
`relativeBoxComparison_naturality_d_fst`/`_snd` exceeds the heartbeat limit every way it can be
written — with the tail morphism explicit, under `by exact`, as
`congrArg (fun m => m ≫ ι) ..`, and inside an `Eq.trans` chain. What does work is `rw` with the
naturality as the rewrite rule: it fires, and leaves a goal whose two sides print identically
but which `rw`'s own closing `rfl`, run at reducible transparency, cannot discharge. The `rfl`
*tactic*, at default transparency, can. That is why `..._whisk` ends in `; rfl` and why
`..._cross` ends in `simp only [Category.assoc]` followed by `rfl` rather than in
`exact Category.assoc _ _ _`, which times out on the very goal the pair closes.

*Each link is its own declaration with both bracketings written out, and they are chained by
`rw`, not by `Eq.trans`.* Two links that each check in seconds still time out when glued by
`Eq.trans`: the composite's implicit middle object is solved to the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling in one statement and to the
`relativeInverseImageTensor` spelling in the other, and reconciling them is a `whnf` the
`Eq.trans` has to pay. Writing both bracketings into each statement lets the unifier read the
splitting off the goal, and `rw` then matches syntactically and fails fast instead of searching.
Note that `simp only [← Category.assoc]` will *not* fire on the left-hand side at that seam
while firing on the right: the two spellings are `rfl` at default transparency but not at the
reducible transparency a rewrite matches at.

*The restriction of scalars is applied to the total complex, not degreewise.* So the target is
not itself the total complex of a bicomplex of `f^{-1}𝒪_S`-modules, and the inclusion of a
summand is `Stacks.Cohomology.BoxKunneth.boxTotalι`, the image under restriction of scalars of
the inclusion in the differential-operator category. `boxTotalι_comp_d` is the differential read
through it.

*The naturality in one operator is read off the bifunctor of the product category.* The source
total complex presents its degreewise tensor product through the curried
`Stacks.SheafOfModules.Tensor.sheafTensor`, whereas
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison_naturality` is
stated for the bifunctor `relativeInverseImageTensor` on the product category. On a pair one of
whose legs is an identity the uncurried map of that bifunctor is the curried map of the other
leg; that identification is `CategoryTheory.uncurry_prod_map_id_right` and `..._left`, stated
over variables so that they run on a goal in which no object has a spelling, which is what the
rest of this file needs them for: at the spellings of this file a rewrite cannot fire, the
objects being type-correct only at default transparency.

*The additivity of `⊗_{f^{-1}𝒪_S}` in the second variable is passed, not searched.* Instance
search finds `(sheafTensor 𝒪).PreservesZeroMorphisms` but not the family
`∀ M, ((sheafTensor 𝒪).obj M).PreservesZeroMorphisms` that a total complex also asks for, so the
four declarations forming or indexing the source total complex supply both from
`AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms` and
`..._obj_preservesZeroMorphisms`, which are stated over arbitrary zero-morphism structures and so
hold at either spelling of the sheaf of rings. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison` for why the two spellings do not meet.

## References

* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

universe u

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-! ### Generic lemmas on total complexes and additive functors -/

/-- **[Stacks, Tag 012Z] for the total complex of `F(K^p, L^q)`**, for any bifunctor additive in
each variable: on the summand of degree `(p, q)` the differential is
`F(d_K, 1) + (-1)^p F(1, d_L)`. -/
theorem HomologicalComplex.ιMapBifunctor_d_up_ℤ {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ Z, (F.obj Z).PreservesZeroMorphisms]
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)]
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n h ≫
        (HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)).d n (n + 1) =
      (F.map (K.d p (p + 1))).app (L.X q) ≫
          HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) (p + 1) q (n + 1)
            (by dsimp; lia) +
        p.negOnePow • ((F.obj (K.X p)).map (L.d q (q + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p (q + 1) (n + 1)
            (by dsimp; lia)) := by
  refine (HomologicalComplex₂.ιTotal_d_up_ℤ _ p q n h).trans ?_
  have h₁ : (((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).d p (p + 1)).f q) =
      (F.map (K.d p (p + 1))).app (L.X q) :=
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f _ _ _ K L p (p + 1) q
  have h₂ : ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).X p).d q (q + 1) =
      (F.obj (K.X p)).map (L.d q (q + 1)) :=
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d _ _ _ K L p q (q + 1)
  rw [h₁, h₂]
  rfl

/-- An additive functor applied to a summandwise differential `u ≫ d = g₁ ≫ k₁ + ε • g₂ ≫ k₂`.
Every object and every morphism is a variable, so the rewrites run on a goal carrying no
concrete spelling. -/
theorem CategoryTheory.Functor.map_comp_eq_add_units_smul {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {P Q R B₁ B₂ : C} (u : P ⟶ Q) (d : Q ⟶ R) (g₁ : P ⟶ B₁) (k₁ : B₁ ⟶ R) (g₂ : P ⟶ B₂)
    (k₂ : B₂ ⟶ R) (ε : ℤˣ) (h : u ≫ d = g₁ ≫ k₁ + ε • (g₂ ≫ k₂)) :
    F.map u ≫ F.map d = F.map g₁ ≫ F.map k₁ + ε • (F.map g₂ ≫ F.map k₂) := by
  rw [← F.map_comp, h, F.map_add, F.map_units_smul, F.map_comp, F.map_comp]

/-- Congruence in the two first factors of a summandwise differential, over variables. -/
theorem CategoryTheory.add_units_smul_congr {C : Type*} [Category* C] [Preadditive C]
    {P B₁ B₂ T : C} (g₁ g₁' : P ⟶ B₁) (k₁ : B₁ ⟶ T) (g₂ g₂' : P ⟶ B₂) (k₂ : B₂ ⟶ T) (ε : ℤˣ)
    (h₁ : g₁ = g₁') (h₂ : g₂ = g₂') :
    g₁ ≫ k₁ + ε • (g₂ ≫ k₂) = g₁' ≫ k₁ + ε • (g₂' ≫ k₂) := by
  rw [h₁, h₂]

/-- **The commutation of a comparison with two summandwise differentials of the shape
`d₁ + ε d₂`**, over variables: if the comparison intertwines each leg, it intertwines the sum.
This is the algebra of the `comm` field below, isolated so that it runs on a goal in which no
object has a spelling. -/
theorem CategoryTheory.summand_comm {C : Type*} [Category* C] [Preadditive C]
    {P Q R S T U N₁ N₂ : C} (ιl : P ⟶ Q) (pm : Q ⟶ R) (d : R ⟶ T) (sd : Q ⟶ S) (p : S ⟶ T)
    (cmp : P ⟶ U) (u : U ⟶ R) (g₁ : U ⟶ N₁) (k₁ : N₁ ⟶ T) (g₂ : U ⟶ N₂) (k₂ : N₂ ⟶ T)
    (ε : ℤˣ) (s₁ s₂ : P ⟶ S)
    (hL : ιl ≫ pm = cmp ≫ u) (hsrc : ιl ≫ sd = s₁ + ε • s₂)
    (hu : u ≫ d = g₁ ≫ k₁ + ε • (g₂ ≫ k₂))
    (h₁ : s₁ ≫ p = cmp ≫ g₁ ≫ k₁) (h₂ : s₂ ≫ p = cmp ≫ g₂ ≫ k₂) :
    ιl ≫ pm ≫ d = ιl ≫ sd ≫ p := by
  rw [← Category.assoc, ← Category.assoc, hL, hsrc, Category.assoc, hu,
    Preadditive.comp_add, Linear.comp_units_smul, ← h₁, ← h₂, Preadditive.add_comp,
    Linear.units_smul_comp]

/-- **A bifunctor on a product category, read on a pair whose second leg is an identity**, over
variables: it is the first leg under the curried bifunctor, whiskered by the second object.
Isolated so that it runs on a goal in which no object has a spelling. -/
theorem CategoryTheory.uncurry_prod_map_id_right {A B C₁ C₂ D : Type*} [Category* A]
    [Category* B] [Category* C₁] [Category* C₂] [Category* D] (L : A ⥤ C₁) (R : B ⥤ C₂)
    (T : C₁ ⥤ C₂ ⥤ D) {P P' : A} (f : P ⟶ P') (Q : B) :
    (Functor.prod L R ⋙ Functor.uncurry.obj T).map (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q) =
      (T.map (L.map f)).app (R.obj Q) := by
  simp

/-- **A bifunctor on a product category, read on a pair whose first leg is an identity**, over
variables: it is the second leg under the curried bifunctor at the first object. Isolated so that
it runs on a goal in which no object has a spelling. -/
theorem CategoryTheory.uncurry_prod_map_id_left {A B C₁ C₂ D : Type*} [Category* A]
    [Category* B] [Category* C₁] [Category* C₂] [Category* D] (L : A ⥤ C₁) (R : B ⥤ C₂)
    (T : C₁ ⥤ C₂ ⥤ D) (P : A) {Q Q' : B} (g : Q ⟶ Q') :
    (Functor.prod L R ⋙ Functor.uncurry.obj T).map (X := (P, Q)) (Y := (P, Q')) (𝟙 P, g) =
      (T.obj (L.obj P)).map (R.map g) := by
  simp

/-! ### Naturality of the degreewise comparison in one operator at a time -/

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The degreewise comparison is natural in the first differential operator**, at the spelling
of the curried tensor bifunctor that the total complex of the source presents. -/
theorem relativeBoxComparison_naturality_fst
    {F F' : FiniteOrderDifferentialOperatorCategory a} (D : F ⟶ F')
    (G : FiniteOrderDifferentialOperatorCategory b) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
          ((leftRelativeInverseImage a b).map D)).app
        ((rightRelativeInverseImage a b).obj G) ≫ relativeBoxComparison a b F' G =
      relativeBoxComparison a b F G ≫
        (boxProductRelative a b).map (X := (F, G)) (Y := (F', G)) (D, 𝟙 G) :=
  Eq.trans
    (congrArg (fun m => m ≫ relativeBoxComparison a b F' G)
      (CategoryTheory.uncurry_prod_map_id_right (leftRelativeInverseImage a b)
          (rightRelativeInverseImage a b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))) D G).symm)
    (relativeBoxComparison_naturality a b D (𝟙 G))

/-- **The degreewise comparison is natural in the second differential operator**, at the
spelling of the curried tensor bifunctor. -/
theorem relativeBoxComparison_naturality_snd
    (F : FiniteOrderDifferentialOperatorCategory a)
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((leftRelativeInverseImage a b).obj F)).map
        ((rightRelativeInverseImage a b).map E) ≫ relativeBoxComparison a b F G' =
      relativeBoxComparison a b F G ≫
        (boxProductRelative a b).map (X := (F, G)) (Y := (F, G')) (𝟙 F, E) :=
  Eq.trans
    (congrArg (fun m => m ≫ relativeBoxComparison a b F G')
      (CategoryTheory.uncurry_prod_map_id_left (leftRelativeInverseImage a b)
          (rightRelativeInverseImage a b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))) F E).symm)
    (relativeBoxComparison_naturality a b (𝟙 F) E)

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

namespace Stacks.Cohomology.BoxKunneth

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- The tensor bifunctor the source total complex is formed with. -/
abbrev inverseImageSheafTensor :
    Modules (inverseImageBase (pullback.fst a b ≫ a)) ⥤
      Modules (inverseImageBase (pullback.fst a b ≫ a)) ⥤
        Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))

/-! ### The differential of the target on the image of a summand -/

/-- The differential of `Tot(𝓕^• ⊠ 𝓖^•)` read over `f^{-1}𝒪_S`, on the image of the summand of
degree `(i, j)`, with the two legs in the restriction-of-scalars spelling. -/
theorem boxTotalι_comp_d_map (i j n : ℤ) (h : i + j = n) :
    boxTotalι a b K L n₁ n₂ i j n h ≫ (boxTotalModules a b K L n₁ n₂).d n (n + 1) =
      (toInverseImageModules (pullback.fst a b ≫ a)).map
            (boxHom (K.d i (i + 1)) (𝟙 (L.X j))) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) (by lia) +
        i.negOnePow •
          ((toInverseImageModules (pullback.fst a b ≫ a)).map
              (boxHom (𝟙 (K.X i)) (L.d j (j + 1))) ≫
            boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) (by lia)) := by
  have := hasMapBifunctor_up_ℤ K L n₁ n₂
  exact Functor.map_comp_eq_add_units_smul (toInverseImageModules (pullback.fst a b ≫ a))
    (HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) i j n h)
    ((boxTotal a b K L n₁ n₂).d n (n + 1)) _ _ _ _ i.negOnePow
    (boxTotal_d a b K L n₁ n₂ i j n h)

/-- **The differential of `Tot(𝓕^• ⊠ 𝓖^•)` read over `f^{-1}𝒪_S`, on the image of a summand**:
`(d_𝓕 ⊠ 1) + (-1)^i (1 ⊠ d_𝓖)`, with both legs read through the box bifunctor over
`f^{-1}𝒪_S`. -/
theorem boxTotalι_comp_d (i j n : ℤ) (h : i + j = n) :
    boxTotalι a b K L n₁ n₂ i j n h ≫ (boxTotalModules a b K L n₁ n₂).d n (n + 1) =
      (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j))
            (K.d i (i + 1), 𝟙 (L.X j)) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) (by lia) +
        i.negOnePow •
          ((boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1)))
              (𝟙 (K.X i), L.d j (j + 1)) ≫
            boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) (by lia)) :=
  Eq.trans (boxTotalι_comp_d_map a b K L n₁ n₂ i j n h)
    (CategoryTheory.add_units_smul_congr _ _ _ _ _ _ i.negOnePow
      (boxProductRelative_map a b (K.d i (i + 1)) (𝟙 (L.X j))).symm
      (boxProductRelative_map a b (𝟙 (K.X i)) (L.d j (j + 1))).symm)

/-! ### The degreewise comparison -/

/-- **The degreewise step-(5) comparison**: on the summand of degree `(i, j)` of
`Tot(p^{-1}𝓕^• ⊗ q^{-1}𝓖^•)^n` it is `relativeBoxComparison` followed by the inclusion of the
summand of `Tot(𝓕^• ⊠ 𝓖^•)^n`. -/
def boxTotalComparisonMap (n : ℤ) :
    (inverseImageTensorTotal a b K L).X n ⟶ (boxTotalModules a b K L n₁ n₂).X n :=
  @HomologicalComplex.mapBifunctorDesc _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
    (inverseImageSheafTensor a b)
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _ _ _ _ _
    (fun i j h => relativeBoxComparison a b (K.X i) (L.X j) ≫
      boxTotalι a b K L n₁ n₂ i j n h)

/-- **The component of the degreewise comparison on a summand is the degreewise comparison**,
which is what the field `BoxTotalComparison.ι_hom` prescribes. -/
theorem ι_boxTotalComparisonMap (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
        (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
        (ComplexShape.up ℤ) i j n h ≫ boxTotalComparisonMap a b K L n₁ n₂ n =
      relativeBoxComparison a b (K.X i) (L.X j) ≫ boxTotalι a b K L n₁ n₂ i j n h :=
  @HomologicalComplex.ι_mapBifunctorDesc _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
    (inverseImageSheafTensor a b)
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _ _ _ _ _ _ i j h

/-! ### The two legs of the commutation -/

/-- Moving a square across a composite: if `a ≫ b = c ≫ d` then `a ≫ (b ≫ e) = c ≫ (d ≫ e)`. -/
private theorem comp_assoc_congr {C : Type*} [Category* C] {P Q R S T : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : P ⟶ S) (d : S ⟶ R) (e : R ⟶ T) (h : a ≫ b = c ≫ d) :
    a ≫ (b ≫ e) = c ≫ (d ≫ e) := by
  rw [← Category.assoc, h, Category.assoc]

/-- The first half-naturality at the complex spelling. -/
theorem relativeBoxComparison_naturality_d_fst (i j : ℤ) :
    ((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
        relativeBoxComparison a b (K.X (i + 1)) (L.X j) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j))
          (K.d i (i + 1), 𝟙 (L.X j)) :=
  relativeBoxComparison_naturality_fst a b (K.d i (i + 1)) (L.X j)

/-- The second half-naturality at the complex spelling. -/
theorem relativeBoxComparison_naturality_d_snd (i j : ℤ) :
    ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
        relativeBoxComparison a b (K.X i) (L.X (j + 1)) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1)))
          (𝟙 (K.X i), L.d j (j + 1)) :=
  relativeBoxComparison_naturality_snd a b (K.X i) (L.d j (j + 1))

/-- The first leg, with the inclusion of the summand of degree `(i+1, j)` evaluated. -/
theorem boxTotalLeg₁_comp_ι (i j n : ℤ) (h' : i + 1 + j = n + 1) :
    ((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
        (HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
            (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
            (ComplexShape.up ℤ) (i + 1) j (n + 1) h' ≫
          boxTotalComparisonMap a b K L n₁ n₂ (n + 1)) =
      ((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
        (relativeBoxComparison a b (K.X (i + 1)) (L.X j) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h') :=
  CategoryTheory.whisker_eq _ (ι_boxTotalComparisonMap a b K L n₁ n₂ (i + 1) j (n + 1) h')

/-- The source of the first leg, left-associated. One `Category.assoc` and nothing else: the
reassociation is affordable only where both bracketings are written out in the statement, so that
the unifier reads the splitting off the goal instead of searching for it across the seam between
the curried tensor bifunctor and the box product. -/
theorem boxTotalLeg₁_assoc₁ (i j n : ℤ) (h' : i + 1 + j = n + 1) :
    ((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
        (relativeBoxComparison a b (K.X (i + 1)) (L.X j) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h') =
      (((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
          relativeBoxComparison a b (K.X (i + 1)) (L.X j)) ≫
        boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h' :=
  (Category.assoc _ _ _).symm

/-- The first leg's naturality square, whiskered on the right by the inclusion of the summand.
Its own declaration: `CategoryTheory.eq_whisker` applied inside a larger term has to solve its
codomain metavariable across that seam and exhausts the heartbeat limit at `whnf`, while with the
whiskered equation written out as the expected type it is read off the goal. -/
theorem boxTotalLeg₁_whisk (i j n : ℤ) (h' : i + 1 + j = n + 1) :
    (((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
          relativeBoxComparison a b (K.X (i + 1)) (L.X j)) ≫
        boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h' =
      (relativeBoxComparison a b (K.X i) (L.X j) ≫
          (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j))
            (K.d i (i + 1), 𝟙 (L.X j))) ≫
        boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h' :=
  by rw [relativeBoxComparison_naturality_d_fst a b K L i j]; rfl

/-- The first leg, with the comparison moved across the differential. -/
theorem boxTotalLeg₁_cross (i j n : ℤ) (h' : i + 1 + j = n + 1) :
    ((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
          ((rightInverseImageComplex a b L).X j) ≫
        (relativeBoxComparison a b (K.X (i + 1)) (L.X j) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h') =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        ((boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j))
            (K.d i (i + 1), 𝟙 (L.X j)) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h') :=
  comp_assoc_congr _ _ _ _ _ (relativeBoxComparison_naturality_d_fst a b K L i j)

/-- **The first leg of the commutation**: `d_𝓕 ⊗ 1` followed by the degreewise comparison is the
degreewise comparison followed by `d_𝓕 ⊠ 1`. -/
theorem boxTotalLeg₁ (i j n : ℤ) (h' : i + 1 + j = n + 1) :
    (((inverseImageSheafTensor a b).map ((leftInverseImageComplex a b K).d i (i + 1))).app
            ((rightInverseImageComplex a b L).X j) ≫
          HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
            (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
            (ComplexShape.up ℤ) (i + 1) j (n + 1) h') ≫
        boxTotalComparisonMap a b K L n₁ n₂ (n + 1) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        ((boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j))
            (K.d i (i + 1), 𝟙 (L.X j)) ≫
          boxTotalι a b K L n₁ n₂ (i + 1) j (n + 1) h') :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (boxTotalLeg₁_comp_ι a b K L n₁ n₂ i j n h')
      (boxTotalLeg₁_cross a b K L n₁ n₂ i j n h'))

/-- The second leg, with the inclusion of the summand of degree `(i, j+1)` evaluated. -/
theorem boxTotalLeg₂_comp_ι (i j n : ℤ) (h' : i + (j + 1) = n + 1) :
    ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
        (HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
            (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
            (ComplexShape.up ℤ) i (j + 1) (n + 1) h' ≫
          boxTotalComparisonMap a b K L n₁ n₂ (n + 1)) =
      ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
        (relativeBoxComparison a b (K.X i) (L.X (j + 1)) ≫
          boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h') :=
  CategoryTheory.whisker_eq _ (ι_boxTotalComparisonMap a b K L n₁ n₂ i (j + 1) (n + 1) h')

/-- The source of the second leg, left-associated. The companion of `boxTotalLeg₁_assoc₁`. -/
theorem boxTotalLeg₂_assoc₁ (i j n : ℤ) (h' : i + (j + 1) = n + 1) :
    ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
        (relativeBoxComparison a b (K.X i) (L.X (j + 1)) ≫
          boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h') =
      (((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
          relativeBoxComparison a b (K.X i) (L.X (j + 1))) ≫
        boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h' :=
  (Category.assoc _ _ _).symm

/-- The second leg's naturality square, whiskered on the right by the inclusion of the summand.
The companion of `boxTotalLeg₁_whisk`. -/
theorem boxTotalLeg₂_whisk (i j n : ℤ) (h' : i + (j + 1) = n + 1) :
    (((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
          relativeBoxComparison a b (K.X i) (L.X (j + 1))) ≫
        boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h' =
      (relativeBoxComparison a b (K.X i) (L.X j) ≫
          (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1)))
            (𝟙 (K.X i), L.d j (j + 1))) ≫
        boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h' :=
  by rw [relativeBoxComparison_naturality_d_snd a b K L i j]; rfl

/-- The second leg, with the comparison moved across the differential. -/
theorem boxTotalLeg₂_cross (i j n : ℤ) (h' : i + (j + 1) = n + 1) :
    ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
          ((rightInverseImageComplex a b L).d j (j + 1)) ≫
        (relativeBoxComparison a b (K.X i) (L.X (j + 1)) ≫
          boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h') =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        ((boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1)))
            (𝟙 (K.X i), L.d j (j + 1)) ≫
          boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h') :=
  comp_assoc_congr _ _ _ _ _ (relativeBoxComparison_naturality_d_snd a b K L i j)

/-- **The second leg of the commutation**: `1 ⊗ d_𝓖` followed by the degreewise comparison is
the degreewise comparison followed by `1 ⊠ d_𝓖`. -/
theorem boxTotalLeg₂ (i j n : ℤ) (h' : i + (j + 1) = n + 1) :
    (((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
            ((rightInverseImageComplex a b L).d j (j + 1)) ≫
          HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
            (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
            (ComplexShape.up ℤ) i (j + 1) (n + 1) h') ≫
        boxTotalComparisonMap a b K L n₁ n₂ (n + 1) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        ((boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1)))
            (𝟙 (K.X i), L.d j (j + 1)) ≫
          boxTotalι a b K L n₁ n₂ i (j + 1) (n + 1) h') :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (boxTotalLeg₂_comp_ι a b K L n₁ n₂ i j n h')
      (boxTotalLeg₂_cross a b K L n₁ n₂ i j n h'))

/-! ### Step (5) -/

/-- **The degreewise comparison commutes with the two differentials.** On the summand of degree
`(i, j)` the differential of the source is `d_𝓕 ⊗ 1 + (-1)^i (1 ⊗ d_𝓖)` and that of the target is
`d_𝓕 ⊠ 1 + (-1)^i (1 ⊠ d_𝓖)`, and the comparison intertwines each leg: that is the naturality of
`relativeBoxComparison` in the two differential operators. -/
theorem boxTotalComparisonMap_comm (n : ℤ) :
    boxTotalComparisonMap a b K L n₁ n₂ n ≫ (boxTotalModules a b K L n₁ n₂).d n (n + 1) =
      (inverseImageTensorTotal a b K L).d n (n + 1) ≫
        boxTotalComparisonMap a b K L n₁ n₂ (n + 1) := by
  refine @HomologicalComplex.mapBifunctor.hom_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
    (inverseImageSheafTensor a b)
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _ _ _ _ _ _ _ (fun i j hij => ?_)
  have h : i + j = n := hij
  exact CategoryTheory.summand_comm _ _ _ _ _ (relativeBoxComparison a b (K.X i) (L.X j))
    (boxTotalι a b K L n₁ n₂ i j n h) _ _ _ _ i.negOnePow _ _
    (ι_boxTotalComparisonMap a b K L n₁ n₂ i j n h)
    (@HomologicalComplex.ιMapBifunctor_d_up_ℤ _ _ _ _ _ _ _ _ _
      (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
      (inverseImageSheafTensor a b)
      (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
      (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
      _ i j n h)
    (boxTotalι_comp_d a b K L n₁ n₂ i j n h)
    (boxTotalLeg₁ a b K L n₁ n₂ i j n (by lia))
    (boxTotalLeg₂ a b K L n₁ n₂ i j n (by lia))

/-- **Step (5) of the construction of [Stacks, Tag 0G4A]**, the morphism of complexes
`Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)` whose component on the summand of
degree `(i, j)` is the degreewise comparison followed by the inclusion of the summand. -/
def boxTotalComparisonHom :
    inverseImageTensorTotal a b K L ⟶ boxTotalModules a b K L n₁ n₂ where
  f n := boxTotalComparisonMap a b K L n₁ n₂ n
  comm' n n' hnn' := by
    obtain rfl : n + 1 = n' := hnn'
    exact boxTotalComparisonMap_comm a b K L n₁ n₂ n

/-- **The step-(5) datum of [Stacks, Tag 0G4A]**: the morphism of complexes
together with the prescription of all of its summandwise components. It is unique by
`BoxTotalComparison.hom_unique`, so every map built from it is canonical. -/
def boxTotalComparison : BoxTotalComparison a b K L n₁ n₂ where
  hom := boxTotalComparisonHom a b K L n₁ n₂
  ι_hom i j n h := ι_boxTotalComparisonMap a b K L n₁ n₂ i j n h

/-- The type of step-(5) data is inhabited by `boxTotalComparison`. -/
instance : Inhabited (BoxTotalComparison a b K L n₁ n₂) :=
  ⟨boxTotalComparison a b K L n₁ n₂⟩

/-- Any step-(5) datum is the one constructed here. -/
theorem eq_boxTotalComparison (c : BoxTotalComparison a b K L n₁ n₂) :
    c = boxTotalComparison a b K L n₁ n₂ :=
  Subsingleton.elim _ _

end Stacks.Cohomology.BoxKunneth

end
