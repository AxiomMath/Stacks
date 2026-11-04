module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre product of three models as a model for the first corner of a cartesian square

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes quasi-separated and of finite type over `S`. Given a good
diagram for `X⁴` over a stage `S_i`, with model `W⁴`, and models `W²` and `W³` for `X²` and `X³`
over the same stage together with morphisms `W² ⟶ W⁴` and `W³ ⟶ W⁴` compatible with `b` and `a`,
the fibre product `W² ×_{W⁴} W³` is a model for `X¹`: it is of finite type over `S_i` and the
induced morphism `X¹ ⟶ S ×_{S_i} (W² ×_{W⁴} W³)` is a closed immersion. This is the choice of
model the Stacks proof of 0CNW makes for the first corner.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ModelOver`: a good diagram for
  `X ⟶ S` whose stage is that of a given good diagram `G` for `Y ⟶ S` and whose model maps to
  the model of `G`, compatibly with a morphism `X ⟶ Y`.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.fibreProductModel`: the good diagram
  for `X¹` with model `W² ×_{W⁴} W³`.

## Main results

* `CategoryTheory.Limits.isPullback_fibreProduct_baseChange`: base change commutes with the
  fibre product, in the form needed here — `T ×_{S₀} (V² ×_{V⁴} V³)` is the fibre product of
  `T ×_{S₀} V²` and `T ×_{S₀} V³` over `T ×_{S₀} V⁴`.
* `AlgebraicGeometry.isClosedImmersion_fibreProduct_baseChange`: the fibre product of three
  closed immersions is a closed immersion into the fibre product of the three ambients, no
  separatedness being needed because the closed immersion of the fourth corner is a
  monomorphism.

## Route

The two general facts are proved first and in a general category where possible. That base
change commutes with the fibre product is four applications of
`CategoryTheory.IsPullback.of_right` and `CategoryTheory.IsPullback.paste_horiz`: the square
`P³ ⟶ P⁴`, `P³ ⟶ V³` is cartesian because pasting it with the defining square of `P⁴` gives the
defining square of `P³`, and similarly for `P²` and for `R ⟶ P³`, `R ⟶ W`; pasting the last with
the defining square of `W` and cancelling the square for `P²` gives the claim.

For the closed immersion: the square `X¹ ⟶ X²`, `X¹ ⟶ X³` over `X⁴` stays cartesian after
composing its two lower edges with the closed immersion `X⁴ ⟶ P⁴`, because that morphism is a
monomorphism, so `X¹` is the fibre product of `X²` and `X³` over `P⁴`; the comparison to the
fibre product of `P²` and `P³` over `P⁴` is then a closed immersion by
`CategoryTheory.MorphismProperty.pullbackMap`, closed immersions being stable under base change
and composition.

The model `W² ×_{W⁴} W³` is of finite type over `S_i` because the projection to `W²` is the base
change of `W³ ⟶ W⁴`, which is locally of finite type by Stacks 01T8 and quasi-compact because
`W³` is Noetherian, being of finite type over the Noetherian `S_i`.

## Universe situation

The index type is at a universe independent of the universe of the schemes and carries no
smallness hypothesis: nothing here is a limit argument, only the commuting square of the good
diagram and fibre products of schemes.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNP](https://stacks.math.columbia.edu/tag/0CNP)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW), whose proof chooses
  this model for the first corner
* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)

## Not done here

Nothing here carries a tag. The two conclusions of Stacks 0CNW — that the comparison
`X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is eventually a closed immersion, and eventually an isomorphism when
`a` and `b` are flat and of finite presentation — are not proved. What is proved is that the
model the source chooses for the first corner exists, which is the first step of its proof. Two
further steps are missing: the morphisms of image systems attached to this choice, and the
transport of a property of a *square* of systems from this choice of model to an arbitrary one,
which is the content of Stacks 0CNS that
`AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'` and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison'` do not
cover.

Also note that the morphisms `W² ⟶ W⁴` and `W³ ⟶ W⁴` are data here: good diagrams chosen
independently for the three corners live over three different stages and admit no morphism
between their models. That data is not an extra *hypothesis*, though. A morphism of the image
systems of two independently chosen good diagrams produces it at every stage of a common tail,
by `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver` of
`StacksFrontier/AlgebraicGeometry/LimitMorphismAt/StageModelOver.lean`, which is how
`StacksFrontier/AlgebraicGeometry/LimitMorphismAt/FibreProductComparison.lean` states Stacks 0CNW
for four independent choices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Limits

/-- A cartesian square stays cartesian after composing both of its lower edges with a
monomorphism. -/
theorem isPullback_comp_right_mono {C : Type*} [Category C] {P X Y Z Z' : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (m : Z ⟶ Z') [Mono m] : IsPullback fst snd (f ≫ m) (g ≫ m) := by
  have ht : IsPullback g (𝟙 Y) m (g ≫ m) :=
    IsPullback.of_vert_isIso_mono ⟨(Category.id_comp _).symm⟩
  simpa using h.paste_vert ht

/-- **Base change commutes with the fibre product.** If `P²`, `P³`, `P⁴` and `R` are the base
changes along `T ⟶ S₀` of `V²`, `V³`, `V⁴` and of a fibre product `W = V² ×_{V⁴} V³`, then `R` is
the fibre product of `P²` and `P³` over `P⁴`. -/
theorem isPullback_fibreProduct_baseChange {C : Type*} [Category C]
    {T S₀ V₂ V₃ V₄ W P₂ P₃ P₄ R : C}
    {t : T ⟶ S₀} {m₁ : W ⟶ S₀} {m₂ : V₂ ⟶ S₀} {m₃ : V₃ ⟶ S₀} {m₄ : V₄ ⟶ S₀}
    {v₂ : V₂ ⟶ V₄} {v₃ : V₃ ⟶ V₄} {w₂ : W ⟶ V₂} {w₃ : W ⟶ V₃}
    {p₂ : P₂ ⟶ T} {q₂ : P₂ ⟶ V₂} {p₃ : P₃ ⟶ T} {q₃ : P₃ ⟶ V₃}
    {p₄ : P₄ ⟶ T} {q₄ : P₄ ⟶ V₄} {pR : R ⟶ T} {qR : R ⟶ W}
    {β : P₂ ⟶ P₄} {α : P₃ ⟶ P₄} {r₂ : R ⟶ P₂} {r₃ : R ⟶ P₃}
    (hP₂ : IsPullback p₂ q₂ t m₂) (hP₃ : IsPullback p₃ q₃ t m₃)
    (hP₄ : IsPullback p₄ q₄ t m₄) (hR : IsPullback pR qR t m₁)
    (hW : IsPullback w₂ w₃ v₂ v₃)
    (hm₂ : v₂ ≫ m₄ = m₂) (hm₃ : v₃ ≫ m₄ = m₃) (hm₁ : w₃ ≫ m₃ = m₁)
    (hβp : β ≫ p₄ = p₂) (hβq : β ≫ q₄ = q₂ ≫ v₂)
    (hαp : α ≫ p₄ = p₃) (hαq : α ≫ q₄ = q₃ ≫ v₃)
    (hr₂p : r₂ ≫ p₂ = pR) (hr₂q : r₂ ≫ q₂ = qR ≫ w₂)
    (hr₃p : r₃ ≫ p₃ = pR) (hr₃q : r₃ ≫ q₃ = qR ≫ w₃) :
    IsPullback r₂ r₃ β α := by
  have hβ : IsPullback β q₂ q₄ v₂ :=
    IsPullback.of_right (by rw [hβp, hm₂]; exact hP₂) hβq hP₄
  have hα : IsPullback α q₃ q₄ v₃ :=
    IsPullback.of_right (by rw [hαp, hm₃]; exact hP₃) hαq hP₄
  have hRW : IsPullback r₃ qR q₃ w₃ :=
    IsPullback.of_right (by rw [hr₃p, hm₁]; exact hR) hr₃q hP₃
  have houter : IsPullback (r₂ ≫ q₂) r₃ v₂ (α ≫ q₄) := by
    rw [hr₂q, hαq]
    exact hRW.flip.paste_horiz hW
  have hcomm : r₂ ≫ β = r₃ ≫ α := by
    refine hP₄.hom_ext ?_ ?_
    · rw [Category.assoc, hβp, hr₂p, Category.assoc, hαp, hr₃p]
    · simp only [Category.assoc, hβq, hαq]
      rw [← Category.assoc, hr₂q, ← Category.assoc, hr₃q]
      simp only [Category.assoc, hW.w]
  exact IsPullback.of_right houter hcomm hβ.flip

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **The fibre product of three closed immersions.** Given a cartesian square of schemes with
morphisms `b : Y² ⟶ Y⁴` and `a : Y³ ⟶ Y⁴`, closed immersions of the three corners into schemes
`P²`, `P³`, `P⁴` compatible with morphisms `P² ⟶ P⁴ ⟵ P³`, and a fibre product `R` of `P²` and
`P³` over `P⁴`, the induced morphism from the first corner to `R` is a closed immersion. -/
@[ega "I 4.3.1" "more general"]
theorem isClosedImmersion_fibreProduct_baseChange
    {Y₁ Y₂ Y₃ Y₄ P₂ P₃ P₄ R : Scheme.{u}}
    {y₂ : Y₁ ⟶ Y₂} {y₃ : Y₁ ⟶ Y₃} {β : Y₂ ⟶ Y₄} {α : Y₃ ⟶ Y₄}
    {c₂ : Y₂ ⟶ P₂} {c₃ : Y₃ ⟶ P₃} {c₄ : Y₄ ⟶ P₄}
    {β' : P₂ ⟶ P₄} {α' : P₃ ⟶ P₄} {r₂ : R ⟶ P₂} {r₃ : R ⟶ P₃} {u : Y₁ ⟶ R}
    [IsClosedImmersion c₂] [IsClosedImmersion c₃] [IsClosedImmersion c₄]
    (hY : IsPullback y₂ y₃ β α) (hR : IsPullback r₂ r₃ β' α')
    (hb : β ≫ c₄ = c₂ ≫ β') (ha : α ≫ c₄ = c₃ ≫ α')
    (hu₂ : u ≫ r₂ = y₂ ≫ c₂) (hu₃ : u ≫ r₃ = y₃ ≫ c₃) :
    IsClosedImmersion u := by
  have hY' : IsPullback y₂ y₃ (c₂ ≫ β') (c₃ ≫ α') := by
    rw [← hb, ← ha]
    exact isPullback_comp_right_mono hY c₄
  have hcond : (pullback.fst (c₂ ≫ β') (c₃ ≫ α') ≫ c₂) ≫ β' =
      (pullback.snd (c₂ ≫ β') (c₃ ≫ α') ≫ c₃) ≫ α' := by
    rw [Category.assoc, Category.assoc]
    exact pullback.condition
  have : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative @IsClosedImmersion).toIsStableUnderComposition
  have hm : IsClosedImmersion (pullback.lift
      (pullback.fst (c₂ ≫ β') (c₃ ≫ α') ≫ c₂)
      (pullback.snd (c₂ ≫ β') (c₃ ≫ α') ≫ c₃) hcond) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl rfl
  have key : u ≫ hR.isoPullback.hom =
      hY'.isoPullback.hom ≫ pullback.lift
        (pullback.fst (c₂ ≫ β') (c₃ ≫ α') ≫ c₂)
        (pullback.snd (c₂ ≫ β') (c₃ ≫ α') ≫ c₃) hcond := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, hu₂, Category.assoc,
        pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, hu₃, Category.assoc,
        pullback.lift_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]
  have hue : u = hY'.isoPullback.hom ≫ (pullback.lift
      (pullback.fst (c₂ ≫ β') (c₃ ≫ α') ≫ c₂)
      (pullback.snd (c₂ ≫ β') (c₃ ≫ α') ≫ c₃) hcond) ≫ hR.isoPullback.inv := by
    rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hue]
  infer_instance

namespace LimitNoetherianSituation

namespace GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

/-- A good diagram for `f : X ⟶ S` over the stage of a given good diagram `G` for
`g : Y ⟶ S`, whose model maps to the model of `G` compatibly with a morphism `u : X ⟶ Y`. This
is the shape the Stacks proof of 0CNW needs the three models of a cartesian square to have
before their fibre product can be formed. -/
structure ModelOver {X Y : Scheme.{u}} {g : Y ⟶ D.limitScheme} (G : GoodDiagram D g)
    (u : X ⟶ Y) (f : X ⟶ D.limitScheme) where
  /-- The model, over the stage of `G`. -/
  W : Scheme.{u}
  /-- The morphism to the model of `G`. -/
  toBase : W ⟶ G.W
  /-- The structure morphism of the model over the stage of `G`. It is recorded separately from
  `toBase ≫ G.modelMap`, to which it is equal, so that one scheme carrying two morphisms to two
  models of the same stage presents the *same* good diagram both ways. -/
  modelMap : W ⟶ D.system.obj (op G.index)
  /-- The structure morphism factors through the model of `G`. -/
  modelMap_eq : toBase ≫ G.modelMap = modelMap
  /-- The horizontal morphism `X ⟶ W`. -/
  toModel : X ⟶ W
  /-- The square with vertical maps `f` and `modelMap` commutes. -/
  commutes : f ≫ D.limitCone.π.app (op G.index) = toModel ≫ modelMap
  /-- The morphism to the model of `G` is compatible with `u`. -/
  compat : toModel ≫ toBase = u ≫ G.toModel
  /-- The model is locally of finite type over the stage. -/
  locallyOfFiniteType : LocallyOfFiniteType modelMap
  /-- The model morphism is quasi-compact, so it is of finite type. -/
  quasiCompact : QuasiCompact modelMap
  /-- The induced morphism from `X` to the base change of the model is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion (pullback.lift f toModel commutes)

namespace ModelOver

variable {X Y : Scheme.{u}} {g : Y ⟶ D.limitScheme} {G : GoodDiagram D g} {u : X ⟶ Y}
  {f : X ⟶ D.limitScheme}

/-- A model over the model of a good diagram is a good diagram.

This is `@[reducible]` for the reason
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem` is: the base changes of its
model are what the statements about its image system mention, and without it the module system
hides the identification of its model morphism with `modelMap` at `instances` transparency, so
no simp lemma about those base changes fires. -/
@[reducible] noncomputable def toGoodDiagram (M : ModelOver G u f) : GoodDiagram D f where
  index := G.index
  W := M.W
  modelMap := M.modelMap
  toModel := M.toModel
  commutes := M.commutes
  locallyOfFiniteType := M.locallyOfFiniteType
  quasiCompact := M.quasiCompact
  isClosedImmersion := M.isClosedImmersion

/-- The stage of the good diagram of a model `M` over `G` is the stage of `G`. -/
@[simp]
lemma toGoodDiagram_index (M : ModelOver G u f) : M.toGoodDiagram.index = G.index := rfl

/-- The model of the good diagram of `M` is the model `M.W`. -/
@[simp]
lemma toGoodDiagram_W (M : ModelOver G u f) : M.toGoodDiagram.W = M.W := rfl

/-- The structure morphism of the good diagram of `M` is `M.modelMap`. -/
@[simp]
lemma toGoodDiagram_modelMap (M : ModelOver G u f) :
    M.toGoodDiagram.modelMap = M.modelMap := rfl

/-- The morphism to the model of the good diagram of `M` is `M.toModel`. -/
@[simp]
lemma toGoodDiagram_toModel (M : ModelOver G u f) : M.toGoodDiagram.toModel = M.toModel := rfl

/-- The model of a model over a good diagram is Noetherian, being of finite type over the
Noetherian stage scheme. -/
instance isNoetherian (M : ModelOver G u f) : IsNoetherian M.W :=
  have := M.locallyOfFiniteType
  have := M.quasiCompact
  have : IsNoetherian (D.system.obj (op G.index)) := D.noetherian G.index
  isNoetherian_of_locallyOfFiniteType M.modelMap

/-- The morphism from the model to the model of the given good diagram is locally of finite
type, since its composite with the structure morphism of that model is (Stacks 01T8). -/
instance locallyOfFiniteType_toBase (M : ModelOver G u f) : LocallyOfFiniteType M.toBase :=
  have : LocallyOfFiniteType (M.toBase ≫ G.modelMap) := M.modelMap_eq ▸ M.locallyOfFiniteType
  locallyOfFiniteType_of_comp M.toBase G.modelMap

end ModelOver

section FibreProduct

variable {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
  {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
  {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
  (G₄ : GoodDiagram D s₄) (M₂ : G₄.ModelOver b s₂) (M₃ : G₄.ModelOver a s₃)

/-- The third corner of a cartesian square over `S` lies over `S`. -/
theorem comp_eq_of_isPullback (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) : p ≫ s₃ = s₁ := by
  rw [← ha, ← Category.assoc, ← hsq.w, Category.assoc, hb, hq]

/-- The two projections of the fibre product of the models induce the same structure morphism
over the stage. -/
theorem fibreProductModelMap_eq :
    pullback.snd M₂.toBase M₃.toBase ≫ M₃.modelMap =
      pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap := by
  rw [← M₂.modelMap_eq, ← M₃.modelMap_eq, ← Category.assoc, ← Category.assoc,
    ← pullback.condition]

/-- The two components of the horizontal morphism `X¹ ⟶ W² ×_{W⁴} W³` agree over `W⁴`. -/
theorem fibreProductToModel_cond (hsq : IsPullback q p b a) :
    (q ≫ M₂.toModel) ≫ M₂.toBase = (p ≫ M₃.toModel) ≫ M₃.toBase := by
  rw [Category.assoc, M₂.compat, Category.assoc, M₃.compat, ← Category.assoc,
    ← Category.assoc, hsq.w]

/-- The square of the fibre-product model commutes. -/
theorem fibreProductModel_commutes (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) :
    s₁ ≫ D.limitCone.π.app (op G₄.index) =
      pullback.lift (q ≫ M₂.toModel) (p ≫ M₃.toModel)
          (fibreProductToModel_cond G₄ M₂ M₃ hsq) ≫
        pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap := by
  rw [← Category.assoc, pullback.lift_fst, ← hq, Category.assoc, M₂.commutes, Category.assoc]

/-- The fibre product of the two models is locally of finite type over the stage: the projection
to `W²` is the base change of `W³ ⟶ W⁴`. -/
instance locallyOfFiniteType_fibreProductModelMap :
    LocallyOfFiniteType (pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap) :=
  have := M₂.locallyOfFiniteType
  inferInstance

/-- The fibre product of the two models is quasi-compact over the stage. -/
instance quasiCompact_fibreProductModelMap :
    QuasiCompact (pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap) :=
  have := M₂.quasiCompact
  inferInstance

/-- **The closed immersion `X¹ ⟶ S ×_{S_i} (W² ×_{W⁴} W³)`.** The first corner of a cartesian
square embeds as a closed subscheme of the base change of the fibre product of the models of the
other three corners. -/
theorem isClosedImmersion_fibreProductInduced (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    IsClosedImmersion (pullback.lift _ _ (fibreProductModel_commutes G₄ M₂ M₃ hsq hq)) := by
  have hW₂ := fibreProductModelMap_eq G₄ M₂ M₃
  have hcond : ∀ {A B : Scheme.{u}} (t : A ⟶ B) (n : B ⟶ D.system.obj (op G₄.index))
      (m : A ⟶ D.system.obj (op G₄.index)), t ≫ n = m →
      pullback.fst (D.limitCone.π.app (op G₄.index)) m ≫ D.limitCone.π.app (op G₄.index) =
        (pullback.snd (D.limitCone.π.app (op G₄.index)) m ≫ t) ≫ n := by
    intro A B t n m h
    rw [Category.assoc, h]
    exact pullback.condition
  have hbcond := hcond _ G₄.modelMap _ M₂.modelMap_eq
  have hacond := hcond _ G₄.modelMap _ M₃.modelMap_eq
  have hrcond₂ := hcond (pullback.fst M₂.toBase M₃.toBase) M₂.modelMap _ rfl
  have hrcond₃ := hcond (pullback.snd M₂.toBase M₃.toBase) M₃.modelMap _ hW₂
  have hRpb : IsPullback (pullback.lift _ _ hrcond₂) (pullback.lift _ _ hrcond₃)
      (pullback.lift _ _ hbcond) (pullback.lift _ _ hacond) :=
    isPullback_fibreProduct_baseChange (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      M₂.modelMap_eq M₃.modelMap_eq hW₂
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hc₂ : IsClosedImmersion (pullback.lift _ _ M₂.commutes) := M₂.isClosedImmersion
  have hc₃ : IsClosedImmersion (pullback.lift _ _ M₃.commutes) := M₃.isClosedImmersion
  have hc₄ : IsClosedImmersion (pullback.lift _ _ G₄.commutes) := G₄.isClosedImmersion
  refine isClosedImmersion_fibreProduct_baseChange (c₂ := pullback.lift _ _ M₂.commutes)
    (c₃ := pullback.lift _ _ M₃.commutes) (c₄ := pullback.lift _ _ G₄.commutes)
    hsq hRpb ?_ ?_ ?_ ?_
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hb, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
        ← Category.assoc, pullback.lift_snd, M₂.compat]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ha, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
        ← Category.assoc, pullback.lift_snd, M₃.compat]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc,
        pullback.lift_fst, hq]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        pullback.lift_fst, Category.assoc, pullback.lift_snd]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc,
        pullback.lift_fst, comp_eq_of_isPullback hsq hq hb ha]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        pullback.lift_snd, Category.assoc, pullback.lift_snd]

/-- **The model `W² ×_{W⁴} W³` for the first corner, read over the model of the second corner.**
This is the choice of model the Stacks proof of 0CNW makes for the first corner. -/
@[reducible] noncomputable def fibreProductModelSnd (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) : (M₂.toGoodDiagram).ModelOver q s₁ where
  W := pullback M₂.toBase M₃.toBase
  toBase := pullback.fst M₂.toBase M₃.toBase
  modelMap := pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap
  modelMap_eq := rfl
  toModel := pullback.lift (q ≫ M₂.toModel) (p ≫ M₃.toModel)
    (fibreProductToModel_cond G₄ M₂ M₃ hsq)
  commutes := fibreProductModel_commutes G₄ M₂ M₃ hsq hq
  compat := pullback.lift_fst _ _ _
  locallyOfFiniteType := locallyOfFiniteType_fibreProductModelMap G₄ M₂ M₃
  quasiCompact := quasiCompact_fibreProductModelMap G₄ M₂ M₃
  isClosedImmersion := isClosedImmersion_fibreProductInduced G₄ M₂ M₃ hsq hq hb ha

/-- The same model for the first corner, read over the model of the third corner. Its structure
morphism over the stage is the *same* morphism, so it presents the same good diagram. -/
@[reducible] noncomputable def fibreProductModelTrd (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) : (M₃.toGoodDiagram).ModelOver p s₁ where
  W := pullback M₂.toBase M₃.toBase
  toBase := pullback.snd M₂.toBase M₃.toBase
  modelMap := pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap
  modelMap_eq := fibreProductModelMap_eq G₄ M₂ M₃
  toModel := pullback.lift (q ≫ M₂.toModel) (p ≫ M₃.toModel)
    (fibreProductToModel_cond G₄ M₂ M₃ hsq)
  commutes := fibreProductModel_commutes G₄ M₂ M₃ hsq hq
  compat := pullback.lift_snd _ _ _
  locallyOfFiniteType := locallyOfFiniteType_fibreProductModelMap G₄ M₂ M₃
  quasiCompact := quasiCompact_fibreProductModelMap G₄ M₂ M₃
  isClosedImmersion := isClosedImmersion_fibreProductInduced G₄ M₂ M₃ hsq hq hb ha

/-- **The good diagram for `X¹` with model `W² ×_{W⁴} W³`.** -/
@[reducible] noncomputable def fibreProductModel (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) : GoodDiagram D s₁ :=
  (fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).toGoodDiagram

/-- Reading the fibre-product model over the third corner presents the same good diagram. -/
lemma fibreProductModelTrd_toGoodDiagram (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).toGoodDiagram =
      fibreProductModel G₄ M₂ M₃ hsq hq hb ha :=
  rfl

/-- The structure morphism of `fibreProductModelSnd` over the stage is the first projection
followed by `M₂.modelMap`. -/
@[simp]
lemma fibreProductModelSnd_modelMap (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).modelMap =
      pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap :=
  rfl

/-- The structure morphism of `fibreProductModelTrd` over the stage is the first projection
followed by `M₂.modelMap`. -/
@[simp]
lemma fibreProductModelTrd_modelMap (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).modelMap =
      pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap :=
  rfl

/-- The morphism from the model of `fibreProductModelSnd` to `W²` is the first projection. -/
@[simp]
lemma fibreProductModelSnd_toBase (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).toBase =
      pullback.fst M₂.toBase M₃.toBase :=
  rfl

/-- The morphism from the model of `fibreProductModelTrd` to `W³` is the second projection. -/
@[simp]
lemma fibreProductModelTrd_toBase (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).toBase =
      pullback.snd M₂.toBase M₃.toBase :=
  rfl

/-- The stage of `fibreProductModel` is the stage of `G₄`. -/
@[simp]
lemma fibreProductModel_index (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModel G₄ M₂ M₃ hsq hq hb ha).index = G₄.index :=
  rfl

/-- The model of `fibreProductModel` is the fibre product `W² ×_{W⁴} W³`. -/
@[simp]
lemma fibreProductModel_W (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModel G₄ M₂ M₃ hsq hq hb ha).W = pullback M₂.toBase M₃.toBase :=
  rfl

/-- The structure morphism of `fibreProductModel` over the stage is the first projection
followed by `M₂.modelMap`. -/
@[simp]
lemma fibreProductModel_modelMap (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModel G₄ M₂ M₃ hsq hq hb ha).modelMap =
      pullback.fst M₂.toBase M₃.toBase ≫ M₂.modelMap :=
  rfl

/-- The morphism `X¹ ⟶ W² ×_{W⁴} W³` of `fibreProductModel` followed by the first projection is
`q ≫ M₂.toModel`. -/
@[reassoc (attr := simp)]
lemma fibreProductModel_toModel_fst (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModel G₄ M₂ M₃ hsq hq hb ha).toModel ≫ pullback.fst M₂.toBase M₃.toBase =
      q ≫ M₂.toModel :=
  pullback.lift_fst _ _ _

/-- The morphism `X¹ ⟶ W² ×_{W⁴} W³` of `fibreProductModel` followed by the second projection is
`p ≫ M₃.toModel`. -/
@[reassoc (attr := simp)]
lemma fibreProductModel_toModel_snd (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃) :
    (fibreProductModel G₄ M₂ M₃ hsq hq hb ha).toModel ≫ pullback.snd M₂.toBase M₃.toBase =
      p ≫ M₃.toModel :=
  pullback.lift_snd _ _ _

end FibreProduct

end GoodDiagram

end LimitNoetherianSituation

end AlgebraicGeometry
