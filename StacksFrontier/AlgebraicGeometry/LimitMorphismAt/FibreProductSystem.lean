module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.CartesianSquare

/-!
# The fibre product of two morphisms of image systems over a third

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a commuting square of schemes quasi-separated and of finite type over `S`, presented by good
diagrams for its four corners and by morphisms `p_i`, `q_i`, `a_i`, `b_i` of the resulting image
systems on a common tail. The stages `X²_i ×_{X⁴_i} X³_i` of the fibre product form an inverse
system, and at every stage where the square of systems commutes the morphism `(q_i, p_i)` goes
from `X¹_i` into it.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.fibreProductSystem`: the inverse system
  `i ↦ X²_i ×_{X⁴_i} X³_i`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.fibreComparisonApp`: the morphism
  `(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` at a stage where the square of systems commutes.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.fibreComparison`: those morphisms as a
  morphism of inverse systems, given commutation at every stage.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.exists_fibreComparison`: on a
  sufficiently late tail the comparison is a morphism of inverse systems whose components are
  `(q_i, p_i)`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.isClosedImmersion_fibreComparisonApp`:
  the comparison at a stage is a closed immersion as soon as the stage fibre product is
  embedded, compatibly, as a closed subscheme of the base change of the model of the good
  diagram for `X¹`.

## Implementation notes

The transitions of the fibre product system are `CategoryTheory.Limits.pullback.map` applied to
the transitions of the three image systems, the two commuting squares being the naturality of
`b_i` and of `a_i`; functoriality is then `CategoryTheory.Limits.pullback.map_id` and
`CategoryTheory.Limits.pullback.map_comp`. The comparison is
`CategoryTheory.Limits.pullback.lift` of `q_i` and `p_i`, which is available exactly where the
two composites of systems agree, that is above the index produced by
`AlgebraicGeometry.LimitNoetherianSituation.eventually_comp_eq_comp_morphismAt`; the four
morphisms of systems are moved to that tail by
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.restrict'`.

The closed-immersion criterion is the scheme-theoretic image inside a closed subscheme: `X¹_i` is
the image of `X¹` in the base change of the model, so a compatible closed embedding of the stage
fibre product into that base change makes the comparison a closed immersion by
`AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion`.

The index type is at a universe independent of the universe of the schemes and carries no
smallness or cofinality hypothesis.

The first conclusion of Stacks 0CNW asserts that the comparison is a closed immersion at every
sufficiently late stage; here that conclusion is reduced to one geometric input, namely a closed
embedding of the stage fibre product into the base change of the model of the good diagram for
`X¹`. The source supplies that input by choosing the model of `X¹` to be the fibre product of the
models of `X²` and `X³` over the model of `X⁴`.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW), whose first conclusion
  is that this comparison is eventually a closed immersion
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace MorphismAt

variable {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
  {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
  {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
  {G₁ : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
  {G₄ : GoodDiagram D s₄} {i₀ : I} {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀}
  {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}

/-- The inverse system of fibre products `X²_i ×_{X⁴_i} X³_i` of the stages of two morphisms of
image systems with the same target system.

This is `@[reducible]` for the reason
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem` is: its objects are the
fibre products the statements below mention, and without it the module system hides them at
`instances` transparency and no statement about a projection of one elaborates. -/
@[reducible] noncomputable def fibreProductSystem (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) : Over (op i₀) ⥤ Scheme.{u} where
  obj j := pullback (B.maps.app j) (A.maps.app j)
  map {j _} c := pullback.lift
    (pullback.fst (B.maps.app j) (A.maps.app j) ≫
      (Over.map (homOfLE h₂).op ⋙ GoodDiagram.imageSystem G₂).map c)
    (pullback.snd (B.maps.app j) (A.maps.app j) ≫
      (Over.map (homOfLE h₃).op ⋙ GoodDiagram.imageSystem G₃).map c)
    (by rw [Category.assoc, Category.assoc, B.maps.naturality c, A.maps.naturality c,
      ← Category.assoc, ← Category.assoc, pullback.condition])
  map_id _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    · rw [pullback.lift_snd, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp c d := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        CategoryTheory.Functor.map_comp, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        CategoryTheory.Functor.map_comp, Category.assoc]

/-- The stage `j` of the fibre product system is `X²_j ×_{X⁴_j} X³_j`. -/
@[simp]
lemma fibreProductSystem_obj (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) (j : Over (op i₀)) :
    (fibreProductSystem A B).obj j = pullback (B.maps.app j) (A.maps.app j) :=
  rfl

/-- The transitions of the fibre product system are compatible, under the first projections,
with the transitions of the image system of `X²`. -/
@[reassoc (attr := simp)]
lemma fibreProductSystem_map_fst (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) {j k : Over (op i₀)} (c : j ⟶ k) :
    (fibreProductSystem A B).map c ≫ pullback.fst (B.maps.app k) (A.maps.app k) =
      pullback.fst (B.maps.app j) (A.maps.app j) ≫
        (Over.map (homOfLE h₂).op ⋙ GoodDiagram.imageSystem G₂).map c :=
  pullback.lift_fst _ _ _

/-- The transitions of the fibre product system are compatible, under the second projections,
with the transitions of the image system of `X³`. -/
@[reassoc (attr := simp)]
lemma fibreProductSystem_map_snd (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) {j k : Over (op i₀)} (c : j ⟶ k) :
    (fibreProductSystem A B).map c ≫ pullback.snd (B.maps.app k) (A.maps.app k) =
      pullback.snd (B.maps.app j) (A.maps.app j) ≫
        (Over.map (homOfLE h₃).op ⋙ GoodDiagram.imageSystem G₃).map c :=
  pullback.lift_snd _ _ _

/-- The morphism `(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` at a stage at which the two composites
of the square of systems agree. -/
noncomputable def fibreComparisonApp (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) (j : Over (op i₀))
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j) :
    (Over.map (homOfLE h₁).op ⋙ GoodDiagram.imageSystem G₁).obj j ⟶
      (fibreProductSystem A B).obj j :=
  pullback.lift (Q.maps.app j) (P.maps.app j) hj.symm

/-- The comparison `(q_i, p_i)` followed by the first projection is `q_i`. -/
@[reassoc (attr := simp)]
lemma fibreComparisonApp_fst (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) (j : Over (op i₀))
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j) :
    fibreComparisonApp P Q A B j hj ≫ pullback.fst (B.maps.app j) (A.maps.app j) =
      Q.maps.app j :=
  pullback.lift_fst _ _ _

/-- The comparison `(q_i, p_i)` followed by the second projection is `p_i`. -/
@[reassoc (attr := simp)]
lemma fibreComparisonApp_snd (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) (j : Over (op i₀))
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j) :
    fibreComparisonApp P Q A B j hj ≫ pullback.snd (B.maps.app j) (A.maps.app j) =
      P.maps.app j :=
  pullback.lift_snd _ _ _

/-- The comparisons into the stage fibre products commute with the transitions of the two
systems. -/
lemma fibreComparisonApp_naturality (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) {j k : Over (op i₀)} (c : j ⟶ k)
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hk : P.maps.app k ≫ A.maps.app k = Q.maps.app k ≫ B.maps.app k) :
    (Over.map (homOfLE h₁).op ⋙ GoodDiagram.imageSystem G₁).map c ≫
        fibreComparisonApp P Q A B k hk =
      fibreComparisonApp P Q A B j hj ≫ (fibreProductSystem A B).map c := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, fibreComparisonApp_fst,
      fibreComparisonApp_snd, fibreComparisonApp_fst_assoc, fibreComparisonApp_snd_assoc]
  exacts [Q.maps.naturality c, P.maps.naturality c]

/-- The comparison from the image system of `X¹` to the fibre product of the image systems of
`X²` and `X³` over that of `X⁴`, as a morphism of inverse systems, on a tail where the square of
systems commutes at every stage. -/
noncomputable def fibreComparison (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄)
    (hcomm : ∀ j : Over (op i₀), P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j) :
    (Over.map (homOfLE h₁).op ⋙ GoodDiagram.imageSystem G₁) ⟶ fibreProductSystem A B where
  app j := fibreComparisonApp P Q A B j (hcomm j)
  naturality _ _ c := fibreComparisonApp_naturality P Q A B c (hcomm _) (hcomm _)

/-- The component of `fibreComparison` at a stage is `fibreComparisonApp` at that stage. -/
@[simp]
lemma fibreComparison_app (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄)
    (hcomm : ∀ j : Over (op i₀), P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (j : Over (op i₀)) :
    (fibreComparison P Q A B hcomm).app j = fibreComparisonApp P Q A B j (hcomm j) :=
  rfl

/-- The comparison at a stage is a closed immersion as soon as the stage fibre product is
embedded as a closed subscheme of the base change of the model of the good diagram for `X¹`
through which the closed embedding of `X¹_i` factors. -/
lemma isClosedImmersion_fibreComparisonApp (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄)
    (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) (j : Over (op i₀))
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (z : (fibreProductSystem A B).obj j ⟶
      G₁.stageTarget ((Over.map (homOfLE h₁).op).obj j)) (hzci : IsClosedImmersion z)
    (hz : fibreComparisonApp P Q A B j hj ≫ z =
      (G₁.stageMap ((Over.map (homOfLE h₁).op).obj j)).imageι) :
    IsClosedImmersion (fibreComparisonApp P Q A B j hj) :=
  have := hzci
  have : IsClosedImmersion (fibreComparisonApp P Q A B j hj ≫ z) := by
    rw [hz]; infer_instance
  IsClosedImmersion.of_comp_isClosedImmersion _ z

end MorphismAt

/-- **The comparison of Stacks 0CNW into the fibre product of the systems.** Given a commuting
square of schemes quasi-separated and of finite type over the limit `S`, good diagrams for its
four corners and morphisms `p_i`, `q_i`, `a_i`, `b_i` of the resulting image systems realizing
the four morphisms on a common tail, there is an index above which the morphisms `(q_i, p_i)`
assemble into a morphism from the image system of `X¹` to the system of fibre products
`X²_i ×_{X⁴_i} X³_i`. -/
theorem exists_fibreComparison (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄} (hsq : p ≫ a = q ≫ b)
    {G₁ : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
    {G₄ : GoodDiagram D s₄} {i₀ : I} {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀}
    {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) :
    ∃ (i₉ : I) (k : i₀ ≤ i₉)
      (F : (Over.map (homOfLE (h₁.trans k)).op ⋙ GoodDiagram.imageSystem G₁) ⟶
        MorphismAt.fibreProductSystem (A.restrict' k) (B.restrict' k)),
      ∀ j : Over (op i₉),
        F.app j ≫ pullback.fst ((B.restrict' k).maps.app j) ((A.restrict' k).maps.app j) =
            (Q.restrict' k).maps.app j ∧
          F.app j ≫ pullback.snd ((B.restrict' k).maps.app j) ((A.restrict' k).maps.app j) =
            (P.restrict' k).maps.app j := by
  obtain ⟨i₉, k, hk⟩ := eventually_comp_eq_comp_morphismAt D hsq P Q A B
  exact ⟨i₉, k, MorphismAt.fibreComparison (P.restrict' k) (Q.restrict' k) (A.restrict' k)
    (B.restrict' k) (fun j => hk _ (leOfHom j.hom.unop)),
    fun _ => ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩⟩

end AlgebraicGeometry.LimitNoetherianSituation
