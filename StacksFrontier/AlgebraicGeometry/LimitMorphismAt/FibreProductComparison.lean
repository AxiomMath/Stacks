module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.FibreProductIsomorphism
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.StageModelOver

/-!
# The comparison into the fibre product of the systems: Stacks 0CNW

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes quasi-separated and of finite type over `S`, with
`p : X¹ ⟶ X³`, `q : X¹ ⟶ X²`, `a : X³ ⟶ X⁴` and `b : X² ⟶ X⁴`. Choose a good diagram for each
corner -- four *independent* choices, at four possibly different stages, with no morphism
between their models -- and morphisms `p_i`, `q_i`, `a_i`, `b_i` of the resulting image systems
realizing the four morphisms of the square on a common tail. Then there is one index above which
the square of systems commutes *and* the induced comparison

```
(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i
```

is a closed immersion; and if `a` and `b` are flat and of finite presentation there is a further
index above which that same comparison is an isomorphism. This is the whole of Stacks 0CNW, and
it is what `exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_fourIndices`
states, with the four morphisms of systems starting at four separate indices as in the source;
`exists_eventually_isClosedImmersion_and_isIso_fibreComparison` is the same statement for one
shared start index, from which it is derived by restricting the four to a common later index.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.fibreComparisonApp_comp_congrHom`:
  replacing the two morphisms into the fourth corner by morphisms of systems that agree with
  them at a stage changes the comparison there only by the canonical isomorphism between the two
  fibre products.
* `MorphismAt.isClosedImmersion_fibreComparisonApp_of_iso`, in the namespace
  `AlgebraicGeometry.LimitNoetherianSituation`: the comparison for one choice of good diagrams
  for the three remaining corners is a closed immersion as soon as the comparison for another
  choice is, the two being related by an isomorphism of image systems at the stage in question.
* `exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_modelOver`, in the same
  namespace: the two conclusions for the restricted shape of input in which the models of the
  second and third corners already live over the stage of the fourth and map to its model.
* `exists_eventually_isClosedImmersion_fibreComparison_of_goodDiagram`, in the same namespace:
  the closed immersion for four independently chosen good diagrams.
* `exists_eventually_isClosedImmersion_and_isIso_fibreComparison`, in the namespace
  `AlgebraicGeometry.LimitNoetherianSituation`: both conclusions of Stacks 0CNW on one index, for
  four independently chosen good diagrams and four morphisms of systems on one shared tail.
* `exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_fourIndices`, in the same
  namespace: the whole of Stacks 0CNW, with the four morphisms of systems starting at four
  separate indices `i₅`, `i₆`, `i₇`, `i₈`.

## Route

The commutation is
`AlgebraicGeometry.LimitNoetherianSituation.eventually_comp_eq_comp_morphismAt`, applied to the
four given morphisms of systems; it needs no compatibility between the four good diagrams.

The closed immersion is first proved for the restricted shape of input, in which the models of
the second and third corners are an
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ModelOver` of the good diagram of the
fourth: there
`AlgebraicGeometry.LimitNoetherianSituation.exists_eventually_isClosedImmersion_fibreComparison`
supplies it for the two canonical morphisms `a_i`, `b_i` attached to the chosen models, the
eventual uniqueness half of Stacks 0CNR,
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_morphismAt_of_dominant`,
identifies the two given morphisms with those at every sufficiently late stage, and
`fibreComparisonApp_comp_congrHom` carries the closed immersion across that identification.

Four independent good diagrams are reduced to that shape without any extra hypothesis. Replace
each of the three good diagrams `G₂`, `G₃`, `G₄` by the one whose model is its own
scheme-theoretic image at the stage `i₀`,
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStageSmallnessFree`, which is the
replacement Remark 0CNS describes. The given morphisms of systems `B` and `A` then *are*
morphisms of those stage models over the stage model of the fourth corner, by their own two
axioms: this is `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver`. So the
restricted statement applies to the replaced diagrams, and Stacks 0CNS transports its conclusion
back: `AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'` makes each of
the three systems isomorphic to its replacement on a common tail, and `pullback.map` of three
isomorphisms is an isomorphism, which `isClosedImmersion_fibreComparisonApp_of_iso` cancels. No
good diagram has to be shown to *exist*, so Stacks 0CNN is not used and no smallness hypothesis
on the index appears.

The isomorphism needs no transport at all: the stage criterion
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.isIso_fibreComparisonApp` holds for
arbitrary good diagrams and arbitrary morphisms of systems, and its inputs are the closed
immersion just obtained together with the two halves of Stacks 0CNT --
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isPullback_limit_morphismAt'`, which
presents `a` and `b` as base changes of `a_i` and `b_i` at late stages, and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_flat_morphismAt'`, which makes `a_i` and
`b_i` flat there.

A stage of the tail above a later index is read as a stage of the tail above `i₀` satisfying an
inequality, rather than as an object of `Over (op i₁)`, so that the two conclusions and the
commutation witness live over one and the same index `i₀`. Passing between the two readings
needs no transport: a hom of a preorder category is a proof inside a structure, so the stage `j`
of `Over (op i₀)` with `i₁ ≤ unop j.left` and the image of its reading in `Over (op i₁)` are
definitionally equal.

## Universe situation

The index type is at a universe independent of the universe of the schemes and carries no
smallness or cofinality hypothesis, as in every ingredient above.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW)

## Hypotheses of the source not needed here

The source asks all four corners to be quasi-separated and of finite type over `S`; the first
corner's own such hypotheses are never used, the good diagram for it and the two morphisms of
systems out of it being given, so they are omitted. Everything the source asks of the other
three corners is kept.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **Transport of a closed immersion into a fibre product along three isomorphisms.** If the
two legs of a comparison into `Y² ×_{Y⁴} Y³` become, after three isomorphisms `Y² ≅ Y²'`,
`Y³ ≅ Y³'`, `Y⁴ ≅ Y⁴'` compatible with the two morphisms into the fourth object, the legs of a
comparison into `Y²' ×_{Y⁴'} Y³'` which is a closed immersion, then the original comparison is a
closed immersion too. -/
theorem isClosedImmersion_pullback_lift_of_isIso {X₁ Y₂ Y₃ Y₄ Y₂' Y₃' Y₄' : Scheme.{u}}
    {β : Y₂ ⟶ Y₄} {α : Y₃ ⟶ Y₄} {β' : Y₂' ⟶ Y₄'} {α' : Y₃' ⟶ Y₄'}
    {u : X₁ ⟶ Y₂} {v : X₁ ⟶ Y₃} {u' : X₁ ⟶ Y₂'} {v' : X₁ ⟶ Y₃'}
    (f₂ : Y₂ ⟶ Y₂') (f₃ : Y₃ ⟶ Y₃') (f₄ : Y₄ ⟶ Y₄')
    [IsIso f₂] [IsIso f₃] [IsIso f₄]
    (e₁ : β ≫ f₄ = f₂ ≫ β') (e₂ : α ≫ f₄ = f₃ ≫ α')
    (hu : u ≫ f₂ = u') (hv : v ≫ f₃ = v')
    (hc : u ≫ β = v ≫ α) (hc' : u' ≫ β' = v' ≫ α')
    (h' : IsClosedImmersion (pullback.lift u' v' hc')) :
    IsClosedImmersion (pullback.lift u v hc) := by
  have key : pullback.lift u v hc ≫ pullback.map β α β' α' f₂ f₃ f₄ e₁ e₂ =
      pullback.lift u' v' hc' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, hu]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, hv]
  have hcomp : IsClosedImmersion
      (pullback.lift u v hc ≫ pullback.map β α β' α' f₂ f₃ f₄ e₁ e₂) := by
    rwa [key]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _
    (pullback.map β α β' α' f₂ f₃ f₄ e₁ e₂)).mp hcomp

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace MorphismAt

variable {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
  {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
  {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
  {G₁ : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
  {G₄ : GoodDiagram D s₄} {i₀ : I} {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀}
  {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}

/-- Two morphisms of image systems into the system of the fourth corner which agree at a stage
give, at that stage, the same comparison from the first corner, up to the canonical isomorphism
between the two fibre products. -/
theorem fibreComparisonApp_comp_congrHom (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) {A A' : MorphismAt D a G₃ G₄ i₀ h₃ h₄}
    {B B' : MorphismAt D b G₂ G₄ i₀ h₂ h₄} (j : Over (op i₀))
    (hA : A.maps.app j = A'.maps.app j) (hB : B.maps.app j = B'.maps.app j)
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hj' : P.maps.app j ≫ A'.maps.app j = Q.maps.app j ≫ B'.maps.app j) :
    fibreComparisonApp P Q A B j hj ≫ (pullback.congrHom hB hA).hom =
      fibreComparisonApp P Q A' B' j hj' := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      fibreComparisonApp_fst]
  · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      fibreComparisonApp_snd]

/-- The comparison at a stage is a closed immersion as soon as the comparison built from two
morphisms of image systems agreeing with `A` and `B` at that stage is one. -/
theorem isClosedImmersion_fibreComparisonApp_congr (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃)
    (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂) {A A' : MorphismAt D a G₃ G₄ i₀ h₃ h₄}
    {B B' : MorphismAt D b G₂ G₄ i₀ h₂ h₄} (j : Over (op i₀))
    (hA : A.maps.app j = A'.maps.app j) (hB : B.maps.app j = B'.maps.app j)
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hj' : P.maps.app j ≫ A'.maps.app j = Q.maps.app j ≫ B'.maps.app j)
    (hci : IsClosedImmersion (fibreComparisonApp P Q A' B' j hj')) :
    IsClosedImmersion (fibreComparisonApp P Q A B j hj) := by
  have hcomp : IsClosedImmersion
      (fibreComparisonApp P Q A B j hj ≫ (pullback.congrHom hB hA).hom) := by
    rwa [fibreComparisonApp_comp_congrHom P Q j hA hB hj hj']
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _
    (pullback.congrHom hB hA).hom).mp hcomp

/-- **Independence of the closed immersion from the choice of good diagrams for the last three
corners.** Let `K²`, `K³`, `K⁴` be a second choice of good diagrams for the second, third and
fourth corners, and let `E²`, `E³`, `E⁴` be morphisms of image systems from the first choice to
the second, with inverses at the stage `j`. Then the comparison built from the first choice is a
closed immersion as soon as the comparison built from the second choice -- with the morphisms of
systems conjugated by `E²`, `E³`, `E⁴` -- is one.

The two comparisons differ by `CategoryTheory.Limits.pullback.map` of the three isomorphisms,
which is an isomorphism, so the closed immersion cancels on the right. -/
theorem isClosedImmersion_fibreComparisonApp_of_iso
    {K₂ : GoodDiagram D s₂} {K₃ : GoodDiagram D s₃} {K₄ : GoodDiagram D s₄}
    {l₂ : K₂.index ≤ i₀} {l₃ : K₃.index ≤ i₀} {l₄ : K₄.index ≤ i₀}
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄)
    (E₂ : MorphismAt D (𝟙 X₂) G₂ K₂ i₀ h₂ l₂) (E₂' : MorphismAt D (𝟙 X₂) K₂ G₂ i₀ l₂ h₂)
    (E₃ : MorphismAt D (𝟙 X₃) G₃ K₃ i₀ h₃ l₃) (E₃' : MorphismAt D (𝟙 X₃) K₃ G₃ i₀ l₃ h₃)
    (E₄ : MorphismAt D (𝟙 X₄) G₄ K₄ i₀ h₄ l₄) (E₄' : MorphismAt D (𝟙 X₄) K₄ G₄ i₀ l₄ h₄)
    (j : Over (op i₀))
    (hc₂ : E₂.maps.app j ≫ E₂'.maps.app j = 𝟙 _)
    (hc₂' : E₂'.maps.app j ≫ E₂.maps.app j = 𝟙 _)
    (hc₃ : E₃.maps.app j ≫ E₃'.maps.app j = 𝟙 _)
    (hc₃' : E₃'.maps.app j ≫ E₃.maps.app j = 𝟙 _)
    (hc₄ : E₄.maps.app j ≫ E₄'.maps.app j = 𝟙 _)
    (hc₄' : E₄'.maps.app j ≫ E₄.maps.app j = 𝟙 _)
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hj' : (P.comp' E₃).ofCompId.maps.app j ≫
          ((E₃'.comp' A).ofIdComp.comp' E₄).ofCompId.maps.app j =
        (Q.comp' E₂).ofCompId.maps.app j ≫
          ((E₂'.comp' B).ofIdComp.comp' E₄).ofCompId.maps.app j)
    (hci : IsClosedImmersion (fibreComparisonApp (P.comp' E₃).ofCompId (Q.comp' E₂).ofCompId
      ((E₃'.comp' A).ofIdComp.comp' E₄).ofCompId ((E₂'.comp' B).ofIdComp.comp' E₄).ofCompId
      j hj')) :
    IsClosedImmersion (fibreComparisonApp P Q A B j hj) := by
  have : IsIso (E₂.maps.app j) := ⟨_, hc₂, hc₂'⟩
  have : IsIso (E₃.maps.app j) := ⟨_, hc₃, hc₃'⟩
  have : IsIso (E₄.maps.app j) := ⟨_, hc₄, hc₄'⟩
  show IsClosedImmersion (pullback.lift (Q.maps.app j) (P.maps.app j) hj.symm)
  refine isClosedImmersion_pullback_lift_of_isIso (E₂.maps.app j) (E₃.maps.app j)
    (E₄.maps.app j) ?_ ?_ rfl rfl hj.symm hj'.symm hci
  · show B.maps.app j ≫ E₄.maps.app j =
      E₂.maps.app j ≫ (E₂'.maps.app j ≫ B.maps.app j) ≫ E₄.maps.app j
    rw [← Category.assoc, ← Category.assoc, hc₂, Category.id_comp]
  · show A.maps.app j ≫ E₄.maps.app j =
      E₃.maps.app j ≫ (E₃'.maps.app j ≫ A.maps.app j) ≫ E₄.maps.app j
    rw [← Category.assoc, ← Category.assoc, hc₃, Category.id_comp]

end MorphismAt

/-- Once the comparison is a closed immersion on a tail, it is an isomorphism on a later tail when
`a` and `b` are flat and of finite presentation. -/
private theorem eventually_isIso_fibreComparisonApp_of_isClosedImmersion
    (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    (hsq : IsPullback q p b a) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
    {G₁ : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
    {G₄ : GoodDiagram D s₄} {i₀ : I} {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀}
    {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) {i₉ : I}
    (hcomm : ∀ j : Over (op i₀), i₉ ≤ unop j.left →
      P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hci : ∀ (j : Over (op i₀)) (hj : i₉ ≤ unop j.left),
      IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j (hcomm j hj)))
    (hfla : Flat a) (hflb : Flat b) (hfa : FinitePresentation a) (hfb : FinitePresentation b) :
    ∃ (i₁₀ : I) (k : i₉ ≤ i₁₀), ∀ (j : Over (op i₀)) (hj : i₁₀ ≤ unop j.left),
      IsIso (MorphismAt.fibreComparisonApp P Q A B j (hcomm j (k.trans hj))) := by
  obtain ⟨iPA, kPA, hPA⟩ := eventually_isPullback_limit_morphismAt' D a ha hfa G₃ G₄ i₀ h₃ h₄ A
  obtain ⟨iPB, kPB, hPB⟩ := eventually_isPullback_limit_morphismAt' D b hb hfb G₂ G₄ i₀ h₂ h₄ B
  obtain ⟨iFA, kFA, hFA⟩ := eventually_flat_morphismAt' D a ha hfa G₃ G₄ i₀ h₃ h₄ A
  obtain ⟨iFB, kFB, hFB⟩ := eventually_flat_morphismAt' D b hb hfb G₂ G₄ i₀ h₂ h₄ B
  obtain ⟨m₁, km₁A, km₁B⟩ := exists_ge_ge iPA iPB
  obtain ⟨m₂, km₂A, km₂B⟩ := exists_ge_ge iFA iFB
  obtain ⟨m, km₁, km₂⟩ := exists_ge_ge m₁ m₂
  obtain ⟨i₁₀, k910, km⟩ := exists_ge_ge i₉ m
  refine ⟨i₁₀, k910, fun j hj => ?_⟩
  have : Flat (A.maps.app j) := hFA j (((km₂A.trans km₂).trans km).trans hj)
  have : Flat (B.maps.app j) := hFB j (((km₂B.trans km₂).trans km).trans hj)
  exact MorphismAt.isIso_fibreComparisonApp hsq P Q A B j (hcomm j (k910.trans hj))
    (hPA j (((km₁A.trans km₁).trans km).trans hj))
    (hPB j (((km₁B.trans km₁).trans km).trans hj))
    (hci j (k910.trans hj))

/-- **Stacks Project, Tag 0CNW, for compatible models.** The two conclusions of Stacks 0CNW
under the restricted hypothesis that the models of the second and third corners live over the
stage of the good diagram for the fourth corner and map to its model. This is the shape in which
the source's own proof uses them, and
`exists_eventually_isClosedImmersion_and_isIso_fibreComparison` reduces the source's four
independent choices to it. -/
theorem exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_modelOver
    (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
    (G₄ : GoodDiagram D s₄) (M₂ : G₄.ModelOver b s₂) (M₃ : G₄.ModelOver a s₃)
    (G₁ : GoodDiagram D s₁) (i₀ : I) (h : G₄.index ≤ i₀) (h₁ : G₁.index ≤ i₀)
    (P : MorphismAt D p G₁ M₃.toGoodDiagram i₀ h₁ h)
    (Q : MorphismAt D q G₁ M₂.toGoodDiagram i₀ h₁ h)
    (A : MorphismAt D a M₃.toGoodDiagram G₄ i₀ h h)
    (B : MorphismAt D b M₂.toGoodDiagram G₄ i₀ h h) :
    ∃ (i₉ : I) (_ : i₀ ≤ i₉)
      (hcomm : ∀ j : Over (op i₀), i₉ ≤ unop j.left →
        P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j),
      (∀ (j : Over (op i₀)) (hj : i₉ ≤ unop j.left),
          IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j (hcomm j hj))) ∧
        (Flat a → Flat b → FinitePresentation a → FinitePresentation b →
          ∃ (i₁₀ : I) (k : i₉ ≤ i₁₀), ∀ (j : Over (op i₀)) (hj : i₁₀ ≤ unop j.left),
            IsIso (MorphismAt.fibreComparisonApp P Q A B j (hcomm j (k.trans hj)))) := by
  obtain ⟨i₆, k06, hComm⟩ := eventually_comp_eq_comp_morphismAt D hsq.w.symm P Q A B
  obtain ⟨i₇, k07, hcomm₀, hci₀⟩ :=
    exists_eventually_isClosedImmersion_fibreComparison G₄ M₂ M₃ hb ha i₀ h hsq hq G₁ h₁ P Q
  obtain ⟨iA, k0A, hEqA⟩ :=
    MorphismAt.eventually_eq_morphismAt_of_dominant A (fibreProductBaseTrd G₄ M₃ ha i₀ h)
  obtain ⟨iB, k0B, hEqB⟩ :=
    MorphismAt.eventually_eq_morphismAt_of_dominant B (fibreProductBaseSnd G₄ M₂ hb i₀ h)
  obtain ⟨i₅, k65, k75⟩ := exists_ge_ge i₆ i₇
  obtain ⟨i₄, kA4, kB4⟩ := exists_ge_ge iA iB
  obtain ⟨i₉, k59, k49⟩ := exists_ge_ge i₅ i₄
  have k69 : i₆ ≤ i₉ := k65.trans k59
  have hcomm : ∀ j : Over (op i₀), i₉ ≤ unop j.left →
      P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j :=
    fun j hj => hComm j (k69.trans hj)
  have hci : ∀ (j : Over (op i₀)) (hj : i₉ ≤ unop j.left),
      IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j (hcomm j hj)) := by
    intro j hj
    have hA := hEqA j ((kA4.trans k49).trans hj)
    have hB := hEqB j ((kB4.trans k49).trans hj)
    have hj' : P.maps.app j ≫ (fibreProductBaseTrd G₄ M₃ ha i₀ h).maps.app j =
        Q.maps.app j ≫ (fibreProductBaseSnd G₄ M₂ hb i₀ h).maps.app j := by
      rw [← hA, ← hB]
      exact hcomm j hj
    exact MorphismAt.isClosedImmersion_fibreComparisonApp_congr P Q j hA hB (hcomm j hj) hj'
      (hci₀ (Over.mk (homOfLE ((k75.trans k59).trans hj)).op))
  exact ⟨i₉, k06.trans k69, hcomm, hci, eventually_isIso_fibreComparisonApp_of_isClosedImmersion
    D hsq hb ha P Q A B hcomm hci⟩

/-- **Stacks Project, Tag 0CNW, the closed immersion, for four independently chosen good
diagrams.** Given a cartesian square of schemes over `S`, a good diagram for each of its four
corners chosen separately, and morphisms `p_i`, `q_i`, `a_i`, `b_i` of the resulting image
systems realizing the four morphisms of the square over a common index `i₀`, the comparison
`(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion at every sufficiently late stage.

The compatible models the restricted statement needs are *produced* from the data: replacing
`G₂`, `G₃` and `G₄` by the good diagrams whose models are their own scheme-theoretic images at
the stage `i₀`, the components of `B` and of `A` at that stage are morphisms of models over one
stage, by `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver`. -/
@[stacks 0CNW
  "closed immersion of the comparison, for four independently chosen good diagrams"]
theorem exists_eventually_isClosedImmersion_fibreComparison_of_goodDiagram
    (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
    (G₁ : GoodDiagram D s₁) (G₂ : GoodDiagram D s₂) (G₃ : GoodDiagram D s₃)
    (G₄ : GoodDiagram D s₄) (i₀ : I) (h₁ : G₁.index ≤ i₀) (h₂ : G₂.index ≤ i₀)
    (h₃ : G₃.index ≤ i₀) (h₄ : G₄.index ≤ i₀)
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) :
    ∃ (i₇ : I) (_ : i₀ ≤ i₇), ∀ (j : Over (op i₀)) (_ : i₇ ≤ unop j.left)
      (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j),
      IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j hj) := by
  obtain ⟨m₂, u₂, v₂, F₂, F₂', hF₂⟩ :=
    exists_eventual_iso_imageSystem' D s₂ G₂
      (B.stageModelOver (Over.mk (𝟙 (op i₀)))).toGoodDiagram
  obtain ⟨m₃, u₃, v₃, F₃, F₃', hF₃⟩ :=
    exists_eventual_iso_imageSystem' D s₃ G₃
      (A.stageModelOver (Over.mk (𝟙 (op i₀)))).toGoodDiagram
  obtain ⟨m₄, u₄, v₄, F₄, F₄', hF₄⟩ :=
    exists_eventual_iso_imageSystem' D s₄ G₄
      (G₄.ofStageSmallnessFree ((Over.map (homOfLE h₄).op).obj (Over.mk (𝟙 (op i₀)))))
  obtain ⟨n, kn₂, kn₃⟩ := exists_ge_ge m₂ m₃
  obtain ⟨n', kn₄, kn₀⟩ := exists_ge_ge m₄ i₀
  obtain ⟨i₅, k5n, k5n'⟩ := exists_ge_ge n n'
  have k05 : i₀ ≤ i₅ := kn₀.trans k5n'
  have km₂ : m₂ ≤ i₅ := kn₂.trans k5n
  have km₃ : m₃ ≤ i₅ := kn₃.trans k5n
  have km₄ : m₄ ≤ i₅ := kn₄.trans k5n'
  obtain ⟨i₉, k59, hcomm', hci', -⟩ :=
    exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_modelOver D hsq hq hb ha
      (G₄.ofStageSmallnessFree ((Over.map (homOfLE h₄).op).obj (Over.mk (𝟙 (op i₀)))))
      (B.stageModelOver (Over.mk (𝟙 (op i₀)))) (A.stageModelOver (Over.mk (𝟙 (op i₀))))
      G₁ i₅ k05 (h₁.trans k05)
      (((P.restrict' k05).comp' (F₃.restrict' km₃)).ofCompId)
      (((Q.restrict' k05).comp' (F₂.restrict' km₂)).ofCompId)
      ((((F₃'.restrict' km₃).comp' (A.restrict' k05)).ofIdComp.comp'
        (F₄.restrict' km₄)).ofCompId)
      ((((F₂'.restrict' km₂).comp' (B.restrict' k05)).ofIdComp.comp'
        (F₄.restrict' km₄)).ofCompId)
  refine ⟨i₉, k05.trans k59, fun j hj hcj => ?_⟩
  have hi₂ := hF₂ ((Over.map (homOfLE km₂).op).obj (Over.mk (homOfLE (k59.trans hj)).op))
  have hi₃ := hF₃ ((Over.map (homOfLE km₃).op).obj (Over.mk (homOfLE (k59.trans hj)).op))
  have hi₄ := hF₄ ((Over.map (homOfLE km₄).op).obj (Over.mk (homOfLE (k59.trans hj)).op))
  exact MorphismAt.isClosedImmersion_fibreComparisonApp_of_iso
    (P.restrict' k05) (Q.restrict' k05) (A.restrict' k05) (B.restrict' k05)
    (F₂.restrict' km₂) (F₂'.restrict' km₂) (F₃.restrict' km₃) (F₃'.restrict' km₃)
    (F₄.restrict' km₄) (F₄'.restrict' km₄) (Over.mk (homOfLE (k59.trans hj)).op)
    hi₂.1 hi₂.2 hi₃.1 hi₃.2 hi₄.1 hi₄.2 hcj
    (hcomm' (Over.mk (homOfLE (k59.trans hj)).op) hj)
    (hci' (Over.mk (homOfLE (k59.trans hj)).op) hj)

/-- **Stacks Project, Tag 0CNW.** In the limit situation `S = lim S_i` of a directed inverse
system of Noetherian schemes with affine transition morphisms, let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes quasi-separated and of finite type over `S`. For each corner
choose, independently of the others, a good diagram -- so the four stages may differ and the
four models carry no morphism between them -- take the resulting limit descriptions
`X^n = lim X^n_i` of their systems of scheme-theoretic images, and morphisms `p_i`, `q_i`,
`a_i`, `b_i` of those systems realizing the four morphisms of the square over a common index
`i₀`. Then there exists `i₉ ≥ i₀` such that at every stage above `i₉` the square of systems
commutes, `a_i ∘ p_i = b_i ∘ q_i`, and the induced morphism

```
(q_i, p_i) : X¹_i ⟶ X²_i ×_{b_i, X⁴_i, a_i} X³_i
```

is a closed immersion; and if moreover `a` and `b` are flat and of finite presentation, there
exists `i₁₀ ≥ i₉` such that at every stage above `i₁₀` that same morphism is an isomorphism.

This is the form with one start index `i₀` shared by the four morphisms of systems; the source
lets each of them start at its own index, which is
`exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_fourIndices`. -/
theorem exists_eventually_isClosedImmersion_and_isIso_fibreComparison
    (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
    (G₁ : GoodDiagram D s₁) (G₂ : GoodDiagram D s₂) (G₃ : GoodDiagram D s₃)
    (G₄ : GoodDiagram D s₄) (i₀ : I) (h₁ : G₁.index ≤ i₀) (h₂ : G₂.index ≤ i₀)
    (h₃ : G₃.index ≤ i₀) (h₄ : G₄.index ≤ i₀)
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) :
    ∃ (i₉ : I) (_ : i₀ ≤ i₉)
      (hcomm : ∀ j : Over (op i₀), i₉ ≤ unop j.left →
        P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j),
      (∀ (j : Over (op i₀)) (hj : i₉ ≤ unop j.left),
          IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j (hcomm j hj))) ∧
        (Flat a → Flat b → FinitePresentation a → FinitePresentation b →
          ∃ (i₁₀ : I) (k : i₉ ≤ i₁₀), ∀ (j : Over (op i₀)) (hj : i₁₀ ≤ unop j.left),
            IsIso (MorphismAt.fibreComparisonApp P Q A B j (hcomm j (k.trans hj)))) := by
  obtain ⟨i₆, k06, hComm⟩ := eventually_comp_eq_comp_morphismAt D hsq.w.symm P Q A B
  obtain ⟨i₇, k07, hci₀⟩ :=
    exists_eventually_isClosedImmersion_fibreComparison_of_goodDiagram D hsq hq hb ha
      G₁ G₂ G₃ G₄ i₀ h₁ h₂ h₃ h₄ P Q A B
  obtain ⟨i₉, k69, k79⟩ := exists_ge_ge i₆ i₇
  have hcomm : ∀ j : Over (op i₀), i₉ ≤ unop j.left →
      P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j :=
    fun j hj => hComm j (k69.trans hj)
  have hci : ∀ (j : Over (op i₀)) (hj : i₉ ≤ unop j.left),
      IsClosedImmersion (MorphismAt.fibreComparisonApp P Q A B j (hcomm j hj)) :=
    fun j hj => hci₀ j (k79.trans hj) (hcomm j hj)
  exact ⟨i₉, k06.trans k69, hcomm, hci, eventually_isIso_fibreComparisonApp_of_isClosedImmersion
    D hsq hb ha P Q A B hcomm hci⟩

/-- **Stacks Project, Tag 0CNW.** In the limit situation `S = lim S_i` of a directed inverse
system of Noetherian schemes with affine transition morphisms, let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes quasi-separated and of finite type over `S`. For each corner
choose, independently of the others, a good diagram, take the resulting limit descriptions
`X^n = lim X^n_i` of their systems of scheme-theoretic images, and morphisms of those systems
`(a_i)_{i ≥ i₅}`, `(b_i)_{i ≥ i₆}`, `(p_i)_{i ≥ i₇}` and `(q_i)_{i ≥ i₈}` realizing the four
morphisms of the square, each starting at its own index. Then there exists
`i₉ ≥ max(i₅, i₆, i₇, i₈)` such that at every stage `i ≥ i₉` the square of systems commutes,
`a_i ∘ p_i = b_i ∘ q_i`, and the induced morphism

```
(q_i, p_i) : X¹_i ⟶ X²_i ×_{b_i, X⁴_i, a_i} X³_i
```

is a closed immersion; and if moreover `a` and `b` are flat and of finite presentation, there
exists `i₁₀ ≥ i₉` such that at every stage above `i₁₀` that same morphism is an isomorphism.

The four morphisms of systems are read on the stages above `i₉` by restriction,
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.restrict'`. -/
@[stacks 0CNW]
theorem exists_eventually_isClosedImmersion_and_isIso_fibreComparison_of_fourIndices
    (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
    (G₁ : GoodDiagram D s₁) (G₂ : GoodDiagram D s₂) (G₃ : GoodDiagram D s₃)
    (G₄ : GoodDiagram D s₄) (i₅ i₆ i₇ i₈ : I)
    (h₃₅ : G₃.index ≤ i₅) (h₄₅ : G₄.index ≤ i₅) (h₂₆ : G₂.index ≤ i₆) (h₄₆ : G₄.index ≤ i₆)
    (h₁₇ : G₁.index ≤ i₇) (h₃₇ : G₃.index ≤ i₇) (h₁₈ : G₁.index ≤ i₈) (h₂₈ : G₂.index ≤ i₈)
    (A : MorphismAt D a G₃ G₄ i₅ h₃₅ h₄₅) (B : MorphismAt D b G₂ G₄ i₆ h₂₆ h₄₆)
    (P : MorphismAt D p G₁ G₃ i₇ h₁₇ h₃₇) (Q : MorphismAt D q G₁ G₂ i₈ h₁₈ h₂₈) :
    ∃ (i₉ : I) (k₅ : i₅ ≤ i₉) (k₆ : i₆ ≤ i₉) (k₇ : i₇ ≤ i₉) (k₈ : i₈ ≤ i₉)
      (hcomm : ∀ j : Over (op i₉),
        (P.restrict' k₇).maps.app j ≫ (A.restrict' k₅).maps.app j =
          (Q.restrict' k₈).maps.app j ≫ (B.restrict' k₆).maps.app j),
      (∀ j : Over (op i₉), IsClosedImmersion (MorphismAt.fibreComparisonApp
          (P.restrict' k₇) (Q.restrict' k₈) (A.restrict' k₅) (B.restrict' k₆) j (hcomm j))) ∧
        (Flat a → Flat b → FinitePresentation a → FinitePresentation b →
          ∃ (i₁₀ : I) (_ : i₉ ≤ i₁₀), ∀ j : Over (op i₉), i₁₀ ≤ unop j.left →
            IsIso (MorphismAt.fibreComparisonApp
              (P.restrict' k₇) (Q.restrict' k₈) (A.restrict' k₅) (B.restrict' k₆) j
              (hcomm j))) := by
  obtain ⟨m₁, k₅₁, k₆₁⟩ := exists_ge_ge i₅ i₆
  obtain ⟨m₂, k₇₂, k₈₂⟩ := exists_ge_ge i₇ i₈
  obtain ⟨m, k₁, k₂⟩ := exists_ge_ge m₁ m₂
  obtain ⟨i₉, km₉, hcomm, hci, hiso⟩ :=
    exists_eventually_isClosedImmersion_and_isIso_fibreComparison D hsq hq hb ha G₁ G₂ G₃ G₄ m
      (h₁₇.trans (k₇₂.trans k₂)) (h₂₆.trans (k₆₁.trans k₁)) (h₃₅.trans (k₅₁.trans k₁))
      (h₄₅.trans (k₅₁.trans k₁))
      (P.restrict' (k₇₂.trans k₂)) (Q.restrict' (k₈₂.trans k₂))
      (A.restrict' (k₅₁.trans k₁)) (B.restrict' (k₆₁.trans k₁))
  let r : Over (op i₉) → Over (op m) := fun j => (Over.map (homOfLE km₉).op).obj j
  have hr : ∀ j : Over (op i₉), i₉ ≤ unop (r j).left := fun j => leOfHom j.hom.unop
  refine ⟨i₉, (k₅₁.trans k₁).trans km₉, (k₆₁.trans k₁).trans km₉,
    (k₇₂.trans k₂).trans km₉, (k₈₂.trans k₂).trans km₉, fun j => hcomm (r j) (hr j),
    fun j => hci (r j) (hr j), fun hfla hflb hfa hfb => ?_⟩
  obtain ⟨i₁₀, k₉₁₀, h⟩ := hiso hfla hflb hfa hfb
  exact ⟨i₁₀, k₉₁₀, fun j hj => h (r j) hj⟩

end LimitNoetherianSituation

end AlgebraicGeometry
