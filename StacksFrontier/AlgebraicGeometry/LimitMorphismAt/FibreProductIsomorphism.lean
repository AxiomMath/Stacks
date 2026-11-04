module

public import StacksFrontier.AlgebraicGeometry.KerDetected.Basic
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.FibreProductClosedImmersion
public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystemModels

/-!
# The comparison into the fibre product of the systems is eventually an isomorphism

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes quasi-separated and of finite type over `S`, with
`p : X¹ ⟶ X³`, `q : X¹ ⟶ X²`, `a : X³ ⟶ X⁴` and `b : X² ⟶ X⁴`, presented over one stage `S_i` by
a good diagram for `X⁴` with model `W⁴` and by models `W²` and `W³` for `X²` and `X³` mapping to
`W⁴`. If `a` and `b` are flat and of finite presentation, then the comparison

```
(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j
```

is an isomorphism at every sufficiently late stage `j`. This is the second conclusion of Stacks
0CNW; the first, that the comparison is eventually a closed immersion, is
`AlgebraicGeometry.LimitNoetherianSituation.isClosedImmersion_fibreProductComparison` and is the
input consumed here.

## Main results

* `CategoryTheory.Limits.isPullback_pullback_map`: a fibre product of two base changes is the
  base change of the fibre product of the two morphisms.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.isIso_fibreComparisonApp`: the stage
  criterion. The comparison at a stage is an isomorphism as soon as it is a closed immersion and
  `a`, `b` are base changes of flat stage morphisms `a_j`, `b_j`.
* `AlgebraicGeometry.LimitNoetherianSituation.exists_eventually_isIso_fibreProductComparison`,
  with its tail form
  `AlgebraicGeometry.LimitNoetherianSituation.exists_eventually_isIso_fibreProductComparison'`:
  the eventual isomorphism for the fibre-product model `W² ×_{W⁴} W³` of the first corner.
* `AlgebraicGeometry.LimitNoetherianSituation.exists_eventually_isIso_fibreComparison`: the
  eventual isomorphism for an arbitrary good diagram of the first corner.

## Route

Fix a stage `j` and write `π^n : X^n ⟶ X^n_j` for the legs of the four cones. The cartesian
limit square of Stacks 0CNT,
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isPullback_limit_morphismAt'`, presents `a`
and `b` at every sufficiently late stage as base changes of `a_j` and `b_j` along `π⁴`, and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_flat_morphismAt'` makes `a_j` and `b_j`
flat there. A fibre product of two base changes is a base change of the fibre product, so
`X² ×_{X⁴} X³` is the base change of `X²_j ×_{X⁴_j} X³_j` along `π⁴`, the comparison morphism
being `CategoryTheory.Limits.pullback.map`. The square being cartesian, `(q, p) : X¹ ⟶ X² ×_{X⁴}
X³` is an isomorphism, and composing its inverse with `π¹` exhibits that `pullback.map` as a
morphism factoring through `(q_j, p_j)`.

That `pullback.map` is scheme-theoretically dominant: `π⁴` is, being the canonical morphism to
the scheme-theoretic image of a quasi-compact morphism
(`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isSchemeTheoreticallyDominant_π`), and
`X²_j ×_{X⁴_j} X³_j ⟶ X⁴_j` is flat, so
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` applies. Hence `(q_j, p_j)` has
trivial kernel ideal sheaf, and a closed immersion with trivial kernel is an isomorphism by
`AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot`. The closed immersion itself is the
first conclusion of Stacks 0CNW,
`AlgebraicGeometry.LimitNoetherianSituation.isClosedImmersion_fibreProductComparison`.

Unlike the source's proof, this route does not use the eventual cartesianness of the
*transition* squares of the morphisms of systems and does not pass through Stacks 081E: the
argument runs at each stage of the tail independently rather than transporting one stage along
the transitions.

The passage from the fibre-product model of the first corner to an arbitrary good diagram for it
is the transport used in the closed-immersion case: Stacks 0CNS makes the two systems isomorphic
on a common tail
(`AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'`), compatibly with
the comparison maps
(`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison'`), and
`CategoryTheory.IsIso` cancels on the right against an isomorphism.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

/-- **A fibre product of two base changes is a base change of the fibre product.** If
`b₁ : B₁ ⟶ T₁` and `c₁ : C₁ ⟶ T₁` are the base changes along `tT : T₁ ⟶ T₀` of `b₀ : B₀ ⟶ T₀`
and `c₀ : C₀ ⟶ T₀`, then `B₁ ×_{T₁} C₁` is the base change of `B₀ ×_{T₀} C₀` along `tT`, the
comparison morphism being `CategoryTheory.Limits.pullback.map`. -/
theorem isPullback_pullback_map {B₁ B₀ C₁ C₀ T₁ T₀ : C}
    {b₁ : B₁ ⟶ T₁} {c₁ : C₁ ⟶ T₁} {b₀ : B₀ ⟶ T₀} {c₀ : C₀ ⟶ T₀}
    {tB : B₁ ⟶ B₀} {tC : C₁ ⟶ C₀} {tT : T₁ ⟶ T₀}
    [HasPullback b₁ c₁] [HasPullback b₀ c₀]
    (hB : IsPullback b₁ tB tT b₀) (hC : IsPullback c₁ tC tT c₀) :
    IsPullback (pullback.fst b₁ c₁ ≫ b₁) (pullback.map b₁ c₁ b₀ c₀ tB tC tT hB.w hC.w) tT
      (pullback.fst b₀ c₀ ≫ b₀) := by
  have hs : IsPullback
      (pullback.map b₁ c₁ b₀ c₀ tB tC tT hB.w hC.w ≫ pullback.fst b₀ c₀)
      (pullback.snd b₁ c₁) b₀ (tC ≫ c₀) := by
    rw [pullback.lift_fst, ← hC.w]
    exact (IsPullback.of_hasPullback b₁ c₁).paste_horiz hB.flip
  have hmid : IsPullback (pullback.map b₁ c₁ b₀ c₀ tB tC tT hB.w hC.w)
      (pullback.snd b₁ c₁) (pullback.snd b₀ c₀) tC :=
    IsPullback.of_right hs (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b₀ c₀)
  have hpaste := hmid.flip.paste_horiz hC
  rwa [← pullback.condition, ← pullback.condition] at hpaste

end CategoryTheory.Limits

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

/-- The comparison at a stage is an isomorphism as soon as it is a closed immersion, the two
morphisms into the fourth corner present `a` and `b` as base changes of their stage morphisms,
and those stage morphisms are flat. -/
theorem isIso_fibreComparisonApp (hsq : IsPullback q p b a)
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄)
    (j : Over (op i₀))
    (hj : P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j)
    (hA : IsPullback a ((GoodDiagram.imageCone G₃).π.app ((Over.map (homOfLE h₃).op).obj j))
      ((GoodDiagram.imageCone G₄).π.app ((Over.map (homOfLE h₄).op).obj j)) (A.maps.app j))
    (hB : IsPullback b ((GoodDiagram.imageCone G₂).π.app ((Over.map (homOfLE h₂).op).obj j))
      ((GoodDiagram.imageCone G₄).π.app ((Over.map (homOfLE h₄).op).obj j)) (B.maps.app j))
    [Flat (A.maps.app j)] [Flat (B.maps.app j)]
    (hci : IsClosedImmersion (fibreComparisonApp P Q A B j hj)) :
    IsIso (fibreComparisonApp P Q A B j hj) := by
  have := hci
  have hYsq := isPullback_pullback_map hB hA
  have : Flat (pullback.fst (B.maps.app j) (A.maps.app j) ≫ B.maps.app j) := inferInstance
  have : IsSchemeTheoreticallyDominant
      ((GoodDiagram.imageCone G₄).π.app ((Over.map (homOfLE h₄).op).obj j)) :=
    G₄.isSchemeTheoreticallyDominant_π _
  have : IsSchemeTheoreticallyDominant
      (pullback.map b a (B.maps.app j) (A.maps.app j) _ _ _ hB.w hA.w) :=
    IsSchemeTheoreticallyDominant.of_isPullback hYsq
  have : IsIso (pullback.lift q p hsq.w) := by
    have hiso : hsq.isoPullback.hom = pullback.lift q p hsq.w := by
      refine pullback.hom_ext ?_ ?_
      · rw [IsPullback.isoPullback_hom_fst, pullback.lift_fst]
      · rw [IsPullback.isoPullback_hom_snd, pullback.lift_snd]
    rw [← hiso]
    infer_instance
  have hcompat : (GoodDiagram.imageCone G₁).π.app ((Over.map (homOfLE h₁).op).obj j) ≫
      fibreComparisonApp P Q A B j hj =
        pullback.lift q p hsq.w ≫
          pullback.map b a (B.maps.app j) (A.maps.app j) _ _ _ hB.w hA.w := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, fibreComparisonApp_fst, Category.assoc, pullback.lift_fst,
        ← Category.assoc, pullback.lift_fst]
      exact Q.induces j
    · rw [Category.assoc, fibreComparisonApp_snd, Category.assoc, pullback.lift_snd,
        ← Category.assoc, pullback.lift_snd]
      exact P.induces j
  refine IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (le_antisymm ?_ bot_le)
  refine (Scheme.Hom.le_ker_comp (inv (pullback.lift q p hsq.w) ≫
    (GoodDiagram.imageCone G₁).π.app ((Over.map (homOfLE h₁).op).obj j)) _).trans ?_
  rw [Category.assoc, hcompat, IsIso.inv_hom_id_assoc]
  exact (Scheme.Hom.ker_eq_bot _).le

end MorphismAt

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}

/-- Reading a restricted morphism of image systems at a stage of a later tail: restricting along
`k₁.trans k₂` and reading at `j` is restricting along `k₁` and reading at `j` seen as a stage of
the tail above the middle index. The two sides differ only in the transition morphism carried by
the stage, which is a proof of an inequality. -/
private theorem restrict_trans_maps_app {f : X ⟶ Y} {GX : GoodDiagram D pX}
    {GY : GoodDiagram D pY} {i₀ i₁ i₂ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (k₁ : i₀ ≤ i₁) (k₂ : i₁ ≤ i₂) (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₂)) :
    (F.restrict' (k₁.trans k₂)).maps.app j =
      (F.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j) := by
  simp only [restrict_maps_app']
  cases over_map_obj_trans k₁ k₂ j
  rfl

/-- **Transporting the comparison into the stage fibre product along an isomorphism of the
systems of the first corner.** Let `P`, `Q`, `A`, `B` present the four morphisms of a square from
good diagrams `G₁`, `G₂`, `G₃`, `G₄` above `i₀`, and let `P'`, `Q'` present the same `p` and `q`
from a second good diagram `G₁'` for the first corner above `i₁`. If the component at a stage
`j₂` of a morphism `F` from the system of `G₁` to that of `G₁'` is an isomorphism carrying `P`
and `Q` to `P'` and `Q'`, then the comparison built from `G₁` at a stage `j` above `j₂` is an
isomorphism as soon as the one built from `G₁'` at `j₂` is: the two comparisons are determined by
their projections, so they differ by that component and by the identification
`CategoryTheory.Limits.pullback.congrHom` of the two spellings of the stage fibre product, and
`CategoryTheory.IsIso` cancels on the right against an isomorphism. -/
private theorem isIso_fibreComparisonApp_of_isIso_comparison
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
    {G₁ G₁' : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
    {G₄ : GoodDiagram D s₄} {i₀ i₁ i₂ : I} (k₁ : i₀ ≤ i₁) (k₂ : i₁ ≤ i₂)
    {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀} {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}
    {h₁' : G₁'.index ≤ i₁}
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄)
    (P' : MorphismAt D p G₁' G₃ i₁ h₁' (h₃.trans k₁))
    (Q' : MorphismAt D q G₁' G₂ i₁ h₁' (h₂.trans k₁))
    (F : MorphismAt D (𝟙 X₁) G₁ G₁' i₁ (h₁.trans k₁) h₁') (j : Over (op i₂))
    (hj : (P.restrict' (k₁.trans k₂)).maps.app j ≫ (A.restrict' (k₁.trans k₂)).maps.app j =
      (Q.restrict' (k₁.trans k₂)).maps.app j ≫ (B.restrict' (k₁.trans k₂)).maps.app j)
    (hj' : P'.maps.app ((Over.map (homOfLE k₂).op).obj j) ≫
          (A.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j) =
        Q'.maps.app ((Over.map (homOfLE k₂).op).obj j) ≫
          (B.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j))
    (hP : (P.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j) =
      F.maps.app ((Over.map (homOfLE k₂).op).obj j) ≫
        P'.maps.app ((Over.map (homOfLE k₂).op).obj j))
    (hQ : (Q.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j) =
      F.maps.app ((Over.map (homOfLE k₂).op).obj j) ≫
        Q'.maps.app ((Over.map (homOfLE k₂).op).obj j))
    (hF : IsIso (F.maps.app ((Over.map (homOfLE k₂).op).obj j)))
    (hc : IsIso (fibreComparisonApp P' Q' (A.restrict' k₁) (B.restrict' k₁)
      ((Over.map (homOfLE k₂).op).obj j) hj')) :
    IsIso (fibreComparisonApp (P.restrict' (k₁.trans k₂)) (Q.restrict' (k₁.trans k₂))
      (A.restrict' (k₁.trans k₂)) (B.restrict' (k₁.trans k₂)) j hj) := by
  have := hF
  have := hc
  have hAj := restrict_trans_maps_app k₁ k₂ A j
  have hBj := restrict_trans_maps_app k₁ k₂ B j
  have hcompEq : fibreComparisonApp (P.restrict' (k₁.trans k₂)) (Q.restrict' (k₁.trans k₂))
          (A.restrict' (k₁.trans k₂)) (B.restrict' (k₁.trans k₂)) j hj ≫
        (pullback.congrHom hBj hAj).hom =
      F.maps.app ((Over.map (homOfLE k₂).op).obj j) ≫
        fibreComparisonApp P' Q' (A.restrict' k₁) (B.restrict' k₁)
          ((Over.map (homOfLE k₂).op).obj j) hj' := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        fibreComparisonApp_fst]
      exact (restrict_trans_maps_app k₁ k₂ Q j).trans hQ
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        fibreComparisonApp_snd]
      exact (restrict_trans_maps_app k₁ k₂ P j).trans hP
  have : IsIso (fibreComparisonApp (P.restrict' (k₁.trans k₂)) (Q.restrict' (k₁.trans k₂))
      (A.restrict' (k₁.trans k₂)) (B.restrict' (k₁.trans k₂)) j hj ≫
      (pullback.congrHom hBj hAj).hom) := by
    rw [hcompEq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.congrHom hBj hAj).hom

end MorphismAt

variable {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
  {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
  {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
  (G₄ : GoodDiagram D s₄) (M₂ : G₄.ModelOver b s₂) (M₃ : G₄.ModelOver a s₃)
  (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
  (i₀ : I) (h : G₄.index ≤ i₀)

/-- The two composites of the square of image systems for the fibre-product model agree at every
stage of every tail. -/
theorem fibreProduct_comp_eq_comp' {i₁ : I} (k : i₀ ≤ i₁) (j : Over (op i₁)) :
    ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k).maps.app j ≫
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
      ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k).maps.app j ≫
        ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j :=
  fibreProduct_comp_eq_comp G₄ M₂ M₃ hsq hq hb ha i₀ h ((Over.map (homOfLE k).op).obj j)

/-- **Stacks Project, Tag 0CNW, the eventual isomorphism, for the fibre-product model.** With
the model `W² ×_{W⁴} W³` for the first corner of a cartesian square whose two morphisms into
the fourth corner are flat and of finite presentation, the comparison
`(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j` is an isomorphism at every sufficiently late stage. -/
theorem exists_eventually_isIso_fibreProductComparison
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    [Flat a] [Flat b] (hfa : FinitePresentation a) (hfb : FinitePresentation b) :
    ∃ (i₉ : I) (_ : i₀ ≤ i₉), ∀ j : Over (op i₀), i₉ ≤ unop j.left →
      IsIso (MorphismAt.fibreComparisonApp
        (fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h)
        (fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h)
        (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h) j
        (fibreProduct_comp_eq_comp G₄ M₂ M₃ hsq hq hb ha i₀ h j)) := by
  obtain ⟨iA, kA, hA⟩ := eventually_isPullback_limit_morphismAt' D a ha hfa
    M₃.toGoodDiagram G₄ i₀ h h (fibreProductBaseTrd G₄ M₃ ha i₀ h)
  obtain ⟨iB, kB, hB⟩ := eventually_isPullback_limit_morphismAt' D b hb hfb
    M₂.toGoodDiagram G₄ i₀ h h (fibreProductBaseSnd G₄ M₂ hb i₀ h)
  obtain ⟨iAf, kAf, hAf⟩ := eventually_flat_morphismAt' D a ha hfa
    M₃.toGoodDiagram G₄ i₀ h h (fibreProductBaseTrd G₄ M₃ ha i₀ h)
  obtain ⟨iBf, kBf, hBf⟩ := eventually_flat_morphismAt' D b hb hfb
    M₂.toGoodDiagram G₄ i₀ h h (fibreProductBaseSnd G₄ M₂ hb i₀ h)
  obtain ⟨i₅, k15, k25⟩ := exists_ge_ge iA iB
  obtain ⟨i₆, k36, k46⟩ := exists_ge_ge iAf iBf
  obtain ⟨i₉, k59, k69⟩ := exists_ge_ge i₅ i₆
  refine ⟨i₉, kA.trans (k15.trans k59), fun j hj => ?_⟩
  have : Flat ((fibreProductBaseTrd G₄ M₃ ha i₀ h).maps.app j) :=
    hAf j ((k36.trans k69).trans hj)
  have : Flat ((fibreProductBaseSnd G₄ M₂ hb i₀ h).maps.app j) :=
    hBf j ((k46.trans k69).trans hj)
  exact MorphismAt.isIso_fibreComparisonApp hsq
    (fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h)
    (fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h)
    (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h) j
    (fibreProduct_comp_eq_comp G₄ M₂ M₃ hsq hq hb ha i₀ h j)
    (hA j ((k15.trans k59).trans hj)) (hB j ((k25.trans k59).trans hj))
    (isClosedImmersion_fibreProductComparison G₄ M₂ M₃ hsq hq hb ha i₀ h j)

/-- The same statement read on the tail above the index it produces: there the comparison is an
isomorphism at *every* stage. -/
theorem exists_eventually_isIso_fibreProductComparison'
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    [Flat a] [Flat b] (hfa : FinitePresentation a) (hfb : FinitePresentation b) :
    ∃ (i₉ : I) (k : i₀ ≤ i₉), ∀ j : Over (op i₉),
      IsIso (MorphismAt.fibreComparisonApp
        ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k)
        ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k)
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k)
        ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k) j
        (fibreProduct_comp_eq_comp' G₄ M₂ M₃ hsq hq hb ha i₀ h k j)) := by
  obtain ⟨i₉, k, hiso⟩ :=
    exists_eventually_isIso_fibreProductComparison G₄ M₂ M₃ hsq hq hb ha i₀ h hfa hfb
  exact ⟨i₉, k, fun j => hiso _ (leOfHom j.hom.unop)⟩

/-- **Stacks Project, Tag 0CNW, the eventual isomorphism, for an arbitrary good diagram of the
first corner.** For *any* good diagram `G₁` of the first corner and *any* morphisms `P` and `Q`
of image systems realizing `p` and `q` from it, there is a sufficiently late stage above which
the two composites of the square of systems agree and the induced comparison
`(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j` is an isomorphism. -/
theorem exists_eventually_isIso_fibreComparison
    [QuasiSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [QuasiSeparated s₃] [LocallyOfFiniteType s₃] [QuasiCompact s₃]
    [QuasiSeparated s₄] [LocallyOfFiniteType s₄] [QuasiCompact s₄]
    [Flat a] [Flat b] (hfa : FinitePresentation a) (hfb : FinitePresentation b)
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (G₁ : GoodDiagram D s₁) (h₁ : G₁.index ≤ i₀)
    (P : MorphismAt D p G₁ M₃.toGoodDiagram i₀ h₁ h)
    (Q : MorphismAt D q G₁ M₂.toGoodDiagram i₀ h₁ h) :
    ∃ (i₉ : I) (k : i₀ ≤ i₉)
      (hcomm : ∀ j : Over (op i₉),
        (P.restrict' k).maps.app j ≫
            ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
          (Q.restrict' k).maps.app j ≫
            ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j),
      ∀ j : Over (op i₉),
        IsIso (MorphismAt.fibreComparisonApp (P.restrict' k) (Q.restrict' k)
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k)
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k) j (hcomm j)) := by
  obtain ⟨i₆, k06, hComm⟩ :=
    eventually_comp_eq_comp_morphismAt D hsq.w.symm P Q
      (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h)
  obtain ⟨i₈, k08, hIso⟩ :=
    exists_eventually_isIso_fibreProductComparison G₄ M₂ M₃ hsq hq hb ha i₀ h hfa hfb
  obtain ⟨i₁, h₁', hW₁', F, Finv, hFF⟩ :=
    exists_eventual_iso_imageSystem' D s₁ G₁ (GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha)
  obtain ⟨i₂, k02, k12⟩ := exists_ge_ge i₀ i₁
  obtain ⟨i₃, k23, hEqP⟩ :=
    eventually_natural_imageSystem_comparison' D p (F.restrict' k12)
      (MorphismAt.id' M₃.toGoodDiagram i₂ (h.trans k02)) (P.restrict' k02)
      ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
  obtain ⟨i₄, k24, hEqQ⟩ :=
    eventually_natural_imageSystem_comparison' D q (F.restrict' k12)
      (MorphismAt.id' M₂.toGoodDiagram i₂ (h.trans k02)) (Q.restrict' k02)
      ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
  obtain ⟨i₇, k37, k47⟩ := exists_ge_ge i₃ i₄
  obtain ⟨i₅, k65, k75⟩ := exists_ge_ge i₆ i₇
  obtain ⟨i₉, k59, k89⟩ := exists_ge_ge i₅ i₈
  have k29 : i₂ ≤ i₉ := ((k23.trans k37).trans k75).trans k59
  have k : i₀ ≤ i₉ := k02.trans k29
  have hcomm : ∀ j : Over (op i₉),
      (P.restrict' k).maps.app j ≫
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
        (Q.restrict' k).maps.app j ≫
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j :=
    fun j => hComm _ ((k65.trans k59).trans (leOfHom j.hom.unop))
  refine ⟨i₉, k, hcomm, fun j => ?_⟩
  set j2 : Over (op i₂) := (Over.map (homOfLE k29).op).obj j
  have hP := hEqP j2 (((k37.trans k75).trans k59).trans (leOfHom j.hom.unop))
  have hQ := hEqQ j2 (((k47.trans k75).trans k59).trans (leOfHom j.hom.unop))
  simp only [MorphismAt.id_maps_app', Category.comp_id] at hP hQ
  have hcomm2 := fibreProduct_comp_eq_comp' G₄ M₂ M₃ hsq hq hb ha i₀ h k02 j2
  have hIsoF : IsIso ((F.restrict' k12).maps.app j2) := by
    have hw := hFF ((Over.map (homOfLE k12).op).obj j2)
    simp only [MorphismAt.restrict_maps_app']
    exact ⟨Finv.maps.app ((Over.map (homOfLE k12).op).obj j2), hw.1, hw.2⟩
  exact MorphismAt.isIso_fibreComparisonApp_of_isIso_comparison k02 k29 P Q
    (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h)
    ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
    ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
    (F.restrict' k12) j (hcomm j) hcomm2 hP hQ hIsoF
    (hIso ((Over.map (homOfLE k02).op).obj j2) (k89.trans (leOfHom j.hom.unop)))

end AlgebraicGeometry.LimitNoetherianSituation

end
