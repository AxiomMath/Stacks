module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving

/-!
# Descending a morphism out of a proper algebraic space along a limit of affine schemes

Let `c.pt = lim E k` be a cofiltered limit of affine objects of the big fppf site of `S`, with
index category `I : Type u` of arbitrary size. For a proper `p₁ : Y₁ ⟶ E i`, a `p₂ : Y₂ ⟶ E i`
locally of finite presentation and a limit preserving sheaf `G` receiving `x₁ : Y₁ ⟶ G` and
`x₂ : Y₂ ⟶ G`, a morphism `c.pt ×_{E i} Y₁ ⟶ Y₂` over `E i` compatible with the `xᵢ` is defined
over some stage `E k ×_{E i} Y₁` (`AlgebraicGeometry.Space.exists_stage_hom_of_isLimit`).

## Main results

* `AlgebraicGeometry.Space.exists_stage_lift_of_isLimit_baseChange` and
  `AlgebraicGeometry.Space.exists_stage_eq_of_isLimit_baseChange`: relative limit preservation
  along the base change of the system to an affine `N ⟶ E i`.
* `AlgebraicGeometry.Space.exists_stage_eq_of_limitPreserving`: the same for a limit preserving
  presheaf.
* `AlgebraicGeometry.Space.isPullback_chartToPullbackYoneda`: the chart of a base change is the
  base change of the chart.
* `AlgebraicGeometry.Space.exists_stage_hom_of_isLimit`: the descent.

## Implementation notes

Stacks 07SK, in the form `AlgebraicGeometry.Space.exists_morphism_after_baseChange`, needs the
index category to be small for the site. The argument here works for an index of any size: it
takes an affine étale atlas `N ⟶ Y₁` with affine kernel pair `R`, uses the relative limit
preservation of `p₂` (Stacks 04AK) over the stages of `N` and `R`, and descends along the atlas
(Stacks 0262).

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section BaseChange

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS}
  {c : Cone E} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)

/-- The second projections of the base change `k ↦ E k ×_{E i} N`, as a cone over `N`. -/
noncomputable def overBaseChangeSnd {N : BigFppfOver B S hS} (n₀ : N ⟶ E.obj i) :
    overBaseChangeDiagram E i n₀ ⟶ (Functor.const (Over i)).obj N where
  app k := pullback.snd (E.map k.hom) n₀
  naturality k l g := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _
    rw [pullback.lift_snd, Category.comp_id]

omit [IsCofiltered I] in
/-- The projection `c.pt ×_{E i} N ⟶ E k ×_{E i} N` followed by the second projection to `N` is
the second projection of `c.pt ×_{E i} N`. -/
theorem overBaseChangeCone_π_app_comp_snd {N : BigFppfOver B S hS} (n₀ : N ⟶ E.obj i)
    (k : Over i) :
    (overBaseChangeCone E c i n₀).π.app k ≫ (overBaseChangeSnd i n₀).app k =
      pullback.snd (c.π.app i) n₀ :=
  pullback.lift_snd _ _ _

/-- The stages `F k ×_{F j} N` of a base-changed system of affine objects are affine. -/
private theorem isAffine_overBaseChangeDiagram_obj {J : Type u} [Category.{u} J]
    {F : J ⥤ BigFppfOver B S hS} (hF : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj j)))
    (j : J) {N : BigFppfOver B S hS} (n₀ : N ⟶ F.obj j)
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) (k : Over j) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((overBaseChangeDiagram F j n₀).obj k)) := by
  have := hF j
  have := hF k.left
  exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS)
    (F.map k.hom) n₀).hom

/-- The vertex `d.pt ×_{F j} N` of the base-changed cone is affine. -/
private theorem isAffine_overBaseChangeCone_pt {J : Type u} [Category.{u} J]
    {F : J ⥤ BigFppfOver B S hS} {d : Cone F}
    (hF : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj j)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj d.pt)) (j : J)
    {N : BigFppfOver B S hS} (n₀ : N ⟶ F.obj j)
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (overBaseChangeCone F d j n₀).pt) := by
  have := hF j
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (((Functor.const J).obj d.pt).obj j)) :=
    hpt
  have : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (d.π.app j)) :=
    isAffineHom_of_isAffine _
  exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS)
    (d.π.app j) n₀).hom

include hc hE hpt in
/-- **Relative limit preservation along a base-changed system.** For `p : Y ⟶ E i` relatively limit
preserving and `n₀ : N ⟶ E i` with `N` affine, the lifts through `p` of `n₀` over the stages
`E k ×_{E i} N` form a colimit presentation of the lifts over `c.pt ×_{E i} N`. -/
theorem nonempty_isColimit_sectionFiber_baseChange {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Y ⟶ yoneda.obj (E.obj i)) (hp : RelativelyLimitPreserving.{u, u, u, u} B S hS p)
    {N : BigFppfOver B S hS} (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (n₀ : N ⟶ E.obj i) :
    Nonempty (IsColimit ((sectionFiber B S hS p N n₀).mapCocone
      (Over.liftCone (overBaseChangeDiagram E i n₀) (overBaseChangeSnd i n₀)
        (overBaseChangeCone E c i n₀) (pullback.snd (c.π.app i) n₀)
        (overBaseChangeCone_π_app_comp_snd i n₀)).op)) := by
  have hlim := isLimitMapOverBaseChangeCone E c i n₀ (BigFppfOver.toScheme B S hS) hc
  exact hp N n₀ (Over i) _ _ hlim (isAffine_overBaseChangeDiagram_obj hE i n₀ hN)
    (isAffine_overBaseChangeCone_pt hE hpt i n₀ hN)

omit [IsCofiltered I] in
/-- A morphism `yoneda T ⟶ Y` lifting `t ≫ n₀` through `p` is a section of the presheaf of lifts
over `t`. -/
theorem yonedaEquiv_mem_sectionFiber {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} (p : Y ⟶ yoneda.obj V) {N T : BigFppfOver B S hS} (n₀ : N ⟶ V)
    (t : T ⟶ N) (b : yoneda.obj T ⟶ Y) (hb : b ≫ p = yoneda.map (t ≫ n₀)) :
    p.app (op T) (yonedaEquiv b) = (yoneda.obj V).map t.op n₀ := by
  rw [← yonedaEquiv_comp, hb, yonedaEquiv_yoneda_map]
  rfl

include hc hE hpt in
/-- **A lift over the limit comes from a stage.** -/
theorem exists_stage_lift_of_isLimit_baseChange {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Y ⟶ yoneda.obj (E.obj i)) (hp : RelativelyLimitPreserving.{u, u, u, u} B S hS p)
    {N : BigFppfOver B S hS} (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (n₀ : N ⟶ E.obj i) (b : yoneda.obj (pullback (c.π.app i) n₀) ⟶ Y)
    (hb : b ≫ p = yoneda.map (pullback.snd (c.π.app i) n₀ ≫ n₀)) :
    ∃ (k : Over i) (b' : yoneda.obj (pullback (E.map k.hom) n₀) ⟶ Y),
      b' ≫ p = yoneda.map (pullback.snd (E.map k.hom) n₀ ≫ n₀) ∧
        yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ b' = b := by
  obtain ⟨hcol⟩ := nonempty_isColimit_sectionFiber_baseChange hc hE hpt i p hp hN n₀
  let x : (sectionFiber B S hS p N n₀).obj (op (Over.mk (pullback.snd (c.π.app i) n₀))) :=
    ⟨yonedaEquiv b, yonedaEquiv_mem_sectionFiber p n₀ (pullback.snd (c.π.app i) n₀) b hb⟩
  obtain ⟨k, y, hy⟩ := exists_eq_map_of_isColimit_mapCocone _ _ _ hcol x
  let y₀ : Y.obj (op (pullback (E.map k.hom) n₀)) := y.1
  have hy₀ : p.app _ y₀ = pullback.snd (E.map k.hom) n₀ ≫ n₀ := y.2
  have hy1 : Y.map ((overBaseChangeCone E c i n₀).π.app k).op y₀ = yonedaEquiv b := by
    have := congrArg Subtype.val hy
    rw [sectionFiber_map_coe] at this
    exact this
  refine ⟨k, yonedaEquiv.symm y₀, ?_, ?_⟩
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map, hy₀]
  · calc yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ yonedaEquiv.symm y₀
        = yonedaEquiv.symm (Y.map ((overBaseChangeCone E c i n₀).π.app k).op y₀) :=
          (yonedaEquiv_symm_map _ _).symm
      _ = b := by rw [hy1, Equiv.symm_apply_apply]

include hc hE hpt in
/-- **Two lifts at a stage agreeing over the limit agree at a later stage.** -/
theorem exists_stage_eq_of_isLimit_baseChange {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Y ⟶ yoneda.obj (E.obj i)) (hp : RelativelyLimitPreserving.{u, u, u, u} B S hS p)
    {N : BigFppfOver B S hS} (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (n₀ : N ⟶ E.obj i) (k : Over i) (b₁ b₂ : yoneda.obj (pullback (E.map k.hom) n₀) ⟶ Y)
    (hb₁ : b₁ ≫ p = yoneda.map (pullback.snd (E.map k.hom) n₀ ≫ n₀))
    (hb₂ : b₂ ≫ p = yoneda.map (pullback.snd (E.map k.hom) n₀ ≫ n₀))
    (h : yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ b₁ =
      yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ b₂) :
    ∃ (k' : Over i) (g : k' ⟶ k), yoneda.map ((overBaseChangeDiagram E i n₀).map g) ≫ b₁ =
      yoneda.map ((overBaseChangeDiagram E i n₀).map g) ≫ b₂ := by
  obtain ⟨hcol⟩ := nonempty_isColimit_sectionFiber_baseChange hc hE hpt i p hp hN n₀
  let x₁ : (sectionFiber B S hS p N n₀).obj
      (op ((Over.lift (overBaseChangeDiagram E i n₀) (overBaseChangeSnd i n₀)).obj k)) :=
    ⟨(yonedaEquiv b₁ : Y.obj (op (pullback (E.map k.hom) n₀))),
      yonedaEquiv_mem_sectionFiber p n₀ (pullback.snd (E.map k.hom) n₀) b₁ hb₁⟩
  let x₂ : (sectionFiber B S hS p N n₀).obj
      (op ((Over.lift (overBaseChangeDiagram E i n₀) (overBaseChangeSnd i n₀)).obj k)) :=
    ⟨(yonedaEquiv b₂ : Y.obj (op (pullback (E.map k.hom) n₀))),
      yonedaEquiv_mem_sectionFiber p n₀ (pullback.snd (E.map k.hom) n₀) b₂ hb₂⟩
  obtain ⟨k', g, hg⟩ := eventually_eq_of_isColimit_mapCocone _ _ _ hcol k x₁ x₂ (by
      apply Subtype.ext
      rw [sectionFiber_map_coe, sectionFiber_map_coe]
      have e₁ := yonedaEquiv_naturality b₁ ((overBaseChangeCone E c i n₀).π.app k)
      have e₂ := yonedaEquiv_naturality b₂ ((overBaseChangeCone E c i n₀).π.app k)
      exact e₁.trans ((congrArg yonedaEquiv h).trans e₂.symm))
  refine ⟨k', g, ?_⟩
  have hg1 : Y.map ((overBaseChangeDiagram E i n₀).map g).op (yonedaEquiv b₁) =
      Y.map ((overBaseChangeDiagram E i n₀).map g).op (yonedaEquiv b₂) := by
    have := congrArg Subtype.val hg
    rw [sectionFiber_map_coe, sectionFiber_map_coe] at this
    exact this
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality] at hg1
  exact yonedaEquiv.injective hg1

include hc hE hpt in
/-- **Two sections of a limit preserving presheaf at a stage of a base-changed system agreeing
over the limit agree at a later stage.** -/
theorem exists_stage_eq_of_limitPreserving (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hG : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    {N : BigFppfOver B S hS} (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (n₀ : N ⟶ E.obj i) (k : Over i) (w₁ w₂ : yoneda.obj (pullback (E.map k.hom) n₀) ⟶ G)
    (h : yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ w₁ =
      yoneda.map ((overBaseChangeCone E c i n₀).π.app k) ≫ w₂) :
    ∃ (k' : Over i) (g : k' ⟶ k), yoneda.map ((overBaseChangeDiagram E i n₀).map g) ≫ w₁ =
      yoneda.map ((overBaseChangeDiagram E i n₀).map g) ≫ w₂ := by
  have hlim := isLimitMapOverBaseChangeCone E c i n₀ (BigFppfOver.toScheme B S hS) hc
  obtain ⟨hcol⟩ := hG (Over i) (overBaseChangeDiagram E i n₀) (overBaseChangeCone E c i n₀) hlim
    (isAffine_overBaseChangeDiagram_obj hE i n₀ hN) (isAffine_overBaseChangeCone_pt hE hpt i n₀ hN)
  obtain ⟨k', g, hg⟩ := eventually_eq_of_isColimit_mapCocone G _ _ hcol k (yonedaEquiv w₁)
    (yonedaEquiv w₂) (by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv h)
  refine ⟨k', g, yonedaEquiv.injective ?_⟩
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality]
  exact hg

end BaseChange

/-! ### Charts of a base change -/

section Charts

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (p : Y ⟶ yoneda.obj V)
  {N : BigFppfOver B S hS} (n : yoneda.obj N ⟶ Y) (n₀ : N ⟶ V) (hn₀ : yoneda.map n₀ = n ≫ p)

/-- The chart `V' ×_V N ⟶ V' ×_V Y` induced by a chart `n : N ⟶ Y` over `V`. -/
noncomputable def chartToPullbackYoneda {V' : BigFppfOver B S hS} (f : V' ⟶ V) :
    yoneda.obj (pullback f n₀) ⟶ pullback (yoneda.map f) p :=
  pullback.lift (yoneda.map (pullback.fst f n₀)) (yoneda.map (pullback.snd f n₀) ≫ n) (by
    rw [Category.assoc, ← hn₀, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- The chart `V' ×_V N ⟶ V' ×_V Y` followed by the first projection to `V'` is the first
projection of `V' ×_V N`. -/
@[reassoc (attr := simp)]
theorem chartToPullbackYoneda_fst {V' : BigFppfOver B S hS} (f : V' ⟶ V) :
    chartToPullbackYoneda p n n₀ hn₀ f ≫ pullback.fst (yoneda.map f) p =
      yoneda.map (pullback.fst f n₀) :=
  pullback.lift_fst _ _ _

/-- The chart `V' ×_V N ⟶ V' ×_V Y` followed by the second projection to `Y` is the second
projection of `V' ×_V N` followed by `n`. -/
@[reassoc (attr := simp)]
theorem chartToPullbackYoneda_snd {V' : BigFppfOver B S hS} (f : V' ⟶ V) :
    chartToPullbackYoneda p n n₀ hn₀ f ≫ pullback.snd (yoneda.map f) p =
      yoneda.map (pullback.snd f n₀) ≫ n :=
  pullback.lift_snd _ _ _

/-- The chart of the base change is the base change of the chart. -/
theorem isPullback_chartToPullbackYoneda {V' : BigFppfOver B S hS} (f : V' ⟶ V) :
    IsPullback (yoneda.map (pullback.snd f n₀)) (chartToPullbackYoneda p n n₀ hn₀ f) n
      (pullback.snd (yoneda.map f) p) := by
  refine IsPullback.of_bot ?_ (chartToPullbackYoneda_snd p n n₀ hn₀ f).symm
    (IsPullback.of_hasPullback (yoneda.map f) p).flip
  rw [chartToPullbackYoneda_fst, ← hn₀]
  exact ((IsPullback.of_hasPullback f n₀).map yoneda).flip

end Charts

/-! ### Descending the morphism -/

section Descent

/-- The map `X ×_Y R ⟶ X ×_Y N` induced by `u : R ⟶ N` over `Y`. -/
noncomputable def pullbackMapRight {X Y R N : BigFppfOver B S hS} (f : X ⟶ Y) {r₀ : R ⟶ Y}
    {n₀ : N ⟶ Y} (u : R ⟶ N) (hu : u ≫ n₀ = r₀) : pullback f r₀ ⟶ pullback f n₀ :=
  pullback.lift (pullback.fst f r₀) (pullback.snd f r₀ ≫ u) (by
    rw [Category.assoc, hu, pullback.condition])

/-- The map `X ×_Y R ⟶ X ×_Y N` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackMapRight_fst {X Y R N : BigFppfOver B S hS} (f : X ⟶ Y) {r₀ : R ⟶ Y}
    {n₀ : N ⟶ Y} (u : R ⟶ N) (hu : u ≫ n₀ = r₀) :
    pullbackMapRight f u hu ≫ pullback.fst f n₀ = pullback.fst f r₀ :=
  pullback.lift_fst _ _ _

/-- The map `X ×_Y R ⟶ X ×_Y N` followed by the second projection to `N` is the second
projection of `X ×_Y R` followed by `u`. -/
@[reassoc (attr := simp)]
theorem pullbackMapRight_snd {X Y R N : BigFppfOver B S hS} (f : X ⟶ Y) {r₀ : R ⟶ Y}
    {n₀ : N ⟶ Y} (u : R ⟶ N) (hu : u ≫ n₀ = r₀) :
    pullbackMapRight f u hu ≫ pullback.snd f n₀ = pullback.snd f r₀ ≫ u :=
  pullback.lift_snd _ _ _

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS}
  {c : Cone E} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)

include hc hE hpt in
/-- **A morphism out of the base change to the limit of a proper algebraic space into an algebraic
space locally of finite presentation over a stage comes from a finite stage**, together with
its compatibilities with the maps to the stage and to a limit preserving sheaf `G`. For a
cofiltered limit `c.pt = lim E k` of affine objects and `p₁ : Y₁ ⟶ E i` proper,
`p₂ : Y₂ ⟶ E i` locally of finite presentation, a morphism `a : c.pt ×_{E i} Y₁ ⟶ Y₂` over `E i`
with `x₂ ∘ a = x₁ ∘ pr` is defined over some `E k ×_{E i} Y₁` with the same two properties. -/
theorem exists_stage_hom_of_isLimit
    {Y₁ Y₂ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hG : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (p₁ : Y₁ ⟶ yoneda.obj (E.obj i)) (hp₁ : IsProper B S hS p₁)
    (p₂ : Y₂ ⟶ yoneda.obj (E.obj i)) (hp₂ : IsLocallyOfFinitePresentation B S hS p₂)
    (x₁ : Y₁ ⟶ G) (x₂ : Y₂ ⟶ G) (a : pullback (yoneda.map (c.π.app i)) p₁ ⟶ Y₂)
    (hap : a ≫ p₂ = pullback.fst (yoneda.map (c.π.app i)) p₁ ≫ yoneda.map (c.π.app i))
    (hax : a ≫ x₂ = pullback.snd (yoneda.map (c.π.app i)) p₁ ≫ x₁) :
    ∃ (k : Over i) (a' : pullback (yoneda.map (E.map k.hom)) p₁ ⟶ Y₂),
      a' ≫ p₂ = pullback.fst (yoneda.map (E.map k.hom)) p₁ ≫ yoneda.map (E.map k.hom) ∧
        a' ≫ x₂ = pullback.snd (yoneda.map (E.map k.hom)) p₁ ≫ x₁ := by
  have hVi := isAlgebraicSpace_yoneda B S hS (E.obj i)
  have hrel := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hY₂ hVi hp₂
  have hqc : IsQuasiCompactSpace B S hS Y₁ :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS (E.obj i) (hE i) hY₁ hVi p₁ hp₁.2.2
  obtain ⟨N, n, hN, hnsurj, hnet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y₁ hY₁).1 hqc
  have hnet' := (isEtale_iff_presheaf_of_yoneda B S hS n).1 hnet
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B S hS n hnet'
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R) :=
    isAffine_of_isAbsolutelySeparated B S hS B.contains_terminal
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal (E.obj i) (hE i)
        p₁ hp₁.1) hR hN hN
  let n₀ : N ⟶ E.obj i := yoneda.preimage (n ≫ p₁)
  have hn₀ : yoneda.map n₀ = n ≫ p₁ := yoneda.map_preimage _
  have hst : s ≫ n₀ = t ≫ n₀ := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hn₀, ← Category.assoc, ← Category.assoc, hR.w])
  let r₀ : R ⟶ E.obj i := s ≫ n₀
  let ν := chartToPullbackYoneda p₁ n n₀ hn₀ (c.π.app i)
  have hb : (ν ≫ a) ≫ p₂ = yoneda.map (pullback.snd (c.π.app i) n₀ ≫ n₀) := by
    rw [Category.assoc, hap, chartToPullbackYoneda_fst_assoc, ← Functor.map_comp,
      pullback.condition]
  obtain ⟨k₁, b₁, hb₁p, hb₁⟩ :=
    exists_stage_lift_of_isLimit_baseChange hc hE hpt i p₂ hrel hN n₀ (ν ≫ a) hb
  have hsr : s ≫ n₀ = r₀ := rfl
  have htr : t ≫ n₀ = r₀ := hst.symm
  let D₁ := overBaseChangeDiagram E i n₀
  let D₂ := overBaseChangeDiagram E i r₀
  let C₁ := overBaseChangeCone E c i n₀
  let C₂ := overBaseChangeCone E c i r₀
  have hDsnd : ∀ {k k' : Over i} (g : k' ⟶ k), D₁.map g ≫ pullback.snd (E.map k.hom) n₀ =
      pullback.snd (E.map k'.hom) n₀ := fun g => pullback.lift_snd _ _ _
  have hCsnd : ∀ k : Over i, C₁.π.app k ≫ pullback.snd (E.map k.hom) n₀ =
      pullback.snd (c.π.app i) n₀ := fun k => pullback.lift_snd _ _ _
  have hD₂ : ∀ {k k' : Over i} (g : k' ⟶ k) (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      D₂.map g ≫ pullbackMapRight (E.map k.hom) u hu =
        pullbackMapRight (E.map k'.hom) u hu ≫ D₁.map g := by
    intro k k' g u hu
    apply pullback.hom_ext
    · simp [D₁, D₂, pullbackMapRight]
    · simp [D₁, D₂, pullbackMapRight]
  have hC₂ : ∀ (k : Over i) (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      C₂.π.app k ≫ pullbackMapRight (E.map k.hom) u hu =
        pullbackMapRight (c.π.app i) u hu ≫ C₁.π.app k := by
    intro k u hu
    apply pullback.hom_ext
    · simp [C₁, C₂, pullbackMapRight]
    · simp [C₁, C₂, pullbackMapRight]
  let βs := yoneda.map (pullbackMapRight (E.map k₁.hom) s hsr) ≫ b₁
  let βt := yoneda.map (pullbackMapRight (E.map k₁.hom) t htr) ≫ b₁
  have hβ : ∀ (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
      (yoneda.map (pullbackMapRight (E.map k₁.hom) u hu) ≫ b₁) ≫ p₂ =
        yoneda.map (pullback.snd (E.map k₁.hom) r₀ ≫ r₀) := by
    intro u hu
    rw [Category.assoc, hb₁p, ← Functor.map_comp, pullbackMapRight_snd_assoc, hu]
  have hνst : yoneda.map (pullbackMapRight (c.π.app i) s hsr) ≫ ν =
      yoneda.map (pullbackMapRight (c.π.app i) t htr) ≫ ν := by
    apply pullback.hom_ext
    · simp only [ν, Category.assoc, chartToPullbackYoneda_fst, ← Functor.map_comp,
        pullbackMapRight_fst]
    · rw [Category.assoc, Category.assoc, chartToPullbackYoneda_snd,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        pullbackMapRight_snd, pullbackMapRight_snd, Functor.map_comp, Functor.map_comp,
        Category.assoc, Category.assoc, hR.w]
  have hlimR : yoneda.map (C₂.π.app k₁) ≫ βs = yoneda.map (C₂.π.app k₁) ≫ βt := by
    simp only [βs, βt, ← Category.assoc, ← Functor.map_comp, hC₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [hb₁, ← Category.assoc, hνst, Category.assoc]
  obtain ⟨k₂, g₂, hg₂⟩ := exists_stage_eq_of_isLimit_baseChange hc hE hpt i p₂ hrel hRaff r₀ k₁
    βs βt (hβ s hsr) (hβ t htr) hlimR
  let b₂ := yoneda.map (D₁.map g₂) ≫ b₁
  have hb₂lim : yoneda.map (C₁.π.app k₂) ≫ b₂ = ν ≫ a := by
    simp only [b₂, ← Category.assoc, ← Functor.map_comp]
    rw [show C₁.π.app k₂ ≫ D₁.map g₂ = C₁.π.app k₁ from (C₁.w g₂)]
    exact hb₁
  have hlimx : yoneda.map (C₁.π.app k₂) ≫ (b₂ ≫ x₂) =
      yoneda.map (C₁.π.app k₂) ≫ (yoneda.map (pullback.snd (E.map k₂.hom) n₀) ≫ n ≫ x₁) := by
    rw [← Category.assoc, hb₂lim, Category.assoc, hax, ← Category.assoc ν,
      chartToPullbackYoneda_snd, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, hCsnd,
      Category.assoc]
  obtain ⟨k₃, g₃, hg₃⟩ := exists_stage_eq_of_limitPreserving hc hE hpt i G hG hN n₀ k₂ _ _ hlimx
  let b₃ := yoneda.map (D₁.map g₃) ≫ b₂
  have hb₃p : b₃ ≫ p₂ = yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀) := by
    simp only [b₃, b₂, Category.assoc, hb₁p, ← Functor.map_comp]
    rw [← Category.assoc (D₁.map g₂), hDsnd, ← Category.assoc, hDsnd]
  have hb₃x : b₃ ≫ x₂ = yoneda.map (pullback.snd (E.map k₃.hom) n₀) ≫ n ≫ x₁ := by
    rw [Category.assoc, hg₃, ← Category.assoc, ← Functor.map_comp, hDsnd]
  have hb₃R : yoneda.map (pullbackMapRight (E.map k₃.hom) s hsr) ≫ b₃ =
      yoneda.map (pullbackMapRight (E.map k₃.hom) t htr) ≫ b₃ := by
    have e : ∀ (u : R ⟶ N) (hu : u ≫ n₀ = r₀),
        yoneda.map (pullbackMapRight (E.map k₃.hom) u hu) ≫ b₃ =
          yoneda.map (D₂.map g₃) ≫ yoneda.map (D₂.map g₂) ≫
            (yoneda.map (pullbackMapRight (E.map k₁.hom) u hu) ≫ b₁) := by
      intro u hu
      simp only [b₃, b₂, ← Category.assoc, ← Functor.map_comp]
      rw [hD₂]
    rw [e s hsr, e t htr]
    exact congrArg (yoneda.map (D₂.map g₃) ≫ ·) hg₂
  let ν₃ := chartToPullbackYoneda p₁ n n₀ hn₀ (E.map k₃.hom)
  have hpb₃ := isPullback_chartToPullbackYoneda p₁ n n₀ hn₀ (E.map k₃.hom)
  have het₃ := presheaf_of_isPullback B S hS hpb₃ hnet'
  have hsurj₃ := presheaf_of_isPullback B S hS hpb₃ hnsurj
  have hY₁₃ := isAlgebraicSpace_pullback B S hS (yoneda.map (E.map k₃.hom)) p₁
    (isAlgebraicSpace_yoneda B S hS _) hY₁ hVi
  obtain ⟨a', ha', -⟩ := existsUnique_hom_of_atlas_invariant B S hS hY₁₃.isSheaf hY₂.isSheaf ν₃
    hsurj₃ het₃ b₃ (by
      intro R' s' t' hsq
      have hw := hsq.w
      have hfst : s' ≫ pullback.fst (E.map k₃.hom) n₀ = t' ≫ pullback.fst (E.map k₃.hom) n₀ :=
        yoneda.map_injective (by
          have := congrArg (· ≫ pullback.fst (yoneda.map (E.map k₃.hom)) p₁) hw
          simpa only [ν₃, Category.assoc, chartToPullbackYoneda_fst, ← Functor.map_comp] using this)
      have hsnd : yoneda.map (s' ≫ pullback.snd (E.map k₃.hom) n₀) ≫ n =
          yoneda.map (t' ≫ pullback.snd (E.map k₃.hom) n₀) ≫ n := by
        have := congrArg (· ≫ pullback.snd (yoneda.map (E.map k₃.hom)) p₁) hw
        simpa only [ν₃, Category.assoc, chartToPullbackYoneda_snd, Functor.map_comp] using this
      let ρ₀ : R' ⟶ R := yoneda.preimage (hR.lift _ _ hsnd)
      have hρs : ρ₀ ≫ s = s' ≫ pullback.snd (E.map k₃.hom) n₀ := yoneda.map_injective (by
        rw [Functor.map_comp, yoneda.map_preimage, hR.lift_fst])
      have hρt : ρ₀ ≫ t = t' ≫ pullback.snd (E.map k₃.hom) n₀ := yoneda.map_injective (by
        rw [Functor.map_comp, yoneda.map_preimage, hR.lift_snd])
      let τ : R' ⟶ pullback (E.map k₃.hom) r₀ :=
        pullback.lift (s' ≫ pullback.fst _ _) ρ₀ (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, ← hρs, Category.assoc])
      have hτs : τ ≫ pullbackMapRight (E.map k₃.hom) s hsr = s' := by
        apply pullback.hom_ext
        · simp [τ]
        · simp [τ, hρs]
      have hτt : τ ≫ pullbackMapRight (E.map k₃.hom) t htr = t' := by
        apply pullback.hom_ext
        · simp [τ, hfst]
        · simp [τ, hρt]
      rw [← hτs, ← hτt, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hb₃R])
  refine ⟨k₃, a', ?_, ?_⟩
  · refine hom_ext_of_etale_atlas B S hS hY₁₃.isSheaf hVi.isSheaf ν₃ hsurj₃ het₃ ?_
    rw [← Category.assoc, ha', hb₃p, ← Category.assoc, chartToPullbackYoneda_fst,
      ← Functor.map_comp, pullback.condition]
  · refine hom_ext_of_etale_atlas B S hS hY₁₃.isSheaf hGs ν₃ hsurj₃ het₃ ?_
    rw [← Category.assoc, ha', hb₃x, chartToPullbackYoneda_snd_assoc]

end Descent

end AlgebraicGeometry.Space

end
