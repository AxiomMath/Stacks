module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres

/-!
# No specializations inside a fibre of an étale chart

Stacks 03IM says that an étale chart of an algebraic space separates the points of a fibre as
far as the specialization order can tell: if `U → X` is étale with `U` a scheme and two points
`u, u'` of `|U|` have the same image `x` in `|X|`, then `u' ⤳ u` forces `u = u'`. The
hypothesis is that the pair `(X, x)` satisfies the equivalent conditions of Stacks 03JS,
taken here in the form of its condition (2): every étale chart of `X` with affine source has
finite fibre of `|U| → |X|` above `x`.

For a decent algebraic space the hypothesis holds at every point, and the statement becomes
Stacks 03K5.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.eq_of_specializes_of_finite_chartFibre`: the statement for a single
  étale chart whose fibre above `x` is known to be finite, with no affineness hypothesis on
  the chart and no hypothesis on `X`.
* `AlgebraicGeometry.Space.eq_of_specializes_of_finite_affine_chartFibres`: Stacks 03IM.
* `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteFibres`: the form
  whose hypothesis is condition (1) of Stacks 03JV, which is what the consumers of this
  statement carry.
* `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`: Stacks 03K5.

## Implementation notes

The argument is the source's, with the tower of specializations replaced by an extremal
choice. Write `R = h_U ×_X h_U` with its two projections `t, s : R → U`; both are étale
morphisms of schemes, because each is a representable base change of the étale chart. The
source's step is: given `a, b` in the fibre of `|U| → |X|` above `x` with `b ⤳ a`, pick
`r ∈ |R|` with `t(r) = a` and `s(r) = b` — possible by Stacks 03H4 — lift the generalization
`b ⤳ t(r)` along the flat morphism `t` to `r' ⤳ r` with `t(r') = b`, and put `c = s(r')`.
Then `c ⤳ b`, and `c` again lies above `x`; moreover `c = b` forces `r'` and `r` into one
fibre of `s`, which is discrete, so `r' = r` and therefore `b = t(r') = t(r) = a`. This is
Stacks 03II: an étale morphism is flat, hence generalizations lift along it, and it is locally
quasi-finite, hence its fibres are discrete; Mathlib supplies both halves as
`AlgebraicGeometry.Flat.generalizingMap` and
`AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton`.

Rather than iterating this step into an infinite tower of strict specializations, the proof
picks an extremal element. Suppose `u ≠ u'`. Inside the — finite — fibre `T` above `x`, let
`A` be the set of points which are *strict* generalizations of some point of `T`; it contains
`u'`, and the step above shows that every element of `A` has a strict generalization inside
`A`. Choose `b ∈ A` with `#{d ∈ T | d ⤳ b}` minimal and let `c ∈ A` be a strict
generalization of it. Then `{d ∈ T | d ⤳ c} ⊆ {d ∈ T | d ⤳ b}` by transitivity, and `b` lies
in the second set but not in the first, since `b ⤳ c` together with `c ⤳ b` would give
`b = c` — the point space of a scheme is `T0`. So the cardinality drops, contradicting
minimality. Antisymmetry of the specialization order is the only place where a separation
property of `|U|` is used, and it is used exactly where the source uses the collapse of its
tower.

The source's reduction "we may and do replace `U` by an affine neighbourhood of `u`" is
needed because condition (2) of Stacks 03JS speaks of *affine* charts only. As in
`AlgebraicGeometry.Space.exists_specialization_lift_of_finite_etale_fibers` it is realised
not by restricting `U` to an open subscheme but by choosing, with
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, an affine étale chart
`b : V ⟶ U` of the algebraic space `h_U` (Stacks 025Z) through the given point `u`. The
second point `u'` is then pulled back to `V` along `b`, which is legitimate for the same
reason that lets the source shrink `U`: `u' ⤳ u` and generalizations lift along the flat
morphism `b`. The chart `b ≫ φ` of `X` is affine and étale, so the hypothesis applies to it,
and the equality obtained upstairs is pushed forward along `b`.

Only the chart-fibre half of condition (1) of Stacks 03JV is consumed, which is why the
tagged statement carries the weaker hypothesis of Stacks 03JS. Neither Stacks 03BW nor the
finiteness of the relation fibre `|R| → |X|` above `x` is used: what the source takes from
Stacks 03BW — a point of `|R|` above a pair of points of `|U|` with the same image in `|X|` —
is already the surjectivity statement of Stacks 03H4, which is formalized as
`AlgebraicGeometry.Space.exists_points_of_isPullback` for an arbitrary cartesian square of
presheaves. Algebraicity of `X` is not used either; it is kept in the statements because the
source assumes it, and the binder is named `_hF` for that reason, except in
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`, where it is
what turns decency into condition (1) of Stacks 03JV.

The specializations in all four statements are specializations of points of the *schemes*
involved, not of the point spaces of Tag 03BX; `AlgebraicGeometry.Space.pointsEquivScheme`,
clause (1) of that tag, translates between the two, and no instance of
`AlgebraicGeometry.Space.pointTopology` is needed.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03IM](https://stacks.math.columbia.edu/tag/03IM)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of `|h_U|` of a point of the scheme underlying `V`, pushed along `yoneda.map α`. -/
private theorem symm_map_eq_pointsMap_yoneda_map {U V : BigFppfOver B S hS} (α : V ⟶ U)
    (c : (BigFppfOver.toScheme B S hS).obj V) :
    (pointsEquivScheme B S hS U).symm ((BigFppfOver.toScheme B S hS).map α c) =
      pointsMap B S hS (yoneda.obj V) (yoneda.map α) ((pointsEquivScheme B S hS V).symm c) :=
  (pointsEquivScheme B S hS U).symm_apply_eq.2 (by
    rw [pointsEquivScheme_pointsMap_yoneda, Equiv.apply_symm_apply])

/-- The relation of an étale chart, with its two projections as *morphisms of the site*.

For a chart `φ : h_U ⟶ F` each of whose representable base changes is étale, the presheaf
`h_U ×_F h_U` is represented by an object `R` of the site and both projections `t, s : R ⟶ U`
have étale underlying morphisms of schemes, being representable base changes of `φ`. The two
composites `|R| → |U| → |F|` agree, and every pair of points of `|U|` with the same image in
`|F|` is the image of a point of `|R|` — the latter by Stacks 03H4,
`AlgebraicGeometry.Space.exists_points_of_isPullback`.

This is the geometric input to the statements below, packaged as an existential so that the
choices `CategoryTheory.Functor.relativelyRepresentable` makes do not appear in them. -/
private theorem exists_etale_relation_of_presheafEtale
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    ∃ (R : BigFppfOver B S hS) (t s : R ⟶ U),
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) ∧
      (∀ r : (BigFppfOver.toScheme B S hS).obj R,
        pointsMap B S hS (yoneda.obj U) φ
            ((pointsEquivScheme B S hS U).symm ((BigFppfOver.toScheme B S hS).map t r)) =
          pointsMap B S hS (yoneda.obj U) φ
            ((pointsEquivScheme B S hS U).symm ((BigFppfOver.toScheme B S hS).map s r))) ∧
      (∀ a b : (BigFppfOver.toScheme B S hS).obj U,
        pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm a) =
            pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm b) →
          ∃ r : (BigFppfOver.toScheme B S hS).obj R,
            (BigFppfOver.toScheme B S hS).map t r = a ∧
              (BigFppfOver.toScheme B S hS).map s r = b) := by
  refine ⟨hφ.rep.pullback φ, hφ.rep.fst' φ, hφ.rep.snd φ,
    hφ.property φ (yoneda.map (hφ.rep.snd φ)) _ (hφ.rep.isPullback' φ).flip,
    hφ.property_snd φ, ?_, ?_⟩
  · intro r
    rw [symm_map_eq_pointsMap_yoneda_map, symm_map_eq_pointsMap_yoneda_map,
      ← pointsMap_comp_apply, ← pointsMap_comp_apply]
    exact congrFun (congrArg (pointsMap B S hS (yoneda.obj (hφ.rep.pullback φ)))
      (hφ.rep.isPullback' φ).w) _
  · intro a b hab
    obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS (hφ.rep.isPullback' φ)
      ((pointsEquivScheme B S hS U).symm a) ((pointsEquivScheme B S hS U).symm b) hab
    exact ⟨pointsEquivScheme B S hS (hφ.rep.pullback φ) w,
      by rw [← pointsEquivScheme_pointsMap_yoneda, hw₁, Equiv.apply_symm_apply],
      by rw [← pointsEquivScheme_pointsMap_yoneda, hw₂, Equiv.apply_symm_apply]⟩

/-- **No specializations in a finite fibre of an étale chart.** Let `φ : h_U ⟶ F` be a
morphism of presheaves on the big fppf site of `S` each of whose representable base changes
is étale, let `x` be a point of `|F|` in the sense of Tag 03BU, and assume the fibre of
`|U| → |F|` above `x` is finite. Then two points of the underlying scheme of `U` lying above
`x`, one a specialization of the other, are equal.

Write `R = h_U ×_F h_U` with its projections `t, s : R → U`. Given `a, b` above `x` with
`b ⤳ a`, Stacks 03H4 produces `r ∈ |R|` with `t(r) = a` and `s(r) = b`, flatness of `t` lifts
`b ⤳ t(r)` to `r' ⤳ r` with `t(r') = b`, and `c = s(r')` is then a point above `x` with
`c ⤳ b` which equals `b` only if `a = b`, the fibres of the étale morphism `s` being
discrete. Choosing, among the strict generalizations inside the fibre, one with as few
generalizations inside the fibre as possible contradicts this.

Neither affineness of `U` nor any hypothesis on `F` is needed. -/
theorem eq_of_specializes_of_finite_chartFibre
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : points B S hS F} {U : BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ F)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hfin : (chartFibre B S hS F φ x).Finite)
    {u u' : (BigFppfOver.toScheme B S hS).obj U}
    (hu : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) = x)
    (hu' : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u') = x)
    (hspec : u' ⤳ u) : u = u' := by
  obtain ⟨R, t, s, hte, hse, hcomm, h34⟩ := exists_etale_relation_of_presheafEtale B S hS φ hφ
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map t) :=
    (Etale.iff_flat_and_formallyUnramified.mp hte).1
  have hgen : GeneralizingMap ((BigFppfOver.toScheme B S hS).map t) := Flat.generalizingMap _
  have hlqf : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map s) :=
    (locallyQuasiFinite_of_etale _).2
  -- A strict specialization inside the fibre has a strict generalization inside the fibre.
  have hdesc : ∀ a b : (BigFppfOver.toScheme B S hS).obj U,
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm a) = x →
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm b) = x →
      b ⤳ a → b ≠ a → ∃ c : (BigFppfOver.toScheme B S hS).obj U, c ⤳ b ∧
        pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm c) = x ∧
        c ≠ b := by
    intro a b ha hb hba hne
    obtain ⟨r, hrt, hrs⟩ := h34 a b (ha.trans hb.symm)
    obtain ⟨r', hr'sp, hr't⟩ := hgen (show b ⤳ (BigFppfOver.toScheme B S hS).map t r by
      rw [hrt]; exact hba)
    refine ⟨(BigFppfOver.toScheme B S hS).map s r',
      by rw [← hrs]; exact hr'sp.map ((BigFppfOver.toScheme B S hS).map s).continuous,
      by rw [← hcomm r', hr't, hb], fun hc => hne ?_⟩
    have hdisc : _root_.IsDiscrete (((BigFppfOver.toScheme B S hS).map s) ⁻¹'
        {(BigFppfOver.toScheme B S hS).map s r}) :=
      Scheme.Hom.isDiscrete_preimage_singleton _ _
    have hrr : r' = r := hdisc.eq_of_specializes hr'sp
      (by simp only [Set.mem_preimage, Set.mem_singleton_iff, hc, hrs]) rfl
    rw [← hr't, hrr, hrt]
  by_contra hne
  -- The fibre above `x`, as a finite set of points of the scheme underlying `U`.
  set T : Set ((BigFppfOver.toScheme B S hS).obj U) :=
    {a | pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm a) = x} with hTdef
  have hmem : ∀ a, a ∈ T ↔
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm a) = x :=
    fun _ => Iff.rfl
  have hTfin : T.Finite := by
    have himg : T = (pointsEquivScheme B S hS U) '' chartFibre B S hS F φ x := by
      ext a
      refine ⟨fun h => ⟨_, (hmem a).1 h, Equiv.apply_symm_apply _ _⟩, ?_⟩
      rintro ⟨p, hp, rfl⟩
      exact (hmem _).2 (by rwa [Equiv.symm_apply_apply])
    rw [himg]
    exact hfin.image _
  -- Among the strict generalizations inside the fibre, one with fewest generalizations.
  obtain ⟨b, hbA, hbmin⟩ := Set.exists_min_image {b ∈ T | ∃ a ∈ T, b ⤳ a ∧ b ≠ a}
    (fun b => {d ∈ T | d ⤳ b}.ncard) (hTfin.subset fun _ hb => hb.1)
    ⟨u', (hmem u').2 hu', u, (hmem u).2 hu, hspec, fun h => hne h.symm⟩
  obtain ⟨hbT, a, haT, hba, hbane⟩ := hbA
  obtain ⟨c, hcb, hcT, hcne⟩ := hdesc a b ((hmem a).1 haT) ((hmem b).1 hbT) hba hbane
  have hsub : {d ∈ T | d ⤳ c} ⊂ {d ∈ T | d ⤳ b} :=
    ⟨fun d hd => ⟨hd.1, hd.2.trans hcb⟩,
      fun hsup => hcne ((hsup ⟨hbT, specializes_rfl⟩).2.antisymm hcb).eq.symm⟩
  exact absurd (hbmin c ⟨(hmem c).2 hcT, b, hbT, hcb, hcne⟩)
    (not_le.2 (Set.ncard_lt_ncard hsub (hTfin.subset fun _ hd => hd.1)))

/-- **Stacks 03IM.** Let `F` be an algebraic space over a scheme `S`, let `φ : h_U ⟶ F` be an
étale morphism from an object of the big fppf site, and let `x` be a point of `|F|` at which
the equivalent conditions of Stacks 03JS hold, in the form of condition (2): every étale
chart of `F` with affine source has finite fibre of `|U| → |F|` above `x`. If two points of
the underlying scheme of `U` lie above `x` and one is a specialization of the other, they are
equal.

An affine étale chart `b : h_V ⟶ h_U` of the algebraic space `h_U` through the specialization
`u` reduces this to `AlgebraicGeometry.Space.eq_of_specializes_of_finite_chartFibre` for the
affine chart `b ≫ φ`, whose chart fibre above `x` the hypothesis makes finite: the
generalization `u'` lifts to `V` along the flat morphism `b` together with the
specialization, and the equality obtained in `|V|` is pushed forward. Algebraicity of `F` is
not used — it is kept in the statement because the source assumes it, and its binder is
named `_hF` for that reason. -/
theorem eq_of_specializes_of_finite_affine_chartFibres
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F)
    (hφ : IsEtale B S hS φ)
    (hfin : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ ψ : yoneda.obj V ⟶ F, IsEtale B S hS ψ → (chartFibre B S hS F ψ x).Finite)
    {u u' : (BigFppfOver.toScheme B S hS).obj U}
    (hu : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) = x)
    (hu' : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u') = x)
    (hspec : u' ⤳ u) : u = u' := by
  have hφp := presheaf_etale_of_isEtale B S hS hφ
  -- An affine étale chart of `h_U` through `u`, named by its underlying morphism of the site.
  obtain ⟨V, b, hVaff, hbEtale, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) ((pointsEquivScheme B S hS U).symm u)
  obtain ⟨β, rfl⟩ : ∃ β : V ⟶ U, yoneda.map β = b := ⟨yoneda.preimage b, yoneda.map_preimage _⟩
  have hβ : Etale ((BigFppfOver.toScheme B S hS).map β) :=
    MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) hbEtale
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map β) :=
    (Etale.iff_flat_and_formallyUnramified.mp hβ).1
  -- The chosen point of `V` lies above `u`, and `u'` lifts to `V` along the chart.
  have hv : (BigFppfOver.toScheme B S hS).map β (pointsEquivScheme B S hS V w) = u := by
    rw [← pointsEquivScheme_pointsMap_yoneda, hw, Equiv.apply_symm_apply]
  obtain ⟨v', hv'sp, hv'⟩ := Flat.generalizingMap ((BigFppfOver.toScheme B S hS).map β)
    (show u' ⤳ (BigFppfOver.toScheme B S hS).map β (pointsEquivScheme B S hS V w) by
      rw [hv]; exact hspec)
  -- The composite is an affine étale chart, so its chart fibre above `x` is finite.
  have := isMultiplicative_presheaf_etale B S hS
  have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map β ≫ φ) :=
    MorphismProperty.comp_mem _ _ _ hbEtale hφp
  have hlift : ∀ c : (BigFppfOver.toScheme B S hS).obj V,
      pointsMap B S hS (yoneda.obj V) (yoneda.map β ≫ φ)
          ((pointsEquivScheme B S hS V).symm c) =
        pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm
          ((BigFppfOver.toScheme B S hS).map β c)) := by
    intro c
    rw [pointsMap_comp_apply, symm_map_eq_pointsMap_yoneda_map]
  have heq : pointsEquivScheme B S hS V w = v' :=
    eq_of_specializes_of_finite_chartFibre B S hS (yoneda.map β ≫ φ) hcomp
      (hfin V hVaff (yoneda.map β ≫ φ) (isEtale_of_presheaf_etale B S hS hcomp))
      (by rw [hlift, hv]; exact hu) (by rw [hlift, hv']; exact hu') hv'sp
  rw [← hv, ← hv', heq]

/-- **Stacks 03IM, with the hypothesis of condition (1) of Stacks 03JV.** Two points of an
étale chart of an algebraic space `F` over `S` which lie above a point `x` of `|F|` satisfying
condition (1) of Stacks 03JV, one a specialization of the other, are equal.

Only the chart-fibre half of condition (1) is consumed; the statement proved from the weaker
hypothesis of Stacks 03JS is
`AlgebraicGeometry.Space.eq_of_specializes_of_finite_affine_chartFibres`. -/
theorem eq_of_specializes_of_pointsMap_eq_of_hasFiniteFibres
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ F) (hφ : IsEtale B S hS φ)
    (x : points B S hS F) (hx : HasFiniteFibresOnEveryAffineEtaleChart B S hS F x)
    (u u' : (BigFppfOver.toScheme B S hS).obj U)
    (hu : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) = x)
    (hu' : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u') = x)
    (hspec : u' ⤳ u) : u = u' :=
  eq_of_specializes_of_finite_affine_chartFibres B S hS hF φ hφ
    (fun V hVaff ψ hψ => (hx V hVaff ψ hψ).1) hu hu' hspec

/-- **Stacks 03K5.** Let `F` be a decent algebraic space over a scheme `S` and let
`φ : h_U ⟶ F` be an étale morphism from an object of the big fppf site. If two points of the
underlying scheme of `U` have the same image in `|F|` and one is a specialization of the
other, they are equal.

Decency is condition (4) of Stacks 03JV at every point, and, in this namespace,
`HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart`
turns it into condition (1) at the common image of the two points, which is the hypothesis of
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteFibres`. -/
theorem eq_of_specializes_of_pointsMap_eq_of_isDecentSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F) (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ F)
    (hφ : IsEtale B S hS φ) (u u' : (BigFppfOver.toScheme B S hS).obj U)
    (huu' : pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u) =
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm u'))
    (hspec : u' ⤳ u) : u = u' :=
  eq_of_specializes_of_pointsMap_eq_of_hasFiniteFibres B S hS hF U φ hφ _
    ((hdec _).hasFiniteFibresOnEveryAffineEtaleChart B S hS F hF) u u' rfl huu'.symm hspec

end AlgebraicGeometry.Space

end
