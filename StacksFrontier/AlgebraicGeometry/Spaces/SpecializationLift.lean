module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Lifting a specialization of points of an algebraic space to an étale chart

Stacks 03K2 says that a specialization `x' ⤳ x` in the point space of an algebraic space `X`
over a scheme `S` lifts to any étale chart: if `φ : U ⟶ X` is étale with `U` a scheme and
`u ∈ |U|` lies over `x`, then some `u' ⤳ u` lies over `x'`. The hypothesis is that the pair
`(X, x')` satisfies the equivalent conditions of Stacks 03JV; the condition actually used is
condition (1), `AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart`, which Stacks
03JV derives from each of the other five and which, in the namespace
`AlgebraicGeometry.Space`,
`HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart`
already supplies from condition (4), the definition of a decent space.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_specializes_of_finite_chartFibre`: the lifting statement for
  one étale chart whose fibre above `x'` is known to be finite, with no affineness hypothesis
  on the chart and no hypothesis on `X`.
* `AlgebraicGeometry.Space.exists_specialization_lift_of_finite_etale_fibers`: Stacks 03K2.

## Implementation notes

The proof given here is shorter than the source's and does not follow it. Write `F` for the
fibre of `|U| → |X|` above `x'` and
`T = ⋃ a ∈ F, closure {a} = {w | ∃ a ∈ F, a ⤳ w}`; the conclusion is exactly `u ∈ T`. Since
`F` is finite, `T` is closed, so its complement is open, and since `|U| → |X|` is open — Stacks
03BX clause (3), `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale` — the image of
that complement is an open subset of `|X|`. If `u ∉ T` that open set contains `x`, hence
contains the generization `x'` because an open set is stable under generization; so some
`w ∉ T` lies over `x'`. But `w` then lies in `F`, and `w ⤳ w`, so `w ∈ T`. Contradiction.

This replaces the whole middle of the source's argument. The source forms the finite sets of
points of `|U|` and of `|R| = |U ×_X U|` above `x'`, takes `T` and the corresponding `T'`, and
shows `T = s(T') = t(T')` so that `T` is an `|R|`-invariant closed set, hence the inverse image
of a closed subset `T'' = φ(T)` of `|X|` (Stacks 03BW and 03BX), and finally `T'' = closure{x'}`
contains `x`. Invariance of `T` is what makes `φ(T)` closed in `|X|`, and the lifting of
generalizations along the two projections of `R` (Remark 03II) is what makes `T` invariant. None
of that is needed once one argues with the complement: openness of `|U| → |X|` makes the image
of the open set `Tᶜ` open outright, with no invariance and no reference to `R`, and the
generization `x'` of `x` cannot escape it. For the same reason neither Stacks 03H4 nor the
finiteness of the relation fibre `|R| → |X|` above `x'` is used, although condition (1) of
Stacks 03JV supplies both; only the finiteness of the chart fibre is consumed.

The source's two reductions are also avoided rather than performed. Its first move, "we may
replace `U` by an affine open neighbourhood of `u`", is needed because condition (1) of Stacks
03JV speaks of *affine* charts only; here it is realised not by restricting `U` to an open
subscheme but by choosing, with
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, an affine étale chart
`b : V ⟶ U` of the algebraic space `h_U` (Stacks 025Z) through the given point. The composite
`b ≫ φ` is an affine étale chart of `X` through a point over `x`, condition (1) applies to it,
and the resulting specialization is pushed forward along `b`, which is continuous on points by
Stacks 03BX clause (2). The source's second move, replacing `X` by the open subspace cut out by
the image of `|U| → |X|` (Stacks 06NF) so that the chart becomes surjective, is not needed at
all: surjectivity entered only through the quotient-topology description of `|X|`, which the
complement argument does not use.

Consequently the only hypothesis on `X` is condition (1) of Stacks 03JV at `x'`. Algebraicity
of `X` is carried in the statement because the source carries it, but it is not used — the
point topology of `AlgebraicGeometry.Space.pointTopology` is defined for every presheaf, and
the one chart whose algebraicity the proof does need is `h_U`, which is an algebraic space by
Stacks 025Z for any object `U` of the site.

`attribute [local instance] pointTopology` makes `⤳` available on the point sets; it is the
idiom this part of the library uses, and is legitimate because `pointTopology` is
`@[instance_reducible]`.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **A specialization lifts to an étale chart with finite fibre above the generic point.**
Let `φ : h_U ⟶ F` be a morphism of presheaves on the big fppf site of `S` each of whose
represented base changes is étale, let `x' ⤳ x` be a specialization in the point space of `F`
of Tag 03BU, and assume the fibre of `|U| → |F|` above `x'` is finite. Then every point `p` of
`|U|` above `x` is a specialization of a point of `|U|` above `x'`.

The set `T` of points of `|U|` which are specializations of points above `x'` is the union of
the closures of the finitely many points above `x'`, hence closed. If `p` were not in `T` then
the image of the open set `Tᶜ` — open because `|U| → |F|` is, by Tag 03BX clause (3) — would
contain `x`, hence also its generization `x'`, so some point outside `T` would lie above `x'`;
but every point above `x'` lies in `T`.

Neither affineness of `U` nor any hypothesis on `F` is needed. -/
theorem exists_specializes_of_finite_chartFibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {x x' : points B S hS F} (hs : x' ⤳ x)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hfin : (chartFibre B S hS F φ x').Finite)
    {p : points B S hS (yoneda.obj U)} (hp : pointsMap B S hS (yoneda.obj U) φ p = x) :
    ∃ p' : points B S hS (yoneda.obj U),
      p' ⤳ p ∧ pointsMap B S hS (yoneda.obj U) φ p' = x' := by
  by_contra hcon
  push Not at hcon
  set T : Set (points B S hS (yoneda.obj U)) :=
    ⋃ a ∈ chartFibre B S hS F φ x', closure {a} with hTdef
  have hmem : ∀ w, w ∈ T ↔ ∃ a, pointsMap B S hS (yoneda.obj U) φ a = x' ∧ a ⤳ w := by
    intro w
    simp only [hTdef, Set.mem_iUnion, exists_prop, ← specializes_iff_mem_closure]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  have hTclosed : IsClosed T := hfin.isClosed_biUnion fun _ _ => isClosed_closure
  have hpT : p ∉ T := fun h => by
    obtain ⟨a, ha, hsp⟩ := (hmem p).mp h
    exact hcon a hsp ha
  have hopen := isOpenMap_pointsMap_of_presheafEtale B S hS φ hφ _ hTclosed.isOpen_compl
  obtain ⟨w, hwT, hw⟩ := hs.mem_open hopen ⟨p, hpT, hp⟩
  exact hwT ((hmem w).mpr ⟨w, hw, specializes_rfl⟩)

/-- **Stacks 03K2.** Let `X` be an algebraic space over a scheme `S` and let `x, x'` be points
of `|X|` with `x' ⤳ x`, that is, `x` a specialization of `x'`. Assume the pair `(X, x')`
satisfies the equivalent conditions of Stacks 03JV, in the form of condition (1): every étale
chart of `X` with affine source has finite fibres of `|U| → |X|` and of `|U ×_X U| → |X|` above
`x'`. Then for every étale `φ : h_U ⟶ X` with `U` an object of the site and every point `p` of
`|U|` above `x` there is a point `p' ⤳ p` of `|U|` above `x'`.

An affine étale chart `b : h_V ⟶ h_U` of the algebraic space `h_U` through `p` reduces this to
`AlgebraicGeometry.Space.exists_specializes_of_finite_chartFibre` for the affine chart `b ≫ φ`,
whose chart fibre above `x'` the hypothesis makes finite; the lifted specialization is then
pushed forward along `b`. Only the chart-fibre half of condition (1) is consumed, and
algebraicity of `X` is not used — it is kept in the statement because the source assumes it,
and its binder is named `_hX` for that reason. -/
theorem exists_specialization_lift_of_finite_etale_fibers
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hX : IsAlgebraicSpace B S hS X)
    (x x' : points B S hS X) (hs : x' ⤳ x)
    (hfinite : HasFiniteFibresOnEveryAffineEtaleChart B S hS X x')
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (p : points B S hS (yoneda.obj U)) (hp : pointsMap B S hS (yoneda.obj U) φ p = x) :
    ∃ p' : points B S hS (yoneda.obj U),
      p' ⤳ p ∧ pointsMap B S hS (yoneda.obj U) φ p' = x' := by
  obtain ⟨V, b, hVaff, hbEtale, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) p
  have := isMultiplicative_presheaf_etale B S hS
  have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (b ≫ φ) :=
    MorphismProperty.comp_mem _ _ _ hbEtale hφ
  obtain ⟨w', hw'sp, hw'⟩ :=
    exists_specializes_of_finite_chartFibre B S hS X hs (b ≫ φ) hcomp
      (hfinite V hVaff (b ≫ φ) (isEtale_of_presheaf_etale B S hS hcomp)).1
      (p := w) (by rw [pointsMap_comp_apply, hw, hp])
  have hsp : pointsMap B S hS (yoneda.obj V) b w' ⤳ pointsMap B S hS (yoneda.obj V) b w :=
    hw'sp.map (continuous_pointsMap B S hS b)
  rw [hw] at hsp
  exact ⟨pointsMap B S hS (yoneda.obj V) b w', hsp, by rw [← pointsMap_comp_apply]; exact hw'⟩

end AlgebraicGeometry.Space

end
