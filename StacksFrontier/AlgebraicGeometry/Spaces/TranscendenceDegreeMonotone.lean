module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Monotonicity of the transcendence degree and of an induced dimension function

Let `X → Y → Z` be morphisms of algebraic spaces over a scheme `S`, let `x` be a point of `X`
and let `y` be its image in `Y`. The transcendence degree of Tag 04NM of `y` over its image in
`Z` is at most the transcendence degree of `x` over its image in `Z`, because the residue field
of `x` is an extension of the residue field of `y` and transcendence degree is additive in a
tower. Consequently the dimension function induced on `Y` by a function on the points of `Z`
takes at `y` a value at most its value at `x` for the function induced on `X`.

## Main results

* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_le_of_comp`: the relative transcendence
  degree at the image point is at most the relative transcendence degree at the point.
* `AlgebraicGeometry.Space.inducedDimensionValue_le_of_comp`: the induced dimension function of
  Tag 0EDN drops weakly along a morphism of algebraic spaces over the base.

## Implementation notes

The route is that of Stacks 06RX,
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp_of_isLocallyQuasiFinite`: both degrees are
read off one commuting diagram `U → V → W` of étale scheme charts over `X → Y → Z`, produced by
applying Tag 02X1 (`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`) twice to
a scheme atlas of `Z`, and the chart equations are
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff`. What differs is the
scheme-level step: where Stacks 06RX makes the upper extension finite and so collapses the sum
of Tag 030H, nothing is assumed here and only one summand of that sum is discarded, which
weakens the equality to an inequality but needs no finiteness. In particular no morphism is
assumed locally quasi-finite, and neither statement assumes a morphism locally of finite type
except where the induced value has to be computed.

## References

* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The scheme-level step.** Let `p : U ⟶ V`, `q : V ⟶ W` and let `h : U ⟶ W` be their
composite. The transcendence degree of the residue field of `V` at `p u` over the residue field
of `W` at the image of `u` is at most the transcendence degree of the residue field of `U` at
`u` over the same field: the two differ by the transcendence degree of `κ(p u) ⊂ κ(u)`, by
additivity of transcendence degree in a tower. -/
@[sga "6 X 1.5" "partial"]
private theorem toENat_trdeg_residueField_le_comp {U V W : Scheme.{u}}
    (p : U ⟶ V) (q : V ⟶ W) (h : U ⟶ W) (hh : h = p ≫ q) (u : U) :
    letI : Algebra (W.residueField (h u)) (U.residueField u) :=
      (h.residueFieldMap u).hom.toAlgebra
    letI : Algebra (W.residueField (q (p u))) (V.residueField (p u)) :=
      (q.residueFieldMap (p u)).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg (W.residueField (q (p u))) (V.residueField (p u))) ≤
      Cardinal.toENat (Algebra.trdeg (W.residueField (h u)) (U.residueField u)) := by
  subst hh
  let _ : Algebra (W.residueField (q (p u))) (V.residueField (p u)) :=
    (q.residueFieldMap (p u)).hom.toAlgebra
  let _ : Algebra (V.residueField (p u)) (U.residueField u) :=
    (p.residueFieldMap u).hom.toAlgebra
  let _ : Algebra (W.residueField (q (p u))) (U.residueField u) :=
    ((p ≫ q).residueFieldMap u).hom.toAlgebra
  let _ : IsScalarTower (W.residueField (q (p u))) (V.residueField (p u))
      (U.residueField u) :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      show ((p ≫ q).residueFieldMap u).hom z =
        (p.residueFieldMap u).hom ((q.residueFieldMap (p u)).hom z)
      rw [Scheme.residueFieldMap_comp]
      rfl
  exact Cardinal.enat_gc.monotone_u <| le_self_add.trans_eq <|
    _root_.trdeg_add_eq (W.residueField (q (p u))) (V.residueField (p u)) (A := U.residueField u)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X → Y → Z` be morphisms of algebraic spaces over `S` and let `x` be a point of `X`
with image `y` in `Y`. The transcendence degree of `y` over its image in `Z` is at most the
transcendence degree of `x` over its image in `Z`. -/
theorem hasTranscendenceDegreeAt_le_of_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : points B S hS X) {r s : ℕ∞}
    (hr : HasTranscendenceDegreeAt B S hS (f ≫ g) x r)
    (hs : HasTranscendenceDegreeAt B S hS g (pointsMap B S hS X f x) s) :
    s ≤ r := by
  obtain ⟨W, w, hwSurj, hwEtale⟩ := hZ.exists_atlas
  obtain ⟨V, b, β, hbg, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W w hwSurj hwEtale
  obtain ⟨U, a, α, hfa, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨ξ, hξ⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨u, hu⟩ : ∃ u, (pointsEquivScheme B S hS U).symm u = ξ :=
    ⟨pointsEquivScheme B S hS U ξ, (pointsEquivScheme B S hS U).symm_apply_apply ξ⟩
  have huξ : pointsToScheme B S hS U ξ = u := by
    rw [← hu]
    exact (pointsEquivScheme B S hS U).apply_symm_apply u
  have hcommComp : yoneda.map (α ≫ β) ≫ w = a ≫ f ≫ g := by
    rw [Functor.map_comp, Category.assoc, ← hbg, ← reassoc_of% hfa]
  have hnat : (pointsEquivScheme B S hS V).symm
      ((BigFppfOver.toScheme B S hS).map α u) =
      pointsMap B S hS (yoneda.obj U) (yoneda.map α) ξ := by
    refine (pointsEquivScheme B S hS V).symm_apply_eq.2 ?_
    show (BigFppfOver.toScheme B S hS).map α u =
      pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj U) (yoneda.map α) ξ)
    rw [pointsToScheme_pointsMap_yoneda, huξ]
  have hx : x = pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u) := by
    rw [hu, hξ]
  have hv : pointsMap B S hS X f x = pointsMap B S hS (yoneda.obj V) b
      ((pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map α u)) := by
    rw [hnat, ← hξ]
    exact pointsMap_apply_comm B S hS hfa ξ
  rw [hx, hasTranscendenceDegreeAt_pointsMap_iff B S hS r (f ≫ g) U W a w (α ≫ β) haEtale
    hwEtale hcommComp u] at hr
  rw [hv, hasTranscendenceDegreeAt_pointsMap_iff B S hS s g V W b w β hbEtale hwEtale hbg.symm
    ((BigFppfOver.toScheme B S hS).map α u)] at hs
  rw [← hr, ← hs]
  exact toENat_trdeg_residueField_le_comp ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) ((BigFppfOver.toScheme B S hS).map (α ≫ β))
    ((BigFppfOver.toScheme B S hS).map_comp α β) u

/-- **Monotonicity of the induced dimension function of Tag 0EDN.** Let `X → Y → Z` be
morphisms of algebraic spaces over `S` with `X → Z` and `Y → Z` locally of finite type, and let
`δ` be a function on the points of `Z`. The function induced on `Y` takes at the image of `x`
a value at most the value at `x` of the function induced on `X`: the two have the same
contribution from `δ`, and the relative transcendence degree can only grow. -/
theorem inducedDimensionValue_le_of_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (δ : points B S hS Z → ℤ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g)) (hg : IsLocallyOfFiniteType B S hS g)
    (x : points B S hS X) :
    inducedDimensionValue B S hS δ g (pointsMap B S hS X f x) ≤
      inducedDimensionValue B S hS δ (f ≫ g) x := by
  obtain ⟨n, hn⟩ := exists_finite_transcendenceDegreeAt B S hS (f ≫ g) hfg x
  obtain ⟨m, hm⟩ :=
    exists_finite_transcendenceDegreeAt B S hS g hg (pointsMap B S hS X f x)
  have hmn : m ≤ n :=
    Nat.cast_le.mp (hasTranscendenceDegreeAt_le_of_comp B S hS hX hY hZ f g x hn hm)
  have hpt : pointsMap B S hS X (f ≫ g) x = pointsMap B S hS Y g (pointsMap B S hS X f x) :=
    congrFun (pointsMap_comp B S hS X f g) x
  rw [inducedDimensionValue_eq B S hS hX hZ δ (f ≫ g) hfg x (n : ℕ∞) hn,
    inducedDimensionValue_eq B S hS hY hZ δ g hg (pointsMap B S hS X f x) (m : ℕ∞) hm, hpt,
    ENat.toNat_natCast, ENat.toNat_natCast]
  omega

end Space

end AlgebraicGeometry

end
