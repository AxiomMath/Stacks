module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart

/-!
# Transcendence degree through a locally quasi-finite morphism

Let `X → Y → Z` be morphisms of algebraic spaces over a scheme `S`, let `x` be a point of
`X` and let `y`, `z` be its images. Stacks 06RX says that if `X → Y` is locally quasi-finite
and `Y → Z` is locally of finite type, then the transcendence degree of `x/z` equals the
transcendence degree of `y/z`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp_of_isLocallyQuasiFinite` is
  Stacks 06RX: the relative transcendence degree of Tag 04NM at `x` for the composite
  `X → Z` is the relative transcendence degree at `y` for `Y → Z`.

## Implementation notes

The source reads both degrees off one commuting diagram `U → V → W` of étale scheme charts
over `X → Y → Z`. Such a diagram is produced by applying Stacks 02X1
(`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`) twice to a scheme atlas
of `Z`, and the point of `U` over `x` exists because the resulting chart of `X` is surjective,
which is surjectivity on the point sets of Tag 03BU by Stacks 03H5
(`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`). Both degrees are then
numbers read off that single chart by
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff`, so no further étale locality
argument is needed here; the chart independence it rests on is Tag 04NK.

What remains is the scheme-level computation. Where the source invokes Morphisms, Lemma 29.21.5
(Tag 01TG) to see that the residue field extension `κ(v) ⊂ κ(u)` is finite, this file uses
Tag 01TF in the form `AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField`, applied to
the clopen fibre singleton of a locally quasi-finite morphism; the conclusion then follows from
additivity of transcendence degree in a tower (Tag 030H, `trdeg_add_eq`) and the vanishing of
the transcendence degree of a finite, hence algebraic, extension.

The hypothesis that `Y → Z` is locally of finite type is retained from the source. It is not
used: Tag 04NM defines the relative transcendence degree for an arbitrary morphism, and the
source's proof appeals only to local quasi-finiteness of `X → Y`.

The composite chart morphism is `α ≫ β`, whose underlying scheme morphism is only
*propositionally* equal to the composite of the two underlying scheme morphisms, so the
scheme-level lemma carries that equation as a hypothesis rather than assuming the composite
shape.

## References

* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue field of the source of a morphism of schemes which is locally of finite type
and locally quasi-finite is a finite extension of the residue field of the image point. This is
the ring-theoretic content of Tag 01TG, obtained here from Tag 01TF: the point is isolated in
its fibre, so its fibre singleton is clopen. -/
private theorem finite_residueField_of_locallyQuasiFinite {U V : Scheme.{u}} (p : U ⟶ V)
    [LocallyOfFiniteType p] [LocallyQuasiFinite p] (u : U) :
    letI : Algebra (V.residueField (p u)) (U.residueField u) :=
      (p.residueFieldMap u).hom.toAlgebra
    Module.Finite (V.residueField (p u)) (U.residueField u) :=
  (isClosed_asFiber_iff_finite_residueField p u).mp
    ((p.quasiFiniteAt u).isClopen_singleton_asFiber.isClosed)

/-- The residue field of the source of a morphism of schemes which is locally of finite type
and locally quasi-finite is a finite extension of the residue field of the image point. This is
the ring-theoretic content of Tag 01TG, obtained here from Tag 01TF: the point is isolated in
its fibre, so its fibre singleton is clopen. -/
alias finite_residueField_of_locallyQuasiFinite' := finite_residueField_of_locallyQuasiFinite

/-- **The scheme-level step of Stacks 06RX.** Let `p : U ⟶ V` be locally of finite type and
locally quasi-finite, let `q : V ⟶ W`, and let `h : U ⟶ W` be their composite. Then the
transcendence degree of the residue field of `U` at `u` over the residue field of `W` at the
image of `u` equals the transcendence degree of the residue field of `V` at `p u` over the same
field: the extension `κ(p u) ⊂ κ(u)` is finite, hence algebraic, and transcendence degree is
additive in a tower. -/
@[sga "6 X 1.5" "special case"]
private theorem toENat_trdeg_residueField_comp_of_locallyQuasiFinite {U V W : Scheme.{u}}
    (p : U ⟶ V) (q : V ⟶ W) (h : U ⟶ W) (hh : h = p ≫ q)
    [LocallyOfFiniteType p] [LocallyQuasiFinite p] (u : U) :
    letI : Algebra (W.residueField (h u)) (U.residueField u) :=
      (h.residueFieldMap u).hom.toAlgebra
    letI : Algebra (W.residueField (q (p u))) (V.residueField (p u)) :=
      (q.residueFieldMap (p u)).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg (W.residueField (h u)) (U.residueField u)) =
      Cardinal.toENat (Algebra.trdeg (W.residueField (q (p u))) (V.residueField (p u))) := by
  subst hh
  let _ : Algebra (W.residueField (q (p u))) (V.residueField (p u)) :=
    (q.residueFieldMap (p u)).hom.toAlgebra
  let _ : Algebra (V.residueField (p u)) (U.residueField u) :=
    (p.residueFieldMap u).hom.toAlgebra
  let _ : Algebra (W.residueField (q (p u))) (U.residueField u) :=
    ((p ≫ q).residueFieldMap u).hom.toAlgebra
  have : IsScalarTower (W.residueField (q (p u))) (V.residueField (p u))
      (U.residueField u) :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      show ((p ≫ q).residueFieldMap u).hom z =
        (p.residueFieldMap u).hom ((q.residueFieldMap (p u)).hom z)
      rw [Scheme.residueFieldMap_comp]
      rfl
  have : Module.Finite (V.residueField (p u)) (U.residueField u) :=
    finite_residueField_of_locallyQuasiFinite p u
  have : Algebra.IsAlgebraic (V.residueField (p u)) (U.residueField u) := .of_finite _ _
  have hadd := _root_.trdeg_add_eq (W.residueField (q (p u))) (V.residueField (p u))
    (A := U.residueField u)
  rw [_root_.trdeg_eq_zero (R := V.residueField (p u)) (A := U.residueField u),
    add_zero] at hadd
  exact congrArg Cardinal.toENat hadd.symm

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06RX.** Let `X → Y → Z` be morphisms of algebraic spaces over `S` with `X → Y`
locally quasi-finite and `Y → Z` locally of finite type, and let `x` be a point of `X` with
image `y` in `Y`. Then the transcendence degree of `x` over its image in `Z` equals the
transcendence degree of `y` over its image in `Z`.

The tag is registered on
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp_iff_of_isLocallyQuasiFinite` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension`, which states the same
equivalence without `_hg`. That hypothesis is retained here from the source and, as its
underscore records, is never used, so the tag reads better on the form that does not take
it. -/
theorem hasTranscendenceDegreeAt_comp_of_isLocallyQuasiFinite
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyQuasiFinite B S hS f) (_hg : IsLocallyOfFiniteType B S hS g)
    (x : points B S hS X) (r : ℕ∞) :
    HasTranscendenceDegreeAt B S hS (f ≫ g) x r ↔
      HasTranscendenceDegreeAt B S hS g (pointsMap B S hS X f x) r := by
  obtain ⟨W, w, hwSurj, hwEtale⟩ := hZ.exists_atlas
  obtain ⟨V, b, β, hbg, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W w hwSurj hwEtale
  obtain ⟨U, a, α, hfa, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨ξ, hξ⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨u, hu⟩ := (pointsEquivScheme B S hS U).symm.surjective ξ
  have huξ : pointsToScheme B S hS U ξ = u := by
    rw [← hu]
    exact (pointsEquivScheme B S hS U).apply_symm_apply u
  have hcommComp : yoneda.map (α ≫ β) ≫ w = a ≫ f ≫ g := by
    rw [Functor.map_comp, Category.assoc, ← hbg, ← Category.assoc, ← hfa, Category.assoc]
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
  rw [hv, hx,
    hasTranscendenceDegreeAt_pointsMap_iff B S hS r (f ≫ g) U W a w (α ≫ β) haEtale hwEtale
      hcommComp u,
    hasTranscendenceDegreeAt_pointsMap_iff B S hS r g V W b w β hbEtale hwEtale hbg.symm
      ((BigFppfOver.toScheme B S hS).map α u)]
  obtain ⟨_, _⟩ := hf U V a b α haEtale hbEtale hfa.symm
  rw [toENat_trdeg_residueField_comp_of_locallyQuasiFinite ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) ((BigFppfOver.toScheme B S hS).map (α ≫ β))
    ((BigFppfOver.toScheme B S hS).map_comp α β) u]

end Space

end AlgebraicGeometry

end
