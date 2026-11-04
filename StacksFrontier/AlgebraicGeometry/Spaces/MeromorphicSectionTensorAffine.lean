module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTensorMultiplication
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# The product of two meromorphic sections is honest on the affine charts

Let `X` be an algebraic space over a scheme `S` satisfying the hypotheses (a) and (b) of
Stacks 0EN6, let `ℒ` and `𝒩` be quasi-coherent `𝒪_X`-modules and let `s` and `t` be meromorphic
sections of `ℒ` and of `𝒩`.  Over an *affine* étale chart the sheafification map of Stacks 0EN5
is bijective (the module analogue of Stacks 0EN6 part (2),
`AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite`), so
there `s` and `t` are honest meromorphic sections `x` and `y` before sheafification and their
chartwise product
`AlgebraicGeometry.Space.meromorphicSectionTensorMul` is a section of `𝒦_X(ℒ ⊗ 𝒩)` with no
choices made.

This file supplies the two facts that make that assignment a **matching family** on the affine
charts, which is what an amalgamation into a global meromorphic section of `ℒ ⊗ 𝒩` consumes:
over an affine chart the local representative exists, and the products attached to two charts
agree on the smaller one.

## Main results

* `AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionSheaf_of_isAffine`: over an affine
  chart a meromorphic section of a quasi-coherent module is the image of a meromorphic section
  before sheafification.
* `AlgebraicGeometry.Space.toMeromorphicSectionSheaf_meromorphicSectionTensorMul_restrict`:
  **the chartwise products of two meromorphic sections form a matching family.**  The product
  attached to a chart `V`, restricted to a chart `V'` over it, is the product attached to `V'`.
* `AlgebraicGeometry.Space.map_toMeromorphicSectionSheaf_meromorphicSectionTensorMul_eq`:
  **the products attached to two charts agree over an arbitrary common refinement**, which need
  not be affine.  This is the compatibility an amalgamation over a covering family by affine
  charts consumes.

## Implementation notes

Only the *smaller* chart has to be affine: the representatives over the larger one are
hypotheses, and affineness is used once, for the injectivity of the sheafification map over
`V'` that identifies the restriction of the representative over `V` with the representative over
`V'`.  That is what makes the statement usable on a covering family whose members are affine but
whose common refinements are not.

The agreement over an arbitrary common refinement is not a special case of the matching
property: a common refinement of two members of a covering family is not affine, and the
matching property compares the representatives over the smaller chart, where affineness is what
makes them unique.  It is obtained by refining the common refinement once more by affine charts
and descending along that covering, `𝒦_X(ℒ ⊗ 𝒩)` being separated.

An invertible `𝒪_X`-module is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertibleModule`), and the hypotheses on
`X` hold on a locally Noetherian integral algebraic space, so on the space of Stacks 0EPW
nothing here is an extra assumption.  Quasi-coherence of `ℒ ⊗ 𝒩` is *not* needed: the product is
built from the representatives of `s` and of `t`, and the sheaf `𝒦_X(ℒ ⊗ 𝒩)` is only ever
mapped into.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)

include hwa hfin in
/-- **Over an affine chart a meromorphic section is an honest meromorphic section.**  The sheaf
`𝒦_X(M)` of Stacks 0EN5 is a sheafification, so a global section of it is only locally the image
of an element of `M(V) ⊗_{𝒪_X(V)} 𝒦_X(V)`; over an affine chart it is one, by the module
analogue of Stacks 0EN6 part (2). -/
theorem exists_eval_eq_toMeromorphicSectionSheaf_of_isAffine
    (M : Modules.{u, u} B S hS X hX) (hM : M.IsQuasicoherentOnSite)
    (s : MeromorphicSection.{u, u} B S hS X hX M)
    (V : SmallEtale B S hS X) (hV : IsAffine (smallEtaleScheme B S hS X V)) :
    ∃ x : (meromorphicSectionModule B S hS X hX M).obj (op V),
      s.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V x := by
  obtain ⟨x, hx⟩ := (bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite B S hS
    ⟨X, hX⟩ M hM hwa hfin V hV).2 (s.eval (op V))
  exact ⟨x, hx.symm⟩

variable (L N : Modules.{u, u} B S hS X hX)

include hwa hfin in
/-- **The chartwise products of two meromorphic sections form a matching family.**  Let `x` and
`y` represent the meromorphic sections `s` of `ℒ` and `t` of `𝒩` over a chart `V`, and let `x'`
and `y'` represent them over a chart `V'` over `V` with affine underlying scheme.  Then the
product attached to `V`, restricted to `V'`, is the product attached to `V'`.

Restriction commutes with the sheafification map of Stacks 0EN5
(`AlgebraicGeometry.Space.toMeromorphicSectionSheaf_map`) and with the chartwise product
(`AlgebraicGeometry.Space.meromorphicSectionTensorMul_map`), so what has to be seen is that the
restriction of `x` *is* `x'`; and that is the injectivity of the sheafification map over the
affine chart `V'`, both of them representing the restriction of `s`. -/
theorem toMeromorphicSectionSheaf_meromorphicSectionTensorMul_restrict
    (hLqc : L.IsQuasicoherentOnSite) (hNqc : N.IsQuasicoherentOnSite)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (V V' : SmallEtale B S hS X) (hV' : IsAffine (smallEtaleScheme B S hS X V'))
    (k : V' ⟶ V)
    (x : (meromorphicSectionModule B S hS X hX L).obj (op V))
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V))
    (x' : (meromorphicSectionModule B S hS X hX L).obj (op V'))
    (y' : (meromorphicSectionModule B S hS X hX N).obj (op V'))
    (hx : s.eval (op V) = toMeromorphicSectionSheaf B S hS X hX L V x)
    (hy : t.eval (op V) = toMeromorphicSectionSheaf B S hS X hX N V y)
    (hx' : s.eval (op V') = toMeromorphicSectionSheaf B S hS X hX L V' x')
    (hy' : t.eval (op V') = toMeromorphicSectionSheaf B S hS X hX N V' y') :
    ((meromorphicSectionSheaf.{u, u} B S hS X hX
          (picardTensorModule B S hS hX L N)).val.map k.op).hom
        (toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V
          (meromorphicSectionTensorMul B S hS hX L N V x y)) =
      toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V'
        (meromorphicSectionTensorMul B S hS hX L N V' x' y') := by
  have key : ∀ (M : Modules.{u, u} B S hS X hX) (hM : M.IsQuasicoherentOnSite)
      (r : MeromorphicSection.{u, u} B S hS X hX M)
      (z : (meromorphicSectionModule B S hS X hX M).obj (op V))
      (z' : (meromorphicSectionModule B S hS X hX M).obj (op V')),
      r.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V z →
      r.eval (op V') = toMeromorphicSectionSheaf B S hS X hX M V' z' →
      ((meromorphicSectionModule B S hS X hX M).map k.op).hom z = z' := by
    intro M hM r z z' hz hz'
    refine (bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite B S hS ⟨X, hX⟩ M hM
      hwa hfin V' hV').1 ?_
    rw [← toMeromorphicSectionSheaf_map, ← hz, PresheafOfModules.sections_property]
    exact hz'
  have hxx := key L hLqc s x x' hx hx'
  have hyy := key N hNqc t y y' hy hy'
  rw [toMeromorphicSectionSheaf_map, meromorphicSectionTensorMul_map, hxx, hyy]

include hwa hfin in
/-- **The chartwise products attached to two charts agree over any common refinement.**  Let
`x₁, y₁` represent `s` and `t` over a chart `V₁` and `x₂, y₂` over a chart `V₂`, and let `Z` be a
chart over both.  Then the two products, restricted to `Z`, agree -- with **no** assumption on
`Z`, on `V₁` or on `V₂`, the representatives over the two being hypotheses.

This is what
`AlgebraicGeometry.Space.toMeromorphicSectionSheaf_meromorphicSectionTensorMul_restrict` does
not give: there the smaller chart has to be affine, because that is where the representatives are
compared, and a common refinement of two members of a covering family is not
affine.  The gap is closed by refining `Z` once more: `Z` is covered by affine charts
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`), over each of which both
restrictions are the product attached to that chart, and the sheaf `𝒦_X(ℒ ⊗ 𝒩)` is separated
(`AlgebraicGeometry.Space.meromorphicSectionSheaf_eq_of_cover`).

It is the compatibility an amalgamation of the products over a covering family by affine charts
consumes, `CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows` testing agreement over an
arbitrary common refinement. -/
theorem map_toMeromorphicSectionSheaf_meromorphicSectionTensorMul_eq
    (hLqc : L.IsQuasicoherentOnSite) (hNqc : N.IsQuasicoherentOnSite)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (V₁ V₂ Z : SmallEtale B S hS X) (k₁ : Z ⟶ V₁) (k₂ : Z ⟶ V₂)
    (x₁ : (meromorphicSectionModule B S hS X hX L).obj (op V₁))
    (y₁ : (meromorphicSectionModule B S hS X hX N).obj (op V₁))
    (x₂ : (meromorphicSectionModule B S hS X hX L).obj (op V₂))
    (y₂ : (meromorphicSectionModule B S hS X hX N).obj (op V₂))
    (hx₁ : s.eval (op V₁) = toMeromorphicSectionSheaf B S hS X hX L V₁ x₁)
    (hy₁ : t.eval (op V₁) = toMeromorphicSectionSheaf B S hS X hX N V₁ y₁)
    (hx₂ : s.eval (op V₂) = toMeromorphicSectionSheaf B S hS X hX L V₂ x₂)
    (hy₂ : t.eval (op V₂) = toMeromorphicSectionSheaf B S hS X hX N V₂ y₂) :
    ((meromorphicSectionSheaf.{u, u} B S hS X hX
          (picardTensorModule B S hS hX L N)).val.map k₁.op).hom
        (toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V₁
          (meromorphicSectionTensorMul B S hS hX L N V₁ x₁ y₁)) =
      ((meromorphicSectionSheaf.{u, u} B S hS X hX
            (picardTensorModule B S hS hX L N)).val.map k₂.op).hom
        (toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V₂
          (meromorphicSectionTensorMul B S hS hX L N V₂ x₂ y₂)) := by
  obtain ⟨I, Y, a, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X Z
  refine meromorphicSectionSheaf_eq_of_cover B S hS X hX (picardTensorModule B S hS hX L N) Z
    Y a hcov _ _ fun i ↦ ?_
  obtain ⟨xi, hxi⟩ := exists_eval_eq_toMeromorphicSectionSheaf_of_isAffine B S hS hX hwa hfin
    L hLqc s (Y i) (hYaff i)
  obtain ⟨yi, hyi⟩ := exists_eval_eq_toMeromorphicSectionSheaf_of_isAffine B S hS hX hwa hfin
    N hNqc t (Y i) (hYaff i)
  refine Eq.trans (PresheafOfModules.map_comp_apply _ k₁.op (a i).op _).symm ?_
  refine Eq.trans (toMeromorphicSectionSheaf_meromorphicSectionTensorMul_restrict B S hS hX
    hwa hfin L N hLqc hNqc s t V₁ (Y i) (hYaff i) (a i ≫ k₁) x₁ y₁ xi yi hx₁ hy₁ hxi hyi) ?_
  refine Eq.trans (toMeromorphicSectionSheaf_meromorphicSectionTensorMul_restrict B S hS hX
    hwa hfin L N hLqc hNqc s t V₂ (Y i) (hYaff i) (a i ≫ k₂) x₂ y₂ xi yi hx₂ hy₂ hxi hyi).symm ?_
  exact PresheafOfModules.map_comp_apply _ k₂.op (a i).op _

end AlgebraicGeometry.Space

end
