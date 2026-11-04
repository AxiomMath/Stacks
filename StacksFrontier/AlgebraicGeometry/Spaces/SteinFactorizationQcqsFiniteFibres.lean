module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqsSurjective
import all StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres

/-!
# Finite fibres of the Stein factorization over an affine base

Let `f : X ⟶ Y` be a universally closed and quasi-separated morphism of algebraic spaces over a
scheme `S`, and let `X ⟶ Y' ⟶ Y` be its Stein factorization (Stacks 0A19): `Y'` is the
normalization of `Y` in `X` (Stacks 0822), `π : Y' ⟶ Y` is integral (Stacks 0823) and
`f' : X ⟶ Y'` is surjective.  Assume in addition that `f` is locally of finite type and that
`Y` is affine.  Then `Y'` is an affine scheme, every fibre `π⁻¹({y}) = {y₁, …, yₙ}` is finite
and every residue field extension `κ(yᵢ)/κ(y)` is finite (Stacks 0E1C).

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_finite_fibres_normalizationInQcqs`: **Stacks 0E1C**.

## Implementation notes

The Stein factorization is the normalization `AlgebraicGeometry.Space.normalizationInQcqs` of
Stacks 0822 together with its canonical morphism
`AlgebraicGeometry.Space.toNormalizationInQcqs`; it is defined for `f` quasi-compact and
quasi-separated, and `f` is quasi-compact because it is universally closed (Stacks 04XW).

`Y` affine is expressed by an isomorphism `yoneda.obj T ≅ Y` from an object `T` of the site
whose scheme is affine.  Integrality of `π`, tested at this chart, presents `Y'` by an affine
object `T'` with an integral morphism of schemes `p : T' ⟶ T` representing `π`; fibres and
residue fields are read in these schemes, as they must be, the points of an algebraic space
carrying no residue fields.  Surjectivity of `f'` over the affine base is
`AlgebraicGeometry.Space.isSurjective_toNormalizationInQcqs_of_isAffine`.

From there the argument is the source's, at the level of schemes
(`AlgebraicGeometry.finite_preimage_singleton_of_surjective_of_locallyOfFiniteType` and
`AlgebraicGeometry.finite_residueFieldMap_of_surjective_of_locallyOfFiniteType`): a compact
surjective étale chart `U` of the quasi-compact space `X` maps onto `T'`, and `U ⟶ T` is locally
of finite type.  The fibre `U_y` is a Noetherian space mapping onto `π⁻¹({y})`, which has no
specializations (Stacks 00GT), so the fibre is finite; a point of `π⁻¹({y})` is the image of a
point closed in its fibre `U_y`, a finite type point, whose residue field is finite over `κ(y)`
(Stacks 01TA), and `κ(yᵢ)` embeds into it.

## References

* [Stacks Project, Tag 0E1C](https://stacks.math.columbia.edu/tag/0E1C)
* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E1C.**  Let `f : X ⟶ Y` be a universally closed and quasi-separated morphism of
algebraic spaces over `S` and `X ⟶ Y' ⟶ Y` its Stein factorization of Stacks 0A19, the
normalization `π : Y' ⟶ Y` of `Y` in `X`.  Assume in addition that `f` is locally of finite type
and that `Y` is affine, represented by an affine `T`.  Then `Y'` is represented by an affine
`T'`, with `π` represented by `p : T' ⟶ T`, and for every point `y` of `Y` the fibre
`π⁻¹({y})` is finite and the residue field extension `κ(y')/κ(y)` is finite for every `y'` in
it. -/
@[stacks 0E1C]
theorem exists_isAffine_finite_fibres_normalizationInQcqs {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (huc : UniversallyClosed B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hlft : IsLocallyOfFiniteType B S hS f.hom)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (eY : yoneda.obj T ⟶ Y.obj) [IsIso eY] :
    ∃ (T' : BigFppfOver B S hS) (p : T' ⟶ T)
      (e : yoneda.obj T' ⟶ (normalizationInQcqs B S hS f
        (isQuasiCompact_of_universallyClosed B S hS X.property Y.property f.hom huc) hfqs).obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') ∧ IsIso e ∧
      yoneda.map p ≫ eY = e ≫ (normalizationInQcqsHom B S hS f
        (isQuasiCompact_of_universallyClosed B S hS X.property Y.property f.hom huc) hfqs).hom ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj T,
        (((BigFppfOver.toScheme B S hS).map p) ⁻¹' {y}).Finite ∧
        ∀ y' ∈ ((BigFppfOver.toScheme B S hS).map p) ⁻¹' {y},
          (((BigFppfOver.toScheme B S hS).map p).residueFieldMap y').hom.Finite := by
  have hfqc := isQuasiCompact_of_universallyClosed B S hS X.property Y.property f.hom huc
  obtain ⟨T', p, e, hpb, hT', hpint⟩ := isIntegralHom_normalizationInQcqsHom f hfqc hfqs T hT eY
  have _ : IsIso e := hpb.isIso_fst_of_isIso
  obtain ⟨U, g, hUcpt, hgsurj, hglft⟩ :=
    exists_compact_chart_scheme_data B S hS Y.property
      (congrArg (fun m => m.hom) (toNormalizationInQcqs_comp f hfqc hfqs)) eY hT e p
      hpb.w.symm (isSurjective_toNormalizationInQcqs_of_isAffine B S hS f hfqc hfqs huc T hT eY)
      hfqc hlft
  have _ : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p) := hpint
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hUcpt
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g ≫
    (BigFppfOver.toScheme B S hS).map p) := hglft
  exact ⟨T', p, e, hT', inferInstance, hpb.w.symm, fun y =>
    ⟨finite_preimage_singleton_of_surjective_of_locallyOfFiniteType _ _ hgsurj y, fun y' _ =>
      finite_residueFieldMap_of_surjective_of_locallyOfFiniteType _ _ hgsurj y'⟩⟩

end AlgebraicGeometry.Space

end
