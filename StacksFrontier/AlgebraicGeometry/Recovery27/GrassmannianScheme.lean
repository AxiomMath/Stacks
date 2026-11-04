module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Recovery27.Representable

/-!
# Grassmannians

The Grassmannian `G(k, n)` over the integers is the scheme representing the Grassmannian
functor, which sends a scheme `S` to the isomorphism classes of finite locally free rank-`n - k`
quotients of the free module of rank `n` on `S`. The Grassmannian over a scheme `S`, and the
Grassmannian over a commutative ring `R`, are its base changes along the unique morphisms
`S ⟶ Spec ℤ` and `Spec R ⟶ Spec ℤ`.

## Main definitions

* `AlgebraicGeometry.Grassmannian.scheme`: the Grassmannian `G(k, n)` over the integers.
* `AlgebraicGeometry.Grassmannian.schemeOver`: the Grassmannian `G(k, n)_S` over a scheme `S`.
* `AlgebraicGeometry.Grassmannian.schemeOverRing`: the Grassmannian `G(k, n)_R` over a ring `R`.

## Main results

* `AlgebraicGeometry.Grassmannian.schemeRepresentableBy`: the Grassmannian represents the
  Grassmannian functor.
* `AlgebraicGeometry.Grassmannian.schemeOver_isPullback`: the Grassmannian over `S` is the
  fibre product of `S` and the integral Grassmannian over `Spec ℤ`.

## Implementation notes

`G(k, n)` is the explicit scheme glued from the coordinate charts,
`AlgebraicGeometry.Grassmannian.gluedScheme`, defined for all `k` and `n`; its universal property
is `AlgebraicGeometry.Grassmannian.schemeRepresentableBy`.

Since `Spec ℤ` is the terminal scheme, base change from the integers is a fibre product over
the terminal object, exactly as for projective space in
`AlgebraicGeometry.projectiveSpaceOver`; the structure morphism of `G(k, n)_S` is the first
projection, recorded as a `CanonicallyOver` instance.

## References

* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Grassmannian

universe u

/-- The Grassmannian `G(k, n)` over the integers: the scheme representing the functor of finite
locally free rank-`n - k` quotients of the free module of rank `n`. -/
@[stacks 089U "the Grassmannian over ℤ", sga "6 VI 4.9" "special case"]
public def scheme (k n : ℕ) : Scheme.{u} :=
  gluedScheme.{u} k n

/-- The Grassmannian represents the Grassmannian functor: a morphism from a scheme `S` to
`G(k, n)` is the same datum as an isomorphism class of finite locally free rank-`n - k`
quotients of the free module of rank `n` on `S`. -/
@[sga "6 VI 4.9" "G^(n, special case", sga "7 XIX 1.4" "partial"]
public def schemeRepresentableBy (k n : ℕ) :
    (functor.{u} k n).RepresentableBy (scheme.{u} k n) :=
  representableBy k n

/-- The Grassmannian `G(k, n)_S` over a scheme `S`: the base change of the integral Grassmannian
along the unique morphism `S ⟶ Spec ℤ`. -/
@[stacks 089U "the Grassmannian over a scheme", sga "6 VI 4.9", sga "7 XIX 1.4" "partial"]
public abbrev schemeOver (k n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (scheme.{u} k n))

/-- The Grassmannian over `S` is a scheme over `S` by the first projection. -/
public instance schemeOver.over (k n : ℕ) (S : Scheme.{u}) :
    (schemeOver k n S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The projection of `G(k, n)_S` onto the integral Grassmannian. -/
public abbrev schemeOver.toIntegral (k n : ℕ) (S : Scheme.{u}) :
    schemeOver k n S ⟶ scheme.{u} k n :=
  pullback.snd _ _

/-- The Grassmannian over `S` is the fibre product of `S` and the integral Grassmannian over
the terminal scheme `Spec ℤ`. -/
public theorem schemeOver_isPullback (k n : ℕ) (S : Scheme.{u}) :
    IsPullback (schemeOver.over k n S).hom (schemeOver.toIntegral k n S)
      (terminal.from S) (terminal.from (scheme.{u} k n)) :=
  IsPullback.of_hasPullback _ _

/-- The Grassmannian `G(k, n)_R` over a commutative ring `R`: the base change of the integral
Grassmannian to `Spec R`. -/
@[stacks 089U "the Grassmannian over a ring",
  sga "6 VI 4.9" "G_S^(n, special case",
  sga "7 XIX 1.4" "partial"]
public abbrev schemeOverRing (k n : ℕ) (R : CommRingCat.{u}) : Scheme.{u} :=
  schemeOver k n (Spec R)

/-- The coordinate chart of `G(k, n)` attached to an embedding `ι : Fin (n - k) ↪ Fin n`: the
affine space over `Spec ℤ` on the `k(n - k)` chart coordinates, mapped into `G(k, n)` by an open
immersion. -/
public noncomputable def chart (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))) ⟶ scheme.{u} k n :=
  chartMap k n ι

/-- Each coordinate chart is an open immersion. -/
public instance isOpenImmersion_chart (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    IsOpenImmersion (chart.{u} k n ι) :=
  isOpenImmersion_chartMap k n ι

/-- The coordinate charts cover `G(k, n)`. -/
public theorem exists_mem_range_chart (k n : ℕ) (x : scheme.{u} k n) :
    ∃ ι : Fin (n - k) ↪ Fin n, x ∈ Set.range (chart.{u} k n ι) :=
  exists_mem_range_chartMap k n x

/-- **Two charts that agree on a scheme classify isomorphic quotients.** If
`g ≫ chart ι = h ≫ chart κ`, the two quotients `𝒪_T^n ⟶ 𝒪_T^{n - k}` differ by an automorphism
of `𝒪_T^{n - k}`. -/
public theorem exists_iso_chartQuotientMap_comp_eq {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hgh : g ≫ chart k n ι = h ≫ chart k n κ) :
    ∃ e : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (n - k))) ≅
        SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (n - k))),
      chartQuotientMap k n ι g ≫ e.hom = chartQuotientMap k n κ h :=
  exists_iso_chartQuotientMap_comp_eq_of_chartMap g h hgh

/-- **A point of the chart attached to `κ` lies in the chart attached to `ι` as soon as its
quotient restricted to the coordinates `ι` is an isomorphism.** -/
public theorem exists_comp_chart_eq_of_isIso {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hiso : IsIso (SheafOfModules.freeMap (R := T.ringCatSheaf)
      (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down)) ≫ chartQuotientMap k n κ h)) :
    ∃ g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))),
      g ≫ chart k n ι = h ≫ chart k n κ :=
  exists_comp_chartMap_eq_of_isIso h hiso

end AlgebraicGeometry.Grassmannian

end
