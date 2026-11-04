module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.RingTheory.Dualizing.GorensteinRegularElement
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# An effective Cartier divisor on a Gorenstein scheme is Gorenstein

Let `X` be a Gorenstein scheme and `D ⊆ X` an effective Cartier divisor. Then the closed
subscheme `D` is again a Gorenstein scheme. This is the scheme-theoretic form of
[Stacks, Tag 0BJJ](https://stacks.math.columbia.edu/tag/0BJJ), which says that quotienting a
Noetherian local ring by a nonzerodivisor in its maximal ideal preserves Gorensteinness.

## Main results

* `Stacks.Divisors.isGorenstein_subscheme_of_isEffectiveCartierDivisor` — the closed subscheme
  underlying an effective Cartier divisor on a Gorenstein scheme is Gorenstein.
* `Stacks.Divisors.isGorenstein_subscheme_of_isRegular_of_isEffectiveCartierDivisor` — the same
  for a regular ambient scheme.

## Implementation notes

The whole content is the identification of a local ring of `D` as a quotient of a local ring of
`X` by one nonzerodivisor. Three results assemble it at a point `y` of `D` lying over
`x : X`:

* `Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor` produces an
  affine open `U ∋ x` and a nonzerodivisor `f ∈ Γ(X, U)` generating the ideal of `D` there, and
  `AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ` turns that into `ℐ_{D, x} = (g)` for the
  germ `g` of `f`, which is a nonzerodivisor by `Stacks.Divisors.germ_mem_nonZeroDivisors`.
* `g` lies in the maximal ideal because `x` lies in the support of `ℐ_D`, being in the range of
  the closed immersion; that is `Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support`.
* `AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion` identifies `ℐ_{D, x}` with
  the kernel of the stalk map of the closed immersion, which is surjective, so
  `RingHom.quotientKerEquivOfSurjective` exhibits `𝒪_{D, y}` as `𝒪_{X, x} / (g)`.

Gorensteinness is then transported across that isomorphism by
`Dualizing.isGorensteinLocalRing_of_ringEquiv`. The `Nontrivial`, `IsLocalRing` and
`IsNoetherianRing` structures on the quotient are introduced exactly as Tag 0BJJ states them;
they are propositions, so no coherence with the ones in that statement has to be arranged.

Local Noetherianity of `D` is not an extra hypothesis: a closed immersion is locally of finite
type, so it follows from local Noetherianity of `X` by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0BJJ](https://stacks.math.columbia.edu/tag/0BJJ)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **The closed subscheme cut out by an effective Cartier divisor on a Gorenstein scheme is
Gorenstein.** -/
@[stacks 0BJJ "scheme-theoretic form: an effective Cartier divisor on a Gorenstein scheme"]
public theorem isGorenstein_subscheme_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [AlgebraicGeometry.IsGorenstein X] (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) :
    AlgebraicGeometry.IsGorenstein D.subscheme := by
  have hN : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  refine { toIsLocallyNoetherian := hN, isGorensteinLocalRing := fun y => ?_ }
  obtain ⟨U, hU, hxU, f, hf, hspan⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD (D.subschemeι y)
  set x := D.subschemeι y with hx
  set g : X.presheaf.stalk x := (X.presheaf.germ U x hxU).hom f with hg
  have hstalk : IdealSheafData.stalk D x = Ideal.span {g} := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ D x ⟨U, hU⟩ hxU, hspan, Ideal.map_span,
      Set.image_singleton]
  have hgnzd : g ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    germ_mem_nonZeroDivisors hU hf x hxU
  have hxsupp : x ∈ D.support := by
    have : x ∈ Set.range D.subschemeι.base := ⟨y, rfl⟩
    rwa [D.range_subschemeι] at this
  have hgmax : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (stalk_le_maximalIdeal_iff_mem_support D x).mpr hxsupp
      (hstalk ▸ Ideal.mem_span_singleton_self g)
  let : Nontrivial (X.presheaf.stalk x ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hgmax))
        (inferInstance :
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsMaximal).lt_top).ne
  let : IsLocalRing (X.presheaf.stalk x ⧸ Ideal.span {g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {g}))
      Ideal.Quotient.mk_surjective
  have hQuot : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x ⧸ Ideal.span {g}) :=
    (Dualizing.isGorensteinLocalRing_quotient_span_singleton_iff
      (X.presheaf.stalk x) g hgmax hgnzd).mp
      (AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing x)
  have hker : RingHom.ker (D.subschemeι.stalkMap y).hom = Ideal.span {g} := by
    have h := (IdealSheafData.stalk_ker_of_isClosedImmersion D.subschemeι y).symm
    rw [D.ker_subschemeι] at h
    exact h.trans hstalk
  let : IsLocallyNoetherian D.subscheme := hN
  refine Dualizing.isGorensteinLocalRing_of_ringEquiv
    (((RingHom.quotientKerEquivOfSurjective
      (f := (D.subschemeι.stalkMap y).hom)
      (D.subschemeι.stalkMap_surjective y)).symm.trans
        (Ideal.quotEquivOfEq hker))) hQuot

/-- **An effective Cartier divisor on a regular scheme is Gorenstein.** -/
public theorem isGorenstein_subscheme_of_isRegular_of_isEffectiveCartierDivisor
    {X : Scheme.{u}} (D : X.IdealSheafData) (hX : IsRegular X)
    (hD : IsEffectiveCartierDivisor D) :
    AlgebraicGeometry.IsGorenstein D.subscheme :=
  let : AlgebraicGeometry.IsGorenstein X := isGorenstein_of_isRegular X hX
  isGorenstein_subscheme_of_isEffectiveCartierDivisor D hD

end Stacks.Divisors

end
