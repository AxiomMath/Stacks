module

import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.LocalProperties.Reduced

public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Flat.ReducedFibres
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# A smooth algebra over a reduced ring is reduced

Proof of `Algebra.isReduced_of_smooth` (Stacks 033B): if `R → S` is a smooth ring map and `R` is
reduced, then `S` is reduced.

The argument is the source's. A smooth ring map is flat with regular, hence reduced, fibres, so
over a Noetherian base reducedness ascends by Lemma 0C21. The general case is a limit argument:
`S` is the base change of a smooth algebra `S₀` over a finitely generated `𝐙`-subalgebra
`R₀ ⊆ R`, and every element of `R ⊗_{R₀} S₀` already lives in `R₁ ⊗_{R₀} S₀` for a subalgebra
`R₁ ⊆ R` finitely generated over `R₀`. Such an `R₁` is a finitely generated `𝐙`-algebra, hence
Noetherian, and is reduced as a subring of `R`, so `R₁ ⊗_{R₀} S₀` is reduced by the Noetherian
case; the transition from the finitely generated subalgebras to `R` is flatness of `S₀` over `R₀`.

Reducedness of the fibres is where the regularity of the fibres of a smooth ring map enters. A
fibre `κ(𝔭) ⊗_R S` is a smooth algebra over the field `κ(𝔭)`, and a smooth algebra over a field is
even geometrically reduced: after base change to the algebraic closure the base field may be
assumed perfect, and then the residue field at every prime is a separable extension of it
(Definition 030O (2)), so smoothness at that prime is regularity of the local ring by Lemma 00TV,
and a regular local ring is a domain by Lemma 00NP. Reducedness is a local property, so this
suffices.

## Main results

* `Stacks.Smooth.ReducedBase.solution`: the statement of Stacks Tag 033B.

## Implementation notes

The limit argument is Mathlib's: `Algebra.Smooth.exists_subalgebra_fg` produces the pair
`R₀ ⊆ R`, `S₀` with `S ≃ₐ[R] R ⊗_{R₀} S₀` (the source's remark (10) of Section 00TZ), and
`IsReduced.tensorProduct_of_flat_of_forall_fg` performs the passage to the limit, so that no
element of `S` has to be moved into a subalgebra by hand. Its shape puts the flat factor on the
left, so the tensor factors are transposed by `Algebra.TensorProduct.comm`.

The steps stated separately here are the ones that are not about the ring map of the statement, and none
of them is in Mathlib. `isRegularLocalRing_of_smooth_of_perfectField` carries the local content of
the proof; it is stated for an arbitrary model of the localization, as Lemma 00TV is, and at an
arbitrary prime rather than only at the maximal ideals used below. Smoothness at the prime is read
off from formal smoothness of the localization, which is formal smoothness of `A` over `k` composed
with that of `A_𝔭` over `A`, rather than from the smooth locus.
`Algebra.isSeparableExtension_of_perfectField` says that every extension of a perfect field is
separable in
the sense of Definition 030O (2), which for a field extension of finite type is Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`. Over a field the conclusion is
stated as geometric reducedness (`Algebra.IsGeometricallyReduced`, Mathlib's form of the notion of
Section 05DS), since that is what base change to the algebraic closure proves and reducedness of
the fibres follows from it by `Algebra.isReduced_of_isGeometricallyReduced`. Finally
`isReduced_of_smooth_of_isNoetherianRing` is the Noetherian case of the statement and
`isReduced_tensorProduct_of_smooth_of_fg` its finitely generated stage, stated in the form that is
the hypothesis of `IsReduced.tensorProduct_of_flat_of_forall_fg`.

## References

* [StacksProject 033B](https://stacks.math.columbia.edu/tag/033B)
* [StacksProject 0C21](https://stacks.math.columbia.edu/tag/0C21)
* [StacksProject 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [StacksProject 00NP](https://stacks.math.columbia.edu/tag/00NP)
* [StacksProject 030O](https://stacks.math.columbia.edu/tag/030O)
* [StacksProject 05DS](https://stacks.math.columbia.edu/tag/05DS)

## Tags

reduced ring, geometrically reduced, smooth ring map, smooth algebra, regular local ring,
separable extension, ascent
-/

@[expose] public section

open TensorProduct

namespace Stacks.Smooth.ReducedBase

/-- **A smooth algebra over a perfect field is regular.** Every model `Ap` of the localization of a
smooth algebra `A` over a perfect field `k` at a prime `p` is a regular local ring: the residue
field `κ(p)` is a separable extension of `k`, so smoothness of `A` at `p` is regularity of `A_p` by
Lemma 00TV. -/
@[ega "IV 17.15.1" "special case",
  ega "IV 17.15.9" "b ⇒ a",
  sga "1 II 5.10" "smooth implies regular"]
private lemma isRegularLocalRing_of_smooth_of_perfectField {k A : Type*} [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (p : Ideal A) [p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p] :
    IsRegularLocalRing Ap := by
  have : Algebra.IsSeparableExtension k p.ResidueField :=
    Algebra.isSeparableExtension_of_perfectField k p.ResidueField
  refine (Algebra.isSmoothAt_iff_isRegularLocalRing (k := k) p Ap).mp ?_
  have : Algebra.FormallySmooth A (Localization.AtPrime p) := .of_isLocalization p.primeCompl
  exact .comp k A (Localization.AtPrime p)

/-- A smooth algebra over a perfect field is reduced: it is regular at every maximal ideal, and a
regular local ring is a domain by Lemma 00NP. -/
private lemma isReduced_of_smooth_of_perfectField (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] : IsReduced A :=
  isReduced_ofLocalizationMaximal A fun J hJ =>
    have := hJ.isPrime
    have := isRegularLocalRing_of_smooth_of_perfectField (k := k) J (Localization.AtPrime J)
    have := IsRegularLocalRing.isDomain (Localization.AtPrime J)
    inferInstance

/-- **A smooth algebra over a field is geometrically reduced.** Its base change to the algebraic
closure of the base field is smooth over a perfect field, hence reduced. -/
private lemma isGeometricallyReduced_of_smooth (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : Algebra.IsGeometricallyReduced k A :=
  (Algebra.isGeometricallyReduced_field_iff k A).mpr
    (isReduced_of_smooth_of_perfectField (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))

/-- The Noetherian case of Stacks 033B: a smooth algebra over a reduced Noetherian ring is reduced.
The fibres are smooth over a field, hence reduced, and reducedness ascends along a flat ring map of
Noetherian rings with reduced fibres (Lemma 0C21). -/
private lemma isReduced_of_smooth_of_isNoetherianRing (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsReduced R] [Algebra.Smooth R S] : IsReduced S :=
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  isReduced_of_flat_of_isReduced_fiber (R := R) (S := S) fun p _ =>
    have := isGeometricallyReduced_of_smooth p.ResidueField (p.Fiber S)
    Algebra.isReduced_of_isGeometricallyReduced p.ResidueField

/-- The finitely generated stage of the limit argument. Let `R` be a reduced `R₀`-algebra with `R₀`
of finite type over `𝐙`, and let `S₀` be a smooth `R₀`-algebra. Then `S₀ ⊗_{R₀} B` is reduced for
every finitely generated `R₀`-subalgebra `B ⊆ R`: such a `B` is of finite type over `𝐙`, hence
Noetherian, and is reduced as a subring of `R`, so the Noetherian case applies. -/
private lemma isReduced_tensorProduct_of_smooth_of_fg {R₀ R S₀ : Type*} [CommRing R₀] [CommRing R]
    [CommRing S₀] [Algebra R₀ R] [Algebra R₀ S₀] [Algebra.FiniteType ℤ R₀] [IsReduced R]
    [Algebra.Smooth R₀ S₀] (B : Subalgebra R₀ R) (hB : B.FG) : IsReduced (S₀ ⊗[R₀] B) :=
  have : Algebra.FiniteType ℤ B := ‹Algebra.FiniteType ℤ R₀›.trans ⟨B.fg_top.mpr hB⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : IsReduced (B ⊗[R₀] S₀) := isReduced_of_smooth_of_isNoetherianRing B (B ⊗[R₀] S₀)
  isReduced_of_injective (Algebra.TensorProduct.comm R₀ S₀ B) (AlgEquiv.injective _)

/-- A smooth algebra over a reduced ring is reduced: `S ≃ₐ[R] R ⊗_{R₀} S₀` with `R₀` of finite
type over `𝐙` and `S₀` smooth over `R₀`, and reducedness passes from the tensor products over the
finitely generated `R₀`-subalgebras of `R` to `R ⊗_{R₀} S₀` by flatness of `S₀`. -/
public theorem solution (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsReduced R] : IsReduced S := by
  obtain ⟨R₀, S₀, _, _, hR₀, _, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R S
  have : Algebra.FiniteType ℤ R₀ := ⟨R₀.fg_top.mpr hR₀⟩
  have : IsReduced (S₀ ⊗[R₀] R) :=
    IsReduced.tensorProduct_of_flat_of_forall_fg
      (isReduced_tensorProduct_of_smooth_of_fg (S₀ := S₀))
  exact isReduced_of_injective
    (e.toRingEquiv.trans (Algebra.TensorProduct.comm R₀ R S₀).toRingEquiv) (RingEquiv.injective _)

end Stacks.Smooth.ReducedBase

end

/-!
# A smooth algebra over a reduced ring is reduced

Let `φ : R → S` be a smooth ring map. If `R` is reduced, then so is `S`. Reducedness of a
commutative ring is Mathlib's `IsReduced`: the only nilpotent element is `0`.

The source's proof. A smooth ring map is flat with regular, in particular reduced, fibres. When
`R` is Noetherian so is `S`, and reducedness then ascends along a flat map with reduced fibres
(Lemma 0C21). In general one writes `S ≅ R ⊗_{R₀} S₀` for a finitely generated `𝐙`-subalgebra
`R₀ ⊆ R` and a smooth ring map `R₀ → S₀`; an element `x ∈ S` with `x² = 0` comes, after
enlarging `R₀`, from an `x₀ ∈ S₀` with `x₀² = 0`, and `S₀` is reduced by the Noetherian case
because `R₀ ⊆ R` is reduced, whence `x₀ = 0` and `x = 0`.

## Main results

* `Algebra.isReduced_of_smooth`: a smooth algebra over a reduced commutative ring is reduced.

## Implementation notes

The ring map is an `Algebra R S` instance, so `φ` is `algebraMap R S` and smoothness of `φ` is
`Algebra.Smooth R S`, that is `Algebra.FormallySmooth R S` together with
`Algebra.FinitePresentation R S`; `RingHom.smooth_algebraMap` identifies this with
`(algebraMap R S).Smooth`, the predicate on the bare ring map. Both hypotheses are instance
arguments, as in the companion Stacks Tag 0C21, so the lemma applies by `inferInstance` wherever the
smooth structure is already registered. `R` and `S` are explicit, as in the Mathlib sibling
`Algebra.isReduced_of_isGeometricallyReduced`, since neither instance argument determines `R`
from the conclusion.

No Noetherian hypothesis is imposed. This is the whole difference between this lemma and the
Noetherian ascent 0C21, and it is what the source's limit argument buys; Mathlib's nearest
statements, `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`
and `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`,
both carry a finiteness hypothesis on the base (locally Noetherian, respectively finitely many
irreducible components), so neither covers a base such as
`R = k[x₁, x₂, …]/(xᵢxⱼ : i ≠ j)`, which is reduced with infinitely many minimal primes.

Faithfulness to [StacksProject 033B]:

1. No dead hypothesis. Smoothness is used: `k → k[x]/(x²)` is of finite presentation with `k`
   reduced, and its target is not reduced, so it is not formally smooth. Reducedness of `R` is
   used: `Algebra.Smooth R R` holds for every `R`, so the identity map of `R = k[x]/(x²)` is
   smooth with non-reduced target.
2. The scalars and base are the source's. Smoothness is that of `S` as an `R`-algebra along
   `algebraMap R S` itself, with no localization of `R` interposed and no extension of the
   residue fields; the conclusion is reducedness of `S` as a ring, which is base-free.
3. The map the source names is pinned, not merely assumed to exist: `φ` is `algebraMap R S` of
   the `Algebra R S` instance, and `Algebra.Smooth R S` is smoothness of that very map.
4. The instantiation is not degenerate. `R = ℚ[t]`, `S = ℚ[t][x]` satisfies the hypotheses, the
   polynomial algebra being smooth (`Algebra.FormallySmooth.polynomial` and
   `Algebra.FinitePresentation`) and `R` reduced, and its conclusion is the reducedness of
   `ℚ[t, x]`. Content beyond the Noetherian case is a base as in the implementation note.

## References

* [StacksProject 033B](https://stacks.math.columbia.edu/tag/033B)
* [StacksProject 0C21](https://stacks.math.columbia.edu/tag/0C21)

## Tags

reduced ring, smooth ring map, smooth algebra, ascent
-/

@[expose] public section

/-- **Stacks Tag 033B.** Let `R → S` be a smooth ring map. If `R` is reduced, then `S` is
reduced. -/
@[stacks 033B "The ring map is an `Algebra R S` instance and smoothness of it is Mathlib's \
  `Algebra.Smooth R S` (equivalently `(algebraMap R S).Smooth`, by `RingHom.smooth_algebraMap`); \
  reducedness is `IsReduced`. No Noetherian hypothesis, so this is not an instance of Mathlib's \
  `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`. \
  See the module docstring.", sga "1 II 3.1" "reduced, O_y ⇒ O_x"]
public theorem Algebra.isReduced_of_smooth (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsReduced R] : IsReduced S :=
  Stacks.Smooth.ReducedBase.solution R S

end
