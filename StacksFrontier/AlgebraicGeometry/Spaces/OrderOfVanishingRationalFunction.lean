module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# The order of vanishing of a rational function along a prime divisor

Let `S` be a scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let
`f ∈ R(X)^*` be an invertible rational function and let `Z ⊂ X` be a prime divisor with generic
point `ξ`. The *order of vanishing of `f` along `Z`* is the integer
`ord_Z(f) = length (𝒪^h_{X, ξ} / a 𝒪^h_{X, ξ}) - length (𝒪^h_{X, ξ} / b 𝒪^h_{X, ξ})`
for `a` and `b` nonzerodivisors of `𝒪^h_{X, ξ}` whose ratio `a / b` is the image of `f` in the
total ring of fractions `Q(𝒪^h_{X, ξ})` along the canonical injection of **Stacks 0ENK**. This
is **Stacks 0ENL**.

## Main definitions

* `AlgebraicGeometry.Space.ordRationalFunction` is `ord_Z(f)`, as a function of `f` and `Z`
  under the hypotheses of the source: `X` integral and locally Noetherian, and nothing else.

## Main results

* `AlgebraicGeometry.Space.ordRationalFunction_eq_length_sub_length`: the value is the
  difference of the two lengths, for *every* presentation of the image of `f` as a ratio of
  nonzerodivisors. This is at once the defining formula of the source and the independence of
  the presentation that the source gets from Algebra, Lemma 02MC.
* `AlgebraicGeometry.Space.exists_ordRationalFunction_eq_length_sub_length`: such a
  presentation exists, so the difference of lengths is an admissible description of `ord_Z(f)`
  at all.

## Implementation notes

The order of vanishing of a unit of `Q(𝒪^h_{X, ξ})` is
`AlgebraicGeometry.Space.PrimeDivisor.ord`, and the coefficient family `Z ↦ ord_Z(f)` of an
invertible rational function is `AlgebraicGeometry.Space.GenericFractionEmbedding.ord`. Both of
those carry the conclusions of Stacks 0ENK as hypotheses — the first as instance arguments on
`𝒪^h_{X, ξ}`, the second as the structure
`AlgebraicGeometry.Space.GenericFractionEmbedding` of data — whereas the source assumes only
that `X` is locally Noetherian and integral and *derives* those conclusions. This file
discharges them, by `AlgebraicGeometry.Space.genericFractionEmbedding`, so that `ord_Z(f)`
becomes a function of `f` and `Z` alone. Decency is not a further hypothesis: an integral
algebraic space is decent by Stacks 0AD4, which is `IsIntegralSpace.isDecentSpace`.

`ordRationalFunction` is kept reducible, as an `abbrev`, so that it *is* the composite
`GenericFractionEmbedding.ord` of the canonical data rather than a second notion with the same
value: the results already proved about the latter — its additivity in `f`, which is Stacks
0ENQ, the principal Weil divisors and the Weil divisor class group — apply to it directly, with
no bridging lemma, on taking the embedding to be
`AlgebraicGeometry.Space.genericFractionEmbedding`.

The length of `𝒪^h_{X, ξ} / a 𝒪^h_{X, ξ}` is spelled `Ring.ord` of the ambient library, which
is by definition `Module.length R (R ⧸ Ideal.span {a})`; it is finite for a nonzerodivisor of a
Noetherian ring of dimension at most one, and `ENat.toNat` takes it to `ℕ` and then to `ℤ`.

## References

* [Stacks Project, Tag 02MC](https://stacks.math.columbia.edu/tag/02MC)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

/-- **Stacks 0ENL.** The *order of vanishing of `f` along `Z`*, for `f` an invertible rational
function on a locally Noetherian integral algebraic space `X` and `Z` a prime divisor of `X`:
the order of vanishing, along `Z`, of the image of `f` in the total ring of fractions of the
henselian local ring at the generic point of `Z` under the canonical injection of Stacks 0ENK.

The hypotheses are those of the source and no others — the conclusions of Stacks 0ENK are
discharged by `AlgebraicGeometry.Space.genericFractionEmbedding`, and decency comes from
integrality by Stacks 0AD4 — and the defining difference of lengths is
`AlgebraicGeometry.Space.ordRationalFunction_eq_length_sub_length`. -/
@[stacks 0ENL "ord_Z(f) for an invertible rational function f on a locally Noetherian integral \
  algebraic space, at the hypotheses of the source; the defining difference-of-lengths formula \
  is `AlgebraicGeometry.Space.ordRationalFunction_eq_length_sub_length`"]
abbrev ordRationalFunction (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X) : ℤ :=
  (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).ord f Z

/-- **Stacks 0ENL, the defining formula.** If the image of `f` in `Q(𝒪^h_{X, ξ})` is the ratio
`a / b` of nonzerodivisors `a` and `b` of `𝒪^h_{X, ξ}`, then `ord_Z(f)` is the difference of the
lengths of `𝒪^h_{X, ξ} / a 𝒪^h_{X, ξ}` and `𝒪^h_{X, ξ} / b 𝒪^h_{X, ξ}`.

The hypothesis is placed on an arbitrary such presentation, so this is simultaneously the
formula the source defines `ord_Z(f)` by and the independence of that formula from the choice
of `a` and `b`, which the source takes from Algebra, Lemma 02MC. -/
@[stacks 0ENL "the difference-of-lengths formula defining ord_Z(f), on an arbitrary \
  presentation of the image of f in Q(𝒪^h_{X, ξ}) as a ratio of nonzerodivisors; hence also \
  the independence of the presentation, which the source cites Algebra, Lemma 02MC for"]
theorem ordRationalFunction_eq_length_sub_length (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X)
    (a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))
    (hab : Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN
        (f : rationalFunctions B S hS hX) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)) b) :
    ordRationalFunction B S hS hX hInt hN f Z =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)
          (a : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))).toNat : ℤ) -
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)
          (b : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))).toNat : ℤ) := by
  let _ := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).nontrivial Z
  let _ := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).isNoetherianRing Z
  let _ := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).krullDimLE Z
  have hu : IsUnit (IsLocalization.mk'
      (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace)
      (a : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)) b) :=
    hab ▸ f.isUnit.map
      (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN)
  calc ordRationalFunction B S hS hX hInt hN f Z
      = Z.ord B S hS hX hInt.isDecentSpace _ hu :=
        PrimeDivisor.ord_congr B S hS hX hInt.isDecentSpace Z _ hu hab
    _ = _ := Z.ord_mk' B S hS hX hInt.isDecentSpace a b hu

/-- **Stacks 0ENL, well-definedness.** The image of an invertible rational function `f` in
`Q(𝒪^h_{X, ξ})` *is* a ratio `a / b` of nonzerodivisors of `𝒪^h_{X, ξ}`, and for one — hence,
by `AlgebraicGeometry.Space.ordRationalFunction_eq_length_sub_length`, for every — such
presentation `ord_Z(f)` is the difference of the lengths of `𝒪^h_{X, ξ} / a 𝒪^h_{X, ξ}` and
`𝒪^h_{X, ξ} / b 𝒪^h_{X, ξ}`.

The source defines `ord_Z(f)` *by* that difference, for `a` and `b` nonzerodivisors such that
the image of `f` is `a / b`, so the existence of such a pair is what makes the difference of
lengths an admissible description of `ord_Z(f)`. Invertibility of `f` is what produces it: the
image of `f` is a unit of the total ring of fractions, and the numerator of any presentation of
a unit is again a nonzerodivisor. -/
@[stacks 0ENL "existence of the presentation a/b by nonzerodivisors of the image of f in \
  Q(𝒪^h_{X, ξ}), which is what makes the difference of lengths an admissible description of \
  ord_Z(f)"]
theorem exists_ordRationalFunction_eq_length_sub_length (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X) :
    ∃ a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace),
      Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN
            (f : rationalFunctions B S hS hX) =
          IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace)
            (a : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)) b ∧
        ordRationalFunction B S hS hX hInt hN f Z =
          ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)
              (a : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))).toNat : ℤ) -
            ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)
              (b : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))).toNat : ℤ) := by
  have hx : IsUnit (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace
      hInt hN (f : rationalFunctions B S hS hX)) :=
    f.isUnit.map
      (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN)
  obtain ⟨a₀, b, hab⟩ :
      ∃ (a₀ : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace))
        (b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)),
        IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace) a₀ b =
          Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN
            (f : rationalFunctions B S hS hX) :=
    IsLocalization.exists_mk'_eq
      (nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)) _
  have hspec : IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace)
        a₀ b * algebraMap _ (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace)
        (b : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)) =
      algebraMap _ (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace) a₀ :=
    IsLocalization.mk'_spec _ a₀ b
  have hua : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)
      (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace) a₀) := by
    rw [← hspec, hab]
    exact hx.mul (IsLocalization.map_units _ b)
  refine ⟨⟨a₀, mem_nonZeroDivisors_of_injective (IsFractionRing.injective _ _)
    hua.mem_nonZeroDivisors⟩, b, hab.symm, ?_⟩
  exact ordRationalFunction_eq_length_sub_length B S hS hX hInt hN f Z _ b hab.symm

end AlgebraicGeometry.Space

end
