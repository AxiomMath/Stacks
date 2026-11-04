module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.OrderOfVanishing

/-!
# The order of vanishing of a meromorphic section as an order of vanishing in the local ring

The key formula Stacks 0AYC writes `s = f_i s_i` with `s_i` a generator of `L_{ξ_i}` and `f_i` in
the fraction field of `B_i = 𝒪_{X, ξ_i}`, and then says

`ord_{Z_i, L}(s) = ord_{B_i}(f_i)`

"by definition". On the two sides of that equation sit two different formalized notions. The left
hand side is `Stacks.Divisors.orderOfVanishingMeromorphic`, Stacks 02SF, an integer attached to a
regular meromorphic section of an invertible module and a prime divisor. The right hand side is
`Ring.ord`, the length of `B_i / (f_i)`, which Mathlib defines for a ring element — with no
locality, no domain and no dimension hypothesis
(`Mathlib/RingTheory/OrderOfVanishing/Basic.lean`), the finiteness of the length needing only
`[IsNoetherianRing]` and `[Ring.KrullDimLE 1]`.

This file is the bridge. The route is through `AlgebraicGeometry.Scheme.ord`, which Stacks 02SF
is already stated in terms of and which is by construction `Ring.ordFrac` on the stalk: the only
thing to do is to evaluate `Ring.ordFrac` on the image of a ring element, which
`Ring.ordFrac_eq_ord` does, and to split a fraction, which the multiplicativity of
`AlgebraicGeometry.Scheme.ord` does. The ring-level statement
`Stacks.Chow.ord_algebraMap_eq_ringOrd` is the function-field analogue of
`Stacks.Chow.ord_eq_ringOrd_germ`, which says the same thing for the germ of a section on an open
neighbourhood rather than for an element of the stalk.

No hypothesis is placed on `B_ξ` beyond what the ambient scheme already gives: it is Noetherian
because `X` is locally Noetherian, local because `X` is a scheme, and a domain because `X` is
integral — the last only because the function field of an integral scheme is its fraction field,
which is what makes `f_ξ` an element of `Frac(B_ξ)` at all.

## Main results

* `Stacks.Chow.ord_algebraMap_eq_ringOrd` — for `b ∈ B_ξ` nonzero, the order of vanishing of the
  rational function `b` at a codimension-one point `ξ` is `Ring.ord B_ξ b`.
* `Stacks.Chow.ord_eq_sub_ringOrd` — for `f ∈ Frac(B_ξ)` written as `b / c`, the order of
  vanishing of `f` at `ξ` is `Ring.ord B_ξ b - Ring.ord B_ξ c`.
* `Stacks.Chow.exists_ringOrd_presentation` — every element of the function field has such a
  presentation, the function field being the fraction field of the stalk.
* `Stacks.Chow.orderOfVanishingMeromorphic_eq_ringOrd` — **`ord_{Z, L}(s) = ord_{B_ξ}(f_ξ)`**
  where `s = f_ξ · s_ξ` with `s_ξ` a generator of `L_ξ` and `f_ξ` the image of an element of
  `B_ξ`.
* `Stacks.Chow.orderOfVanishingMeromorphic_eq_sub_ringOrd` — the same with `f_ξ` an arbitrary
  element of `Frac(B_ξ)`, presented as a fraction.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-! ### `Ring.ord` on the stalk and `Scheme.ord` on the function field -/

/-- A nonzero element of the stalk stays nonzero in the function field. -/
private theorem algebraMap_functionField_ne_zero {Y : Scheme.{u}} [IsIntegral Y] {ξ : Y}
    {b : Y.presheaf.stalk ξ} (hb : b ≠ 0) : algebraMap (Y.presheaf.stalk ξ) Y.functionField b ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Y.presheaf.stalk ξ) Y.functionField)).mpr hb

/-- **The order of vanishing of a rational function coming from the local ring is its
`Ring.ord`.** At a codimension-one point `ξ` of an integral, locally Noetherian scheme the
function field is the fraction field of `B_ξ = 𝒪_{X, ξ}`, and `AlgebraicGeometry.Scheme.ord` is
`Ring.ordFrac B_ξ`; on the image of a nonzero `b ∈ B_ξ` the latter is the length of `B_ξ / (b)`,
which is `Ring.ord B_ξ b`.

This is `Stacks.Chow.ord_eq_ringOrd_germ` with the section on an open neighbourhood replaced by
an element of the stalk, which is the form the key formula Stacks 0AYC uses: there the local
generator is an element of `L_{ξ}` and the ratio is an element of `B_ξ`, with no open
neighbourhood in sight. -/
theorem ord_algebraMap_eq_ringOrd {ξ : X} (hco : coheight ξ = 1)
    {b : X.presheaf.stalk ξ} (hb : b ≠ 0) {n : ℕ}
    (hn : Ring.ord (X.presheaf.stalk ξ) b = n) :
    X.ord (algebraMap (X.presheaf.stalk ξ) X.functionField b) ξ = n := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk ξ) := krullDimLE_one_stalk_of_coheight_eq_one hco
  rw [Scheme.ord_eq_iff hco (algebraMap_functionField_ne_zero hb)]
  show (Ring.ordFrac (X.presheaf.stalk ξ)) _ = _
  rw [Ring.ordFrac_eq_ord _ hb,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hb) hn]

/-- **The order of vanishing of a fraction is the difference of the `Ring.ord`s of its numerator
and denominator.** The hypothesis `hf` says that `f` is `b / c` in the function field; the
conclusion is the valuation-theoretic additivity of `Ring.ord`, read through
`AlgebraicGeometry.Scheme.ord_mul`. -/
theorem ord_eq_sub_ringOrd {ξ : X} (hco : coheight ξ = 1) {f : X.functionField}
    {b c : X.presheaf.stalk ξ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hf : algebraMap (X.presheaf.stalk ξ) X.functionField c * f =
      algebraMap (X.presheaf.stalk ξ) X.functionField b)
    {m k : ℕ} (hm : Ring.ord (X.presheaf.stalk ξ) b = m)
    (hk : Ring.ord (X.presheaf.stalk ξ) c = k) :
    X.ord f ξ = (m : ℤ) - k := by
  have hcff := algebraMap_functionField_ne_zero hc
  have hfne : f ≠ 0 := fun h => algebraMap_functionField_ne_zero hb (by rw [← hf, h, mul_zero])
  have hsum : X.ord (algebraMap (X.presheaf.stalk ξ) X.functionField c) ξ + X.ord f ξ =
      (m : ℤ) := by
    rw [← Scheme.ord_mul hcff hfne, hf, ord_algebraMap_eq_ringOrd hco hb hm]
  rw [ord_algebraMap_eq_ringOrd hco hc hk] at hsum
  omega

/-- **Every rational function is a fraction of elements of the local ring at any point**, with
the two `Ring.ord`s of numerator and denominator finite. The function field of an integral
scheme is the fraction field of each of its stalks, and the lengths are finite at a
codimension-one point because the stalk is Noetherian of dimension one. -/
theorem exists_ringOrd_presentation {ξ : X} (hco : coheight ξ = 1) {f : X.functionField}
    (hf : f ≠ 0) :
    ∃ (b c : X.presheaf.stalk ξ) (m k : ℕ), b ≠ 0 ∧ c ≠ 0 ∧
      algebraMap (X.presheaf.stalk ξ) X.functionField c * f =
        algebraMap (X.presheaf.stalk ξ) X.functionField b ∧
      Ring.ord (X.presheaf.stalk ξ) b = m ∧ Ring.ord (X.presheaf.stalk ξ) c = k := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk ξ) := krullDimLE_one_stalk_of_coheight_eq_one hco
  obtain ⟨b, c, hcmem, hbc⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk ξ) f
  have hcne : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hcmem
  have hcff := algebraMap_functionField_ne_zero hcne
  have hmul : algebraMap (X.presheaf.stalk ξ) X.functionField c * f =
      algebraMap (X.presheaf.stalk ξ) X.functionField b := by
    rw [← hbc, mul_div_cancel₀ _ hcff]
  have hbne : b ≠ 0 := by
    intro h
    exact hf (by simpa [h] using hbc.symm)
  refine ⟨b, c, (Ring.ord (X.presheaf.stalk ξ) b).toNat,
    (Ring.ord (X.presheaf.stalk ξ) c).toNat, hbne, hcne, hmul, ?_, ?_⟩
  · exact (ENat.natCast_toNat
      (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hbne))).symm
  · exact (ENat.natCast_toNat (Ring.ord_ne_top hcmem)).symm

/-! ### The order of vanishing of a meromorphic section -/

section Meromorphic

variable (X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)

/-- **`ord_{Z, L}(s) = ord_{B_ξ}(f_ξ)`, Stacks 0AYC's "by definition".** Let `Z` be a prime
divisor with generic point `ξ`, let `s_ξ` be a generator of the stalk `L_ξ` and suppose the
meromorphic section `s` is `f_ξ · s_ξ` with `f_ξ` the image in the function field of a nonzero
element `b` of `B_ξ = 𝒪_{X, ξ}`. Then the order of vanishing of `s` along `Z` in the sense of
Stacks 02SF is the order of vanishing of `b` in `B_ξ` in the sense of Stacks 02MD.

Being a generator of `L_ξ` and being a basis of it agree, by
`Stacks.Divisors.isStalkBasis_iff_span_eq_top`. -/
theorem orderOfVanishingMeromorphic_eq_ringOrd (Z : PrimeDivisor X)
    {m : L.presheaf.stalk Z.genericPoint} (hm : IsStalkBasis L Z.genericPoint m)
    {b : X.presheaf.stalk Z.genericPoint} (hb : b ≠ 0)
    (hsb : genericValue L s =
      algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b •
        toGenericStalk L Z.genericPoint m)
    {n : ℕ} (hn : Ring.ord (X.presheaf.stalk Z.genericPoint) b = n) :
    orderOfVanishingMeromorphic X L s hs Z = n :=
  (orderOfVanishingMeromorphic_eq X L s hs ⟨m, hm, hsb⟩).trans
    (ord_algebraMap_eq_ringOrd Z.coheight_genericPoint hb hn)

/-- **`ord_{Z, L}(s) = ord_{B_ξ}(f_ξ)` for `f_ξ` an arbitrary element of `Frac(B_ξ)`.** The
situation of the key formula Stacks 0AYC: the meromorphic section `s` is `f_ξ · s_ξ` with `s_ξ` a
generator of `L_ξ` and `f_ξ ∈ Frac(B_ξ)` written as `b / c`. The order of vanishing of `s` along
`Z` is then `ord_{B_ξ}(b) - ord_{B_ξ}(c)`, which is what `ord_{B_ξ}` means on a fraction.

Every `f_ξ` admits such a presentation, by `Stacks.Chow.exists_ringOrd_presentation`. -/
theorem orderOfVanishingMeromorphic_eq_sub_ringOrd (Z : PrimeDivisor X)
    {mb : L.presheaf.stalk Z.genericPoint} (hm : IsStalkBasis L Z.genericPoint mb)
    {f : X.functionField} {b c : X.presheaf.stalk Z.genericPoint} (hb : b ≠ 0) (hc : c ≠ 0)
    (hf : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField c * f =
      algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b)
    (hsf : genericValue L s = f • toGenericStalk L Z.genericPoint mb)
    {m k : ℕ} (hm' : Ring.ord (X.presheaf.stalk Z.genericPoint) b = m)
    (hk : Ring.ord (X.presheaf.stalk Z.genericPoint) c = k) :
    orderOfVanishingMeromorphic X L s hs Z = (m : ℤ) - k :=
  (orderOfVanishingMeromorphic_eq X L s hs ⟨mb, hm, hsf⟩).trans
    (ord_eq_sub_ringOrd Z.coheight_genericPoint hb hc hf hm' hk)

end Meromorphic

end Stacks.Chow

end
