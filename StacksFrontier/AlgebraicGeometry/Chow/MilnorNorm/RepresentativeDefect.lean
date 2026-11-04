module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FiltrationProduct
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.TopDegreeReduction

/-!
# The multiplicative defect of low-degree representatives dies against the uniformizer

Let `k` be a field, let `φ ∈ k[X]` be of degree `e + 1`, and let `f, g, h` be nonzero polynomials
of degree at most `e` with `φ ∣ f g - h`. The symbols `{f}, {g}, {h}` of
`K^M_*(RatFunc k)` then satisfy

`({f} + {g} - {h}) {φ} ∈ L_e`

(`Stacks.Chow.milnorKSymbol_representativeDefect_mul_mem`). This is the one computation the
construction of the inverse of the residue map rests on: it says that the failure of
`Stacks.Chow.polyRep` to be multiplicative — the only obstruction to lifting the relations of
`κ = k[X] ⧸ φ` to `k[X]` — is invisible after multiplying by the uniformizer and reducing modulo
`L_e`.

## The computation

Write `F = f g` and `G = h`, so `{F} = {f} + {g}` and `F - G = φ q`. If `q = 0` then `F = G` and
there is nothing to prove. Otherwise `G / F + φ q / F = 1`, so the Steinberg relation of
`RatFunc k` gives `({G} - {F})({φ} + {q} - {F}) = 0`, that is

`({F} - {G}) {φ} = {G} {q} - {G} {F} - {F} {q} - {F} {-1}`,

using `{F}{F} = -{F}{-1}`. Every symbol on the right is of a polynomial of degree at most `e`:
`f`, `g` and `h` by hypothesis, `-1` because it is a constant, and `q` because

`deg φ + deg q = deg (F - G) ≤ max (deg f + deg g) (deg h) ≤ 2 e`,

so `deg q ≤ e - 1`. Hence every term lies in `L_e`, which is closed under multiplication by
`Stacks.Chow.mul_mem_milnorKPolyFiltration_self`.

Note where the degree bookkeeping is used: `deg F` may be as large as `2 e`, which is why `{F}`
has to be rewritten as `{f} + {g}` rather than used as the symbol of a single polynomial, and why
`q` lands one degree below `e` rather than merely below `2 e`.

## Main results

* `Stacks.Chow.milnorKSymbol_mem_milnorKPolyFiltration` — a single low-degree symbol lies in the
  filtration.
* `Stacks.Chow.milnorKNegOne_mem_milnorKPolyFiltration` — so does `{-1}`.
* `Stacks.Chow.milnorKSymbol_representativeDefect_mul_mem` — **the computation.**

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-! ### Single symbols in the filtration -/

/-- The symbol of a nonzero polynomial of degree at most `d` lies in `L_d`. -/
theorem milnorKSymbol_mem_milnorKPolyFiltration {d : ℕ} {u : (RatFunc k)ˣ}
    (hu : u ∈ polyUnitsOfDegreeLE k d) :
    milnorKSymbol (RatFunc k) u ∈ milnorKPolyFiltration k d := by
  rw [← milnorKSymbolProd_singleton (k := RatFunc k) u]
  exact milnorKSymbolProd_mem_milnorKPolyFiltration (by
    intro v hv
    rw [List.mem_singleton.mp hv]
    exact hu)

/-- `{-1}` lies in every step of the filtration, `-1` being a constant. -/
theorem milnorKNegOne_mem_milnorKPolyFiltration (d : ℕ) :
    milnorKNegOne (RatFunc k) ∈ milnorKPolyFiltration k d := by
  rw [milnorKNegOne_eq]
  exact milnorKSymbol_mem_milnorKPolyFiltration
    (polyUnitsOfDegreeLE_mono (Nat.zero_le d)
      (polyFactorUnits_subset_polyUnitsOfDegreeLE 0 (neg_one_mem_polyFactorUnits 0)))

/-! ### The defect against the uniformizer -/

/-- **The multiplicative defect of the low-degree representatives dies against `φ`.** For `φ` of
degree `e + 1` and `f, g, h` nonzero of degree at most `e` with `φ ∣ f g - h`,

`({f} + {g} - {h}) {φ} ∈ L_e`.

This is the Steinberg relation of `RatFunc k` at `h / f g`, whose complement to one is
`φ q / f g` with `q = (f g - h) / φ` of degree at most `e - 1`. -/
theorem milnorKSymbol_representativeDefect_mul_mem {φ : Polynomial k} (hφ0 : φ ≠ 0) {e : ℕ}
    (hφd : φ.natDegree = e + 1) {f g h : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hfe : f.natDegree ≤ e) (hge : g.natDegree ≤ e) (hhe : h.natDegree ≤ e)
    (hdvd : φ ∣ f * g - h) :
    (milnorKSymbol (RatFunc k) (polyUnit hf) + milnorKSymbol (RatFunc k) (polyUnit hg) -
          milnorKSymbol (RatFunc k) (polyUnit hh)) *
        milnorKSymbol (RatFunc k) (polyUnit hφ0) ∈
      milnorKPolyFiltration k e := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hsum : milnorKSymbol (RatFunc k) (polyUnit hf) + milnorKSymbol (RatFunc k) (polyUnit hg) =
      milnorKSymbol (RatFunc k) (polyUnit hfg) :=
    (milnorKSymbol_polyUnit_mul hf hg hfg).symm
  rw [hsum]
  obtain ⟨q, hq⟩ := hdvd
  by_cases hq0 : q = 0
  · have heq : f * g = h := sub_eq_zero.mp (by rw [hq, hq0, mul_zero])
    have hunit : polyUnit hfg = polyUnit hh := Units.ext (by rw [coe_polyUnit, coe_polyUnit, heq])
    rw [hunit, sub_self, zero_mul]
    exact zero_mem _
  -- the quotient `q` has degree at most `e - 1`
  have hqdeg : q.natDegree ≤ e := by
    have hmul : (φ * q).natDegree = φ.natDegree + q.natDegree :=
      Polynomial.natDegree_mul hφ0 hq0
    have hle : (f * g - h).natDegree ≤ max (f * g).natDegree h.natDegree :=
      Polynomial.natDegree_sub_le _ _
    have hfgdeg : (f * g).natDegree = f.natDegree + g.natDegree :=
      Polynomial.natDegree_mul hf hg
    rw [hq, hmul, hφd] at hle
    omega
  -- the Steinberg relation at `h / f g`
  have hsteinberg : (milnorKSymbol (RatFunc k) (polyUnit hh) -
        milnorKSymbol (RatFunc k) (polyUnit hfg)) *
      (milnorKSymbol (RatFunc k) (polyUnit hφ0) + milnorKSymbol (RatFunc k) (polyUnit hq0) -
        milnorKSymbol (RatFunc k) (polyUnit hfg)) = 0 := by
    have hne : algebraMap (Polynomial k) (RatFunc k) (f * g) ≠ 0 :=
      algebraMap_polynomial_ratFunc_ne_zero hfg
    have hnum : algebraMap (Polynomial k) (RatFunc k) h +
        algebraMap (Polynomial k) (RatFunc k) φ * algebraMap (Polynomial k) (RatFunc k) q =
          algebraMap (Polynomial k) (RatFunc k) (f * g) := by
      rw [← map_mul, ← map_add]
      exact congrArg _ (by rw [← hq]; ring)
    have hval : ((polyUnit hh / polyUnit hfg : (RatFunc k)ˣ) : RatFunc k) +
        ((polyUnit hφ0 * polyUnit hq0 / polyUnit hfg : (RatFunc k)ˣ) : RatFunc k) = 1 := by
      rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, Units.val_mul, coe_polyUnit,
        coe_polyUnit, coe_polyUnit, coe_polyUnit, ← add_div, hnum, div_self hne]
    have h0 := milnorKSymbol_mul_steinberg (k := RatFunc k) hval
    rwa [milnorKSymbol_div, milnorKSymbol_div, milnorKSymbol_mul] at h0
  -- the identity the Steinberg relation yields
  have hexpand : (milnorKSymbol (RatFunc k) (polyUnit hfg) -
        milnorKSymbol (RatFunc k) (polyUnit hh)) * milnorKSymbol (RatFunc k) (polyUnit hφ0) =
      milnorKSymbol (RatFunc k) (polyUnit hh) * milnorKSymbol (RatFunc k) (polyUnit hq0) -
        milnorKSymbol (RatFunc k) (polyUnit hh) * milnorKSymbol (RatFunc k) (polyUnit hfg) -
        milnorKSymbol (RatFunc k) (polyUnit hfg) * milnorKSymbol (RatFunc k) (polyUnit hq0) +
        milnorKSymbol (RatFunc k) (polyUnit hfg) * milnorKSymbol (RatFunc k) (polyUnit hfg) -
      ((milnorKSymbol (RatFunc k) (polyUnit hh) -
          milnorKSymbol (RatFunc k) (polyUnit hfg)) *
        (milnorKSymbol (RatFunc k) (polyUnit hφ0) +
          milnorKSymbol (RatFunc k) (polyUnit hq0) -
          milnorKSymbol (RatFunc k) (polyUnit hfg))) := by
    noncomm_ring
  rw [hexpand, hsteinberg, sub_zero,
    eq_neg_of_add_eq_zero_left
      (milnorKSymbol_mul_self_add_mul_negOne (k := RatFunc k) (polyUnit hfg))]
  -- every term is a product of two symbols of polynomials of degree at most `e`
  have hmem : ∀ {p : Polynomial k} (hp : p ≠ 0), p.natDegree ≤ e →
      milnorKSymbol (RatFunc k) (polyUnit hp) ∈ milnorKPolyFiltration k e := fun hp hpe =>
    milnorKSymbol_mem_milnorKPolyFiltration (polyUnit_mem_polyUnitsOfDegreeLE hp hpe)
  have hmemfg : milnorKSymbol (RatFunc k) (polyUnit hfg) ∈ milnorKPolyFiltration k e :=
    hsum ▸ add_mem (hmem hf hfe) (hmem hg hge)
  have hmemh := hmem hh hhe
  have hmemq := hmem hq0 hqdeg
  exact add_mem
    (sub_mem (sub_mem (mul_mem_milnorKPolyFiltration_self hmemh hmemq)
      (mul_mem_milnorKPolyFiltration_self hmemh hmemfg))
      (mul_mem_milnorKPolyFiltration_self hmemfg hmemq))
    (neg_mem (mul_mem_milnorKPolyFiltration_self hmemfg
      (milnorKNegOne_mem_milnorKPolyFiltration e)))

end Stacks.Chow

end
