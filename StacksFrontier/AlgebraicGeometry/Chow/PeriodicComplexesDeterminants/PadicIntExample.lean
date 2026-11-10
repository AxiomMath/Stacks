module

public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.DiscreteValuationRing

/-!
# The periodic determinant of a p-adic periodic complex

Let `R = ℤ_[p]` and `M = ℤ_[p] / (p ^ l)`. Write the two differentials as multiplication by
`α = p ^ b * u` and `β = p ^ a * v` with `a + b = l` and `u, v` units of `ℤ_[p]`. The resulting
exact two-periodic complex on `M` has periodic determinant `(-1) ^ (a * b) * u ^ a / v ^ b` in
the residue field `𝔽_p`. Writing `a` and `b` as the orders of vanishing of `β` and `α` turns
this into the order-of-vanishing form
`(-1) ^ (ord α * ord β) * α ^ (ord β) / β ^ (ord α)` reduced mod `p`.

## Main results

* `AlgebraicGeometry.periodicDeterminant_padicInt_quotient` computes the periodic determinant
  of the two multiplications on `ℤ_[p] / (p ^ l)` as a unit of the residue field of `ℤ_[p]`.
* `AlgebraicGeometry.periodicDeterminant_padicInt_quotient_toZMod` is the same computation
  transported to `ZMod p` and written with the orders of vanishing of the two differentials.

## Implementation notes

This is an instance of the symbol of a discrete valuation ring, so it is deduced from
`AlgebraicGeometry.tameSymbol_eq_negOnePow_mul_residue` rather than recomputed from the
determinant maps. Two presentations of the module have to be matched up: the symbol is built
on the quotient by the range of the composite multiplication map, while the source presents
the module as `ℤ_[p] / (p ^ l)`. Those two submodules of `ℤ_[p]` are equal but not
syntactically so, so the submodule is kept as a variable in
`AlgebraicGeometry.moduleSymbol_eq_periodicDeterminant_lsmul` and substituted, which also
replaces `AlgebraicGeometry.periodicQuotientPhi` and
`AlgebraicGeometry.periodicQuotientPsi` by plain scalar multiplications on the quotient.

As for the other examples, the exactness and finite-length witnesses are produced rather than
assumed, since they hold for every prime, every pair of exponents and every pair of units. No
positivity is assumed of `a` and `b`: the degenerate case `l = 0` gives the zero module and
the determinant `1`, and the formula still holds.

In the second statement the quotient `α ^ (ord β) / β ^ (ord α)` is not an element of `ℤ_[p]`
term by term, so it is presented the way the discrete valuation ring symbol presents it: by a
unit of `ℤ_[p]` whose image in the fraction field `ℚ_[p]` is that quotient. Its reduction mod
`p` is then `PadicInt.toZMod` of that unit.

## References

* [Stacks Project, Tag 02PQ](https://stacks.math.columbia.edu/tag/02PQ)
-/

@[expose] public section

noncomputable section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- The endomorphism induced by multiplication by `x` on the quotient by `xyM` is again
multiplication by `x`. -/
private theorem periodicQuotientPhi_lsmul {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x y : A) :
    periodicQuotientPhi (LinearMap.lsmul A M x) (LinearMap.lsmul A M y)
        (range_lsmul_comp_comm x y)
      = LinearMap.lsmul A (M ⧸ LinearMap.range ((LinearMap.lsmul A M x) ∘ₗ
          (LinearMap.lsmul A M y))) x := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m => simp [periodicQuotientPhi, Submodule.mapQ_apply, Submodule.Quotient.mk_smul]

/-- The endomorphism induced by multiplication by `y` on the quotient by `xyM` is again
multiplication by `y`. -/
private theorem periodicQuotientPsi_lsmul {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x y : A) :
    periodicQuotientPsi (LinearMap.lsmul A M x) (LinearMap.lsmul A M y)
        (range_lsmul_comp_comm x y)
      = LinearMap.lsmul A (M ⧸ LinearMap.range ((LinearMap.lsmul A M x) ∘ₗ
          (LinearMap.lsmul A M y))) y := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m => simp [periodicQuotientPsi, Submodule.mapQ_apply, Submodule.Quotient.mk_smul]

/-- The symbol of `M` at `x` and `y` is the periodic determinant of the two scalar
multiplications on `M ⧸ N`, for any submodule `N` equal to the range of multiplication by
`xy`. The exactness and finite-length witnesses for that presentation are produced along with
the equality. -/
theorem moduleSymbol_eq_periodicDeterminant_lsmul
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (x y : A) (hx : IsSMulRegular M x) (hy : IsSMulRegular M y)
    (hdim : Module.supportDim A M = 1) {N : Submodule A M}
    (hN : LinearMap.range ((LinearMap.lsmul A M x) ∘ₗ (LinearMap.lsmul A M y)) = N) :
    ∃ (hφψ : Function.Exact (LinearMap.lsmul A (M ⧸ N) x) (LinearMap.lsmul A (M ⧸ N) y))
      (hψφ : Function.Exact (LinearMap.lsmul A (M ⧸ N) y) (LinearMap.lsmul A (M ⧸ N) x))
      (hM : IsFiniteLength A (M ⧸ N)),
      periodicDeterminant (LinearMap.lsmul A (M ⧸ N) x) (LinearMap.lsmul A (M ⧸ N) y)
          hφψ hψφ hM = moduleSymbol x y hx hy hdim := by
  subst hN
  have hphi := periodicQuotientPhi_lsmul (M := M) x y
  have hpsi := periodicQuotientPsi_lsmul (M := M) x y
  have hMq := isFiniteLength_quotient_mul (M := M) x y hx hy hdim
  refine ⟨?_, ?_, hMq, ?_⟩
  · rw [← hphi, ← hpsi]
    exact exact_mul_left_right (M := M) x y hy
  · rw [← hphi, ← hpsi]
    exact exact_mul_right_left (M := M) x y hx
  have hsym : moduleSymbol x y hx hy hdim =
      periodicDeterminant
        (periodicQuotientPhi (LinearMap.lsmul A M x) (LinearMap.lsmul A M y)
          (range_lsmul_comp_comm x y))
        (periodicQuotientPsi (LinearMap.lsmul A M x) (LinearMap.lsmul A M y)
          (range_lsmul_comp_comm x y))
        (exact_mul_left_right (M := M) x y hy)
        (exact_mul_right_left (M := M) x y hx) hMq := rfl
  rw [hsym]
  exact periodicDeterminant_eq_of_linearEquiv _ _ _ _ _ _ _ _
    (LinearEquiv.refl A _) (by simpa using hphi.symm) (by simpa using hpsi.symm) hMq hMq

variable (p : ℕ) [Fact p.Prime]

/-- A power of `p` times a unit is nonzero in `ℤ_[p]`. -/
private theorem padicInt_pow_mul_unit_ne_zero (b : ℕ) (u : ℤ_[p]ˣ) :
    ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ ?_) u.ne_zero
  exact_mod_cast (PadicInt.irreducible_p (p := p)).ne_zero

/-- A nonzero element of `ℤ_[p]` has nonzero image in `ℚ_[p]`. -/
private theorem padicInt_algebraMap_ne_zero {z : ℤ_[p]} (hz : z ≠ 0) :
    algebraMap ℤ_[p] ℚ_[p] z ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hz)

/-- A power of `p` times a unit is regular in `ℤ_[p]`. -/
private theorem padicInt_pow_mul_unit_isRegular (b : ℕ) (u : ℤ_[p]ˣ) :
    IsRegular ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) :=
  isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_of_ne_zero (padicInt_pow_mul_unit_ne_zero p b u))

/-- A power of `p` times a unit acts regularly on `ℤ_[p]`. -/
private theorem padicInt_pow_mul_unit_isSMulRegular (b : ℕ) (u : ℤ_[p]ˣ) :
    IsSMulRegular ℤ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) :=
  (padicInt_pow_mul_unit_isRegular p b u).isSMulRegular

/-- The support of `ℤ_[p]` as a module over itself has dimension one. -/
private theorem padicInt_supportDim_self : Module.supportDim ℤ_[p] ℤ_[p] = 1 :=
  (Module.supportDim_self_eq_ringKrullDim ℤ_[p]).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p])

/-- The range of multiplication by `(p ^ b * u) * (p ^ a * v)` on `ℤ_[p]` is the ideal
generated by `p ^ l`, for `a + b = l`: the two units are absorbed into the generator. -/
private theorem range_lsmul_padicInt (a b l : ℕ) (hl : a + b = l) (u v : ℤ_[p]ˣ) :
    LinearMap.range ((LinearMap.lsmul ℤ_[p] ℤ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p]))) ∘ₗ
        (LinearMap.lsmul ℤ_[p] ℤ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))))
      = Ideal.span {(p : ℤ_[p]) ^ l} := by
  subst hl
  have hrange : LinearMap.range
      ((LinearMap.lsmul ℤ_[p] ℤ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p]))) ∘ₗ
        (LinearMap.lsmul ℤ_[p] ℤ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))))
      = Ideal.span {((p : ℤ_[p]) ^ b * (u : ℤ_[p])) * ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))} := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply, smul_eq_mul, Ideal.mem_span_singleton]
    constructor <;> rintro ⟨w, rfl⟩ <;> exact ⟨w, by ring⟩
  have hgen : ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) * ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))
      = ((u * v : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (a + b) := by
    push_cast [pow_add]
    ring
  rw [hrange, hgen, Ideal.span_singleton_mul_left_unit (u * v).isUnit]

/-- The order of vanishing of `p ^ b * u` at the maximal ideal of `ℤ_[p]` is `b`. -/
private theorem padicInt_ord_pow_mul_unit (b : ℕ) (u : ℤ_[p]ˣ) :
    Ring.ord ℤ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) = b := by
  rw [Ring.ord_eq_addVal, mul_comm,
    IsDiscreteValuationRing.addVal_def' u PadicInt.irreducible_p b]

/-- The order of vanishing of the image of `p ^ b * u` in `ℚ_[p]` is `b`. -/
private theorem padicInt_ordInt_pow_mul_unit (b : ℕ) (u : ℤ_[p]ˣ)
    (h : algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ≠ 0) :
    ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p]))) h = (b : ℤ) := by
  rw [ordInt_algebraMap ℤ_[p] _ (padicInt_pow_mul_unit_ne_zero p b u) h]
  have hlen : Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ b * (u : ℤ_[p])})
      = Ring.ord ℤ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) := rfl
  rw [hlen, padicInt_ord_pow_mul_unit]
  simp

/-- The image of `p ^ b * u` in `ℚ_[p]` is nonzero. -/
theorem padicInt_algebraMap_pow_mul_unit_ne_zero (b : ℕ) (u : ℤ_[p]ˣ) :
    algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ≠ 0 :=
  padicInt_algebraMap_ne_zero p (padicInt_pow_mul_unit_ne_zero p b u)

/-- The unit `u ^ a / v ^ b` of `ℤ_[p]` has image `α ^ a / β ^ b` in `ℚ_[p]`, where
`α = p ^ b * u` and `β = p ^ a * v`: the two powers of `p` cancel. -/
private theorem padicInt_algebraMap_unitQuotient (a b : ℕ) (u v : ℤ_[p]ˣ) :
    algebraMap ℤ_[p] ℚ_[p] ((u ^ a / v ^ b : ℤ_[p]ˣ) : ℤ_[p]) =
      algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ^ a /
        algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p])) ^ b := by
  have hmapU : ∀ z : ℤ_[p]ˣ, algebraMap ℤ_[p] ℚ_[p] (z : ℤ_[p]) =
      ((Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom z : ℚ_[p]ˣ) : ℚ_[p]) :=
    fun z => by simp [Units.coe_map]
  have hdivmap : algebraMap ℤ_[p] ℚ_[p] ((u ^ a / v ^ b : ℤ_[p]ˣ) : ℤ_[p]) =
      (algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p])) ^ a /
        (algebraMap ℤ_[p] ℚ_[p] (v : ℤ_[p])) ^ b := by
    rw [hmapU (u ^ a / v ^ b), hmapU u, hmapU v]
    simp only [map_div, map_pow, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  have hu0 := padicInt_algebraMap_ne_zero p u.ne_zero
  have hv0 := padicInt_algebraMap_ne_zero p v.ne_zero
  have hp0 : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by
    refine padicInt_algebraMap_ne_zero p ?_
    exact_mod_cast (PadicInt.irreducible_p (p := p)).ne_zero
  rw [hdivmap, map_mul, map_mul, map_pow, map_pow]
  field_simp
  ring

/-- The symbol of `ℤ_[p]` at `p ^ b * u` and `p ^ a * v` is
`(-1) ^ (a * b) * u ^ a / v ^ b` in the residue field. -/
private theorem moduleSymbol_padicInt (a b : ℕ) (u v : ℤ_[p]ˣ) :
    moduleSymbol (M := ℤ_[p]) ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))
        (padicInt_pow_mul_unit_isSMulRegular p b u)
        (padicInt_pow_mul_unit_isSMulRegular p a v)
        (padicInt_supportDim_self p) =
      (-1) ^ (a * b) *
        Units.map (IsLocalRing.residue ℤ_[p]).toMonoidHom (u ^ a / v ^ b) := by
  classical
  have hdim : ringKrullDim ℤ_[p] = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]
  set α : ℤ_[p] := (p : ℤ_[p]) ^ b * (u : ℤ_[p]) with hα
  set β : ℤ_[p] := (p : ℤ_[p]) ^ a * (v : ℤ_[p]) with hβ
  have hαreg : IsRegular α := padicInt_pow_mul_unit_isRegular p b u
  have hβreg : IsRegular β := padicInt_pow_mul_unit_isRegular p a v
  set xU : ℚ_[p]ˣ := (IsLocalization.map_units ℚ_[p]
    (⟨α, isRegular_iff_mem_nonZeroDivisors.mp hαreg⟩ : nonZeroDivisors ℤ_[p])).unit with hxU
  set yU : ℚ_[p]ˣ := (IsLocalization.map_units ℚ_[p]
    (⟨β, isRegular_iff_mem_nonZeroDivisors.mp hβreg⟩ : nonZeroDivisors ℤ_[p])).unit with hyU
  have hxval : (xU : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] α := IsUnit.unit_spec _
  have hyval : (yU : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] β := IsUnit.unit_spec _
  have hord : ∀ (c : ℕ) (z : ℤ_[p]ˣ) (q : ℚ_[p]ˣ),
      (q : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ c * (z : ℤ_[p])) →
        ordInt ℤ_[p] (q : ℚ_[p]) q.ne_zero = (c : ℤ) := by
    intro c z q hq
    rw [show ordInt ℤ_[p] (q : ℚ_[p]) q.ne_zero
        = ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ c * (z : ℤ_[p])))
          (hq ▸ q.ne_zero) by congr 1]
    exact padicInt_ordInt_pow_mul_unit p c z _
  have hxord := hord b u xU hxval
  have hyord := hord a v yU hyval
  set w : ℤ_[p]ˣ := u ^ a / v ^ b with hw
  have hwspec : algebraMap ℤ_[p] ℚ_[p] (w : ℤ_[p]) =
      (xU : ℚ_[p]) ^ (ordInt ℤ_[p] (yU : ℚ_[p]) yU.ne_zero) /
        (yU : ℚ_[p]) ^ (ordInt ℤ_[p] (xU : ℚ_[p]) xU.ne_zero) := by
    rw [hxord, hyord, hxval, hyval, hw, zpow_natCast, zpow_natCast]
    exact padicInt_algebraMap_unitQuotient p a b u v
  have hmain := tameSymbol_eq_negOnePow_mul_residue (A := ℤ_[p]) (K := ℚ_[p]) xU yU w hwspec
  rw [hxord, hyord] at hmain
  have hsym := (tameSymbol (K := ℚ_[p]) hdim).eq_moduleSymbol α β hαreg hβreg
  apply Units.ext
  rw [← hsym]
  change ((tameSymbol (K := ℚ_[p]) hdim) xU yU : IsLocalRing.ResidueField ℤ_[p]) = _
  rw [hmain]
  have hsign : ((-1 : (IsLocalRing.ResidueField ℤ_[p])ˣ) ^ ((b : ℤ) * (a : ℤ))) =
      ((-1 : (IsLocalRing.ResidueField ℤ_[p])ˣ) ^ (a * b)) := by
    rw [mul_comm (b : ℤ) (a : ℤ), ← Nat.cast_mul, zpow_natCast]
  rw [hsign, hw]
  have hcoe : (IsLocalRing.residue ℤ_[p]) ((u ^ a / v ^ b : ℤ_[p]ˣ) : ℤ_[p]) =
      ((Units.map (IsLocalRing.residue ℤ_[p]).toMonoidHom (u ^ a / v ^ b) :
        (IsLocalRing.ResidueField ℤ_[p])ˣ) : IsLocalRing.ResidueField ℤ_[p]) := rfl
  rw [hcoe, Units.val_mul]

/-- **Stacks Project, Tag 02PQ.** Let `p` be a prime, let `a + b = l`, and let `u` and `v` be
units of `ℤ_[p]`. Multiplication by `p ^ b * u` and by `p ^ a * v` on `ℤ_[p] / (p ^ l)` is an
exact two-periodic complex of finite length, and its periodic determinant is
`(-1) ^ (a * b) * u ^ a / v ^ b` in the residue field of `ℤ_[p]`. -/
@[stacks 02PQ "the determinant of the p-adic periodic complex"]
theorem periodicDeterminant_padicInt_quotient (a b l : ℕ) (hl : a + b = l) (u v : ℤ_[p]ˣ) :
    ∃ (hφψ : Function.Exact
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))))
      (hψφ : Function.Exact
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ a * (v : ℤ_[p])))
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ b * (u : ℤ_[p]))))
      (hM : IsFiniteLength ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})),
      periodicDeterminant
          (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
            ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
          (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
            ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))) hφψ hψφ hM =
        (-1) ^ (a * b) *
          Units.map (IsLocalRing.residue ℤ_[p]).toMonoidHom (u ^ a / v ^ b) := by
  obtain ⟨hφψ, hψφ, hM, hdet⟩ :=
    moduleSymbol_eq_periodicDeterminant_lsmul (M := ℤ_[p])
      ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))
      (padicInt_pow_mul_unit_isSMulRegular p b u)
      (padicInt_pow_mul_unit_isSMulRegular p a v)
      (padicInt_supportDim_self p)
      (range_lsmul_padicInt p a b l hl u v)
  exact ⟨hφψ, hψφ, hM, hdet.trans (moduleSymbol_padicInt p a b u v)⟩

/-- **Stacks Project, Tag 02PQ.** The same determinant read in `𝔽_p = ZMod p` and written with
the orders of vanishing of the two differentials `α = p ^ b * u` and `β = p ^ a * v`: it is
`(-1) ^ (ord α * ord β)` times the reduction mod `p` of the unit `α ^ (ord β) / β ^ (ord α)`,
which is exhibited together with its defining identity in `ℚ_[p]`. -/
@[stacks 02PQ "the determinant mod p in order-of-vanishing form"]
theorem periodicDeterminant_padicInt_quotient_toZMod (a b l : ℕ) (hl : a + b = l)
    (u v : ℤ_[p]ˣ) :
    ∃ (hφψ : Function.Exact
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))))
      (hψφ : Function.Exact
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ a * (v : ℤ_[p])))
        (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
          ((p : ℤ_[p]) ^ b * (u : ℤ_[p]))))
      (hM : IsFiniteLength ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})) (w : ℤ_[p]ˣ),
      algebraMap ℤ_[p] ℚ_[p] (w : ℤ_[p]) =
          algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ^
              ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p])))
                (padicInt_algebraMap_pow_mul_unit_ne_zero p a v) /
            algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p])) ^
              ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
                (padicInt_algebraMap_pow_mul_unit_ne_zero p b u) ∧
        PadicInt.residueField
            ((periodicDeterminant
              (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
                ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
              (LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ l})
                ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))) hφψ hψφ hM :
                IsLocalRing.ResidueField ℤ_[p])) =
          (-1) ^ (ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ b * (u : ℤ_[p])))
                (padicInt_algebraMap_pow_mul_unit_ne_zero p b u) *
              ordInt ℤ_[p] (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ a * (v : ℤ_[p])))
                (padicInt_algebraMap_pow_mul_unit_ne_zero p a v)) *
            PadicInt.toZMod (w : ℤ_[p]) := by
  obtain ⟨hφψ, hψφ, hM, hdet⟩ := periodicDeterminant_padicInt_quotient p a b l hl u v
  refine ⟨hφψ, hψφ, hM, u ^ a / v ^ b, ?_, ?_⟩
  · rw [padicInt_ordInt_pow_mul_unit p b u, padicInt_ordInt_pow_mul_unit p a v,
      zpow_natCast, zpow_natCast]
    exact padicInt_algebraMap_unitQuotient p a b u v
  · have hcoe : ((Units.map (IsLocalRing.residue ℤ_[p]).toMonoidHom (u ^ a / v ^ b) :
        (IsLocalRing.ResidueField ℤ_[p])ˣ) : IsLocalRing.ResidueField ℤ_[p])
        = IsLocalRing.residue ℤ_[p] ((u ^ a / v ^ b : ℤ_[p]ˣ) : ℤ_[p]) := rfl
    rw [hdet, padicInt_ordInt_pow_mul_unit p b u, padicInt_ordInt_pow_mul_unit p a v,
      ← Nat.cast_mul, zpow_natCast, mul_comm b a,
      PadicInt.toZMod_eq_residueField_comp_residue, Units.val_mul, hcoe, map_mul,
      Units.val_pow_eq_pow_val, Units.coe_neg_one, map_pow, map_neg, map_one]
    rfl

end AlgebraicGeometry

end

end
