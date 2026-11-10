module

public import StacksFrontier.RingTheory.DeRham.LogPolesWedge
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz

/-!
# The product on the de Rham complex of log poles

Let `A → R` be a ring map and let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`, and assume the de Rham complex of log poles is defined for
`Y ⊆ X` over `S = Spec A` (Stacks Tag 0FMV).  Clause (1) of Stacks Tag 0FUP asserts that the
wedge product `Ω^p_{X/S} × Ω^q_{X/S} → Ω^{p+q}_{X/S}` extends uniquely to an `𝒪_X`-bilinear
product on `Ω^•_{X/S}(log Y)` satisfying the Leibniz rule.  The uniqueness half is proved, in the
stronger form with the Leibniz hypothesis dropped, as
`Stacks.LogPoles.logWedge_unique`; this file supplies the **existence** of the extension, by
construction.

The construction is the local one the source's proof refers to.  A form of degree `p + 1` is a
pair `(ω, η)` standing for `ω + dlog t ∧ η`, and

`(ω₁ + dlog t ∧ η₁) ∧ (ω₂ + dlog t ∧ η₂) = ω₁ ∧ ω₂ + dlog t ∧ (η₁ ∧ ω₂ + (-1)^{p+1} ω₁ ∧ η₂)`

because `dlog t ∧ dlog t = 0` and because moving the second `dlog t` to the front past `ω₁`
contributes the sign.  So the product of pairs is
`(ω₁ ∧ ω₂, η₁ ∧ ω₂ + (-1)^{p+1} ω₁ ∧ η₂)`, with three degenerate cases in which one of the two
degrees is zero and the factor is a function.

## Main definitions

* `Stacks.LogPoles.logWedgePair`, `Stacks.LogPoles.logWedgePairLeftZero` and
  `Stacks.LogPoles.logWedgePairRightZero`: the product on representing pairs, in the four
  combinations of degrees.
* `Stacks.LogPoles.logWedge`: **Stacks Tag 0FUP, clause (1), existence.** The `𝒪_X`-bilinear
  product `Ω^p_{X/S}(log Y) × Ω^q_{X/S}(log Y) → Ω^{p+q}_{X/S}(log Y)`.
* `Stacks.LogPoles.dlogForm`: `dlog t`, the pair `(0, 1)`, as a log form of degree one.

## Main results

* `Stacks.LogPoles.mem_logRel_iff_coe`: the relations of the pair model read in the exterior
  algebra, which is the form in which every computation below is done.
* `Stacks.LogPoles.logWedgePair_mem_logRel_left` and
  `Stacks.LogPoles.logWedgePair_mem_logRel_right`: the product respects the relations, so it
  descends to the quotients.  The first uses that a relation has a `dt`-free first component
  (`Stacks.LogPoles.wedgeLeft_D_fst_eq_zero_of_mem_logRel`, hence the `t`-torsion freeness of
  Tag 0FMV); the second uses that together with graded commutativity.
* `Stacks.LogPoles.logWedge_logInclR`: **the product extends the wedge product** of the forms
  with no pole — the defining property in clause (1).
* `Stacks.LogPoles.smul_smul_logWedge`: the product satisfies the computed formula
  `t² (α ∧ β) = (t α) ∧ (t β)` of `Stacks.LogPoles.smul_logWedge_eq`.
* `Stacks.LogPoles.eq_logWedge_of_logInclR`: **the product is the unique such extension**,
  obtained by discharging the hypothesis of `Stacks.LogPoles.logWedge_unique` with
  this construction.
* `Stacks.LogPoles.logWedge_dlogForm_logInclR`: `dlog t ∧ ω` is the log form presented by the
  pair `(0, ω)`, so the product does leave the forms with no pole.
* `Stacks.LogPoles.not_surjective_logInclR`: and the forms with no pole are strictly smaller, by
  `Stacks.LogPoles.not_surjective_logIncl_f_succ`.

## Implementation notes

**Scope.**  Everything here is at the ring level, as Tag 0FMW is formalized
(`Stacks.LogPoles.shortExact_logShortComplex`): `A → R` a ring map, `t ∈ R`, and the complex is a
`CochainComplex (ModuleCat A) ℕ`.  The sheaf-theoretic statement of Tag 0FMW for an arbitrary
morphism of schemes does not exist in the library — see the implementation notes of
`StacksFrontier.RingTheory.DeRham.LogPolesSequence` — so no scheme-level formulation of clause (1)
is given, and the attribute says so.

**Why the computations are done in the exterior algebra.**  The three degree indices
`(p+1)+q`, `p+(q+1)` and `(p+q)+1` are equal but not definitionally equal, since `Nat.add`
recurses on its second argument.  `⋀^n M` is a submodule of `ExteriorAlgebra R M`, so every one
of these elements is an element of one ungraded ring in which the bookkeeping disappears;
`Stacks.LogPoles.mem_logRel_iff_coe` moves the relations there, and
`exteriorPower.degCongr` carries the one genuine transport that the formula for the second
component of a product needs.  This is why there is no `HEq` and no raised heartbeat limit in
this file.

**What is not proved.**  The Leibniz rule for `Stacks.LogPoles.logWedge` is not proved, so the
existence delivered here is the existence of the `𝒪_X`-bilinear extension, not yet of a
differential graded algebra; the uniqueness statement it is matched against is the one in the
library,
which has the Leibniz hypothesis dropped and is therefore exactly what this construction
discharges.  Stating the Leibniz rule for the descended product needs a transport
`Ω^{(p+1)+q}(log Y) ≅ Ω^{(p+q)+1}(log Y)` of the quotients, and proving it needs the four degree
cases separately, because the degree-zero term of the complex is not a pair.  Clauses (2), (3)
and (4) of Tag 0FUP are not proved either.

**The ring-level graded commutativity** of the exterior algebra used here is proved in
`StacksFrontier.RingTheory.DeRham.WedgeLeibniz` as `exteriorPower.mul_comm_of_mem`.  The same
statement exists in the library as `Koszul.mul_comm_of_mem`, but it lives in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.GradedCommutativity`, downstream of this tree, so it
cannot be imported here.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP), clause (1)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), the complex
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA), its name
-/
@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### The relations, read in the exterior algebra -/

/-- The relations of the pair model, read in the exterior algebra: `(ω, η)` is a relation exactly
when `t ω + dt ∧ η = 0` as an element of `ExteriorAlgebra R (Ω[R⁄A])`. -/
theorem mem_logRel_iff_coe (t : R) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} :
    x ∈ logRel A t p ↔
      t • (x.1 : ExteriorAlgebra R (Ω[R⁄A])) +
        ExteriorAlgebra.ι R (D A R t) * (x.2 : ExteriorAlgebra R (Ω[R⁄A])) = 0 := by
  rw [mem_logRel_iff]
  rw [show (t • x.1 + exteriorPower.wedgeLeft (D A R t) p x.2 = 0) ↔
      ((t • x.1 + exteriorPower.wedgeLeft (D A R t) p x.2 :
        ⋀[R]^(p + 1) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) = 0 from
    ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Subtype.coe_injective h⟩]
  rw [Submodule.coe_add, SetLike.val_smul, exteriorPower.coe_wedgeLeft]

/-! ### The pair-model product -/

/-- The product of two forms with a logarithmic pole, on the pair model, in the case where both
degrees are positive: `(ω₁, η₁) ∧ (ω₂, η₂) = (ω₁ ∧ ω₂, η₁ ∧ ω₂ + (-1)^{p+1} ω₁ ∧ η₂)`.

This is the formula forced by `dlog t ∧ dlog t = 0` and graded commutativity:
`(ω₁ + dlog t ∧ η₁) ∧ (ω₂ + dlog t ∧ η₂)` has no `dlog t ∧ dlog t` term, and moving the `dlog t`
of the second factor to the front past `ω₁` contributes the sign. -/
def logWedgePair (A : Type u) [CommRing A] [Algebra A R] (p q : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[R]
      (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) →ₗ[R]
        (⋀[R]^(p + 1 + q + 1) (Ω[R⁄A]) × ⋀[R]^(p + 1 + q) (Ω[R⁄A])) :=
  LinearMap.compr₂
      ((exteriorPower.wedgeMul (p + 1) (q + 1)).compl₁₂
        (LinearMap.fst R _ _) (LinearMap.fst R _ _)) (LinearMap.inl R _ _) +
    LinearMap.compr₂
      (LinearMap.compr₂
          ((exteriorPower.wedgeMul p (q + 1)).compl₁₂
            (LinearMap.snd R _ _) (LinearMap.fst R _ _))
          (exteriorPower.degCongr (Nat.succ_add p q).symm).toLinearMap +
        (-1 : R) ^ (p + 1) • (exteriorPower.wedgeMul (p + 1) q).compl₁₂
          (LinearMap.fst R _ _) (LinearMap.snd R _ _))
      (LinearMap.inr R _ _)

/-- The two components of `Stacks.LogPoles.logWedgePair A p q x y` are `x.1 ∧ y.1` and
`x.2 ∧ y.1 + (-1)^{p+1} x.1 ∧ y.2`. -/
@[simp]
theorem logWedgePair_apply (p q : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))
    (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedgePair A p q x y =
      (exteriorPower.wedgeMul (p + 1) (q + 1) x.1 y.1,
        exteriorPower.degCongr (Nat.succ_add p q).symm
            (exteriorPower.wedgeMul p (q + 1) x.2 y.1) +
          (-1 : R) ^ (p + 1) • exteriorPower.wedgeMul (p + 1) q x.1 y.2) := by
  refine Prod.ext ?_ ?_ <;> simp [logWedgePair]

/-- The product of a form of degree zero — a function — with a form with a logarithmic pole:
`f ∧ (ω, η) = (f ∧ ω, f ∧ η)`. -/
def logWedgePairLeftZero (A : Type u) [CommRing A] [Algebra A R] (q : ℕ) :
    ⋀[R]^0 (Ω[R⁄A]) →ₗ[R]
      (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) →ₗ[R]
        (⋀[R]^(0 + q + 1) (Ω[R⁄A]) × ⋀[R]^(0 + q) (Ω[R⁄A])) :=
  LinearMap.compr₂
      ((exteriorPower.wedgeMul 0 (q + 1)).compl₁₂ LinearMap.id (LinearMap.fst R _ _))
      (LinearMap.inl R _ _) +
    LinearMap.compr₂
      ((exteriorPower.wedgeMul 0 q).compl₁₂ LinearMap.id (LinearMap.snd R _ _))
      (LinearMap.inr R _ _)

/-- The two components of `Stacks.LogPoles.logWedgePairLeftZero A q f y` are `f ∧ y.1` and
`f ∧ y.2`. -/
@[simp]
theorem logWedgePairLeftZero_apply (q : ℕ) (f : ⋀[R]^0 (Ω[R⁄A]))
    (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedgePairLeftZero A q f y =
      (exteriorPower.wedgeMul 0 (q + 1) f y.1, exteriorPower.wedgeMul 0 q f y.2) := by
  refine Prod.ext ?_ ?_ <;> simp [logWedgePairLeftZero]

/-- The product of a form with a logarithmic pole with a form of degree zero:
`(ω, η) ∧ f = (ω ∧ f, η ∧ f)`. -/
def logWedgePairRightZero (A : Type u) [CommRing A] [Algebra A R] (p : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[R]
      ⋀[R]^0 (Ω[R⁄A]) →ₗ[R]
        (⋀[R]^(p + 1 + 0) (Ω[R⁄A]) × ⋀[R]^(p + 0) (Ω[R⁄A])) :=
  LinearMap.compr₂
      ((exteriorPower.wedgeMul (p + 1) 0).compl₁₂ (LinearMap.fst R _ _) LinearMap.id)
      (LinearMap.inl R _ _) +
    LinearMap.compr₂
      ((exteriorPower.wedgeMul p 0).compl₁₂ (LinearMap.snd R _ _) LinearMap.id)
      (LinearMap.inr R _ _)

/-- The two components of `Stacks.LogPoles.logWedgePairRightZero A p x f` are `x.1 ∧ f` and
`x.2 ∧ f`. -/
@[simp]
theorem logWedgePairRightZero_apply (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) (f : ⋀[R]^0 (Ω[R⁄A])) :
    logWedgePairRightZero A p x f =
      (exteriorPower.wedgeMul (p + 1) 0 x.1 f, exteriorPower.wedgeMul p 0 x.2 f) := by
  refine Prod.ext ?_ ?_ <;> simp [logWedgePairRightZero]

/-! ### The product respects the relations -/

section WellDefined

variable {t : R}

/-- `dt ∧ ω = 0` for the first component of a relation, read in the exterior algebra. -/
theorem coe_mul_fst_eq_zero_of_mem_logRel
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    ExteriorAlgebra.ι R (D A R t) * (x.1 : ExteriorAlgebra R (Ω[R⁄A])) = 0 := by
  rw [← exteriorPower.coe_wedgeLeft, wedgeLeft_D_fst_eq_zero_of_mem_logRel ht p hx]
  rfl

/-- The sign `(-1)^n` is central in the exterior algebra. -/
private theorem neg_one_pow_comm (n : ℕ) (z w : ExteriorAlgebra R (Ω[R⁄A])) :
    z * ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ n * w) =
      (-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ n * (z * w) := by
  rw [← mul_assoc, ← ((Commute.neg_one_left z).pow_left n).eq, mul_assoc]

/-- The algebra behind `Stacks.LogPoles.logWedgePair_mem_logRel_left`, with the elements of the
exterior algebra abstracted: `τ` is `dt`, `(u, v)` the first factor and `(a, b)` the second. -/
private theorem logRel_left_aux (p : ℕ) (t : R) {u v a b τ : ExteriorAlgebra R (Ω[R⁄A])} :
    t • (u * a) + τ * (v * a + (-1) ^ (p + 1) * (u * b)) =
      (t • u + τ * v) * a + (-1) ^ (p + 1) * ((τ * u) * b) := by
  simp only [add_mul, mul_add, mul_assoc, smul_mul_assoc, neg_one_pow_comm, add_assoc]

/-- **The product respects the relations in its first argument.**  If `t ω₁ + dt ∧ η₁ = 0` then
`t (ω₁ ∧ ω₂) + dt ∧ (η₁ ∧ ω₂ + (-1)^{p+1} ω₁ ∧ η₂) = 0`: the first two terms combine into
`(t ω₁ + dt ∧ η₁) ∧ ω₂`, and the last vanishes because `dt ∧ ω₁ = 0`. -/
theorem logWedgePair_mem_logRel_left
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p)
    (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedgePair A p q x y ∈ logRel A t (p + 1 + q) := by
  have h1 := (mem_logRel_iff_coe t p).mp hx
  have h2 := coe_mul_fst_eq_zero_of_mem_logRel ht p hx
  rw [mem_logRel_iff_coe]
  simp only [logWedgePair_apply, exteriorPower.wedgeMul_apply_coe, Submodule.coe_add,
    exteriorPower.coe_degCongr, exteriorPower.coe_neg_one_pow_smul]
  rw [logRel_left_aux p t, h1, zero_mul, h2, zero_mul, mul_zero, add_zero]

/-- The algebra behind `Stacks.LogPoles.logWedgePair_mem_logRel_right`, with the elements of the
exterior algebra abstracted: `τ` is `dt`, `(u, v)` the first factor and `(a, b)` the second, and
the two hypotheses are graded commutativity of `τ` past `v` and past `u`. -/
private theorem logRel_right_aux (p : ℕ) (t : R)
    {u v a b τ : ExteriorAlgebra R (Ω[R⁄A])}
    (hv : τ * v = (-1) ^ (1 * p) * (v * τ))
    (hu : τ * u = (-1) ^ (1 * (p + 1)) * (u * τ)) :
    t • (u * a) + τ * (v * a + (-1) ^ (p + 1) * (u * b)) =
      u * (t • a + τ * b) + (-1) ^ (1 * p) * (v * (τ * a)) := by
  have hsq : ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (p + 1)) *
      ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (1 * (p + 1))) = 1 := by
    rw [one_mul, ← pow_add, show p + 1 + (p + 1) = 2 * (p + 1) by ring, pow_mul]
    simp
  have e1 : t • (u * a) = u * (t • a) := (mul_smul_comm t u a).symm
  have e2 : τ * (v * a) = (-1) ^ (1 * p) * (v * (τ * a)) := by
    rw [← mul_assoc τ v a, hv, mul_assoc ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (1 * p)) (v * τ) a,
      mul_assoc v τ a]
  have e3 : τ * ((-1) ^ (p + 1) * (u * b)) = u * (τ * b) := by
    rw [neg_one_pow_comm, ← mul_assoc τ u b, hu,
      mul_assoc ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (1 * (p + 1))) (u * τ) b, mul_assoc u τ b,
      ← mul_assoc ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (p + 1)), hsq, one_mul]
  rw [mul_add, e1, e2, e3, mul_add]
  abel

/-- **The product respects the relations in its second argument.**  If `t ω₂ + dt ∧ η₂ = 0` then
`t (ω₁ ∧ ω₂) = -ω₁ ∧ dt ∧ η₂`, the term `dt ∧ η₁ ∧ ω₂` vanishes because `dt ∧ ω₂ = 0`, and the
remaining term cancels the first; the two sign moves are graded commutativity. -/
theorem logWedgePair_mem_logRel_right
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))
    {y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])} (hy : y ∈ logRel A t q) :
    logWedgePair A p q x y ∈ logRel A t (p + 1 + q) := by
  have h1 := (mem_logRel_iff_coe t q).mp hy
  have h2 := coe_mul_fst_eq_zero_of_mem_logRel ht q hy
  rw [mem_logRel_iff_coe]
  simp only [logWedgePair_apply, exteriorPower.wedgeMul_apply_coe, Submodule.coe_add,
    exteriorPower.coe_degCongr, exteriorPower.coe_neg_one_pow_smul]
  rw [logRel_right_aux p t
      (exteriorPower.mul_comm_of_mem (exteriorPower.ι_mem_degreeOne (D A R t)) x.2.2)
      (exteriorPower.mul_comm_of_mem (exteriorPower.ι_mem_degreeOne (D A R t)) x.1.2),
    h1, mul_zero, h2, mul_zero, mul_zero, add_zero]

/-- **The degree-zero-on-the-left product respects the relations**: a function commutes past
everything, so `t (f ω) + dt ∧ (f η) = f (t ω + dt ∧ η) = 0`. -/
theorem logWedgePairLeftZero_mem_logRel (q : ℕ) (f : ⋀[R]^0 (Ω[R⁄A]))
    {y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])} (hy : y ∈ logRel A t q) :
    logWedgePairLeftZero A q f y ∈ logRel A t (0 + q) := by
  have h1 := (mem_logRel_iff_coe t q).mp hy
  have hcomm : ExteriorAlgebra.ι R (D A R t) * (f : ExteriorAlgebra R (Ω[R⁄A])) =
      (-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ (1 * 0) *
        ((f : ExteriorAlgebra R (Ω[R⁄A])) * ExteriorAlgebra.ι R (D A R t)) :=
    exteriorPower.mul_comm_of_mem (exteriorPower.ι_mem_degreeOne _) f.2
  rw [mem_logRel_iff_coe]
  simp only [logWedgePairLeftZero_apply, exteriorPower.wedgeMul_apply_coe]
  rw [← mul_zero (f : ExteriorAlgebra R (Ω[R⁄A])), ← h1]
  simp only [mul_add, mul_smul_comm, ← mul_assoc, hcomm, mul_zero, pow_zero, one_mul]

/-- **The degree-zero-on-the-right product respects the relations**: both components are wedged
with the same function, so `t (ω f) + dt ∧ (η f) = (t ω + dt ∧ η) f = 0`. -/
theorem logWedgePairRightZero_mem_logRel (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p)
    (f : ⋀[R]^0 (Ω[R⁄A])) :
    logWedgePairRightZero A p x f ∈ logRel A t p := by
  have h1 := (mem_logRel_iff_coe t p).mp hx
  rw [mem_logRel_iff_coe]
  simp only [logWedgePairRightZero_apply, exteriorPower.wedgeMul_apply_coe]
  rw [← zero_mul (f : ExteriorAlgebra R (Ω[R⁄A])), ← h1]
  simp only [add_mul, mul_assoc, smul_mul_assoc]

end WellDefined

/-! ### The product on the de Rham complex of log poles -/

section Product

variable {t : R}

/-- The product of two functions, the degenerate case of `Stacks.LogPoles.logWedge` in which both
degrees are zero. -/
def logWedgeZeroZero (A : Type u) [CommRing A] [Algebra A R] (t : R) :
    logFormsR A t 0 →ₗ[R] logFormsR A t 0 →ₗ[R] logFormsR A t (0 + 0) :=
  exteriorPower.wedgeMul 0 0

/-- The product of a function with a form with a logarithmic pole, descended to the pair model
modulo the relations. -/
def logWedgeZeroSucc (A : Type u) [CommRing A] [Algebra A R] (t : R) (q : ℕ) :
    logFormsR A t 0 →ₗ[R] logFormsR A t (q + 1) →ₗ[R] logFormsR A t (0 + (q + 1)) :=
  (Submodule.liftQ (logRel A t q)
    (LinearMap.flip (LinearMap.compr₂ (logWedgePairLeftZero A q)
      (logRel A t (0 + q)).mkQ))
    fun _ hy ↦ LinearMap.mem_ker.mpr (LinearMap.ext fun f ↦
      (Submodule.Quotient.mk_eq_zero _).mpr
        (logWedgePairLeftZero_mem_logRel q f hy))).flip

/-- The product of a form with a logarithmic pole with a function, descended to the pair model
modulo the relations. -/
def logWedgeSuccZero (A : Type u) [CommRing A] [Algebra A R] (t : R) (p : ℕ) :
    logFormsR A t (p + 1) →ₗ[R] logFormsR A t 0 →ₗ[R] logFormsR A t (p + 1 + 0) :=
  Submodule.liftQ (logRel A t p)
    (LinearMap.compr₂ (logWedgePairRightZero A p) (logRel A t p).mkQ)
    fun _ hx ↦ LinearMap.mem_ker.mpr (LinearMap.ext fun f ↦
      (Submodule.Quotient.mk_eq_zero _).mpr
        (logWedgePairRightZero_mem_logRel p hx f))

/-- The product of two forms with a logarithmic pole of positive degree, descended to the pair
model modulo the relations in the *first* variable only.  Well-definedness here is
`Stacks.LogPoles.logWedgePair_mem_logRel_left`. -/
def logWedgeSuccSuccLeft (A : Type u) [CommRing A] [Algebra A R] {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ) :
    ((⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) ⧸ logRel A t p) →ₗ[R]
      (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) →ₗ[R]
        ((⋀[R]^(p + 1 + q + 1) (Ω[R⁄A]) × ⋀[R]^(p + 1 + q) (Ω[R⁄A])) ⧸
          logRel A t (p + 1 + q)) :=
  Submodule.liftQ (logRel A t p)
    (LinearMap.compr₂ (logWedgePair A p q) (logRel A t (p + 1 + q)).mkQ)
    fun _ hx ↦ LinearMap.mem_ker.mpr (LinearMap.ext fun y ↦
      (Submodule.Quotient.mk_eq_zero (logRel A t (p + 1 + q))).mpr
        (logWedgePair_mem_logRel_left ht p q hx y))

/-- On the class of a pair `x`, `Stacks.LogPoles.logWedgeSuccSuccLeft` is the class of
`Stacks.LogPoles.logWedgePair A p q x y`. -/
@[simp]
theorem logWedgeSuccSuccLeft_apply
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))
    (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedgeSuccSuccLeft A ht p q (Submodule.Quotient.mk (p := logRel A t p) x) y =
      Submodule.Quotient.mk (p := logRel A t (p + 1 + q)) (logWedgePair A p q x y) := rfl

/-- The product of two forms with a logarithmic pole of positive degree, descended to the pair
model modulo the relations in both variables.  Well-definedness in the second variable is
`Stacks.LogPoles.logWedgePair_mem_logRel_right`. -/
def logWedgeSuccSucc (A : Type u) [CommRing A] [Algebra A R] {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ) :
    ((⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) ⧸ logRel A t p) →ₗ[R]
      ((⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸ logRel A t q) →ₗ[R]
        ((⋀[R]^(p + 1 + q + 1) (Ω[R⁄A]) × ⋀[R]^(p + 1 + q) (Ω[R⁄A])) ⧸
          logRel A t (p + 1 + q)) :=
  (Submodule.liftQ (logRel A t q) (logWedgeSuccSuccLeft A ht p q).flip
    fun y hy ↦ LinearMap.mem_ker.mpr (LinearMap.ext fun z ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (logRel A t p) z
      rw [LinearMap.zero_apply, LinearMap.flip_apply, logWedgeSuccSuccLeft_apply]
      exact (Submodule.Quotient.mk_eq_zero (logRel A t (p + 1 + q))).mpr
        (logWedgePair_mem_logRel_right ht p q x hy))).flip

/-- **The product on the de Rham complex of log poles**, `Ω^p(log Y) × Ω^q(log Y) → Ω^{p+q}(log
Y)`, as an `𝒪_X`-bilinear map.  On the pair model it is
`(ω₁, η₁) ∧ (ω₂, η₂) = (ω₁ ∧ ω₂, η₁ ∧ ω₂ + (-1)^{p+1} ω₁ ∧ η₂)`, with the three degenerate cases
where a degree is zero given by wedging a function into both components. -/
@[stacks 0FUP "clause (1), existence: the O_X-bilinear extension of the wedge product to the log \
poles complex of 0FMW, at the ring level for a principal divisor (t); the Leibniz rule for this \
product is not proved"]
def logWedge (A : Type u) [CommRing A] [Algebra A R]
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    (p q : ℕ) →
      (logFormsR A t p →ₗ[R] logFormsR A t q →ₗ[R] logFormsR A t (p + q))
  | 0, 0 => logWedgeZeroZero A t
  | 0, q + 1 => logWedgeZeroSucc A t q
  | p + 1, 0 => logWedgeSuccZero A t p
  | p + 1, q + 1 => logWedgeSuccSucc A ht p q

/-- In degrees `0` and `0`, `Stacks.LogPoles.logWedge` is the wedge product of functions. -/
@[simp]
theorem logWedge_zero_zero_apply
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (f g : ⋀[R]^0 (Ω[R⁄A])) :
    logWedge A ht 0 0 f g = exteriorPower.wedgeMul 0 0 f g := rfl

/-- In degrees `0` and `q + 1`, `Stacks.LogPoles.logWedge` sends a function `f` and the class of a
pair `y` to the class of `Stacks.LogPoles.logWedgePairLeftZero A q f y`. -/
@[simp]
theorem logWedge_zero_succ_apply
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (q : ℕ)
    (f : ⋀[R]^0 (Ω[R⁄A])) (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedge A ht 0 (q + 1) f (Submodule.Quotient.mk (p := logRel A t q) y) =
      Submodule.Quotient.mk (p := logRel A t (0 + q)) (logWedgePairLeftZero A q f y) := rfl

/-- In degrees `p + 1` and `0`, `Stacks.LogPoles.logWedge` sends the class of a pair `x` and a
function `f` to the class of `Stacks.LogPoles.logWedgePairRightZero A p x f`. -/
@[simp]
theorem logWedge_succ_zero_apply
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) (f : ⋀[R]^0 (Ω[R⁄A])) :
    logWedge A ht (p + 1) 0 (Submodule.Quotient.mk (p := logRel A t p) x) f =
      Submodule.Quotient.mk (p := logRel A t p) (logWedgePairRightZero A p x f) := rfl

/-- In degrees `p + 1` and `q + 1`, `Stacks.LogPoles.logWedge` sends the classes of pairs `x` and
`y` to the class of `Stacks.LogPoles.logWedgePair A p q x y`. -/
@[simp]
theorem logWedge_succ_succ_apply
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p q : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))
    (y : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) :
    logWedge A ht (p + 1) (q + 1) (Submodule.Quotient.mk (p := logRel A t p) x)
        (Submodule.Quotient.mk (p := logRel A t q) y) =
      Submodule.Quotient.mk (p := logRel A t (p + 1 + q)) (logWedgePair A p q x y) := rfl

/-- **The product extends the wedge product of the forms with no pole.**  This is the defining
property of the extension in clause (1) of Stacks Tag 0FUP: a form with no pole is the pair
`(ω, 0)`, and the formula on pairs leaves the second component zero. -/
@[stacks 0FUP "clause (1), existence: the constructed product restricts to the wedge product on \
the forms with no pole, which is the defining property of the extension"]
theorem logWedge_logInclR
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A])) :
    logWedge A ht p q (logInclR t p ω) (logInclR t q η) =
      logInclR t (p + q) (exteriorPower.wedgeMul p q ω η) := by
  cases p with
  | zero =>
      cases q with
      | zero => rfl
      | succ q =>
          rw [logInclR_zero_apply, logInclR_succ_apply, logWedge_zero_succ_apply]
          refine congrArg (Submodule.Quotient.mk (p := logRel A t (0 + q))) ?_
          rw [logWedgePairLeftZero_apply]
          simp
  | succ p =>
      cases q with
      | zero =>
          rw [logInclR_succ_apply, logInclR_zero_apply, logWedge_succ_zero_apply]
          refine congrArg (Submodule.Quotient.mk (p := logRel A t p)) ?_
          rw [logWedgePairRightZero_apply]
          simp
      | succ q =>
          rw [logInclR_succ_apply, logInclR_succ_apply, logWedge_succ_succ_apply]
          refine congrArg (Submodule.Quotient.mk (p := logRel A t (p + 1 + q))) ?_
          rw [logWedgePair_apply]
          refine Prod.ext rfl ?_
          simp

/-- **The product of clause (1) satisfies the computed formula** `t² (α ∧ β) = (t α) ∧ (t β)` of
`Stacks.LogPoles.smul_logWedge_eq`, whose right-hand side involves only forms with no
pole.  So the construction here is the product that formula computes. -/
theorem smul_smul_logWedge
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (p q : ℕ) (α : logFormsR A t p) (β : logFormsR A t q) :
    (t * t) • logWedge A ht p q α β =
      logInclR t (p + q) (exteriorPower.wedgeMul p q
        (logMulT A t p α) (logMulT A t q β)) :=
  smul_logWedge_eq (logWedge A ht) (logWedge_logInclR ht) p q α β

/-- **The product of clause (1) is the unique `𝒪_X`-bilinear extension.**  Any `𝒪_X`-bilinear
product on the de Rham complex of log poles that restricts to the wedge product on the forms with
no pole is `Stacks.LogPoles.logWedge`.  This discharges the hypothesis of the uniqueness
statement `Stacks.LogPoles.logWedge_unique` with the construction, so uniqueness is not vacuous.
-/
@[stacks 0FUP "clause (1): the product built here is THE O_X-bilinear extension, discharging the \
hypothesis of the uniqueness statement; the Leibniz rule is not proved"]
theorem eq_logWedge_of_logInclR
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (w : (p q : ℕ) →
      logFormsR A t p →ₗ[R] logFormsR A t q →ₗ[R] logFormsR A t (p + q))
    (hw : ∀ (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A])),
      w p q (logInclR t p ω) (logInclR t q η) =
        logInclR t (p + q) (exteriorPower.wedgeMul p q ω η)) :
    w = logWedge A ht :=
  logWedge_unique ht w (logWedge A ht) hw (logWedge_logInclR ht)

end Product

/-! ### Non-vacuity: the product reaches the forms that really have poles -/

section NonVacuous

variable {t : R}

/-- **The logarithmic differential `dlog t`**, as a form with a logarithmic pole of degree one:
the pair `(0, 1)`.  It is not a form with no pole, and it is the factor that generates the pole
part of the complex. -/
def dlogForm (A : Type u) [CommRing A] [Algebra A R] (t : R) : logFormsR A t 1 :=
  Submodule.Quotient.mk (p := logRel A t 0)
    ((0 : ⋀[R]^1 (Ω[R⁄A])), exteriorPower.unitDegZero R (Ω[R⁄A]))

/-- **`dlog t ∧ ω` is the form with a logarithmic pole presented by the pair `(0, ω)`.**  So the
product of clause (1) genuinely leaves the forms with no pole: its value on `dlog t` and a form
with no pole has `ω` as its pole part, whose residue is `ω|_Y`. -/
theorem logWedge_dlogForm_logInclR
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (q : ℕ)
    (η : ⋀[R]^(q + 1) (Ω[R⁄A])) :
    logWedge A ht 1 (q + 1) (dlogForm A t) (logInclR t (q + 1) η) =
      Submodule.Quotient.mk (p := logRel A t (0 + 1 + q))
        ((0 : ⋀[R]^(0 + 1 + q + 1) (Ω[R⁄A])),
          exteriorPower.degCongr (Nat.succ_add 0 q).symm
            (exteriorPower.wedgeMul 0 (q + 1) (exteriorPower.unitDegZero R (Ω[R⁄A])) η)) := by
  rw [dlogForm, logInclR_succ_apply, logWedge_succ_succ_apply ht 0 q]
  refine congrArg (Submodule.Quotient.mk (p := logRel A t (0 + 1 + q))) ?_
  rw [logWedgePair_apply]
  refine Prod.ext ?_ ?_ <;> simp

/-- The pole part produced by `dlog t ∧ ω` is `ω` itself, read in the exterior algebra. -/
theorem coe_wedgeMul_unitDegZero (q : ℕ) (η : ⋀[R]^(q + 1) (Ω[R⁄A])) :
    ((exteriorPower.wedgeMul 0 (q + 1) (exteriorPower.unitDegZero R (Ω[R⁄A])) η :
        ⋀[R]^(0 + (q + 1)) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
      (η : ExteriorAlgebra R (Ω[R⁄A])) := by
  rw [exteriorPower.wedgeMul_apply_coe, exteriorPower.coe_unitDegZero, one_mul]

/-- **The product of clause (1) is defined on strictly more than the forms with no pole.**  The
inclusion `Ω^{p+1}_{X/S} → Ω^{p+1}_{X/S}(log Y)` is not surjective as soon as the divisor carries
a nonzero `p`-form, by `Stacks.LogPoles.not_surjective_logIncl_f_succ`; so the
extension built here is not an extension along a bijection. -/
theorem not_surjective_logInclR
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) (hne : ∃ ζ : ⋀[R ⧸ Ideal.span {t}]^p (Ω[(R ⧸ Ideal.span {t})⁄A]), ζ ≠ 0) :
    ¬ Function.Surjective (logInclR (A := A) t (p + 1)) :=
  fun h ↦ not_surjective_logIncl_f_succ ht hsplit p hne fun z ↦ h z

end NonVacuous

end Stacks.LogPoles

end
