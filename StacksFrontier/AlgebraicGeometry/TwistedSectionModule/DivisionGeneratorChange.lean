module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.SectionMultiplication

/-!
# Changing the generator of the division over a common open

Stacks Tag 0B5I's local datum is indexed by the homogeneous elements of positive degree of the
section ring, and its compatibility field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` compares the
local maps at **two different** elements `a` and `b` with `D₊(b) ≤ D₊(a)`. Beyond shrinking the
open — which is
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestrictionShrink.lean` — that asks for
the divisions by the powers of `a` and by the powers of `b` to agree on an open where both are
invertible. **This file proves that agreement.**

The containment `D₊(b) ≤ D₊(a)` is what produces a relation `y · a = b ^ N` in the section ring,
and such a relation is the hypothesis here; it is not derived, because it is the geometry of the
standard opens and not the arithmetic of the division. Granted it, the fraction `t / aⁿ` is the
fraction `(yⁿ · t) / b ^ (N n)`, and the two divisions produce the same section.

Nothing in this file crosses two sites: `a`, `b`, `y` and the numerator live on `X`, and every
division happens in the modules on the slice site over the **one** open `V`. That is what makes
the proof available at all — see the implementation notes.

## Main results

* `Stacks.TwistedSections.shiftPow_eq_gsmul_shiftPow`: **multiplication by `b ^ M` is
  multiplication by `aⁿ` followed by multiplication by `Y`**, given `aⁿ · Y = b ^ M`.
* `Stacks.TwistedSections.powerDivision_gsmul_changeGenerator`: **the change of generator for the
  divisions**, in an arbitrary monoidal category and for sections invertible there.
* `Stacks.TwistedSections.monoidalDivision_gsmul_changeGenerator`: the same after a monoidal
  functor, with the relation still read in the section ring upstairs.
* `Stacks.TwistedSections.changeGenerator_sectionPow_mul`: **the relation `y · a = b ^ N` raised
  to the `n`-th power**, `aⁿ · yⁿ = b ^ (N n)`. This is the one step that uses commutativity of
  the section ring, and it is used where that commutativity is available — on `X`, not on the
  slice site.
* `Stacks.TwistedSections.openDivision_gsmul_changeGenerator`: **the deliverable** — over an open
  `V` inside both nonvanishing loci, the division of `yⁿ · t` by `b ^ (N n)` is the division of
  `t` by `aⁿ`, as sections of `ℱ` over `V`.

## Implementation notes

**Why this half is the easy one.** Both divisions here are
`Stacks.TwistedSections.monoidalDivision` along the *same* monoidal functor
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenRestriction` at the *same* open `V`, so the
comparison is between two elements of one group and `Stacks.TwistedSections.bijective_shiftPow`
applies to it directly. The companion half of `app_restrict` — restricting the division at a
fixed generator from `V` to a smaller `V'` — does cross two sites, and is
`Stacks.TwistedSections.openDivision_restrict`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestrictionShrink.lean`), proved by
taking the multiplication out of the slice site altogether.

**No commutativity on the slice site.** `Stacks.TwistedSections.actMap_mul` — the product rule
for the action — needs `CategoryTheory.BraidedCategory` and
`Stacks.GradedSections.HasTrivialSelfBraiding`, which the modules on a slice site do not have in
this repository. So the abstract core below uses only
`Stacks.TwistedSections.actMap_comp`, which needs neither, and takes the product in the single
order that lemma produces: `Stacks.GradedSections.mul (sectionPowOfDegree a n) Y`, the power acting
first. Commutativity is spent exactly once, in `changeGenerator_sectionPow_mul`, which is a
statement about the section ring of `X` and is proved in the ring, where `mul_pow` is available.

**The degree equalities are passed as hypotheses, not derived.** A twisted section of degree
`d n + p` and one of degree `e M` are of the same type only up to
`Stacks.TwistedSections.twistCongr`, and the two orders `d n + p` and `p + d n` are not
definitionally equal, so both reindexings are named. Equality proofs being definitionally
irrelevant, which proof of a degree identity is supplied never matters.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections mul mulMap sectionRing HasTrivialSelfBraiding powCongr
  powCongr_rfl mul_comm')
open Stacks.TensorPowers (natTensorPow)

universe v₂ u₂ v u

namespace Stacks.TwistedSections

/-! ### The degrees -/

/-- The degree of the numerator after a change of generator: if `y` has degree `p`, `a` degree `d`
and `y · a = b ^ N` with `b` of degree `e`, then `yⁿ · t` for `t` of degree `d n` is homogeneous
of degree `e (N n)`, which is the degree of a numerator over `b ^ (N n)`. -/
theorem changeGenerator_degree {d e p : ℕ} (N : ℕ) (hdeg : p + d = e * N) (n : ℕ) :
    d * n + p * n = e * (N * n) := by
  rw [Nat.add_comm (d * n) (p * n), ← Nat.add_mul, hdeg, Nat.mul_assoc]

/-- `changeGenerator_degree` with the two summands in the order
`Stacks.TwistedSections.gsmul` produces, the acting section's degree first. -/
theorem changeGenerator_degree_comm {d e p : ℕ} (N : ℕ) (hdeg : p + d = e * N) (n : ℕ) :
    p * n + d * n = e * (N * n) := by
  rw [← Nat.add_mul, hdeg, Nat.mul_assoc]

/-! ### An arbitrary monoidal category -/

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F L : C}
  [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]

/-- **Multiplication by `b ^ M` is multiplication by `aⁿ` followed by multiplication by `Y`**,
for a relation `aⁿ · Y = b ^ M` in the section ring. This is `gsmul_shiftPow` with the product
rewritten by that relation; the two reindexings of the degree are both passed in. -/
theorem shiftPow_eq_gsmul_shiftPow {d e p : ℕ} (a : powSections L d) (b : powSections L e)
    (Y : powSections L p) {n M : ℕ} (hd₁ : d * n + p = e * M) (hd₂ : p + d * n = e * M)
    (hY : mul (sectionPowOfDegree a n) Y ≫ powCongr L hd₁ = sectionPowOfDegree b M)
    (u : twistSections F L 0) :
    shiftPow b M u = twistCongr hd₂ (gsmul Y (shiftPow a n u)) := by
  rw [gsmul_shiftPow a Y n u ((Nat.zero_add (d * n + p)).trans (Nat.add_comm (d * n) p)),
    twistCongr_trans, shiftPow_eq_actMap b M u, ← hY, Category.assoc,
    eqToHom_comp_actMap u hd₁]
  simp only [twistCongr, Category.assoc, eqToHom_trans]

/-- **The change of generator for the divisions.** For `a` and `b` both invertible and a relation
`aⁿ · Y = b ^ M`, dividing `Y · t` by `b ^ M` is dividing `t` by `aⁿ`. Both sides are degree-zero
twisted sections in the *same* category, so the identity is checked by multiplying by `b ^ M`,
which is injective (`Stacks.TwistedSections.bijective_shiftPow`). -/
theorem powerDivision_gsmul_changeGenerator {d e p : ℕ} (a : powSections L d) [IsIso a]
    (b : powSections L e) [IsIso b] (Y : powSections L p) {n M : ℕ}
    (hd₁ : d * n + p = e * M) (hd₂ : p + d * n = e * M)
    (hY : mul (sectionPowOfDegree a n) Y ≫ powCongr L hd₁ = sectionPowOfDegree b M)
    (t : twistSections F L (d * n)) :
    powerDivision b M (twistCongr hd₂ (gsmul Y t)) = powerDivision a (F := F) n t := by
  refine (bijective_shiftPow b (F := F) M).injective ?_
  rw [shiftPow_powerDivision, shiftPow_eq_gsmul_shiftPow a b Y hd₁ hd₂ hY,
    shiftPow_powerDivision]

end Abstract

/-! ### After a monoidal functor -/

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal]
  {F L : C} [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]
  [Preadditive D] [G.Additive]
  [(_root_.CategoryTheory.MonoidalCategory.tensorRight (G.obj L)).Additive]

omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]
  [Preadditive D] [G.Additive]
  [(_root_.CategoryTheory.MonoidalCategory.tensorRight (G.obj L)).Additive] in
/-- Carrying a section of a tensor power along `G` commutes with reindexing its degree. -/
theorem mapPowSections_comp_powCongr {p q : ℕ} (h : p = q) (x : powSections L p) :
    mapPowSections G (x ≫ powCongr L h) = mapPowSections G x ≫ powCongr (G.obj L) h := by
  subst h
  rw [powCongr_rfl, powCongr_rfl, Category.comp_id,
    Category.comp_id]

/-- **The change of generator for the divisions obtained through a monoidal functor.** The
relation `aⁿ · Y = b ^ M` is read upstairs, where the section ring lives; `mapPowSections` is
multiplicative and sends powers to powers, so it carries the relation to the image sections, and
`powerDivision_gsmul_changeGenerator` applies there. -/
theorem monoidalDivision_gsmul_changeGenerator {d e p : ℕ} (a : powSections L d)
    (b : powSections L e) [IsIso (mapPowSections G a)] [IsIso (mapPowSections G b)]
    (Y : powSections L p) {n M : ℕ} (hd₁ : d * n + p = e * M) (hd₂ : p + d * n = e * M)
    (hY : mul (sectionPowOfDegree a n) Y ≫ powCongr L hd₁ = sectionPowOfDegree b M)
    (t : twistSections F L (d * n)) :
    monoidalDivision G b M (twistCongr hd₂ (gsmul Y t)) =
      monoidalDivision G a (F := F) n t := by
  have hY' : mul (sectionPowOfDegree (mapPowSections G a) n) (mapPowSections G Y) ≫
      powCongr (G.obj L) hd₁ = sectionPowOfDegree (mapPowSections G b) M := by
    rw [← mapPowSections_sectionPow G a n, ← mapPowSections_sectionPow G b M,
      ← mapPowSections_mul, ← mapPowSections_comp_powCongr, hY]
  rw [monoidalDivision_apply, monoidalDivision_apply, mapTwistSections_twistCongr,
    mapTwistSections_gsmul]
  exact powerDivision_gsmul_changeGenerator (mapPowSections G a) (mapPowSections G b)
    (mapPowSections G Y) hd₁ hd₂ hY' (mapTwistSections G t)

end Monoidal

/-! ### Raising the relation to a power -/

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {L : C}
  [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]
  [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The relation `y · a = b ^ N` raised to the `n`-th power:** `aⁿ · yⁿ = b ^ (N n)`, modulo
the degree transport the grading forces.

This is the one place commutativity of the section ring is used, and it is used where that
commutativity is available: the identity is proved in `Stacks.GradedSections.sectionRing`, which
is a commutative ring, and read back on the homogeneous pieces. -/
theorem changeGenerator_sectionPow_mul {d e p : ℕ} (a : powSections L d) (b : powSections L e)
    (y : powSections L p) {N : ℕ} (hdeg : p + d = e * N)
    (hy : mul y a ≫ powCongr L hdeg = sectionPowOfDegree b N) (n : ℕ) :
    mul (sectionPowOfDegree a n) (sectionPowOfDegree y n) ≫
        powCongr L (changeGenerator_degree N hdeg n) =
      sectionPowOfDegree b (N * n) := by
  have hof : ∀ {i j : ℕ} (h : i = j) (x : powSections L i),
      DirectSum.of (powSections L) j (x ≫ powCongr L h) =
        DirectSum.of (powSections L) i x := by
    intro i j h x
    subst h
    rw [powCongr_rfl, Category.comp_id]
  have hprod : homogeneousSectionOfDegree y * homogeneousSectionOfDegree a =
      DirectSum.of (powSections L) (p + d) (mul y a) := DirectSum.of_mul_of y a
  have hβ : homogeneousSectionOfDegree b ^ N =
      homogeneousSectionOfDegree y * homogeneousSectionOfDegree a := by
    rw [hprod, ← hof hdeg (mul y a), hy, of_sectionPowOfDegree]
  have hpow : homogeneousSectionOfDegree y ^ n * homogeneousSectionOfDegree a ^ n =
      DirectSum.of (powSections L) (p * n + d * n)
        (mul (sectionPowOfDegree y n) (sectionPowOfDegree a n)) := by
    rw [← of_sectionPowOfDegree y n, ← of_sectionPowOfDegree a n]
    exact DirectSum.of_mul_of (sectionPowOfDegree y n) (sectionPowOfDegree a n)
  have key : DirectSum.of (powSections L) (e * (N * n)) (sectionPowOfDegree b (N * n)) =
      DirectSum.of (powSections L) (e * (N * n))
        (mul (sectionPowOfDegree a n) (sectionPowOfDegree y n) ≫
          powCongr L (changeGenerator_degree N hdeg n)) := by
    rw [hof (changeGenerator_degree N hdeg n), of_sectionPowOfDegree, pow_mul, hβ, mul_pow, hpow,
      ← mul_comm' (sectionPowOfDegree a n) (sectionPowOfDegree y n),
      hof (Nat.add_comm (d * n) (p * n)) (mul (sectionPowOfDegree a n) (sectionPowOfDegree y n))]
  simpa using congrArg (fun z : sectionRing L => z (e * (N * n))) key.symm

end Braided

/-! ### On a scheme, with the quotient read as a section over the open -/

section Scheme

open AlgebraicGeometry Opposite
open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal

variable {X : Scheme.{u}}

/-- **The change of generator for the divisions over a common open.** Let `a` and `b` be global
sections of tensor powers of `L`, let `V` be an open inside both nonvanishing loci, and let
`y · a = b ^ N` in the section ring. Then over `V` the division of `yⁿ · t` by `b ^ (N n)` is the
division of `t` by `aⁿ`, as sections of `ℱ` over `V`.

This is the half of Stacks Tag 0B5I's field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` that compares two
generators; it runs entirely inside the modules on the slice site over the one open `V`, so no
comparison of two sites occurs. -/
theorem openDivision_gsmul_changeGenerator (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d e p : ℕ} (a : powSections L d) (b : powSections L e)
    (y : powSections L p) (V : X.Opens) (hVa : V ≤ nvOpen L a) (hVb : V ≤ nvOpen L b)
    {N : ℕ} (hdeg : p + d = e * N)
    (hy : mul y a ≫ powCongr L hdeg = sectionPowOfDegree b N) (n : ℕ)
    (t : twistSections F L (d * n)) :
    openDivision F L b V hVb (N * n)
        (twistCongr (changeGenerator_degree_comm N hdeg n) (gsmul (sectionPowOfDegree y n) t)) =
      openDivision F L a V hVa n t := by
  have := isIso_mapPowSections_openRestriction L a hVa
  have := isIso_mapPowSections_openRestriction L b hVb
  exact congrArg (schemeOpenUnitHomAddEquiv V F)
    (monoidalDivision_gsmul_changeGenerator (schemeOpenRestriction X V) a b (sectionPowOfDegree y n)
      (changeGenerator_degree N hdeg n) (changeGenerator_degree_comm N hdeg n)
      (changeGenerator_sectionPow_mul a b y hdeg hy n) t)

end Scheme

end Stacks.TwistedSections

end
