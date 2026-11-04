module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Nilpotent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting units across a surjective closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `U` an affine open of `X`. The restriction
map `Γ(X, U) → Γ(Z, i⁻¹U)` is surjective (`AlgebraicGeometry.Scheme.Hom.app_surjective`,
affineness of `U` being what makes it so), and a surjection of commutative rings **whose kernel
consists of nilpotents** is surjective *on units*: a lift `a` of a unit satisfies `a * a' = 1 + j`
with `j` in the kernel, so `a * a'` is a unit and therefore `a` is. So every invertible function
on `i⁻¹U` extends to an invertible function on `U`.

**The hypothesis is that `i` is onto, not that its ideal sheaf is nilpotent.** Only one element
of the kernel is ever inverted, so no uniform nilpotency exponent is needed; the condition
`RingHom.ker (i.app U).hom ≤ nilradical Γ(X, U)` over every affine open is exactly
`i.ker ≤ X.nilradical`, which for a closed immersion says exactly that the underlying map of `i`
is **surjective** — `Z` and `X` have the same underlying space. Nilpotency of `i.ker` implies it,
and the two coincide when each kernel ideal is finitely generated
(`Ideal.FG.isNilpotent_iff_le_nilradical`).

Surjectivity cannot be dropped, and this is the one step of
[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) that fails for a general closed
immersion: for `k[t] → k[t]/(t(t-1)) = k × k` the map on units is `kˣ → kˣ × kˣ`, since
`k[t]ˣ = kˣ`, and in characteristic `≠ 2` the unit `(1, -1)` has no lift. That `i` is not onto —
its image is two points of the affine line. The surjective case is the one that matters
downstream: `Z = X_red` has the same underlying space as `X` by construction, and that is the
instance of Tag 09NY that [Stacks, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
consumes.

## Main results

* `Stacks.LiftInvertible.exists_isUnit_of_ker_le_nilradical`: a surjective ring homomorphism
  whose kernel lies in the nilradical is surjective on units. The ring-theoretic core.
  `Stacks.LiftInvertible.exists_isUnit_of_isNilpotent_ker` is its nilpotent special case.
* `Stacks.LiftInvertible.ker_le_nilradical_of_surjective`: a surjective quasi-compact morphism
  has `i.ker ≤ X.nilradical`; `Stacks.LiftInvertible.ker_le_nilradical_of_isNilpotent` is the
  same conclusion from nilpotency, and `Stacks.LiftInvertible.ker_app_le_nilradical` reads the
  bound over one affine open.
* `Stacks.LiftInvertible.exists_units_app_eq`: a unit of `Γ(Z, i⁻¹U)` lifts to a unit of
  `Γ(X, U)`, for `U` an affine open over which the kernel lies in the nilradical.
* `Stacks.LiftInvertible.exists_unitsMap_app_eq`,
  `Stacks.LiftInvertible.exists_unitsMap_app_eq_of_surjective` and
  `Stacks.LiftInvertible.exists_unitsMap_app_eq_of_isNilpotent_ker`: the same in the `Units.map`
  spelling, the last two with a single global hypothesis on `i` rather than one on each open.

## Implementation notes

The ring-theoretic core is proved directly rather than through
`IsNilpotent.isUnit_quotient_mk_iff`, which is the nilpotent-ideal statement for the canonical
projection `R → R ⧸ I`: going through it would need the first isomorphism theorem to turn an
arbitrary surjection into a quotient map and then transport the unit back, and it carries a
hypothesis this argument does not use.

Only the surjectivity-on-units half is proved here. The converse half — a surjection whose
kernel lies in the nilradical *reflects* units — is already public elsewhere in this repository,
in the root namespace of `StacksFrontier/RingTheory/Henselian/Pair/Nilpotent.lean`:
`isUnit_of_map_of_surjective_of_ker_le_nilradical`, with `isUnit_of_quotient_of_le_nilradical`
beneath it and `isLocalHom_of_surjective_of_ker_le_nilradical` packaging it as `IsLocalHom`.
That chapter's import surface is much heavier than this file's, which is why the two halves live
apart; a consumer that needs only one of them should take it from the lighter file.

Nilpotency of the ideal sheaf is read through `AlgebraicGeometry.Scheme.IdealSheafData`'s
semiring structure, where `(I ^ n).ideal U = (I.ideal U) ^ n` holds by `rfl`, so nilpotency of
`i.ker` passes to each `i.ker.ideal U` with no quasi-coherence bookkeeping. The identification
of `i.ker.ideal U` with `RingHom.ker (i.app U).hom` is `AlgebraicGeometry.Scheme.Hom.ker_apply`
and needs `i` quasi-compact, which a closed immersion is. The surjective hypothesis reaches the
same place through `AlgebraicGeometry.Scheme.Hom.support_ker`, the support of the kernel ideal
sheaf being the closure of the range.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.LiftInvertible

/-- **A nilpotent ideal is contained in the nilradical.** If `I ^ n = ⊥` then every `x ∈ I` has
`x ^ n ∈ I ^ n = ⊥`. The converse holds for a finitely generated `I`
(`Ideal.FG.isNilpotent_iff_le_nilradical`); in general the containment is the weaker
condition. -/
theorem le_nilradical_of_isNilpotent {R : Type*} [CommSemiring R] {I : Ideal R}
    (h : IsNilpotent I) : I ≤ nilradical R := by
  obtain ⟨n, hn⟩ := h
  intro x hx
  refine mem_nilradical.mpr ⟨n, ?_⟩
  simpa [hn] using Ideal.pow_mem_pow hx n

/-- **A surjective ring homomorphism whose kernel consists of nilpotents is surjective on
units.** If `φ : A → B` is surjective with `RingHom.ker φ ≤ nilradical A` and `b` is a unit of
`B`, then some unit `a` of `A` has `φ a = b`.

Lift `b` and `b⁻¹` to `a` and `a'`. Then `φ (a * a' - 1) = 0`, so `a * a' - 1` is nilpotent and
`a * a' = 1 + (a * a' - 1)` is a unit; a factor of a unit in a commutative ring is a unit.

**Nilpotency of the kernel is not what the argument uses.** The element produced is a single
member of the kernel and only its own nilpotency is needed, so no uniform exponent is required:
this hypothesis is weaker than `IsNilpotent (RingHom.ker φ)`, the two coinciding when the kernel
is finitely generated. Geometrically the difference is the one that matters for
[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) — `RingHom.ker φ ≤ nilradical A`
says exactly that `Spec B → Spec A` is **surjective**. -/
theorem exists_isUnit_of_ker_le_nilradical {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical A) {b : B}
    (hb : IsUnit b) : ∃ a : A, IsUnit a ∧ φ a = b := by
  obtain ⟨a, ha⟩ := hsurj b
  obtain ⟨a', ha'⟩ := hsurj (↑hb.unit⁻¹ : B)
  have hmem : a * a' - 1 ∈ RingHom.ker φ := by simp [RingHom.mem_ker, ha, ha']
  have hu : IsUnit (a * a') := by
    have h := (mem_nilradical.mp (hker hmem)).isUnit_one_add
    rwa [show (1 : A) + (a * a' - 1) = a * a' by ring] at h
  exact ⟨a, isUnit_of_mul_isUnit_left hu, ha⟩

/-- **A surjective ring homomorphism with nilpotent kernel is surjective on units.** The special
case of `Stacks.LiftInvertible.exists_isUnit_of_ker_le_nilradical` in which the kernel has a
uniform nilpotency exponent. -/
theorem exists_isUnit_of_isNilpotent_ker {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hsurj : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) {b : B}
    (hb : IsUnit b) : ∃ a : A, IsUnit a ∧ φ a = b :=
  exists_isUnit_of_ker_le_nilradical φ hsurj (le_nilradical_of_isNilpotent hnil) hb

variable {X Z : Scheme.{u}}

/-- The ideal of a nilpotent ideal sheaf over an open is nilpotent. -/
private theorem isNilpotent_ideal_of_isNilpotent (I : X.IdealSheafData) (hnil : IsNilpotent I)
    (U : X.affineOpens) : IsNilpotent (I.ideal U) := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have h : (I ^ n).ideal U = (I.ideal U) ^ n := congrFun (Scheme.IdealSheafData.ideal_pow I n) U
  rw [← h, hn]
  simp

/-- **A nilpotent ideal sheaf has nilpotent kernel ideal over every affine open.** For a
quasi-compact `i`, `i.ker.ideal U` is `RingHom.ker (i.app U).hom`
(`AlgebraicGeometry.Scheme.Hom.ker_apply`), and nilpotency of the ideal sheaf passes to each
affine open because taking the ideal over an open commutes with powers. -/
theorem isNilpotent_ker_app (i : Z ⟶ X) [QuasiCompact i] (hnil : IsNilpotent i.ker)
    (U : X.affineOpens) : IsNilpotent (RingHom.ker (i.app U).hom) := by
  rw [← Scheme.Hom.ker_apply i U]
  exact isNilpotent_ideal_of_isNilpotent i.ker hnil U

/-- **An ideal sheaf whose vanishing locus is everything is contained in the nilradical.** For a
closed immersion — more generally for any quasi-compact `i` — the support of `i.ker` is the
closure of the range of `i` (`AlgebraicGeometry.Scheme.Hom.support_ker`), so a surjective `i`
has `i.ker.support = ⊤` and hence
`i.ker ≤ i.ker.radical = vanishingIdeal ⊤ = X.nilradical`.

This is the hypothesis under which units lift, and it is **purely topological**: it says that
`i` is a closed immersion whose underlying map is onto, i.e. that `Z` and `X` have the same
underlying space. -/
@[sga "1 IX 1.7" "partial", sga "3 X 2.1" "partial"]
theorem ker_le_nilradical_of_surjective (i : Z ⟶ X) [QuasiCompact i]
    (hsurj : Function.Surjective i.base) : i.ker ≤ X.nilradical := by
  have hsupp : i.ker.support = ⊤ := by
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]
    rfl
  calc i.ker ≤ i.ker.radical := Scheme.IdealSheafData.le_radical _
    _ = Scheme.IdealSheafData.vanishingIdeal i.ker.support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal ⊤ := by rw [hsupp]
    _ = X.nilradical := Scheme.IdealSheafData.vanishingIdeal_top

/-- **A nilpotent ideal sheaf is contained in the nilradical.** The ideal-sheaf form of
`Stacks.LiftInvertible.le_nilradical_of_isNilpotent`, obtained over each affine open because
taking the ideal over an open commutes with powers. So nilpotency of the ideal sheaf implies the
hypothesis that makes units lift. -/
theorem ker_le_nilradical_of_isNilpotent (i : Z ⟶ X) (hnil : IsNilpotent i.ker) :
    i.ker ≤ X.nilradical := by
  intro U x hx
  exact le_nilradical_of_isNilpotent (isNilpotent_ideal_of_isNilpotent i.ker hnil U) hx

/-- **An ideal sheaf inside the nilradical has kernel ideal inside the nilradical over every
affine open.** The nilradical of a scheme is the radical of `⊥`, which over an affine open is the
nilradical of the section ring; and for quasi-compact `i` the ideal of `i.ker` over an affine
open is `RingHom.ker (i.app U).hom`
(`AlgebraicGeometry.Scheme.Hom.ker_apply`). -/
theorem ker_app_le_nilradical (i : Z ⟶ X) [QuasiCompact i] (hker : i.ker ≤ X.nilradical)
    (U : X.affineOpens) : RingHom.ker (i.app U.1).hom ≤ nilradical Γ(X, U.1) := by
  rw [← Scheme.Hom.ker_apply i U]
  exact Scheme.IdealSheafData.le_def.mp hker U

/-- **Units lift across a closed immersion whose kernel consists of nilpotents, over an affine
open.** Let `i : Z ⟶ X` be a closed immersion and `U` an affine open of `X` over which every
element of the kernel of `Γ(X, U) → Γ(Z, i⁻¹U)` is nilpotent. Then every unit of `Γ(Z, i⁻¹U)` is
the image of a unit of `Γ(X, U)`.

Affineness of `U` is what makes the map on sections surjective
(`AlgebraicGeometry.Scheme.Hom.app_surjective`); the nilradical bound is what makes a surjection
surject on units. The hypothesis is weaker than nilpotency of the kernel — see
`Stacks.LiftInvertible.exists_isUnit_of_ker_le_nilradical`. -/
theorem exists_units_app_eq (i : Z ⟶ X) [IsClosedImmersion i] {U : X.Opens}
    (hU : IsAffineOpen U) (hker : RingHom.ker (i.app U).hom ≤ nilradical Γ(X, U))
    (v : Γ(Z, i ⁻¹ᵁ U)ˣ) : ∃ w : Γ(X, U)ˣ, (i.app U).hom w.val = v.val := by
  obtain ⟨a, ha, hav⟩ :=
    exists_isUnit_of_ker_le_nilradical (i.app U).hom (i.app_surjective U hU) hker v.isUnit
  exact ⟨ha.unit, by simpa using hav⟩

/-- **Units lift across a closed immersion whose kernel consists of nilpotents, in the
`Units.map` spelling.** The restatement of `Stacks.LiftInvertible.exists_units_app_eq` that a
transition cocycle consumes, the transition data of
`Stacks.SheafOfModules.UnitTransitionCocycle` being written with `Units.map`. -/
theorem exists_unitsMap_app_eq (i : Z ⟶ X) [IsClosedImmersion i] {U : X.Opens}
    (hU : IsAffineOpen U) (hker : RingHom.ker (i.app U).hom ≤ nilradical Γ(X, U))
    (v : Γ(Z, i ⁻¹ᵁ U)ˣ) : ∃ w : Γ(X, U)ˣ, Units.map (i.app U).hom w = v :=
  (exists_units_app_eq i hU hker v).imp fun _ hw => Units.ext hw

/-- **Units lift across a surjective closed immersion, over any affine open.** The form of
`Stacks.LiftInvertible.exists_unitsMap_app_eq` whose hypothesis is a single global and purely
topological one: `i` is onto. A closed immersion is quasi-compact, so the kernel ideal over an
affine open is the kernel of the map on sections, and surjectivity puts it inside the
nilradical. -/
theorem exists_unitsMap_app_eq_of_surjective (i : Z ⟶ X) [IsClosedImmersion i]
    (hsurj : Function.Surjective i.base) (U : X.affineOpens) (v : Γ(Z, i ⁻¹ᵁ U.1)ˣ) :
    ∃ w : Γ(X, U.1)ˣ, Units.map (i.app U.1).hom w = v :=
  exists_unitsMap_app_eq i U.2
    (ker_app_le_nilradical i (ker_le_nilradical_of_surjective i hsurj) U) v

/-- **Units lift across a closed immersion with nilpotent ideal sheaf, over any affine open.**
The special case of `Stacks.LiftInvertible.exists_unitsMap_app_eq_of_surjective` in which the
ideal sheaf has a uniform nilpotency exponent. -/
theorem exists_unitsMap_app_eq_of_isNilpotent_ker (i : Z ⟶ X) [IsClosedImmersion i]
    (hnil : IsNilpotent i.ker) (U : X.affineOpens) (v : Γ(Z, i ⁻¹ᵁ U.1)ˣ) :
    ∃ w : Γ(X, U.1)ˣ, Units.map (i.app U.1).hom w = v :=
  exists_unitsMap_app_eq i U.2
    (ker_app_le_nilradical i (ker_le_nilradical_of_isNilpotent i hnil) U) v

end Stacks.LiftInvertible

end
