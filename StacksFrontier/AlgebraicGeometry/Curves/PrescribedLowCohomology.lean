module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingTwistWithSection
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules with prescribed low-degree cohomology on a proper curve

Let `k` be an algebraically closed field and let `X` be a proper curve over `k`.
[Stacks, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z) asserts that there exist

1. an invertible `𝒪_X`-module `ℒ` with `dim_k H⁰(X, ℒ) = 1` and `H¹(X, ℒ) = 0`, and
2. an invertible `𝒪_X`-module `𝒩` with `H⁰(X, 𝒩) = 0` and `H¹(X, 𝒩) = 0`.

Both are proved here, from the source's own argument and at the source's own hypotheses: a
descending induction on `t = dim_k H⁰(X, ℒ)` which twists down by the ideal sheaf of a
nonsingular closed point.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_zero_add_one_eq_of_shortExact`: the
  cohomological heart of the induction step. For a short exact sequence
  `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `H¹(X, ℱ₂) = 0`, with `dim_k H⁰(X, ℱ₃) = 1` and with some class
  of `H⁰(X, ℱ₂)` having nonzero image in `H⁰(X, ℱ₃)`, one has
  `dim_k H⁰(X, ℱ₁) + 1 = dim_k H⁰(X, ℱ₂)` and `H¹(X, ℱ₁) = 0`.
* `AlgebraicGeometry.exists_invertible_finrank_cohomologyOverField_zero_eq_one`:
  **[Stacks, Tag 0B8Z], assertion (1).**
* `AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_zero_one`:
  **[Stacks, Tag 0B8Z], assertion (2).**

## Implementation notes

**Spellings.** Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible` at the structure
sheaf of `X` ([Stacks, Tag 01CS]), in the argument shape `X.sheaf.obj`,
`X.ringCatSheaf.property` that the Chapter 31 divisor API uses. `dim_k Hⁱ(X, ℱ)` is
`Module.finrank k (AlgebraicGeometry.cohomologyOverField k f ℱ i)` ([Stacks, Tag 0BEF]) and
vanishing is `CategoryTheory.Limits.IsZero`, as in
`StacksFrontier/AlgebraicGeometry/Curves/GenusZeroPositiveDegree/Basic.lean`. Assertion (2) is
stated as the vanishing of `H⁰` rather than as `dim_k H⁰ = 0`, which is the stronger reading:
a `Module.finrank` is zero on a module that is merely not finite-dimensional. The finite
dimensionality needed to make the two agree is *proved* along the induction, from the injection
of `H⁰(X, ℱ₁)` into `H⁰(X, ℱ₂)`, and is not assumed.

**The two halves of the source's proof, and where each is.**

* **The start.** The source produces an invertible `ℒ₀` with `H¹(X, ℒ₀) = 0` and
  `H⁰(X, ℒ₀) ≠ 0` from a closed immersion `X ⟶ 𝐏ⁿ_k` ([Stacks, Tag 0A26]) followed by
  `ℒ₀ = i^* 𝒪(d)` for `d ≫ 0` and the vanishing of [Stacks, Tag 0B5U]. That is
  `AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank` in
  `StacksFrontier/AlgebraicGeometry/Curves/VanishingTwistWithSection.lean`, where the projective
  embedding is bypassed: only the *ampleness* of such an `ℒ₀` is used, and on an integral curve
  an ample invertible module comes directly from [Stacks, Tag 09ND].
* **The geometric step.** The source's `0 ⟶ ℐ ⊗ ℒ ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` for the ideal sheaf of a
  nonsingular closed point at which a chosen section does not vanish, together with the
  `k`-rationality of that point, is `AlgebraicGeometry.exists_pointTwistDown` in
  `StacksFrontier/AlgebraicGeometry/Curves/PointTwistDown.lean`.

What is left here is the cohomology: that the descending induction drops `dim_k H⁰` by exactly
one at each step and keeps `H¹` zero, which is
`AlgebraicGeometry.finrank_cohomologyOverField_zero_add_one_eq_of_shortExact`, proved from the
long exact sequence `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`
([Stacks, Tag 010Q]); and that it terminates at `t = 1` for assertion (1) and at `t = 0` for
assertion (2).

## References

* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### A linear map hitting a nonzero vector of a line is surjective -/

/-- A linear map into a one-dimensional space which takes some value `≠ 0` is surjective: a
nonzero vector of a line spans it. -/
private theorem surjective_of_finrank_eq_one {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (φ : M →ₗ[k] N) (hN : Module.finrank k N = 1) {a : M}
    (ha : φ a ≠ 0) : Function.Surjective φ := by
  intro y
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ a) ha).mp hN y
  exact ⟨c • a, by rw [map_smul, hc]⟩

/-! ### The cohomological step -/

/-- **The cohomological heart of the induction of [Stacks, Tag 0B8Z]**. Let
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of modules on a scheme over `k` with
`H⁰(X, ℱ₂)` finite-dimensional and `H¹(X, ℱ₂) = 0`, let `dim_k H⁰(X, ℱ₃) = 1` and suppose some
class of `H⁰(X, ℱ₂)` has nonzero image in `H⁰(X, ℱ₃)`. Then `H⁰(X, ℱ₂) ⟶ H⁰(X, ℱ₃)` is onto,
so `dim_k H⁰(X, ℱ₁) + 1 = dim_k H⁰(X, ℱ₂)`, and `H¹(X, ℱ₁) = 0` because the connecting map out
of `H⁰(X, ℱ₃)` is both surjective — its cokernel injects into `H¹(X, ℱ₂) = 0` — and zero.

`H⁰(X, ℱ₁)` is finite-dimensional as well, since it injects into `H⁰(X, ℱ₂)`; this is what makes
the vanishing of `H⁰` in assertion (2) of the tag, rather than only its dimension, available at
the end of the induction. -/
theorem finrank_cohomologyOverField_zero_add_one_eq_of_shortExact
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hfd : FiniteDimensional k (cohomologyOverField k f S.X₂ 0))
    (hone : Module.finrank k (cohomologyOverField k f S.X₃ 0) = 1)
    (hvan : IsZero (cohomologyOverField k f S.X₂ 1))
    {a : cohomologyOverField k f S.X₂ 0} (ha : cohomologyOverFieldMap k f S.g 0 a ≠ 0) :
    Module.finrank k (cohomologyOverField k f S.X₁ 0) + 1
        = Module.finrank k (cohomologyOverField k f S.X₂ 0) ∧
      IsZero (cohomologyOverField k f S.X₁ 1) ∧
      FiniteDimensional k (cohomologyOverField k f S.X₁ 0) := by
  obtain ⟨d, hinj, hab, hbc, hca⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have _ := hfd
  have honto : Function.Surjective (cohomologyOverFieldMap k f S.g 0).hom :=
    surjective_of_finrank_eq_one k _ hone ha
  have hfd₁ : FiniteDimensional k (cohomologyOverField k f S.X₁ 0) :=
    .of_injective (cohomologyOverFieldMap k f S.f 0).hom hinj
  refine ⟨?_, ?_, hfd₁⟩
  · have hker : LinearMap.ker (cohomologyOverFieldMap k f S.g 0).hom
        = LinearMap.range (cohomologyOverFieldMap k f S.f 0).hom :=
      LinearMap.exact_iff.mp (hab 0)
    have hrk := LinearMap.finrank_range_add_finrank_ker (cohomologyOverFieldMap k f S.g 0).hom
    rw [LinearMap.range_eq_top.mpr honto, finrank_top, hker,
      LinearMap.finrank_range_of_inj hinj, hone] at hrk
    lia
  · have _ := ModuleCat.subsingleton_of_isZero hvan
    have key : ∀ z : (cohomologyOverField k f S.X₁ 1 : Type u), z = 0 := by
      intro z
      obtain ⟨w, hw⟩ := (hca 0 z).1 (Subsingleton.elim _ _)
      obtain ⟨v, hv⟩ := honto w
      rw [← hw, ← hv]
      exact (hbc 0).apply_apply_eq_zero v
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun z z' => by rw [key z, key z']⟩

/-! ### The geometric step, carried -/

/-- **The geometric step of the induction of [Stacks, Tag 0B8Z]**, as a property of
`f : X ⟶ Spec k`: twisting down by a closed point at which a given section does not vanish.

For every invertible `ℒ` with `dim_k H⁰(X, ℒ) > 0` there are a closed immersion `i : Z ⟶ X`, an
invertible `ℒ'` and a short exact sequence `0 ⟶ ℒ' ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` such that
`dim_k H⁰(Z, i^* ℒ) = 1` and some class of `H⁰(X, ℒ)` has nonzero image in `H⁰(X, i_* i^* ℒ)`.
On a proper curve over an algebraically closed field this holds by
`AlgebraicGeometry.exists_pointTwistDown`, with `ℒ' = ℐ ⊗ ℒ` for `ℐ` the ideal sheaf of a
nonsingular closed point. -/
public def HasPointTwistDown (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ L : X.Modules, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
    0 < Module.finrank k (cohomologyOverField k f L 0) →
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (L' : X.Modules) (α : L' ⟶ L)
      (β : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L))
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
        SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
        Module.finrank k
            (cohomologyOverField k (i ≫ f) ((Scheme.Modules.pullback i).obj L) 0) = 1 ∧
        ∃ a, cohomologyOverFieldMap k f β 0 a ≠ 0

/-! ### The induction -/

/-- One step of the descending induction: from an invertible `ℒ` with `H¹(X, ℒ) = 0` and a
nonzero global section, an invertible `ℒ'` with `dim_k H⁰(X, ℒ') + 1 = dim_k H⁰(X, ℒ)` and
`H¹(X, ℒ') = 0`. The geometry comes from `AlgebraicGeometry.exists_pointTwistDown` and the
cohomology from `AlgebraicGeometry.finrank_cohomologyOverField_zero_add_one_eq_of_shortExact`;
the dimension count on the point is transported from `Z` to `X` along
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`. -/
private theorem exists_invertible_finrank_add_one_eq [IsAlgClosed k] [IsProper f] [IsCurve k f]
    (L : X.Modules) (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hvan : IsZero (cohomologyOverField k f L 1))
    (hpos : 0 < Module.finrank k (cohomologyOverField k f L 0)) :
    ∃ L' : X.Modules, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
      Module.finrank k (cohomologyOverField k f L' 0) + 1
          = Module.finrank k (cohomologyOverField k f L 0) ∧
        IsZero (cohomologyOverField k f L' 1) ∧
        FiniteDimensional k (cohomologyOverField k f L' 0) := by
  obtain ⟨Z, i, hi, L', α, β, w, hSE, hL', hone, a, ha⟩ := exists_pointTwistDown k f L hL hpos
  have _ := hi
  have hone' : Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L)) 0) = 1 := by
    rw [← (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f
      ((Scheme.Modules.pullback i).obj L) 0).toLinearEquiv.finrank_eq]
    exact hone
  obtain ⟨hrk, hv, hfd⟩ := finrank_cohomologyOverField_zero_add_one_eq_of_shortExact k f hSE
    (FiniteDimensional.of_finrank_pos hpos) hone' hvan ha
  exact ⟨L', hL', hrk, hv, hfd⟩

/-- Iterating `AlgebraicGeometry.exists_invertible_finrank_add_one_eq`: from an invertible module
with `H¹ = 0` whose `H⁰` has dimension `m + n` one reaches, in `n` steps, an invertible module
with `H¹ = 0` whose `H⁰` has dimension exactly `m`. Finite dimensionality of `H⁰` is carried
along, so that the endpoint `m = 0` gives the vanishing of `H⁰` and not merely `dim_k H⁰ = 0`. -/
private theorem exists_invertible_finrank_eq_of_finrank_eq_add [IsAlgClosed k] [IsProper f]
    [IsCurve k f] (m : ℕ) :
    ∀ (n : ℕ) (L : X.Modules),
      SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
      IsZero (cohomologyOverField k f L 1) →
      FiniteDimensional k (cohomologyOverField k f L 0) →
      Module.finrank k (cohomologyOverField k f L 0) = m + n →
      ∃ L' : X.Modules, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
        Module.finrank k (cohomologyOverField k f L' 0) = m ∧
          IsZero (cohomologyOverField k f L' 1) ∧
          FiniteDimensional k (cohomologyOverField k f L' 0) := by
  intro n
  induction n with
  | zero => exact fun L hL hvan hfd hrk => ⟨L, hL, by simpa using hrk, hvan, hfd⟩
  | succ n ih =>
    intro L hL hvan _ hrk
    obtain ⟨L', hL', hrk', hvan', hfd'⟩ :=
      exists_invertible_finrank_add_one_eq k f L hL hvan (by lia)
    exact ih L' hL' hvan' hfd' (by lia)

/-! ### Tag 0B8Z -/

/-- **[Stacks, Tag 0B8Z], assertion (1).** On a proper curve over an algebraically closed field
there is an invertible module `ℒ` with `dim_k H⁰(X, ℒ) = 1` and `H¹(X, ℒ) = 0`.

Starting from an invertible module with vanishing `H¹` and a nonzero global section
(`AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank`) and
twisting down `dim_k H⁰(X, ℒ₀) - 1` times by
`AlgebraicGeometry.exists_pointTwistDown`, each step lowering `dim_k H⁰` by one and preserving
the vanishing of `H¹`. -/
@[stacks 0B8Z "assertion (1)"]
public theorem exists_invertible_finrank_cohomologyOverField_zero_eq_one [IsAlgClosed k]
    [IsProper f] [IsCurve k f] :
    ∃ L : X.Modules, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L ∧
      Module.finrank k (cohomologyOverField k f L 0) = 1 ∧
        IsZero (cohomologyOverField k f L 1) := by
  obtain ⟨L₀, hL₀, hvan₀, hpos₀⟩ :=
    exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank k f
  obtain ⟨L, hL, hrk, hvan, _⟩ := exists_invertible_finrank_eq_of_finrank_eq_add k f 1
    (Module.finrank k (cohomologyOverField k f L₀ 0) - 1) L₀ hL₀ hvan₀
    (FiniteDimensional.of_finrank_pos hpos₀) (by lia)
  exact ⟨L, hL, hrk, hvan⟩

/-- **[Stacks, Tag 0B8Z], assertion (2).** On a proper curve over an algebraically closed field
there is an invertible module `𝒩` with `H⁰(X, 𝒩) = 0` and `H¹(X, 𝒩) = 0`.

The same descent as for assertion (1), run one step further, down to `dim_k H⁰ = 0`; the
vanishing of `H⁰` — rather than only its dimension — comes from the finite dimensionality
carried along the induction. -/
@[stacks 0B8Z "assertion (2), the vanishing of both `H⁰` and `H¹`"]
public theorem exists_invertible_isZero_cohomologyOverField_zero_one [IsAlgClosed k] [IsProper f]
    [IsCurve k f] :
    ∃ N : X.Modules, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N ∧
      IsZero (cohomologyOverField k f N 0) ∧ IsZero (cohomologyOverField k f N 1) := by
  obtain ⟨L₀, hL₀, hvan₀, hpos₀⟩ :=
    exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank k f
  obtain ⟨N, hN, hrk, hvan, hfd⟩ := exists_invertible_finrank_eq_of_finrank_eq_add k f 0
    (Module.finrank k (cohomologyOverField k f L₀ 0)) L₀ hL₀ hvan₀
    (FiniteDimensional.of_finrank_pos hpos₀) (by lia)
  have _ := hfd
  exact ⟨N, hN, ModuleCat.isZero_iff_subsingleton.mpr (Module.finrank_zero_iff.mp hrk), hvan⟩

end AlgebraicGeometry

end
