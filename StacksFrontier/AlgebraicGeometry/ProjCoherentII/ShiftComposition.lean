module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic

/-!
# `M(dn + q)~ = M(q)(dn)~`, and the splitting of a `ℤ`-indexed sum into residue classes

Two pieces of bookkeeping that the Veronese trick in the proof of [Stacks, Tag 0B5R] part (1)
rests on.

**The shift identification.** The source writes "Using the isomorphisms
`M(dn + q)~ = M(q)~(dn)` we can write `N' = ⨁_q ⨁_{dn + q ≥ k} H⁰(X, M(q)~(dn))`". The
identification has two halves, and only one of them is geometry:

* `M(q)(m) = M(m + q)` as *graded modules* — the gradings are literally the same family of
  subobjects, `i ↦ M_{i + m + q}`, written with the two additions associated the other way. This
  file proves it (`Stacks.GradedModule.shiftedGrading_shiftedGrading`) and propagates it to the
  associated sheaf and to the groups of global sections, where it becomes an *equality of types*:
  `H⁰(X, M(q)(m)~) = H⁰(X, M(m + q)~)`.
* `M(q)~(m) ≅ M(q)(m)~` — the comparison of the twisted sheaf with the sheaf of the shifted
  module. This is *not* an identity; it is Tag 01MU, and it is bijective on global sections only
  for `m` divisible by the `d` whose degree-`d` standard opens cover `Proj A`. That half is
  `Stacks.AlgebraicGeometry.ProjCoherentII.bijective_twistedToShiftedComponent`, i.e. part (6) of
  Tag 0B5R, and the instance of it this file records is the one the Veronese trick applies, at the
  shifted module `M(q)`.

Keeping the two apart is the point. The first is an equality and costs nothing at any `q` and `m`;
the second is where `d` is needed, and writing the pair as a single "isomorphism" hides that.

**The residue splitting.** `N'` is re-indexed by writing every integer uniquely as `d · n + q`
with `0 ≤ q < d`. `Stacks.GradedModule.intEquivResidue` is that bijection `Fin d × ℤ ≃ ℤ`, and
`Stacks.GradedModule.directSumEquivResidue` the resulting regrouping of a `ℤ`-indexed direct sum
into `d` sums over `ℤ`.

## Main definitions

* `Stacks.GradedModule.intEquivResidue`: `Fin d × ℤ ≃ ℤ`, `(q, n) ↦ d * n + q`.
* `Stacks.GradedModule.directSumEquivResidue`: the regrouping
  `⨁_{n ∈ ℤ} V n ≃+ ⨁_{(q, n)} V (d * n + q)`.

## Main results

* `Stacks.GradedModule.shiftedGrading_shiftedGrading`: `M(q)(m) = M(m + q)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_congr`: equal gradings give
  the same associated sheaf.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_shiftedGrading`:
  `M(q)(m)~ = M(m + q)~`.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent_shiftedGrading`:
  `H⁰(X, M(q)(m)~) = H⁰(X, M(m + q)~)`, as types.
* `Stacks.AlgebraicGeometry.ProjCoherentII.bijective_twistedToShiftedComponent_shiftedGrading`:
  part (6) at the shifted module, which is the geometric half of the source's identification.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` takes no
`DirectSum.Decomposition` argument, and its only other hypothesis on the grading,
`SetLike.GradedSMul`, is `Prop`-valued; so once the two gradings are equal the two instance
arguments are equal by proof irrelevance and the sheaves are equal, not merely isomorphic. That
is why `associatedModuleSheaf_congr` can be stated as an equality and closed by `subst` and
`rfl`, and why the sections identification is an equality of types rather than an `AddEquiv` that
would have to be carried through every formula.

`Stacks.GradedModule.intEquivResidue` takes the residue to be `k % d`, nonnegative and below `d`
because `d` is positive. One round trip is `Int.add_mul_emod_self_left` together with
`Int.add_mul_ediv_left`, after commuting the sum so that the multiple of `d` is on the right; the
other is `Int.emod_def`.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

universe u v w t

/-! ### `M(q)(m) = M(m + q)` -/

namespace Stacks.GradedModule

/-- **The shift of a shift is a shift.** The degree-`i` piece of `M(q)(m)` is `M_{(i + m) + q}`
and that of `M(m + q)` is `M_{i + (m + q)}`; the two families are equal. -/
theorem shiftedGrading_shiftedGrading {M : Type v} {τ : Type t} [SetLike τ M] (𝒨 : ℤ → τ)
    (q m : ℤ) : shiftedGrading (shiftedGrading 𝒨 q) m = shiftedGrading 𝒨 (m + q) :=
  funext fun i => congrArg 𝒨 (add_assoc i m q)

end Stacks.GradedModule

/-! ### The associated sheaf depends only on the grading -/

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M]

/-- **Equal gradings have the same associated sheaf.** The construction takes no decomposition
datum, and the compatibility `SetLike.GradedSMul` it does take is a proposition, so the two
instance arguments agree by proof irrelevance. -/
theorem associatedModuleSheaf_congr {𝒨₁ 𝒨₂ : ℤ → τ} [SetLike.GradedSMul 𝒜 𝒨₁]
    [SetLike.GradedSMul 𝒜 𝒨₂] (h : 𝒨₁ = 𝒨₂) :
    associatedModuleSheaf 𝒜 𝒨₁ = associatedModuleSheaf 𝒜 𝒨₂ := by
  subst h
  rfl

/-- **`M(q)(m)~ = M(m + q)~`**, the half of the source's identification that is an identity. -/
theorem associatedModuleSheaf_shiftedGrading (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒜 𝒨] (q m : ℤ) :
    associatedModuleSheaf 𝒜 (shiftedGrading (shiftedGrading 𝒨 q) m)
      = associatedModuleSheaf 𝒜 (shiftedGrading 𝒨 (m + q)) :=
  associatedModuleSheaf_congr 𝒜 (Stacks.GradedModule.shiftedGrading_shiftedGrading 𝒨 q m)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### The global sections of the two shifts are the same group -/

namespace Stacks.AlgebraicGeometry.ProjShiftedSections

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- **`H⁰(X, M(q)(m)~) = H⁰(X, M(m + q)~)`.** The two shifts have the same associated sheaf, so
their groups of global sections are the same group, not merely isomorphic ones. -/
theorem shiftedSectionsComponent_shiftedGrading (q m : ℤ) :
    shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q) m = shiftedSectionsComponent 𝒮 𝒨 (m + q) := by
  change ↥((associatedModuleSheaf 𝒮 (shiftedGrading (shiftedGrading 𝒨 q) m)).val.obj (op ⊤))
      = ↥((associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (m + q))).val.obj (op ⊤))
  rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_shiftedGrading]

end Stacks.AlgebraicGeometry.ProjShiftedSections

/-! ### Part (6) at the shifted module -/

namespace Stacks.AlgebraicGeometry.ProjCoherentII

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The geometric half of the source's identification, at the shifted module `M(q)`.** If the
standard opens of the homogeneous elements of degree `d` cover `Proj A` then for every `m`
divisible by `d` the comparison `H⁰(X, M(q)~(m)) → H⁰(X, M(q)(m)~)` is bijective; by
`Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent_shiftedGrading` its target
is `H⁰(X, M(m + q)~)`.

This is part (6) of Tag 0B5R applied to `M(q)`, which is the only place where the Veronese trick
of part (1) uses `d`. -/
theorem bijective_twistedToShiftedComponent_shiftedGrading
    {d : ℕ} (hd : AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) (q : ℤ) {m : ℤ}
    (hdm : (d : ℤ) ∣ m) :
    Function.Bijective (twistedToShiftedComponent 𝒮 (shiftedGrading 𝒨 q) m) :=
  bijective_twistedToShiftedComponent 𝒮 (shiftedGrading 𝒨 q) hd hdm

end Stacks.AlgebraicGeometry.ProjCoherentII

/-! ### Splitting a `ℤ`-indexed direct sum into residue classes -/

namespace Stacks.GradedModule

/-- **Division with remainder as a bijection** `Fin d × ℤ ≃ ℤ`, `(q, n) ↦ d * n + q`. This is the
re-indexing the Veronese trick of [Stacks, Tag 0B5R] part (1) performs on `N'`. -/
def intEquivResidue (d : ℕ) (hd : 0 < d) : Fin d × ℤ ≃ ℤ where
  toFun p := (d : ℤ) * (p.2 : ℤ) + (p.1 : ℕ)
  invFun k := (⟨(k % (d : ℤ)).toNat, by
      have h1 : (0 : ℤ) ≤ k % (d : ℤ) := Int.emod_nonneg k (by exact_mod_cast hd.ne')
      have h2 : k % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos k (by exact_mod_cast hd)
      omega⟩, k / (d : ℤ))
  left_inv p := by
    obtain ⟨⟨q, hq⟩, n⟩ := p
    have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    have hq' : ((q : ℕ) : ℤ) < (d : ℤ) := by exact_mod_cast hq
    have hq0 : (0 : ℤ) ≤ ((q : ℕ) : ℤ) := Int.natCast_nonneg q
    have hcomm : (d : ℤ) * n + ((q : ℕ) : ℤ) = ((q : ℕ) : ℤ) + (d : ℤ) * n := by ring
    have hmod : ((d : ℤ) * n + ((q : ℕ) : ℤ)) % (d : ℤ) = ((q : ℕ) : ℤ) := by
      rw [hcomm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hq0 hq']
    have hdiv : ((d : ℤ) * n + ((q : ℕ) : ℤ)) / (d : ℤ) = n := by
      rw [hcomm, Int.add_mul_ediv_left _ _ (by omega : (d : ℤ) ≠ 0),
        Int.ediv_eq_zero_of_lt hq0 hq', zero_add]
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    refine ⟨?_, hdiv⟩
    rw [hmod]
    omega
  right_inv k := by
    have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    have h1 : (0 : ℤ) ≤ k % (d : ℤ) := Int.emod_nonneg k (by omega)
    change (d : ℤ) * (k / (d : ℤ)) + (((k % (d : ℤ)).toNat : ℕ) : ℤ) = k
    rw [Int.toNat_of_nonneg h1, Int.emod_def]
    ring

/-- `intEquivResidue d hd` sends `(q, n)` to `d * n + q`. -/
@[simp] theorem intEquivResidue_apply (d : ℕ) (hd : 0 < d) (p : Fin d × ℤ) :
    intEquivResidue d hd p = (d : ℤ) * (p.2 : ℤ) + (p.1 : ℕ) := rfl

/-- **A `ℤ`-indexed direct sum regrouped by residue classes modulo `d`.** Every integer is
uniquely `d * n + q` with `0 ≤ q < d`, so the summands can be gathered into `d` families indexed
by `ℤ`. -/
def directSumEquivResidue (d : ℕ) (hd : 0 < d) (V : ℤ → Type*) [∀ n, AddCommGroup (V n)] :
    (⨁ n : ℤ, V n) ≃+ ⨁ p : Fin d × ℤ, V ((d : ℤ) * (p.2 : ℤ) + (p.1 : ℕ)) :=
  DirectSum.equivCongrLeft (β := V) (intEquivResidue d hd).symm

end Stacks.GradedModule

end
