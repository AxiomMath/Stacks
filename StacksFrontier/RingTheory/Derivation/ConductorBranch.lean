module

public import StacksFrontier.RingTheory.Derivation.ConductorGlobal

/-!
# The branch residues and the conductor at one node among several

`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor`
extends a `k`-derivation of `A` to the integral closure `A'` of `A` in a localization and makes
the extension fix the two branches of a node, from a generator `t'` of `A'` over `A`, a conductor
ideal `𝔠` carrying `t'` into `A`, and two residues `ε₁, ε₂ : A' →ₐ[k] k` agreeing on `A` with
`ε₁ t' - ε₂ t' = 1`. Its last hypothesis asks that *every* `b : A` killed by `ε₁` carry `t'` back
into `A`, that is

`ker (ε₁ ∘ algebraMap A A') ⊆ 𝔠`,

and that is exactly what a global curve with more than one node does not satisfy. The kernel is
the maximal ideal `𝔪` of the node under `ε₁`, while the conductor of `A` in `A'` is the product
`𝔪₁ ⋯ 𝔪ᵤ` of *all* the nodes, and `𝔪ᵢ ⊆ 𝔪₁ ⋯ 𝔪ᵤ` fails as soon as `u ≥ 2`: for two disjoint
nodal cubics, `A = A₁ × A₂` with `A₁ = A₂ = {h ∈ k[s] : h 1 = h (-1)}` and `A' = k[s] × k[s]`,
the element `(0, 1)` of `𝔪₁ = m × A₂` carries `(0, s) ∈ A'` to `(0, s) ∉ A`.

What survives, and is all the argument uses, is the same containment after multiplying by a
single element invertible at the node:

`α₀ ∉ 𝔪` and `α₀ · ker (ε₁ ∘ algebraMap A A') ⊆ 𝔠`.

On a curve with nodes `𝔪₁, …, 𝔪ᵤ` this holds with `α₀` any element of `∏_{j ≠ i} 𝔪ⱼ` outside
`𝔪ᵢ`, which exists because the nodes are distinct maximal ideals. For `u = 1` one may take
`α₀ = 1` and recover the original hypothesis. The step that needs the weakening is the one
deducing that a vector field vanishes at a node: from `ε₁ (D (α₀ b)) = 0` and the Leibniz rule,
`ε₁ α₀ · ε₁ (D b) + ε₁ b · ε₁ (D α₀) = 0`, and the second summand vanishes because `b` is killed
by `ε₁`, so `ε₁ (D b) = 0` as `ε₁ α₀ ≠ 0`.

## Main results

* `Stacks.DerivationExtension.apply_eq_zero_of_mul_eq_of_mul` — a `k`-derivation of `A` is killed
  by the residue at a branch point, with the conductor condition weakened by a factor invertible
  at the node.
* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor_mul`
  — the extension and the fixing of both branches, under that weakened condition.

## Implementation notes

Nothing here assumes `A` local, and no element of `A'` is assumed invertible. The two statements
are the strict generalizations of
`Stacks.DerivationExtension.apply_eq_zero_of_mul_eq` and
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor`
obtained by taking `α₀ = 1`, and the proofs are those proofs with the single extra Leibniz step.

No `@[stacks]` tag is carried here: this is machinery for item (3) of Stacks 0E68, not a
statement of any of its items.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.DerivationExtension

section Branch

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

omit [IsLocalization (nonZeroDivisors A) L] in
/-- **One element of the conductor at a time.** If `b : A` is killed by `ε₁` and `b t'` already
lies in the image of `A`, then `ε₁` kills `D b`.

This is the inner step of `Stacks.DerivationExtension.apply_eq_zero_of_mul_eq`, isolated so that
it can be fed an element of the conductor other than `b` itself. -/
private theorem apply_eq_zero_of_mul_eq_aux (D : Derivation k A A)
    (D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L))
    (hD' : ∀ b : A, D' (algebraMap A ↥(integralClosure A L) b) =
      algebraMap A ↥(integralClosure A L) (D b))
    (t' : ↥(integralClosure A L)) (ε₁ ε₂ : ↥(integralClosure A L) →ₐ[k] k)
    (hres : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) =
      ε₂ (algebraMap A ↥(integralClosure A L) b))
    (hne : ε₁ t' - ε₂ t' = 1)
    (b : A) (hb : ε₁ (algebraMap A ↥(integralClosure A L) b) = 0)
    (b'' : A) (hb'' : algebraMap A ↥(integralClosure A L) b * t' =
      algebraMap A ↥(integralClosure A L) b'') :
    ε₁ (algebraMap A ↥(integralClosure A L) (D b)) = 0 := by
  have hb' : ε₂ (algebraMap A ↥(integralClosure A L) b) = 0 := by rw [← hres b, hb]
  have hDb : D' (algebraMap A ↥(integralClosure A L) b * t') =
      algebraMap A ↥(integralClosure A L) (D b'') := by rw [hb'', hD']
  have hDl : D' (algebraMap A ↥(integralClosure A L) b * t') =
      algebraMap A ↥(integralClosure A L) b * D' t' +
        t' * algebraMap A ↥(integralClosure A L) (D b) := by
    rw [D'.leibniz, hD']
    simp only [smul_eq_mul]
  have e : ∀ ε : ↥(integralClosure A L) →ₐ[k] k,
      ε (algebraMap A ↥(integralClosure A L) b) = 0 →
      ε t' * ε (algebraMap A ↥(integralClosure A L) (D b)) =
        ε (algebraMap A ↥(integralClosure A L) (D b'')) := by
    intro ε hε
    rw [← hDb, hDl, map_add, map_mul, map_mul, hε]
    ring
  have e₁ := e ε₁ hb
  have e₂ := e ε₂ hb'
  rw [← hres (D b), ← hres (D b'')] at e₂
  have hfin : (ε₁ t' - ε₂ t') * ε₁ (algebraMap A ↥(integralClosure A L) (D b)) = 0 := by
    linear_combination e₁ - e₂
  rwa [hne, one_mul] at hfin

omit [IsLocalization (nonZeroDivisors A) L] in
/-- **A `k`-derivation of `A` is killed by the residue at a branch point, with the conductor
condition weakened by a factor invertible at the node.** Let `ε₁, ε₂ : A' → k` be two `k`-algebra
maps agreeing on `A` with `ε₁ t' - ε₂ t' = 1`, and let `α₀ : A` be an element *not* killed by
`ε₁` such that for every `b : A` killed by `ε₁` the product `α₀ b` carries `t'` back into the
image of `A`. Then `ε₁` kills `D b` for every `b : A`: a vector field vanishes at the node.

This is `Stacks.DerivationExtension.apply_eq_zero_of_mul_eq` with the hypothesis that the ideal
of the node lie in the conductor replaced by the hypothesis that it do so after multiplication by
one element invertible at the node. The extra step is the Leibniz rule: `ε₁` kills `D (α₀ b)`,
which is `ε₁ α₀ · ε₁ (D b) + ε₁ b · ε₁ (D α₀)`, and the second summand vanishes. -/
public theorem apply_eq_zero_of_mul_eq_of_mul (D : Derivation k A A)
    (D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L))
    (hD' : ∀ b : A, D' (algebraMap A ↥(integralClosure A L) b) =
      algebraMap A ↥(integralClosure A L) (D b))
    (t' : ↥(integralClosure A L)) (ε₁ ε₂ : ↥(integralClosure A L) →ₐ[k] k)
    (hres : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) =
      ε₂ (algebraMap A ↥(integralClosure A L) b))
    (hne : ε₁ t' - ε₂ t' = 1)
    (α₀ : A) (hα₀ : ε₁ (algebraMap A ↥(integralClosure A L) α₀) ≠ 0)
    (hcond : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) = 0 →
      ∃ b' : A, algebraMap A ↥(integralClosure A L) (α₀ * b) * t' =
        algebraMap A ↥(integralClosure A L) b')
    (b : A) : ε₁ (algebraMap A ↥(integralClosure A L) (D b)) = 0 := by
  have hkey : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) = 0 →
      ε₁ (algebraMap A ↥(integralClosure A L) (D b)) = 0 := by
    intro b hb
    have hαb : ε₁ (algebraMap A ↥(integralClosure A L) (α₀ * b)) = 0 := by
      rw [map_mul, map_mul, hb, mul_zero]
    obtain ⟨b'', hb''⟩ := hcond b hb
    have h := apply_eq_zero_of_mul_eq_aux D D' hD' t' ε₁ ε₂ hres hne (α₀ * b) hαb b'' hb''
    have hle : D (α₀ * b) = α₀ * D b + b * D α₀ := by
      rw [D.leibniz]
      simp only [smul_eq_mul]
    rw [hle] at h
    simp only [map_add, map_mul, hb, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hα₀
  have h := hkey (b - algebraMap k A (ε₁ (algebraMap A ↥(integralClosure A L) b))) ?_
  · rwa [map_sub, Derivation.map_algebraMap, sub_zero] at h
  · rw [map_sub, map_sub, apply_algebraMap_algebraMap, sub_self]

/-- **The extension and the fixing of both branches at one node among several.** Let the integral
closure `A'` of `A` in the localization be generated over `A` by a single `t'` with
`t' ^ 2 = a + c t'`; let `𝔠` be an ideal of `A` every element of which carries `t'` back into `A`;
suppose only finitely many maximal ideals of `A'` contain `u = 2 t' - c` and none of them
contracts to an ideal containing `𝔠`; and let `ε₁, ε₂ : A' → k` agree on `A` with
`ε₁ t' - ε₂ t' = 1` and be such that for some `α₀ : A` outside the kernel of `ε₁` the product
`α₀ · ker (ε₁ ∘ algebraMap A A')` lies in `𝔠`. Then every `k`-derivation of `A` extends uniquely
to `A'`, and the extension is killed by both residues, so it fixes both points above the node.

This is
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor` with
the containment `ker (ε₁ ∘ algebraMap A A') ⊆ 𝔠` — which on a curve with more than one node is
false, the conductor being the product of *all* the nodes — weakened to that containment after
multiplication by one element invertible at the node. `A` is not assumed local, and no element
is assumed invertible. -/
public theorem existsUnique_extend_integralClosure_apply_eq_zero_of_conductor_mul
    (D : Derivation k A A) (t' : ↥(integralClosure A L)) (a c : A) (𝔠 : Ideal A)
    (hS : Algebra.adjoin A ({(t' : L)} : Set L) = integralClosure A L)
    (hrel : t' * t' = algebraMap A ↥(integralClosure A L) a +
      algebraMap A ↥(integralClosure A L) c * t')
    (hcond : ∀ α ∈ 𝔠, ∃ β : A, algebraMap A ↥(integralClosure A L) α * t' =
      algebraMap A ↥(integralClosure A L) β)
    (hfin : {m : Ideal ↥(integralClosure A L) | m.IsMaximal ∧
      t' + t' - algebraMap A ↥(integralClosure A L) c ∈ m}.Finite)
    (hnode : ∀ m : Ideal ↥(integralClosure A L), m.IsMaximal →
      t' + t' - algebraMap A ↥(integralClosure A L) c ∈ m →
      ¬ 𝔠 ≤ Ideal.comap (algebraMap A ↥(integralClosure A L)) m)
    (ε₁ ε₂ : ↥(integralClosure A L) →ₐ[k] k)
    (hres : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) =
      ε₂ (algebraMap A ↥(integralClosure A L) b))
    (hne : ε₁ t' - ε₂ t' = 1)
    (α₀ : A) (hα₀ : ε₁ (algebraMap A ↥(integralClosure A L) α₀) ≠ 0)
    (hcondε : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) = 0 → α₀ * b ∈ 𝔠) :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      (∀ b : A, D' (algebraMap A ↥(integralClosure A L) b) =
          algebraMap A ↥(integralClosure A L) (D b)) ∧
        (∀ s, ε₁ (D' s) = 0) ∧ (∀ s, ε₂ (D' s) = 0) := by
  -- prime avoidance supplies a conductor element comaximal with `u`
  obtain ⟨α, hα𝔠, w₁, w₂, hcomb⟩ := exists_mem_mul_add_mul_eq_one_of_finite 𝔠
    (t' + t' - algebraMap A ↥(integralClosure A L) c) hfin hnode
  obtain ⟨β, hβ⟩ := hcond α hα𝔠
  -- the data, read in the localization
  have hrelL : (t' : L) * (t' : L) =
      algebraMap A L a + algebraMap A L c * (t' : L) := by
    have h := congrArg (fun z : ↥(integralClosure A L) => (z : L)) hrel
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_integralClosure] using h
  have hcondL : algebraMap A L α * (t' : L) = algebraMap A L β := by
    have h := congrArg (fun z : ↥(integralClosure A L) => (z : L)) hβ
    simpa only [Subalgebra.coe_mul, coe_algebraMap_integralClosure] using h
  have hcombL : (w₁ : L) * algebraMap A L α +
      (w₂ : L) * ((t' : L) + (t' : L) - algebraMap A L c) = 1 := by
    have h := congrArg (fun z : ↥(integralClosure A L) => (z : L)) hcomb
    simpa only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub,
      Subalgebra.coe_one, coe_algebraMap_integralClosure] using h
  -- the conductor element is killed by the residues, so `u` is not
  have hα : ε₁ (algebraMap A ↥(integralClosure A L) α) = 0 := by
    have h₁ := congrArg ε₁ hβ
    have h₂ := congrArg ε₂ hβ
    rw [map_mul] at h₁ h₂
    rw [← hres α, ← hres β] at h₂
    have hz : ε₁ (algebraMap A ↥(integralClosure A L) α) * (ε₁ t' - ε₂ t') = 0 := by
      linear_combination h₁ - h₂
    rwa [hne, mul_one] at hz
  have hu : ∀ ε : ↥(integralClosure A L) →ₐ[k] k,
      ε (algebraMap A ↥(integralClosure A L) α) = 0 →
      ε (t' + t' - algebraMap A ↥(integralClosure A L) c) ≠ 0 := by
    intro ε hε h0
    have h := congrArg ε hcomb
    rw [map_add, map_mul, map_mul, hε, h0, mul_zero, mul_zero, add_zero, map_one] at h
    exact zero_ne_one h
  obtain ⟨D', hD', huniq⟩ := existsUnique_extend_integralClosure_of_quadratic_conductor D
    (t' : L) a c α β hS hrelL hcondL w₁.2 w₂.2 hcombL
  have hεD : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) (D b)) = 0 :=
    apply_eq_zero_of_mul_eq_of_mul D D' hD' t' ε₁ ε₂ hres hne α₀ hα₀
      fun b hb => hcond (α₀ * b) (hcondε b hb)
  have hεD₂ : ∀ b : A, ε₂ (algebraMap A ↥(integralClosure A L) (D b)) = 0 := by
    intro b
    rw [← hres (D b)]
    exact hεD b
  exact ⟨D', ⟨hD',
    apply_extension_eq_zero_of_quadratic D D' hD' t' a c hS hrel ε₁ hεD (hu ε₁ hα),
    apply_extension_eq_zero_of_quadratic D D' hD' t' a c hS hrel ε₂ hεD₂
      (hu ε₂ (by rw [← hres α]; exact hα))⟩,
    fun E hE => huniq E hE.1⟩

end Branch

end Stacks.DerivationExtension

end
