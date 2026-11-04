module

public import StacksFrontier.RingTheory.CyclicComaximal
public import StacksFrontier.RingTheory.Derivation.ConductorRelation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A single generator of the integral closure, and a conductor element comaximal with `2 t - c`

`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_forall_isMaximal`
extends a `k`-derivation of `A` to the integral closure `A'` of `A` in a localization, and makes
the extension fix the two branches of a node, from three pieces of data:

1. a single `t : A'` with `A [t] = A'` (the quadratic relation `t ^ 2 = a + c t` is then
   automatic, since `t ^ 2 ∈ A' = A + A t`);
2. a conductor element `α : A`, that is one with `α t ∈ A`, comaximal in `A'` with `2 t - c`;
3. two residues `ε₁, ε₂ : A' →ₐ[k] k` agreeing on `A` with `ε₁ t - ε₂ t = 1` and with
   `ker (ε₁ ∘ algebraMap A A')` inside the conductor.

This file supplies (1) and (2) from data attached to the *finitely many* singular points, with
no locality hypothesis anywhere.

For (1) the point is that `A' / A` is a module supported at the nodes, so the Chinese remainder
theorem assembles one generator per node into a single global generator
(`Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top`). This is **not** an instance of
"locally cyclic implies cyclic", which is false; it works because the support is a finite set of
comaximal maximal ideals, so that `A' / A` is the direct sum of its pieces there.

For (2) the point is prime avoidance. The element `u = 2 t - c` is not a unit of `A'` — it cannot
be, since `u ^ 2` is the image of an element of `A`
(`Stacks.DerivationExtension.sq_two_mul_sub_algebraMap`), so a unit `u` would force an element of
`A` to vanish nowhere on `Spec A'`, which on an affine curve it does not. What is true is that
`u` is comaximal with the conductor: `u` is invertible at the points above a node, so the
finitely many maximal ideals of `A'` containing `u` do not contain the conductor, and prime
avoidance produces a single `α` in the conductor outside all of them.

## Main results

* `Stacks.DerivationExtension.exists_add_mul_of_sup_span_eq_top` — if the image of `A` together
  with one element `t` spans `A'` as an `A`-module, every element of `A'` is `a₀ + a₁ t`.
* `Stacks.DerivationExtension.adjoin_eq_integralClosure_of_sup_span_eq_top` — hence
  `A [t] = A'`, which is hypothesis (1).
* `Stacks.DerivationExtension.exists_quadratic_of_sup_span_eq_top` — and the quadratic relation
  comes for free.
* `Stacks.DerivationExtension.exists_adjoin_eq_integralClosure_of_comaximal` — **item (1) from
  node-local data**: finitely many pairwise comaximal ideals whose product carries `A'` into `A`,
  and modulo each of which `A'` is `A` plus one element, give a single global generator together
  with its quadratic relation.
* `Stacks.DerivationExtension.exists_adjoin_eq_integralClosure_of_isCoatom` — the same with the
  per-node hypothesis written as the simplicity of `A' / (A + Iᵢ A')`, which is the global form
  of `Ring.deltaInvariant = 1`.
* `Stacks.DerivationExtension.exists_mem_forall_notMem_of_finite` — prime avoidance over a
  finite family of primes.
* `Stacks.DerivationExtension.exists_mem_mul_add_mul_eq_one_of_finite` — **item (2)**: an element
  of a given ideal of `A` comaximal in `A'` with a given `u`, as soon as only finitely many
  maximal ideals of `A'` contain `u` and none of them contracts to an ideal containing the given
  one.
* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor` —
  the extension and the fixing of both branches, with the comaximality replaced by the conductor
  ideal and the finiteness of the zero locus of `u`.

## Implementation notes

The `A`-module structure in which (1) is stated is the one on the subalgebra `A'` itself, and the
image of `A` is `LinearMap.range (Algebra.linearMap A A')`; the statement
`range ⊔ span {t} = ⊤` is therefore literally "`A' = A + A t`".

Nothing here is registered against Tag 0E68. The data of items (1) and (2) is reduced to
statements at the finitely many singular points, but producing those statements for
`A = Γ(X, U)` on a nodal curve — which needs the localization of the integral closure at a node
to be the integral closure of the localization, and the node locus to be finite — is not done
here, and (3) is not produced at all.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 00DT](https://stacks.math.columbia.edu/tag/00DT)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.DerivationExtension

section Monogenic

variable {A : Type v} {L : Type w} [CommRing A] [CommRing L] [Algebra A L]

/-- **`A' = A + A t` read elementwise.** If the image of `A` in the integral closure together
with a single element `t` spans it as an `A`-module, then every element of the integral closure
is `a₀ + a₁ t` with `a₀, a₁ : A`. -/
public theorem exists_add_mul_of_sup_span_eq_top (t : ↥(integralClosure A L))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {t} = ⊤)
    {z : L} (hz : z ∈ integralClosure A L) :
    ∃ a₀ a₁ : A, z = algebraMap A L a₀ + algebraMap A L a₁ * (t : L) := by
  have hmem : (⟨z, hz⟩ : ↥(integralClosure A L)) ∈
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
        Submodule.span A {t} := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a₀, rfl⟩ := hp
  obtain ⟨a₁, rfl⟩ := Submodule.mem_span_singleton.mp hq
  refine ⟨a₀, a₁, ?_⟩
  have hc := congrArg (fun w : ↥(integralClosure A L) => (w : L)) hpq
  simp only [Algebra.linearMap_apply, Algebra.smul_def, Subalgebra.coe_add, Subalgebra.coe_mul,
    coe_algebraMap_integralClosure] at hc
  exact hc.symm

/-- **A single generator of the integral closure.** If the image of `A` together with `t` spans
the integral closure as an `A`-module, then `t` generates it as an `A`-algebra. This is the
hypothesis `hS` of
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_forall_isMaximal`
and of `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_quadratic_conductor`. -/
public theorem adjoin_eq_integralClosure_of_sup_span_eq_top (t : ↥(integralClosure A L))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {t} = ⊤) :
    Algebra.adjoin A ({(t : L)} : Set L) = integralClosure A L := by
  refine le_antisymm (Algebra.adjoin_le ?_) fun z hz => ?_
  · rw [Set.singleton_subset_iff]
    exact t.2
  · obtain ⟨a₀, a₁, rfl⟩ := exists_add_mul_of_sup_span_eq_top t hspan hz
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Set.mem_singleton _)))

/-- An equation `x = a₀ + a₁ t` in the integral closure holds iff it holds after coercion to `L`. -/
private theorem eq_add_mul_iff_coe_eq (x t : ↥(integralClosure A L)) (a₀ a₁ : A) :
    x = algebraMap A ↥(integralClosure A L) a₀ + algebraMap A ↥(integralClosure A L) a₁ * t ↔
      (x : L) = algebraMap A L a₀ + algebraMap A L a₁ * (t : L) := by
  rw [Subtype.ext_iff]
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, coe_algebraMap_integralClosure]

/-- **The quadratic relation is automatic.** A generator of the integral closure over `A` as a
module satisfies `t ^ 2 = a + c t` with `a, c : A`, because `t ^ 2` is again an element of the
integral closure and therefore of `A + A t`. So the quadratic shape in which the normalization
of a node presents itself costs nothing once a single generator is available. -/
public theorem exists_quadratic_of_sup_span_eq_top (t : ↥(integralClosure A L))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {t} = ⊤) :
    ∃ a c : A, t * t = algebraMap A ↥(integralClosure A L) a +
      algebraMap A ↥(integralClosure A L) c * t := by
  obtain ⟨a, c, hac⟩ := exists_add_mul_of_sup_span_eq_top t hspan
    (Subalgebra.mul_mem _ t.2 t.2)
  exact ⟨a, c, (eq_add_mul_iff_coe_eq _ _ _ _).2 hac⟩

/-- **The module form of a quadratic algebra generator.** If `t` generates the integral closure
as an `A`-algebra and satisfies a monic quadratic relation over `A`, then the image of `A`
together with `t` already spans the integral closure as an `A`-module: `A' = A + A t`.

This is the converse of `Stacks.DerivationExtension.adjoin_eq_integralClosure_of_sup_span_eq_top`
in the presence of the quadratic relation, and it is what lets the conclusion of item (1) — which
is stated with `Algebra.adjoin` — be fed to the submodule-localization machinery, whose statements
are about `LinearMap.range (Algebra.linearMap A A') ⊔ Submodule.span A {t}`. -/
public theorem sup_span_eq_top_of_adjoin_eq_integralClosure (t : ↥(integralClosure A L)) (a c : A)
    (hS : Algebra.adjoin A ({(t : L)} : Set L) = integralClosure A L)
    (hrel : t * t = algebraMap A ↥(integralClosure A L) a +
      algebraMap A ↥(integralClosure A L) c * t) :
    LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {t} = ⊤ := by
  have hrelL : (t : L) * (t : L) = algebraMap A L a + algebraMap A L c * (t : L) :=
    (eq_add_mul_iff_coe_eq _ _ _ _).1 hrel
  refine le_antisymm le_top fun x _ => ?_
  have hxa : (x : L) ∈ Algebra.adjoin A ({(t : L)} : Set L) := by rw [hS]; exact x.2
  obtain ⟨a₀, a₁, hx⟩ := exists_add_mul_of_mem_adjoin_of_quadratic (t : L) a c hrelL hxa
  rw [(eq_add_mul_iff_coe_eq _ _ _ _).2 hx]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a₀, rfl⟩)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨a₁, Algebra.smul_def a₁ t⟩))

/-- A spanning element yields both the algebra generator and the quadratic relation. -/
private theorem exists_adjoin_and_quadratic_of_sup_span_eq_top (t : ↥(integralClosure A L))
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      Submodule.span A {t} = ⊤) :
    ∃ a c : A, Algebra.adjoin A ({(t : L)} : Set L) = integralClosure A L ∧
      t * t = algebraMap A ↥(integralClosure A L) a +
        algebraMap A ↥(integralClosure A L) c * t :=
  have ⟨a, c, hac⟩ := exists_quadratic_of_sup_span_eq_top t hspan
  ⟨a, c, adjoin_eq_integralClosure_of_sup_span_eq_top t hspan, hac⟩

/-- **Item (1), from data at the finitely many singular points.** Let `Iᵢ` be finitely many
pairwise comaximal ideals of `A` such that the product `∏ Iᵢ` carries the integral closure `A'`
into `A`, and such that modulo each `Iᵢ` the module `A'` is generated by `A` and one element.
Then there is a *single* `t : A'` generating `A'` as an `A`-algebra, together with its quadratic
relation.

For the coordinate ring of an affine open of a nodal curve the `Iᵢ` are the maximal ideals of
the nodes: their product annihilates `A' / A`, which is supported there, and at each of them the
local statement of Tag 0C1X gives a generator. Neither hypothesis mentions a local ring. -/
public theorem exists_adjoin_eq_integralClosure_of_comaximal {ι : Type*}
    (I : ι → Ideal A) (s : Finset ι)
    (hcom : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → I i ⊔ I j = ⊤)
    (hann : (∏ i ∈ s, I i) • (⊤ : Submodule A ↥(integralClosure A L)) ≤
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)))
    (hcyc : ∀ i ∈ s, ∃ t : ↥(integralClosure A L),
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
        (Submodule.span A {t} ⊔ I i • (⊤ : Submodule A ↥(integralClosure A L))) = ⊤) :
    ∃ (t : ↥(integralClosure A L)) (a c : A),
      Algebra.adjoin A ({(t : L)} : Set L) = integralClosure A L ∧
        t * t = algebraMap A ↥(integralClosure A L) a +
          algebraMap A ↥(integralClosure A L) c * t := by
  obtain ⟨t, ht⟩ := Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top
    (LinearMap.range (Algebra.linearMap A ↥(integralClosure A L))) I s hcom hann hcyc
  obtain ⟨a, c, h⟩ := exists_adjoin_and_quadratic_of_sup_span_eq_top t ht
  exact ⟨t, a, c, h⟩

/-- **Item (1) with the per-node hypothesis in the form the development proves it.** The
hypothesis on each singular point is that `A' / (A + Iᵢ A')` is a simple `A`-module, written as
the coatomicity of `A + Iᵢ A'`; at a node that quotient is a one-dimensional vector space over
the residue field, which is the content of `Ring.deltaInvariant = 1`
(`Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra` is the same
statement for a local ring, with `Iᵢ = 0`).

Together with the product of the `Iᵢ` carrying `A'` into `A` — the conductor cutting out the
nodes — this yields a single `t` generating `A'` over `A`, with its quadratic relation. Nothing
in the hypotheses or the proof localizes. -/
public theorem exists_adjoin_eq_integralClosure_of_isCoatom {ι : Type*}
    (I : ι → Ideal A) (s : Finset ι)
    (hcom : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → I i ⊔ I j = ⊤)
    (hann : (∏ i ∈ s, I i) • (⊤ : Submodule A ↥(integralClosure A L)) ≤
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)))
    (hco : ∀ i ∈ s, IsCoatom (LinearMap.range (Algebra.linearMap A ↥(integralClosure A L)) ⊔
      I i • (⊤ : Submodule A ↥(integralClosure A L)))) :
    ∃ (t : ↥(integralClosure A L)) (a c : A),
      Algebra.adjoin A ({(t : L)} : Set L) = integralClosure A L ∧
        t * t = algebraMap A ↥(integralClosure A L) a +
          algebraMap A ↥(integralClosure A L) c * t := by
  obtain ⟨t, ht⟩ := Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top_of_isCoatom_sup
    (LinearMap.range (Algebra.linearMap A ↥(integralClosure A L))) I s hcom hann hco
  obtain ⟨a, c, h⟩ := exists_adjoin_and_quadratic_of_sup_span_eq_top t ht
  exact ⟨t, a, c, h⟩

end Monogenic

section Avoidance

/-- **Prime avoidance over a finite family.** An ideal contained in none of finitely many prime
ideals contains an element lying outside all of them. -/
@[sga "3 V 4.1" "more general"]
public theorem exists_mem_forall_notMem_of_finite {R : Type*} [CommRing R] (J : Ideal R)
    (F : Set (Ideal R)) (hF : F.Finite) (hp : ∀ p ∈ F, p.IsPrime) (hJ : ∀ p ∈ F, ¬ J ≤ p) :
    ∃ α ∈ J, ∀ p ∈ F, α ∉ p := by
  have hsub : ¬ ((J : Set R) ⊆ ⋃ p ∈ F, (p : Set R)) := fun hle => by
    obtain ⟨p, hpF, hple⟩ :=
      (Ideal.subset_union_prime_finite (f := fun p : Ideal R => p) hF ⊥ ⊥
        fun p hpF _ _ => hp p hpF).mp hle
    exact hJ p hpF hple
  obtain ⟨α, hαJ, hα⟩ := Set.not_subset.mp hsub
  exact ⟨α, hαJ, fun p hpF hmem => hα (Set.mem_biUnion hpF hmem)⟩

/-- **Item (2): a conductor element comaximal with `u`.** Let `S` be an `A`-algebra and `u : S`.
If only finitely many maximal ideals of `S` contain `u`, and none of them contracts to an ideal
of `A` containing the ideal `J`, then some `α ∈ J` is comaximal with `u` in `S`.

Neither `α` nor `u` is a unit: the hypothesis is that their zero loci are disjoint, which is
exactly what holds at a node — the conductor cuts out the nodes and `u = 2 t - c` is invertible
at the points above a node. -/
public theorem exists_mem_mul_add_mul_eq_one_of_finite {A : Type v} {S : Type w} [CommRing A]
    [CommRing S] [Algebra A S] (J : Ideal A) (u : S)
    (hF : {m : Ideal S | m.IsMaximal ∧ u ∈ m}.Finite)
    (hJ : ∀ m : Ideal S, m.IsMaximal → u ∈ m → ¬ J ≤ Ideal.comap (algebraMap A S) m) :
    ∃ α ∈ J, ∃ w₁ w₂ : S, w₁ * algebraMap A S α + w₂ * u = 1 := by
  obtain ⟨α, hαJ, hα⟩ := exists_mem_forall_notMem_of_finite J
    (Ideal.comap (algebraMap A S) '' {m : Ideal S | m.IsMaximal ∧ u ∈ m})
    (hF.image _)
    (by
      rintro p ⟨m, ⟨hm, -⟩, rfl⟩
      have := hm.isPrime
      exact Ideal.comap_isPrime (algebraMap A S) m)
    (by
      rintro p ⟨m, ⟨hm, hu⟩, rfl⟩
      exact hJ m hm hu)
  obtain ⟨w₁, w₂, hw⟩ := exists_mul_add_mul_eq_one_of_forall_isMaximal (algebraMap A S α) u
    fun m hm => by
      by_cases hu : u ∈ m
      · exact Or.inl fun hmem => hα _ ⟨m, ⟨hm, hu⟩, rfl⟩ hmem
      · exact Or.inr hu
  exact ⟨α, hαJ, w₁, w₂, hw⟩

end Avoidance

section Assemble

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

/-- **The extension and the fixing of both branches, with the comaximality supplied by the
conductor ideal.** Let the integral closure `A'` of `A` in the localization be generated over `A`
by a single `t'` with `t' ^ 2 = a + c t'`; let `𝔠` be an ideal of `A` every element of which
carries `t'` back into `A`; suppose only finitely many maximal ideals of `A'` contain
`u = 2 t' - c` and none of them contracts to an ideal containing `𝔠`; and let `ε₁, ε₂ : A' → k`
agree on `A` with `ε₁ t' - ε₂ t' = 1` and with `ker (ε₁ ∘ algebraMap A A') ⊆ 𝔠`. Then every
`k`-derivation of `A` extends uniquely to `A'`, and the extension is killed by both residues, so
it fixes both points above the node.

This is `existsUnique_extend_integralClosure_apply_eq_zero_of_quadratic_conductor` in
`Stacks.DerivationExtension` with the comaximality of the conductor element with `2 t' - c`
replaced by the two facts the geometry supplies: the conductor cuts out the nodes, and `2 t' - c`
vanishes at finitely many points, none of them a node. `A` is not assumed local, and no element
is assumed invertible. -/
public theorem existsUnique_extend_integralClosure_apply_eq_zero_of_conductor
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
    (hcondε : ∀ b : A, ε₁ (algebraMap A ↥(integralClosure A L) b) = 0 →
      ∃ b' : A, algebraMap A ↥(integralClosure A L) b * t' =
        algebraMap A ↥(integralClosure A L) b') :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      (∀ b : A, D' (algebraMap A ↥(integralClosure A L) b) =
          algebraMap A ↥(integralClosure A L) (D b)) ∧
        (∀ s, ε₁ (D' s) = 0) ∧ (∀ s, ε₂ (D' s) = 0) := by
  obtain ⟨α, hα𝔠, w₁, w₂, hw⟩ := exists_mem_mul_add_mul_eq_one_of_finite 𝔠
    (t' + t' - algebraMap A ↥(integralClosure A L) c) hfin hnode
  obtain ⟨β, hβ⟩ := hcond α hα𝔠
  exact existsUnique_extend_integralClosure_apply_eq_zero_of_quadratic_conductor D t' a c α β
    hS hrel hβ w₁ w₂ hw ε₁ ε₂ hres hne hcondε

end Assemble

end Stacks.DerivationExtension

end
