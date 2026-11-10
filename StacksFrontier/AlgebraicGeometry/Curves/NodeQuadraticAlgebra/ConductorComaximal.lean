module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorMonogenic
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Discriminant
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.RingTheory.Ideal.FiniteMaximalContainingElement

/-!
# A conductor element comaximal with `2 t - c`: item (2) of Stacks 0E68

Let `k` be a field and let `A` be a reduced Nagata `k`-algebra of dimension at most one whose
singularities are a finite family of distinct maximal ideals `𝔪₁, …, 𝔪ᵤ`, each a node. Let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of fractions,
let `t` generate `A'` over `A` — item (1),
`Stacks.Curves.exists_adjoin_eq_integralClosure_of_isNodalAlgebra` — with `t ^ 2 = a + c t`, and
put `u = 2 t - c`. Then the conductor ideal `𝔠 = 𝔪₁ ⋯ 𝔪ᵤ` contains an element `α` comaximal with
`u` in `A'`:

`w₁ α + w₂ u = 1` for some `w₁, w₂ ∈ A'`.

This is item (2) of Stacks Tag 0E68, and it is proved exactly as the tag says: *neither* `α` nor
`u` is a unit — `u` is not (`u ^ 2` is the image of the discriminant `4 a + c ^ 2`, which on an
affine curve has zeros, for instance at the smooth point `s = 0` of `y ^ 2 = x ^ 3 + x ^ 2`) — but
their zero loci are disjoint, so prime avoidance produces `α`. The two geometric inputs are the
two facts collected here:

* **the zero locus of `u` is finite**: `u ^ 2` is the image of `4 a + c ^ 2`, and a nonzerodivisor
  of a one-dimensional Noetherian ring lies in finitely many maximal ideals, finitely many also
  after passing to the module-finite extension `A'`
  (`Stacks.RingTheory.finite_setOf_isMaximal_mem_algebraMap_of_moduleFinite`);
* **the zero locus of `u` misses the nodes**: a maximal ideal of `A'` whose contraction contains
  `𝔠` contracts to one of the `𝔪ᵢ`, and the discriminant is a unit at a node
  (`Stacks.Curves.four_mul_add_mul_self_notMem_of_isNodalAlgebra`), so `u` is invertible there.

Prime avoidance is then `Stacks.DerivationExtension.exists_mem_mul_add_mul_eq_one_of_finite`.

## Main results

* `Stacks.Curves.finite_setOf_isMaximal_two_mul_sub_mem` — the maximal ideals of `A'` containing
  `2 t - c` are finite in number, as soon as the discriminant is a nonzerodivisor.
* `Stacks.Curves.not_le_comap_of_isMaximal_two_mul_sub_mem` — none of them contracts to an ideal
  containing the product of the nodes.
* `Stacks.Curves.exists_mem_prod_mul_add_mul_eq_one_of_isNodalAlgebra` — **item (2)** for a given
  generator: an element of `𝔠` comaximal with `2 t - c`.
* `Stacks.Curves.exists_adjoin_eq_integralClosure_and_comaximal_of_isNodalAlgebra` — items (1) and
  (2) together: the generator, its quadratic relation, and the conductor element, with no
  hypothesis on the generator.
* `Stacks.Curves.existsUnique_extend_integralClosure_apply_eq_zero_of_isNodalAlgebra` — items (1)
  and (2) discharged against the extension theorem, leaving quantified over exactly the data of
  item (3): a derivation and the two residues at the branches of a node.

## Implementation notes

The last statement needs the discriminant of the generator produced by item (1) to be a
nonzerodivisor, and that is *not* automatic: if `A = k[x]` is already normal then `t = 0`,
`a = c = 0` satisfies item (1), `u = 0`, and every maximal ideal of `A'` contains `u`. What rules
this out is that every irreducible component of `Spec A` passes through a node, which is the
hypothesis `hcomp` below — for `A` a domain with at least one node it is automatic. Under it the
discriminant lies outside every minimal prime, since it lies outside the node that minimal prime
is contained in, and in a reduced ring that makes it a nonzerodivisor
(`Stacks.RingTheory.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes`).

No `@[stacks]` tag is carried here: item (2) is one of the three items of Stacks 0E68, and a tag
goes only on a declaration stating the whole of it. Item (3), the two residues at the branches of
a node, is not produced here.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- If every minimal prime of `A` lies in a node, the discriminant of `t` is a nonzerodivisor. -/
private theorem discriminant_mem_nonZeroDivisors_of_forall_le_node (k : Type u) (A : Type v)
    [Field k] [CommRing A] [IsReduced A] [IsNoetherianRing A] [Algebra k A] {ι : Type*}
    (𝔪 : ι → Ideal A) (s : Finset ι) (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hcomp : ∀ p ∈ minimalPrimes A, ∃ i ∈ s, p ≤ 𝔪 i)
    (t : ↥(integralClosure A (FractionRing A))) (a c : A)
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t} = ⊤)
    (hrel : t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
      algebraMap A ↥(integralClosure A (FractionRing A)) c * t) :
    4 * a + c * c ∈ nonZeroDivisors A := by
  refine Stacks.RingTheory.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes
    fun p hp hmem => ?_
  obtain ⟨i, hi, hple⟩ := hcomp p hp
  have := hmax i hi
  exact four_mul_add_mul_self_notMem_of_isNodalAlgebra k A (𝔪 i)
    (hnodal (𝔪 i) ⟨i, hi, rfl⟩) t a c hspan hrel (hple hmem)

/-- **The zero locus of `2 t - c` on the normalization is finite.** Let `A` be a reduced Nagata
ring of Krull dimension at most one, let `A'` be its integral closure in its total ring of
fractions and let `t ∈ A'` satisfy `t ^ 2 = a + c t` with `4 a + c ^ 2` a nonzerodivisor. Then
only finitely many maximal ideals of `A'` contain `u = 2 t - c`.

Indeed `u ^ 2` is the image of `4 a + c ^ 2`, so a maximal ideal containing `u` contains that
image; a nonzerodivisor of a one-dimensional Noetherian ring lies in only finitely many maximal
ideals, and `A'` is module-finite over `A`. -/
public theorem finite_setOf_isMaximal_two_mul_sub_mem (A : Type v) [CommRing A] [IsReduced A]
    [Ring.KrullDimLE 1 A] (hNagata : IsNagataRing A)
    (t : ↥(integralClosure A (FractionRing A))) (a c : A)
    (hrel : t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
      algebraMap A ↥(integralClosure A (FractionRing A)) c * t)
    (hd : 4 * a + c * c ∈ nonZeroDivisors A) :
    {n : Ideal ↥(integralClosure A (FractionRing A)) | n.IsMaximal ∧
      t + t - algebraMap A ↥(integralClosure A (FractionRing A)) c ∈ n}.Finite := by
  have := hNagata
  have : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_fractionRing hNagata
  have : Algebra.IsIntegral A ↥(integralClosure A (FractionRing A)) :=
    ⟨fun x => IsIntegralClosure.isIntegral A (FractionRing A) x⟩
  refine (Stacks.RingTheory.finite_setOf_isMaximal_mem_algebraMap_of_moduleFinite
    (S := ↥(integralClosure A (FractionRing A))) (4 * a + c * c)
    (Stacks.RingTheory.finite_setOf_isMaximal_mem_of_mem_nonZeroDivisors hd)).subset ?_
  rintro n ⟨hn, hun⟩
  refine ⟨hn, ?_⟩
  rw [← Stacks.DerivationExtension.sq_two_mul_sub_algebraMap t a c hrel]
  exact Ideal.mul_mem_left n _ hun

/-- **The zero locus of `2 t - c` misses the nodes.** With `A`, `A'` and `t` as in item (1), no
maximal ideal of `A'` containing `u = 2 t - c` contracts to an ideal of `A` containing the product
of the nodes.

Such a contraction is prime, so containing `𝔪₁ ⋯ 𝔪ᵤ` it contains some `𝔪ᵢ`, hence equals it, the
`𝔪ᵢ` being maximal. But the discriminant `4 a + c ^ 2` is a unit at a node
(`Stacks.Curves.four_mul_add_mul_self_notMem_of_isNodalAlgebra`) while `u ^ 2` is its image, so
`u` cannot lie in a maximal ideal over `𝔪ᵢ`. -/
public theorem not_le_comap_of_isMaximal_two_mul_sub_mem (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsReduced A] [IsNoetherianRing A] [Algebra k A] {ι : Type*} (𝔪 : ι → Ideal A)
    (s : Finset ι) (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (t : ↥(integralClosure A (FractionRing A))) (a c : A)
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t} = ⊤)
    (hrel : t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
      algebraMap A ↥(integralClosure A (FractionRing A)) c * t) :
    ∀ n : Ideal ↥(integralClosure A (FractionRing A)), n.IsMaximal →
      t + t - algebraMap A ↥(integralClosure A (FractionRing A)) c ∈ n →
      ¬ (∏ i ∈ s, 𝔪 i) ≤
        Ideal.comap (algebraMap A ↥(integralClosure A (FractionRing A))) n := by
  intro n hn hun hle
  have := hn
  have hP : (Ideal.comap (algebraMap A ↥(integralClosure A (FractionRing A))) n).IsPrime :=
    Ideal.comap_isPrime _ n
  obtain ⟨i, hi, hile⟩ := hP.prod_le.mp hle
  have := hmax i hi
  have heq : 𝔪 i = Ideal.comap (algebraMap A ↥(integralClosure A (FractionRing A))) n :=
    (hmax i hi).eq_of_le hP.ne_top hile
  refine four_mul_add_mul_self_notMem_of_isNodalAlgebra k A (𝔪 i)
    (hnodal (𝔪 i) ⟨i, hi, rfl⟩) t a c hspan hrel ?_
  rw [heq]
  change algebraMap A ↥(integralClosure A (FractionRing A)) (4 * a + c * c) ∈ n
  rw [← Stacks.DerivationExtension.sq_two_mul_sub_algebraMap t a c hrel]
  exact Ideal.mul_mem_left n _ hun

/-- **Item (2) of Stacks 0E68, for a given generator.** Let `A` be a reduced Nagata `k`-algebra of
dimension at most one whose singularities are the nodes `𝔪ᵢ`, `i ∈ s`, let `t` generate its
normalization `A'` over `A` with `t ^ 2 = a + c t`, and suppose the discriminant `4 a + c ^ 2` is
a nonzerodivisor. Then the product of the nodes contains an element comaximal in `A'` with
`u = 2 t - c`.

Neither the element nor `u` is a unit; what holds is that their zero loci are disjoint, which is
the conjunction of `Stacks.Curves.finite_setOf_isMaximal_two_mul_sub_mem` and
`Stacks.Curves.not_le_comap_of_isMaximal_two_mul_sub_mem`. -/
public theorem exists_mem_prod_mul_add_mul_eq_one_of_isNodalAlgebra (k : Type u) (A : Type v)
    [Field k] [CommRing A] [IsReduced A] [Ring.KrullDimLE 1 A] [Algebra k A]
    (hNagata : IsNagataRing A) {ι : Type*} (𝔪 : ι → Ideal A) (s : Finset ι)
    (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (t : ↥(integralClosure A (FractionRing A))) (a c : A)
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t} = ⊤)
    (hrel : t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
      algebraMap A ↥(integralClosure A (FractionRing A)) c * t)
    (hd : 4 * a + c * c ∈ nonZeroDivisors A) :
    ∃ α ∈ ∏ i ∈ s, 𝔪 i, ∃ w₁ w₂ : ↥(integralClosure A (FractionRing A)),
      w₁ * algebraMap A ↥(integralClosure A (FractionRing A)) α +
        w₂ * (t + t - algebraMap A ↥(integralClosure A (FractionRing A)) c) = 1 := by
  have := hNagata
  exact Stacks.DerivationExtension.exists_mem_mul_add_mul_eq_one_of_finite _ _
    (finite_setOf_isMaximal_two_mul_sub_mem A hNagata t a c hrel hd)
    (not_le_comap_of_isMaximal_two_mul_sub_mem k A 𝔪 s hmax hnodal t a c hspan hrel)

/-- **Items (1) and (2) of Stacks 0E68 together.** Let `A` be a reduced Nagata `k`-algebra of
dimension at most one whose singularities are a finite family of distinct maximal ideals `𝔪ᵢ`,
each a node, and suppose every minimal prime of `A` is contained in one of them — every
irreducible component of `Spec A` passes through a node, which for a domain with at least one node
is automatic. Then there is a single `t` generating the normalization `A'` over `A`, satisfying a
monic quadratic relation `t ^ 2 = a + c t`, together with an element of the product of the nodes
that is comaximal in `A'` with `2 t - c`.

The hypothesis on the components is what makes the discriminant of the generator a nonzerodivisor,
and it cannot be dropped: for `A = k[x]`, already normal, item (1) is satisfied by `t = 0`,
`a = c = 0`, and then `2 t - c = 0` lies in every maximal ideal of `A'`. -/
public theorem exists_adjoin_eq_integralClosure_and_comaximal_of_isNodalAlgebra (k : Type u)
    (A : Type v) [Field k] [CommRing A] [IsReduced A] [Ring.KrullDimLE 1 A] [Algebra k A]
    (hNagata : IsNagataRing A) {ι : Type*} (𝔪 : ι → Ideal A) (s : Finset ι)
    (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔪 i ≠ 𝔪 j)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], (∀ i ∈ s, 𝔪 i ≠ P) →
      IsRegularLocalRing (Localization.AtPrime P))
    (hcomp : ∀ p ∈ minimalPrimes A, ∃ i ∈ s, p ≤ 𝔪 i) :
    ∃ (t : ↥(integralClosure A (FractionRing A))) (a c : A),
      Algebra.adjoin A ({(t : FractionRing A)} : Set (FractionRing A)) =
          integralClosure A (FractionRing A) ∧
        t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
            algebraMap A ↥(integralClosure A (FractionRing A)) c * t ∧
          ∃ α ∈ ∏ i ∈ s, 𝔪 i, ∃ w₁ w₂ : ↥(integralClosure A (FractionRing A)),
            w₁ * algebraMap A ↥(integralClosure A (FractionRing A)) α +
              w₂ * (t + t - algebraMap A ↥(integralClosure A (FractionRing A)) c) = 1 := by
  have := hNagata
  obtain ⟨t, a, c, hS, hrel⟩ :=
    exists_adjoin_eq_integralClosure_of_isNodalAlgebra k A 𝔪 s hmax hdistinct hnodal hreg
  have hspan :=
    Stacks.DerivationExtension.sup_span_eq_top_of_adjoin_eq_integralClosure t a c hS hrel
  have hd := discriminant_mem_nonZeroDivisors_of_forall_le_node k A 𝔪 s hmax hnodal hcomp t a c
    hspan hrel
  exact ⟨t, a, c, hS, hrel, exists_mem_prod_mul_add_mul_eq_one_of_isNodalAlgebra k A hNagata 𝔪 s
    hmax hnodal t a c hspan hrel hd⟩

/-- **Items (1) and (2) of Stacks 0E68 discharged against the extension theorem.** Under the
hypotheses of `Stacks.Curves.exists_adjoin_eq_integralClosure_and_comaximal_of_isNodalAlgebra`
there is a generator `t` of the normalization `A'` over `A`, with its quadratic relation, such
that *for every* `k`-derivation `D` of `A` and every pair of residues `ε₁, ε₂ : A' → k` agreeing
on `A`, normalized by `ε₁ t - ε₂ t = 1` and killing `A` only inside the conductor, `D` extends
uniquely to `A'` and the extension is killed by both residues — so it fixes both points above
each node.

What items (1) and (2) supply is everything about `t`: that it generates, its quadratic relation,
the conductor property of the product of the nodes, the finiteness of the zero locus of
`u = 2 t - c` and its disjointness from the nodes. What remains quantified over is exactly the
data of item (3), the two residues at the branches of a node. -/
public theorem existsUnique_extend_integralClosure_apply_eq_zero_of_isNodalAlgebra (k : Type u)
    (A : Type v) [Field k] [CommRing A] [IsReduced A] [Ring.KrullDimLE 1 A] [Algebra k A]
    (hNagata : IsNagataRing A) {ι : Type*} (𝔪 : ι → Ideal A) (s : Finset ι)
    (hmax : ∀ i ∈ s, (𝔪 i).IsMaximal)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔪 i ≠ 𝔪 j)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], (∀ i ∈ s, 𝔪 i ≠ P) →
      IsRegularLocalRing (Localization.AtPrime P))
    (hcomp : ∀ p ∈ minimalPrimes A, ∃ i ∈ s, p ≤ 𝔪 i) :
    ∃ (t : ↥(integralClosure A (FractionRing A))) (a c : A),
      Algebra.adjoin A ({(t : FractionRing A)} : Set (FractionRing A)) =
          integralClosure A (FractionRing A) ∧
        t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
            algebraMap A ↥(integralClosure A (FractionRing A)) c * t ∧
          ∀ (D : Derivation k A A)
            (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k),
            (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
                ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) b)) →
              ε₁ t - ε₂ t = 1 →
              (∀ b : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) b) = 0 →
                ∃ b' : A, algebraMap A ↥(integralClosure A (FractionRing A)) b * t =
                  algebraMap A ↥(integralClosure A (FractionRing A)) b') →
              ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
                  ↥(integralClosure A (FractionRing A)),
                (∀ b : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) b) =
                    algebraMap A ↥(integralClosure A (FractionRing A)) (D b)) ∧
                  (∀ z, ε₁ (D' z) = 0) ∧ (∀ z, ε₂ (D' z) = 0) := by
  have := hNagata
  obtain ⟨t, a, c, hS, hrel⟩ :=
    exists_adjoin_eq_integralClosure_of_isNodalAlgebra k A 𝔪 s hmax hdistinct hnodal hreg
  have hspan :=
    Stacks.DerivationExtension.sup_span_eq_top_of_adjoin_eq_integralClosure t a c hS hrel
  have hd := discriminant_mem_nonZeroDivisors_of_forall_le_node k A 𝔪 s hmax hnodal hcomp t a c
    hspan hrel
  have hann := prod_smul_top_le_range_algebraMap_integralClosure_of_isNodalAlgebra k A 𝔪 s
    hnodal hreg
  have hcond : ∀ α ∈ ∏ i ∈ s, 𝔪 i, ∃ β : A,
      algebraMap A ↥(integralClosure A (FractionRing A)) α * t =
        algebraMap A ↥(integralClosure A (FractionRing A)) β := by
    intro α hα
    obtain ⟨β, hβ⟩ := hann (Submodule.smul_mem_smul hα Submodule.mem_top)
    rw [Algebra.linearMap_apply] at hβ
    exact ⟨β, by rw [hβ, Algebra.smul_def]⟩
  refine ⟨t, a, c, hS, hrel, fun D ε₁ ε₂ hres hne hcondε => ?_⟩
  exact Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor
    D t a c (∏ i ∈ s, 𝔪 i) hS hrel hcond
    (finite_setOf_isMaximal_two_mul_sub_mem A hNagata t a c hrel hd)
    (not_le_comap_of_isMaximal_two_mul_sub_mem k A 𝔪 s hmax hnodal t a c hspan hrel)
    ε₁ ε₂ hres hne hcondε

end Stacks.Curves

end
