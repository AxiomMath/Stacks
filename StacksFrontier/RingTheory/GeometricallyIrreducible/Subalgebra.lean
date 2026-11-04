module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Colimit.Ring

public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric irreducibility passes to subalgebras and directed colimits

Let `k` be a field and `S` a `k`-algebra. Three statements are proved.

1. If `S` is geometrically irreducible over `k`, so is every `k`-subalgebra.
2. If every finitely generated `k`-subalgebra of `S` is geometrically irreducible, then so
   is `S`.
3. A directed colimit of geometrically irreducible `k`-algebras is geometrically
   irreducible.

A `k`-algebra `S` is *geometrically irreducible over `k`* when for every field extension
`k'/k` the prime spectrum `Spec (S ⊗[k] k')` is irreducible; recall that an irreducible
space is by convention nonempty. That is `Algebra.IsGeometricallyIrreducible`
[stacks, 037L], spelled there through `AlgebraicGeometry.GeometricallyIrreducible` and
related to the condition on tensor products by
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct`,
which is the form the arguments below use. Because that spelling passes through `Spec`,
the field, the algebra and the test extensions all lie in one universe; the three
statements are therefore stated for a `k`-algebra in the universe of `k`, and for a
directed system indexed by and valued in that universe.
-/

@[expose] public section

universe u v w w₁ w₂

open scoped TensorProduct

/-- Auxiliary `k`-algebra structure on a directed colimit (`Ring.DirectLimit`) of
`k`-algebras, with the colimit base point used to define the structure morphism
`k → colim`.  See `dlAlg_of_apply` for the compatibility characterizing it as the
colimit `k`-algebra structure (when the transition maps are `k`-algebra maps). -/
@[reducible] noncomputable def dlAlg
    (k : Type u) [CommRing k]
    {ι : Type w₁} [Preorder ι] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i → G j) :
    Algebra k (Ring.DirectLimit G f) :=
  RingHom.toAlgebra
    ((Ring.DirectLimit.of G f (Classical.arbitrary ι)).comp
      (algebraMap k (G (Classical.arbitrary ι))))

/-! ## Auxiliary algebraic lemmas -/

/-- The map `S' ⊗[k] k' → S ⊗[k] k'` induced by a subalgebra inclusion is injective
(since `k'` is flat over the field `k`). -/
theorem tensorProduct_map_subalgebra_val_injective
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    (k' : Type w) [Field k'] [Algebra k k'] (S' : Subalgebra k S) :
    Function.Injective (Algebra.TensorProduct.map S'.val (AlgHom.id k k')) := by
  have heq : ((Algebra.TensorProduct.map S'.val (AlgHom.id k k')).toLinearMap
        : (S' ⊗[k] k') →ₗ[k] (S ⊗[k] k'))
      = LinearMap.rTensor k' S'.val.toLinearMap := by
    ext x y
    simp [LinearMap.rTensor_tmul]
  show Function.Injective (Algebra.TensorProduct.map S'.val (AlgHom.id k k')).toLinearMap
  rw [heq]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- Any element of `S ⊗[k] k'` lies in the range of `S' ⊗[k] k' → S ⊗[k] k'` for some
finitely generated `k`-subalgebra `S' ⊆ S`. -/
theorem exists_fg_subalgebra_mem_range
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    (k' : Type w) [Field k'] [Algebra k k'] (a : S ⊗[k] k') :
    ∃ (S' : Subalgebra k S), S'.FG ∧
      a ∈ AlgHom.range (Algebra.TensorProduct.map S'.val (AlgHom.id k k')) := by
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset a
  set S' := Algebra.adjoin k (s.image Prod.fst : Set S)
  have hmem : ∀ p ∈ s, p.fst ∈ S' := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hp))
  refine ⟨S', Subalgebra.fg_adjoin_finset _, ?_⟩
  rw [AlgHom.mem_range]
  refine ⟨∑ p ∈ s.attach, (⟨p.val.fst, hmem p.val p.property⟩ : S') ⊗ₜ[k] p.val.snd, ?_⟩
  rw [map_sum, ← Finset.sum_attach s (fun p => p.fst ⊗ₜ[k] p.snd)]
  exact Finset.sum_congr rfl fun p _ => by simp [Algebra.TensorProduct.map_tmul]

/-! ## Auxiliary topological lemmas -/

/-- `Spec R` is irreducible iff the nilradical of `R` is a prime ideal. -/
@[ega "0 16.1.1" "special case", ega "I 1.1.13", ega "I 6.1.10" "(e)"]
theorem irreducibleSpace_primeSpectrum_iff_nilradical_isPrime (R : Type*) [CommRing R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime := by
  rw [← PrimeSpectrum.vanishingIdeal_univ,
    ← PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime]
  exact irreducibleSpace_def _

/-- If `A` is geometrically irreducible over `k`, the nilradical of `A ⊗[k] k'` is prime. -/
theorem nilradical_tensorProduct_isPrime_of_isGeometricallyIrreducible {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (h : Algebra.IsGeometricallyIrreducible k A)
    (k' : Type u) [Field k'] [Algebra k k'] : (nilradical (A ⊗[k] k')).IsPrime :=
  (irreducibleSpace_primeSpectrum_iff_nilradical_isPrime _).mp
    ((Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      k A).mp h k')

/-- If `A` is geometrically irreducible over `k`, then `A ⊗[k] k'` is nontrivial. -/
theorem nontrivial_tensorProduct_of_isGeometricallyIrreducible {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (h : Algebra.IsGeometricallyIrreducible k A)
    (k' : Type u) [Field k'] [Algebra k k'] : Nontrivial (A ⊗[k] k') := by
  by_contra h'
  rw [not_nontrivial_iff_subsingleton] at h'
  exact (nilradical_tensorProduct_isPrime_of_isGeometricallyIrreducible h k').ne_top
    (Subsingleton.elim _ _)

/-- A continuous map with dense range from an irreducible space makes the target
irreducible. -/
@[ega "0 2.1.5" "more general"]
theorem irreducibleSpace_of_denseRange {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace X] {g : X → Y}
    (hg : Continuous g) (hd : DenseRange g) : IrreducibleSpace Y := by
  rw [irreducibleSpace_def]
  have h : IsIrreducible (closure (g '' Set.univ)) :=
    (((irreducibleSpace_def X).mp ‹_›).image g hg.continuousOn).closure
  rwa [Set.image_univ, hd.closure_range] at h

/-- If `Spec S` is irreducible and `g : R →+* S` is injective, then `Spec R` is
irreducible. -/
@[ega "IV 4.4.1" "special case"]
theorem irreducibleSpace_primeSpectrum_of_injective {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] (g : R →+* S) (hg : Function.Injective g)
    [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum R) := by
  refine irreducibleSpace_of_denseRange (PrimeSpectrum.continuous_comap g)
    ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).mpr ?_)
  rw [(RingHom.injective_iff_ker_eq_bot g).mp hg]
  exact bot_le

/-- For an injective ring homomorphism `j : A →+* B`, an element `a` is nilpotent in
`A` iff its image `j a` is nilpotent in `B`.  (Forward: ring homs preserve nilpotents;
backward: injectivity reflects `(j a)^n = j (a^n) = 0` to `a^n = 0`.)  This lets us
transport `nilradical` membership across injections of (commutative) rings. -/
theorem nilradical_mem_iff_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (j : A →+* B) (hj : Function.Injective j) (a : A) :
    a ∈ nilradical A ↔ j a ∈ nilradical B := by
  simp only [mem_nilradical, IsNilpotent]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
  · rintro ⟨n, hn⟩; exact ⟨n, hj (by rw [map_pow, hn, map_zero])⟩

/-- A `k`-algebra `S` is geometrically irreducible once every `S ⊗[k] k'` is nontrivial and
its nilradical satisfies the multiplicative property of a prime ideal. -/
private theorem isGeometricallyIrreducible_of_nilradical_mem_or_mem
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    (hnt : ∀ (k' : Type u) [Field k'] [Algebra k k'], Nontrivial (S ⊗[k] k'))
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k'] {x y : S ⊗[k] k'},
      x * y ∈ nilradical (S ⊗[k] k') → x ∈ nilradical (S ⊗[k] k') ∨ y ∈ nilradical (S ⊗[k] k')) :
    Algebra.IsGeometricallyIrreducible k S := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro k' _ _
  rw [irreducibleSpace_primeSpectrum_iff_nilradical_isPrime]
  have := hnt k'
  refine ⟨?_, fun {x y} hxy => h k' hxy⟩
  rw [Ideal.ne_top_iff_one]
  simpa [mem_nilradical] using not_isNilpotent_one (R := S ⊗[k] k')

/-- Monotonicity of the range of the base-change map under subalgebra inclusion:
if `S₁ ≤ S₂` and `a` is hit by `S₁ ⊗ k' → S ⊗ k'`, then it is hit by
`S₂ ⊗ k' → S ⊗ k'`.  (The first map factors through the second via the inclusion
`S₁ ↪ S₂` tensored with `id`.) -/
theorem mem_range_tensorMap_mono
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    {k' : Type w} [Field k'] [Algebra k k']
    {S₁ S₂ : Subalgebra k S} (h : S₁ ≤ S₂) (a : S ⊗[k] k')
    (ha : a ∈ AlgHom.range (Algebra.TensorProduct.map S₁.val (AlgHom.id k k'))) :
    a ∈ AlgHom.range (Algebra.TensorProduct.map S₂.val (AlgHom.id k k')) := by
  obtain ⟨b, rfl⟩ := ha
  rw [AlgHom.mem_range]
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id k k') b, ?_⟩
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  congr 1

/-- **Statement 1 (Subalgebras).** If `S` is geometrically irreducible over `k`, then
every `k`-subalgebra `S' ⊆ S` is geometrically irreducible over `k`. -/
@[stacks 037N "(1)"]
theorem isGeometricallyIrreducible_of_subalgebra
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : Algebra.IsGeometricallyIrreducible k S)
    (S' : Subalgebra k S) :
    Algebra.IsGeometricallyIrreducible k S' := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro k' _ _
  have := (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
    k S).mp hS k'
  -- the algebra map `S' ⊗ k' → S ⊗ k'`
  exact irreducibleSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.map S'.val (AlgHom.id k k')).toRingHom
    (tensorProduct_map_subalgebra_val_injective k S k' S')

/-- **Statement 2, nontriviality part.** Under the fg hypothesis, `S ⊗[k] k'` is
nontrivial (so `nilradical (S ⊗[k] k') ≠ ⊤`, equivalently `Spec` is nonempty).

Argument: apply `hS` to the finitely generated subalgebra `S' = ⊥` (which is fg, e.g.
`Subalgebra.fg_bot`).  Then `Algebra.IsGeometricallyIrreducible k ↥⊥` applied to `k'`
gives `IrreducibleSpace (PrimeSpectrum (↥⊥ ⊗[k] k'))`, which is in particular nonempty,
hence `↥⊥ ⊗[k] k'` is `Nontrivial` (via `PrimeSpectrum.instNonempty`-type reasoning, or
`nilradical ≠ ⊤` from `IsPrime.ne_top` after
`irreducibleSpace_primeSpectrum_iff_nilradical_isPrime`).  The base-change map
`j : ↥⊥ ⊗[k] k' → S ⊗[k] k'` (`Algebra.TensorProduct.map (⊥ : Subalgebra k S).val
(AlgHom.id k k')`) is injective by `tensorProduct_map_subalgebra_val_injective`, and an
injective ring hom out of a nontrivial ring lands in a nontrivial ring
(`Function.Injective.nontrivial`). -/
theorem nontrivial_tensorProduct_of_forall_fg
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : ∀ (S' : Subalgebra k S), S'.FG →
      Algebra.IsGeometricallyIrreducible k S')
    (k' : Type u) [Field k'] [Algebra k k'] :
    Nontrivial (S ⊗[k] k') := by
  -- Apply hS to ⊥, which is finitely generated.
  -- Get IrreducibleSpace for ↥⊥ ⊗ k', hence the nilradical is prime, hence Nontrivial.
  have := nontrivial_tensorProduct_of_isGeometricallyIrreducible (hS ⊥ Subalgebra.fg_bot) k'
  -- Transport along the injective base-change map.
  exact (tensorProduct_map_subalgebra_val_injective k S k' ⊥).nontrivial

/-- **Statement 2, prime implication part.** Under the fg hypothesis, the nilradical of
`S ⊗[k] k'` satisfies the multiplicative property of a prime ideal.

Argument (the heart of Statement 2): given `x * y ∈ nilradical (S ⊗[k] k')`, use
`exists_fg_subalgebra_mem_range` on `x` and on `y` to obtain fg subalgebras `S₁, S₂`
with `x ∈ range jₛ₁`, `y ∈ range jₛ₂`.  Put `S' := S₁ ⊔ S₂`, finitely generated by
`Subalgebra.FG.sup`.  By `mem_range_tensorMap_mono` (since `S₁, S₂ ≤ S'`) both `x` and
`y` lie in the range of `j := Algebra.TensorProduct.map S'.val (AlgHom.id k k')`, which
is injective (`tensorProduct_map_subalgebra_val_injective`).  Pull back to
`x₀, y₀ : ↥S' ⊗[k] k'` with `j x₀ = x`, `j y₀ = y`.  Since `j` is a ring hom,
`j (x₀ * y₀) = x * y ∈ nilradical`, so by `nilradical_mem_iff_of_injective`,
`x₀ * y₀ ∈ nilradical (↥S' ⊗[k] k')`.  Now `hS S' (fg)` applied to `k'` and rewritten by
`irreducibleSpace_primeSpectrum_iff_nilradical_isPrime` gives
`(nilradical (↥S' ⊗[k] k')).IsPrime`; its `mem_or_mem` yields
`x₀ ∈ nilradical ∨ y₀ ∈ nilradical`.  Transport each disjunct back up with
`nilradical_mem_iff_of_injective` (using `j x₀ = x`, `j y₀ = y`) to conclude
`x ∈ nilradical ∨ y ∈ nilradical`. -/
theorem nilradical_tensorProduct_mem_or_mem_of_forall_fg
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : ∀ (S' : Subalgebra k S), S'.FG →
      Algebra.IsGeometricallyIrreducible k S')
    (k' : Type u) [Field k'] [Algebra k k']
    {x y : S ⊗[k] k'} (hxy : x * y ∈ nilradical (S ⊗[k] k')) :
    x ∈ nilradical (S ⊗[k] k') ∨ y ∈ nilradical (S ⊗[k] k') := by
  obtain ⟨S₁, hS₁fg, hxr⟩ := exists_fg_subalgebra_mem_range k S k' x
  obtain ⟨S₂, hS₂fg, hyr⟩ := exists_fg_subalgebra_mem_range k S k' y
  set S' : Subalgebra k S := S₁ ⊔ S₂
  obtain ⟨x₀, hx₀⟩ := mem_range_tensorMap_mono (S₂ := S') le_sup_left x hxr
  obtain ⟨y₀, hy₀⟩ := mem_range_tensorMap_mono (S₂ := S') le_sup_right y hyr
  set j : (S' ⊗[k] k') →ₐ[k] (S ⊗[k] k') := Algebra.TensorProduct.map S'.val (AlgHom.id k k')
  have hinj : Function.Injective j := tensorProduct_map_subalgebra_val_injective k S k' S'
  -- x₀ * y₀ ∈ nilradical (S' ⊗ k')
  have hxy0 : x₀ * y₀ ∈ nilradical (S' ⊗[k] k') := by
    rwa [nilradical_mem_iff_of_injective j.toRingHom hinj, map_mul, hx₀, hy₀]
  -- nilradical is prime
  refine ((nilradical_tensorProduct_isPrime_of_isGeometricallyIrreducible
    (hS S' (hS₁fg.sup hS₂fg)) k').mem_or_mem hxy0).imp (fun h => ?_) (fun h => ?_)
  · rwa [nilradical_mem_iff_of_injective j.toRingHom hinj, hx₀] at h
  · rwa [nilradical_mem_iff_of_injective j.toRingHom hinj, hy₀] at h

/-- **Statement 2 (Detection by finitely generated subalgebras).** If every finitely
generated `k`-subalgebra of `S` is geometrically irreducible over `k`, then `S` is
geometrically irreducible over `k`.

Proof outline: for each field extension `k'/k`, reduce
`IrreducibleSpace (PrimeSpectrum (S ⊗[k] k'))` to `(nilradical (S ⊗[k] k')).IsPrime`
via `irreducibleSpace_primeSpectrum_iff_nilradical_isPrime`, then build `IsPrime` from
its two pieces: `ne_top` (from `nontrivial_tensorProduct_of_forall_fg`) and `mem_or_mem`
(from `nilradical_tensorProduct_mem_or_mem_of_forall_fg`). -/
@[stacks 037N "(2)"]
theorem isGeometricallyIrreducible_of_forall_fg
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : ∀ (S' : Subalgebra k S), S'.FG →
      Algebra.IsGeometricallyIrreducible k S') :
    Algebra.IsGeometricallyIrreducible k S := by
  exact isGeometricallyIrreducible_of_nilradical_mem_or_mem k S
    (nontrivial_tensorProduct_of_forall_fg k S hS)
    (nilradical_tensorProduct_mem_or_mem_of_forall_fg k S hS)

/-- Correctness characterization for `dlAlg`: when the transition maps `f` are
`k`-algebra maps (hypothesis `hf`), the structure map of `dlAlg` agrees with applying
each colimit inclusion `Ring.DirectLimit.of` to the structure map of `G i`, i.e. each
inclusion is a `k`-algebra homomorphism.  This identifies `dlAlg` as *the* `k`-algebra
structure exhibiting `Ring.DirectLimit G f` as the directed colimit of the `G i` in
`k`-algebras. -/
theorem dlAlg_of_apply
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (i : ι) (x : k) :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i (algebraMap k (G i) x)
      = algebraMap k (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j))) x := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  show Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i (algebraMap k (G i) x)
      = Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) (Classical.arbitrary ι)
          (algebraMap k (G (Classical.arbitrary ι)) x)
  obtain ⟨m, him, ham⟩ := directed_of (· ≤ ·) i (Classical.arbitrary ι)
  rw [← Ring.DirectLimit.of_f him, ← Ring.DirectLimit.of_f ham, hf, hf]

/-! ## Infrastructure for Statement 3 (directed colimits) -/

/-- The colimit inclusion `G i → Ring.DirectLimit G f`, packaged as a `k`-algebra
homomorphism w.r.t. the `dlAlg` structure (the commuting square `dlAlg_of_apply`). -/
noncomputable def dlOfAlg
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (i : ι) :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    G i →ₐ[k] Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) :=
  letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
  { Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i with
    commutes' := fun x => dlAlg_of_apply k G f hf i x }

/-- The transition map `f i j` base-changed to `G i ⊗ k' → G j ⊗ k'`, as a
`k`-algebra hom (`f i j` commutes with the structure maps by `hf`). -/
noncomputable def dlTransAlg
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    (k' : Type w) [Field k'] [Algebra k k'] {i j : ι} (hij : i ≤ j) :
    (G i ⊗[k] k') →ₐ[k] (G j ⊗[k] k') :=
  Algebra.TensorProduct.map
    ({ f i j hij with commutes' := fun x => hf i j hij x }) (AlgHom.id k k')

/-- The base-changed stage map `φᵢ : G i ⊗[k] k' → (Ring.DirectLimit G f) ⊗[k] k'`. -/
noncomputable def dlTensorMap
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (k' : Type w) [Field k'] [Algebra k k'] (i : ι) :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    (G i ⊗[k] k') →ₐ[k] (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k') :=
  letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
  Algebra.TensorProduct.map (dlOfAlg k G f hf i) (AlgHom.id k k')

/-- **Cocone compatibility for the stage maps.** For `i ≤ j`, the stage map `φᵢ`
factors through `φⱼ` via the base-changed transition map: `φⱼ ∘ (f i j ⊗ id) = φᵢ`.

Argument: both sides are `k`-algebra maps `G i ⊗ k' → DirectLimit ⊗ k'`; by
`Algebra.TensorProduct.ext` (or checking on simple tensors `a ⊗ c`) it suffices to
check on elements `a ⊗ c`, where the identity reduces to
`Ring.DirectLimit.of G f j (f i j hij a) = Ring.DirectLimit.of G f i a`, which is
exactly `Ring.DirectLimit.of_f hij`. -/
theorem dlTensorMap_comp_dlTransAlg
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (k' : Type w) [Field k'] [Algebra k k'] {i j : ι} (hij : i ≤ j)
    (a₀ : G i ⊗[k] k') :
    dlTensorMap k G f hf k' j (dlTransAlg k G f hf k' hij a₀)
      = dlTensorMap k G f hf k' i a₀ := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  have key : (dlTensorMap k G f hf k' j).comp (dlTransAlg k G f hf k' hij)
      = dlTensorMap k G f hf k' i := by
    apply Algebra.TensorProduct.ext
    · ext b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        dlTransAlg, dlTensorMap, dlOfAlg, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_mk, AlgHom.coe_id, id_eq]
      rw [Ring.DirectLimit.of_f]
    · ext c
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply,
        dlTransAlg, dlTensorMap, dlOfAlg, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
  exact DFunLike.congr_fun key a₀

/-- **Joint surjectivity of the stage maps.** Every element of
`(Ring.DirectLimit G f) ⊗[k] k'` is in the image of some `φᵢ`.

Argument: write `a = ∑ₗ gₗ ⊗ cₗ` as a finite sum of simple tensors
(`TensorProduct.exists_finset`).  Each `gₗ ∈ Ring.DirectLimit G f` is `of iₗ hₗ`
for some stage `iₗ` and `hₗ : G iₗ` (`Ring.DirectLimit.exists_of`).  By directedness of
`ι` (`Finset`-version `Finset.exists_le` / iterated `directed_of`), pick a common stage
`i` with `iₗ ≤ i` for all `l`; replace each `gₗ = of i (f iₗ i _ hₗ)` via
`Ring.DirectLimit.of_f`.  Then `a₀ := ∑ₗ (f iₗ i _ hₗ) ⊗ cₗ : G i ⊗ k'` satisfies
`φᵢ a₀ = a` because `φᵢ` is a `k`-algebra hom sending `b ⊗ c ↦ (of i b) ⊗ c`. -/
theorem dlTensorMap_surjective
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (k' : Type w) [Field k'] [Algebra k k']
    (a : letI := dlAlg k G (fun i j h => (f i j h : G i → G j));
         Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k') :
    ∃ (i : ι) (a₀ : G i ⊗[k] k'), dlTensorMap k G f hf k' i a₀ = a := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨Classical.arbitrary ι, 0, map_zero _⟩
  | tmul g c =>
    obtain ⟨i, b, hb⟩ := Ring.DirectLimit.exists_of g
    refine ⟨i, b ⊗ₜ c, ?_⟩
    simp only [dlTensorMap, dlOfAlg, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_mk, AlgHom.coe_id, id_eq]
    rw [hb]
  | add x y hx hy =>
    obtain ⟨i₁, a₁, ha₁⟩ := hx
    obtain ⟨i₂, a₂, ha₂⟩ := hy
    obtain ⟨i, hi₁, hi₂⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨i, dlTransAlg k G f hf k' hi₁ a₁ + dlTransAlg k G f hf k' hi₂ a₂, ?_⟩
    rw [map_add, dlTensorMap_comp_dlTransAlg, dlTensorMap_comp_dlTransAlg, ha₁, ha₂]

section TensorSystem

variable (k : Type u) [Field k] {ι : Type w₁} [Preorder ι]
  (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
  (f : (i j : ι) → i ≤ j → G i →+* G j)
  (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
    f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
  (k' : Type w) [Field k'] [Algebra k k']

/-- The base-changed transition map acts on simple tensors by `a ⊗ c ↦ f i j a ⊗ c`. -/
@[simp]
theorem dlTransAlg_tmul {i j : ι} (hij : i ≤ j) (a : G i) (c : k') :
    dlTransAlg k G f hf k' hij (a ⊗ₜ c) = f i j hij a ⊗ₜ c :=
  rfl

/-- The base-changed transition map `G i ⊗ k' → G i ⊗ k'` is the identity. -/
theorem dlTransAlg_refl [DirectedSystem G (fun i j h => (f i j h : G i → G j))] (i : ι) :
    dlTransAlg k G f hf k' (le_refl i) = AlgHom.id k (G i ⊗[k] k') :=
  Algebra.TensorProduct.ext' fun a c => by
    rw [dlTransAlg_tmul, AlgHom.id_apply]
    congr 1
    exact DirectedSystem.map_self (f := fun i j h => (f i j h : G i → G j)) a

/-- The base-changed transition maps compose. -/
theorem dlTransAlg_comp [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    {i j l : ι} (hij : i ≤ j) (hjl : j ≤ l) :
    (dlTransAlg k G f hf k' hjl).comp (dlTransAlg k G f hf k' hij)
      = dlTransAlg k G f hf k' (hij.trans hjl) :=
  Algebra.TensorProduct.ext' fun a c => by
    rw [AlgHom.comp_apply, dlTransAlg_tmul, dlTransAlg_tmul, dlTransAlg_tmul]
    congr 1
    exact DirectedSystem.map_map (f := fun i j h => (f i j h : G i → G j)) hij hjl a

/-- The base-changed transition maps form a directed system. -/
theorem dlTransAlg_directedSystem [DirectedSystem G (fun i j h => (f i j h : G i → G j))] :
    DirectedSystem (fun i => G i ⊗[k] k')
      (fun i j h => ((dlTransAlg k G f hf k' h).toRingHom : G i ⊗[k] k' → G j ⊗[k] k')) := by
  constructor
  · intro i x
    exact DFunLike.congr_fun (dlTransAlg_refl k G f hf k' i) x
  · intro _ _ _ hij hjk x
    exact DFunLike.congr_fun (dlTransAlg_comp k G f hf k' hij hjk) x

/-- The directed colimit of the base-changed system `i ↦ G i ⊗[k] k'`. -/
abbrev dlTensorLimit : Type _ :=
  Ring.DirectLimit (fun i => G i ⊗[k] k')
    (fun i j h => ((dlTransAlg k G f hf k' h).toRingHom : G i ⊗[k] k' → G j ⊗[k] k'))

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]
  [DirectedSystem G (fun i j h => (f i j h : G i → G j))]

/-- The colimit inclusion `G i ⊗[k] k' → dlTensorLimit k G f hf k'`, as a `k`-algebra map. -/
noncomputable def dlTensorOf (i : ι) :
    letI : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
    G i ⊗[k] k' →ₐ[k] dlTensorLimit k G f hf k' :=
  haveI := dlTransAlg_directedSystem k G f hf k'
  dlOfAlg k (fun i => G i ⊗[k] k') (fun _ _ h => (dlTransAlg k G f hf k' h).toRingHom)
    (fun _ _ h x => (dlTransAlg k G f hf k' h).commutes x) i

/-- The colimit inclusions are compatible with the base-changed transition maps. -/
theorem dlTensorOf_trans {i j : ι} (hij : i ≤ j) (a : G i ⊗[k] k') :
    dlTensorOf k G f hf k' j (dlTransAlg k G f hf k' hij a) = dlTensorOf k G f hf k' i a := by
  have := dlTransAlg_directedSystem k G f hf k'
  exact Ring.DirectLimit.of_f (G := fun i => G i ⊗[k] k')
    (f := fun i j h => ((dlTransAlg k G f hf k' h).toRingHom : G i ⊗[k] k' → G j ⊗[k] k')) hij a

/-- The image of `1 ⊗ c` in the colimit does not depend on the stage. -/
theorem dlTensorOf_one_tmul {i j : ι} (hij : i ≤ j) (c : k') :
    dlTensorOf k G f hf k' j (1 ⊗ₜ c) = dlTensorOf k G f hf k' i (1 ⊗ₜ c) := by
  simpa using dlTensorOf_trans k G f hf k' hij (1 ⊗ₜ c)

/-- The map `Ring.DirectLimit G f → dlTensorLimit k G f hf k'` induced by `x ↦ x ⊗ₜ 1`. -/
noncomputable def dlTensorInvLeft :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    letI : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
    Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) →ₐ[k] dlTensorLimit k G f hf k' :=
  letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
  letI : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
  { Ring.DirectLimit.lift G (fun i j h => (f i j h : G i → G j)) _
      (fun i => ((dlTensorOf k G f hf k' i).comp Algebra.TensorProduct.includeLeft).toRingHom)
      (fun _ _ hij x => by simpa using dlTensorOf_trans k G f hf k' hij (x ⊗ₜ 1)) with
    commutes' := fun x =>
      (Ring.DirectLimit.lift_of _ _ _ (Classical.arbitrary ι) _).trans
        (((dlTensorOf k G f hf k' _).comp Algebra.TensorProduct.includeLeft).commutes x) }

/-- `dlTensorInvLeft` sends `of i b` to the class of `b ⊗ 1`. -/
theorem dlTensorInvLeft_of (i : ι) (b : G i) :
    dlTensorInvLeft k G f hf k' (Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i b)
      = dlTensorOf k G f hf k' i (b ⊗ₜ 1) := by
  simp [dlTensorInvLeft]

/-- The inverse comparison map `(Ring.DirectLimit G f) ⊗[k] k' → dlTensorLimit k G f hf k'`. -/
noncomputable def dlTensorInv :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    letI : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
    Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k' →ₐ[k]
      dlTensorLimit k G f hf k' :=
  letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
  letI : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
  Algebra.TensorProduct.lift (dlTensorInvLeft k G f hf k')
    ((dlTensorOf k G f hf k' (Classical.arbitrary ι)).comp Algebra.TensorProduct.includeRight)
    fun _ _ => Commute.all _ _

/-- `dlTensorInv` is a left inverse of each stage map `dlTensorMap`. -/
theorem dlTensorInv_dlTensorMap (i : ι) (a : G i ⊗[k] k') :
    dlTensorInv k G f hf k' (dlTensorMap k G f hf k' i a) = dlTensorOf k G f hf k' i a := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  let : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    obtain ⟨m, him, ham⟩ := directed_of (· ≤ ·) i (Classical.arbitrary ι)
    show dlTensorInv k G f hf k'
      (Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i b ⊗ₜ c) = _
    rw [dlTensorInv, Algebra.TensorProduct.lift_tmul, dlTensorInvLeft_of, AlgHom.comp_apply,
      Algebra.TensorProduct.includeRight_apply, ← dlTensorOf_one_tmul k G f hf k' ham,
      dlTensorOf_one_tmul k G f hf k' him, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]

end TensorSystem

/-- **Zero-exactness of the stage maps (tensor version of
`Ring.DirectLimit.of.zero_exact`).** If `φᵢ a₀ = 0`, then `a₀` already dies at some
later stage `j ≥ i`: `(f i j ⊗ id) a₀ = 0` in `G j ⊗ k'`.

Argument: this is the statement that `(Ring.DirectLimit G f) ⊗ k'` is the directed
colimit of the `G i ⊗ k'` (tensoring with the flat — indeed free — `k`-module `k'`
commutes with filtered colimits and preserves the relations).  Concretely: writing the
colimit as a quotient of `⨁ᵢ G i` by the colimit relation and base-changing by `k'`
(flatness over the field `k`), an element that maps to `0` in the colimit-tensor is
killed by a finite stage.  Formalization route: transport `Ring.DirectLimit.of.zero_exact`
through the `RingEquiv` (tensor commutes with `Ring.DirectLimit`), or build the colimit
`Ring.DirectLimit (fun i => G i ⊗ k') (dlTransAlg …)` and the comparison iso to
`(Ring.DirectLimit G f) ⊗ k'`, whose `of.zero_exact` gives the witness stage.  This is
the single genuinely analytic kernel of Statement 3. -/
theorem dlTensorMap_zero_exact
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w₂) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (k' : Type w) [Field k'] [Algebra k k'] (i : ι) (a₀ : G i ⊗[k] k')
    (h0 : dlTensorMap k G f hf k' i a₀ = 0) :
    ∃ (j : ι) (hij : i ≤ j), dlTransAlg k G f hf k' hij a₀ = 0 := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  let : Algebra k (dlTensorLimit k G f hf k') := dlAlg k _ _
  have := dlTransAlg_directedSystem k G f hf k'
  have h : dlTensorOf k G f hf k' i a₀ = 0 := by
    rw [← dlTensorInv_dlTensorMap, h0, map_zero]
  exact Ring.DirectLimit.of.zero_exact
    (f' := fun i j h => (dlTransAlg k G f hf k' h).toRingHom) h

/-- **Statement 3, nontriviality part.** `(Ring.DirectLimit G f) ⊗[k] k'` is nontrivial.

Argument: pick any stage `i₀` (using `Nonempty ι`).  `hG i₀` applied to `k'` shows
`G i₀ ⊗ k'` is irreducible hence nontrivial, so `(1 : G i₀ ⊗ k') ≠ 0`.  Suppose for
contradiction `(1 : DirectLimit ⊗ k') = 0`.  Since `φ_{i₀}` is a ring hom,
`φ_{i₀} 1 = 1 = 0`, so by `dlTensorMap_zero_exact` there is `j ≥ i₀` with
`(f i₀ j ⊗ id) 1 = 0`, i.e. `(1 : G j ⊗ k') = 0` — contradicting that `G j ⊗ k'` is
nontrivial (`hG j` applied to `k'`). -/
theorem nontrivial_directLimit_tensorProduct
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (hG : ∀ i, Algebra.IsGeometricallyIrreducible k (G i))
    (k' : Type u) [Field k'] [Algebra k k'] :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    Nontrivial (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k') := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  -- Pick a base stage.
  set i₀ := Classical.arbitrary ι
  -- Show `(1 : DirectLimit ⊗ k') ≠ 0`, giving nontriviality.
  refine ⟨1, 0, fun hcontra => ?_⟩
  -- `φ_{i₀} (1 : G i₀ ⊗ k') = 1 = 0`.
  have h0 : dlTensorMap k G f hf k' i₀ (1 : G i₀ ⊗[k] k') = 0 := by
    rw [map_one, hcontra]
  -- Zero-exactness: `1` dies at some later stage `j`.
  obtain ⟨j, hij, hj⟩ := dlTensorMap_zero_exact k G f hf k' i₀ (1 : G i₀ ⊗[k] k') h0
  -- But `dlTransAlg` is a `k`-algebra hom, so it sends `1 ↦ 1`.
  rw [map_one] at hj
  -- Hence `(1 : G j ⊗ k') = 0`, contradicting nontriviality of `G j ⊗ k'`.
  -- Every stage `G i ⊗ k'` is nontrivial (its nilradical is prime, hence ≠ ⊤).
  have := nontrivial_tensorProduct_of_isGeometricallyIrreducible (hG j) k'
  exact one_ne_zero hj

/-- **Statement 3, prime implication part.** The nilradical of
`(Ring.DirectLimit G f) ⊗[k] k'` satisfies the prime multiplicative property.

Argument (heart of Statement 3): suppose `x * y ∈ nilradical`, so `(x*y)^n = 0` for some
`n`.  By `dlTensorMap_surjective` get a common stage `i` and `x₀, y₀ : G i ⊗ k'` with
`φᵢ x₀ = x`, `φᵢ y₀ = y` (pick the stage common to both by directedness, transporting via
`dlTensorMap_comp_dlTransAlg`).  Then `φᵢ ((x₀*y₀)^n) = (x*y)^n = 0`, so by
`dlTensorMap_zero_exact` there is `j ≥ i` with `(f i j ⊗ id) ((x₀*y₀)^n) = 0` in
`G j ⊗ k'`; writing `x₁ := (f i j ⊗ id) x₀`, `y₁ := (f i j ⊗ id) y₀` this says
`(x₁*y₁)^n = 0`, i.e. `x₁*y₁ ∈ nilradical (G j ⊗ k')`.  Now `hG j` applied to `k'`,
rewritten by `irreducibleSpace_primeSpectrum_iff_nilradical_isPrime`, gives
`(nilradical (G j ⊗ k')).IsPrime`, whose `mem_or_mem` yields
`x₁ ∈ nilradical ∨ y₁ ∈ nilradical`.  Apply `φⱼ` (ring hom preserves nilpotents) and use
`dlTensorMap_comp_dlTransAlg` (`φⱼ x₁ = φᵢ x₀ = x`, similarly `y`) to push the chosen
disjunct up to `x ∈ nilradical ∨ y ∈ nilradical`. -/
theorem nilradical_directLimit_tensorProduct_mem_or_mem
    (k : Type u) [Field k]
    {ι : Type w₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (hG : ∀ i, Algebra.IsGeometricallyIrreducible k (G i))
    (k' : Type u) [Field k'] [Algebra k k']
    {x y : letI := dlAlg k G (fun i j h => (f i j h : G i → G j));
           Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k'}
    (hxy : letI := dlAlg k G (fun i j h => (f i j h : G i → G j));
           x * y ∈ nilradical (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k')) :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j));
    x ∈ nilradical (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k')
      ∨ y ∈ nilradical (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ⊗[k] k') := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  -- Step 1: surjectivity to get stages for x and y
  obtain ⟨i₁, x₀, hx₀⟩ := dlTensorMap_surjective k G f hf k' x
  obtain ⟨i₂, y₀', hy₀'⟩ := dlTensorMap_surjective k G f hf k' y
  -- Step 2: common stage
  obtain ⟨i, hi₁, hi₂⟩ := directed_of (· ≤ ·) i₁ i₂
  set X₀ : G i ⊗[k] k' := dlTransAlg k G f hf k' hi₁ x₀ with hX₀def
  set Y₀ : G i ⊗[k] k' := dlTransAlg k G f hf k' hi₂ y₀' with hY₀def
  have hx : dlTensorMap k G f hf k' i X₀ = x := by
    rw [hX₀def, dlTensorMap_comp_dlTransAlg, hx₀]
  have hy : dlTensorMap k G f hf k' i Y₀ = y := by
    rw [hY₀def, dlTensorMap_comp_dlTransAlg, hy₀']
  -- Step 3: (x*y)^n = 0 lifts to φᵢ ((X₀*Y₀)^n) = 0
  rw [mem_nilradical] at hxy
  obtain ⟨n, hn⟩ := hxy
  have hφ0 : dlTensorMap k G f hf k' i ((X₀ * Y₀) ^ n) = 0 := by
    rw [map_pow, map_mul, hx, hy, hn]
  -- Step 4: zero-exactness gives a later stage j
  obtain ⟨j, hij, hj⟩ := dlTensorMap_zero_exact k G f hf k' i ((X₀ * Y₀) ^ n) hφ0
  set x₁ : G j ⊗[k] k' := dlTransAlg k G f hf k' hij X₀ with hx₁def
  set y₁ : G j ⊗[k] k' := dlTransAlg k G f hf k' hij Y₀ with hy₁def
  have hxy1 : x₁ * y₁ ∈ nilradical (G j ⊗[k] k') := by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    rw [hx₁def, hy₁def, ← map_mul, ← map_pow, hj]
  -- Step 5: nilradical of G j ⊗ k' is prime
  have hirr := nilradical_tensorProduct_isPrime_of_isGeometricallyIrreducible (hG j) k'
  -- relate φⱼ x₁ = x and φⱼ y₁ = y
  have hφjx : dlTensorMap k G f hf k' j x₁ = x := by
    rw [hx₁def, dlTensorMap_comp_dlTransAlg, hx]
  have hφjy : dlTensorMap k G f hf k' j y₁ = y := by
    rw [hy₁def, dlTensorMap_comp_dlTransAlg, hy]
  exact (hirr.mem_or_mem hxy1).imp
    (fun h => hφjx ▸ IsNilpotent.map h (dlTensorMap k G f hf k' j))
    (fun h => hφjy ▸ IsNilpotent.map h (dlTensorMap k G f hf k' j))

/-- **Statement 3 (Directed colimits).** A directed colimit of geometrically
irreducible `k`-algebras is geometrically irreducible over `k`.

The directed system is given by a directed preorder `ι`, `k`-algebras `G i`, and
transition ring homomorphisms `f i j : G i →+* G j` (for `i ≤ j`) that commute with
the structure maps from `k` (`hf`) and form a `DirectedSystem`.  The colimit is
`Ring.DirectLimit G f`, equipped with the `k`-algebra structure `dlAlg k G f`.

Proof outline: for each field extension `k'/k`, reduce to
`(nilradical (DirectLimit ⊗ k')).IsPrime` via
`irreducibleSpace_primeSpectrum_iff_nilradical_isPrime`, then assemble `IsPrime` from
`nontrivial_directLimit_tensorProduct` (nontriviality ⇒ `ne_top`) and
`nilradical_directLimit_tensorProduct_mem_or_mem` (the prime implication). -/
@[stacks 037N "(3)"]
theorem isGeometricallyIrreducible_directLimit
    (k : Type u) [Field k]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    (hf : ∀ (i j : ι) (h : i ≤ j) (x : k),
      f i j h (algebraMap k (G i) x) = algebraMap k (G j) x)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (hG : ∀ i, Algebra.IsGeometricallyIrreducible k (G i)) :
    letI := dlAlg k G (fun i j h => (f i j h : G i → G j))
    Algebra.IsGeometricallyIrreducible k
      (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j))) := by
  let := dlAlg k G (fun i j h => (f i j h : G i → G j))
  exact isGeometricallyIrreducible_of_nilradical_mem_or_mem k _
    (nontrivial_directLimit_tensorProduct k G f hf hG)
    (nilradical_directLimit_tensorProduct_mem_or_mem k G f hf hG)
