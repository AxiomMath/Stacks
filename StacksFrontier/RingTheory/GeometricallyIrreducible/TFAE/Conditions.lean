module

public import StacksCore.FieldTheory.MvRatFunc.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Geometric irreducibility: the four conditions and first reductions

This file defines the four conditions `GeomIrred1`–`GeomIrred4`, proves the arrows
`(2) ⇒ (3)` and `(3) ⇒ (4)`, and develops the first reduction stages of the field main lemma
(dense-range transfer, filtered-colimit reduction, the finitely generated presentation, and the
localization base-change kernel). It is part of
`StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE`.
-/

/-!
# Four equivalent forms of geometric irreducibility

Throughout, `k` is a field and `R` a commutative unital `k`-algebra. The following four
conditions on `(k, R)` are equivalent, and together say that `R` is *geometrically irreducible*
over `k`.

1. For every field extension `k'/k`, the space `Spec (R ⊗_k k')` is irreducible.
2. For every finite separable field extension `k'/k`, the space `Spec (R ⊗_k k')` is
   irreducible.
3. The space `Spec (R ⊗_k k^sep)` is irreducible, `k^sep` being a separable algebraic closure
   of `k`.
4. The space `Spec (R ⊗_k k̄)` is irreducible, `k̄` being an algebraic closure of `k`.

## Background and conventions

`R ⊗_k k'` is the tensor product of `k`-algebras, regarded as a commutative ring, and `Spec A`
is the prime spectrum with its Zariski topology. A topological space is *irreducible* when it
is nonempty and not the union of two proper closed subsets, equivalently when any two nonempty
opens intersect; by convention the empty space is not irreducible, so each of the four
conditions implies `R ≠ 0`.

Here `k^sep` is `SeparableClosure k` and `k̄` is `AlgebraicClosure k`. Since any two separable
algebraic closures of `k` are `k`-isomorphic, the truth of conditions 3 and 4 does not depend on
the chosen closure. A finite separable field extension is `FiniteDimensional k k'` together
with `Algebra.IsSeparable k k'`.

## Quantifier scope in conditions 1 and 2

Every field extension `k'/k` means every field `k'` carrying a `k`-algebra structure. Here `k`
and `R` live in a fixed universe `u`, and the test field `k'` is quantified over `Type u`, the
same universe as the fixed closures `SeparableClosure k` and `AlgebraicClosure k`. This is the
faithful choice: it lets condition 1 be instantiated at the closures, giving `(1) → (3)` and
`(1) → (4)`, while the substantive directions `(2)/(3)/(4) → (1)` show that checking the single
field `k̄`, or `k^sep`, already forces irreducibility for every such extension. The content,
that no enlargement of the base field destroys irreducibility, is fully captured.

The implications `(1) → (2)`, `(1) → (3)` and `(1) → (4)` are immediate instantiations of
condition 1. The substantive content is that each of the weaker conditions 2, 3 and 4 implies
condition 1.
-/

@[expose] public section

open TensorProduct

universe u

/-- Condition (1): for every field extension `k'/k`, `Spec(R ⊗_k k')` is irreducible. -/
@[ega "IV 4.5.2" "(c), special case", ega "IV 4.5.9"]
def GeomIrred1 (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'],
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] k'))

/-- Condition (2): for every finite separable field extension `k'/k`, `Spec(R ⊗_k k')` is
irreducible. -/
def GeomIrred2 (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'],
    FiniteDimensional k k' → Algebra.IsSeparable k k' →
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] k'))

/-- Condition (3): `Spec(R ⊗_k k^sep)` is irreducible, for `k^sep = SeparableClosure k`. -/
def GeomIrred3 (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] : Prop :=
  IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k))

/-- Condition (4): `Spec(R ⊗_k k̄)` is irreducible, for `k̄ = AlgebraicClosure k`. -/
@[ega "IV 4.5.2" "special case"]
def GeomIrred4 (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] : Prop :=
  IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k))

/-
## Proof strategy (the Stacks 037K cycle `(1) ⇒ (2) ⇒ (3) ⇒ (4) ⇒ (1)`)

`(1) ⇒ (2)` is immediate: a finite separable extension is in particular a field extension,
so we just instantiate `GeomIrred1` at `k'` and discard the two extra hypotheses. This arm
is closed inline in the main theorem (`intro h k' _ _ _ _; exact h k'`); `tfae_finish` then
derives every remaining implication of the TFAE from the 4-cycle.

The three substantive arrows are isolated as the named sub-lemmas
`geomIrred_step_2_3`, `geomIrred_step_3_4` and `geomIrred_step_4_1` below, each documented with
its mathematical argument.

A *key reusable characterization* used throughout (Mathlib):
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical :`
     `IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime`.
So for a commutative ring `A`, `Spec A` is irreducible iff the nilradical of `A` is a prime
ideal. Equivalently `A` has a unique minimal prime AND `A ≠ 0` (a prime ideal is proper, so
the existence of a prime forces `A ≠ 0`; and `nilradical A = ⋂ minimal primes`, which is
prime iff there is a unique minimal prime over the reduced ring — more precisely
`(nilradical A).IsPrime` says the set of nilpotents is prime). This translates each
`IrreducibleSpace` goal into "`nilradical` is prime", a purely ring-theoretic statement on
which the integral / flat / base-change machinery acts.
-/

-- Main Sub-lemmas (one per substantive arrow of the cycle)

/-- A sum of pure tensors whose factors lie in the ranges of `f` and `g` lies in the range of
`Algebra.TensorProduct.map f g`. -/
private theorem tensor_mem_range_map {k A B C D : Type*} [CommRing k] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] C) (g : B →ₐ[k] D) (s : Finset (C × D))
    (hs : ∀ i ∈ s, i.1 ∈ f.range ∧ i.2 ∈ g.range) :
    (∑ i ∈ s, i.1 ⊗ₜ[k] i.2) ∈ (Algebra.TensorProduct.map f g).range := by
  refine Subalgebra.sum_mem _ fun i hi => ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hs i hi
  exact ⟨a ⊗ₜ[k] b, by simp [show f a = i.1 from ha, show g b = i.2 from hb]⟩

/-- If `ι : A → B` is injective and `nilradical A` is prime, then two elements of the range of `ι`
whose product is nilpotent have a nilpotent one among them. -/
private theorem mem_or_mem_nilradical_of_mem_range {A B : Type*} [CommRing A] [CommRing B]
    (ι : A →+* B) (hinj : Function.Injective ι) (hprime : (nilradical A).IsPrime) {x y : B}
    (hx : x ∈ ι.range) (hy : y ∈ ι.range) (hxy : x * y ∈ nilradical B) :
    x ∈ nilradical B ∨ y ∈ nilradical B := by
  obtain ⟨x₀, rfl⟩ := hx
  obtain ⟨y₀, rfl⟩ := hy
  have hxy0 : x₀ * y₀ ∈ nilradical A := by
    obtain ⟨n, hn⟩ := mem_nilradical.mp hxy
    exact mem_nilradical.mpr ⟨n, hinj (by rw [map_pow, map_mul, hn, map_zero])⟩
  rcases hprime.mem_or_mem hxy0 with h | h
  · exact .inl (mem_nilradical.mpr ((mem_nilradical.mp h).map ι))
  · exact .inr (mem_nilradical.mpr ((mem_nilradical.mp h).map ι))

/-- **Arrow `(2) ⇒ (3)`.** If `Spec(R ⊗_k k')` is irreducible for every *finite separable*
extension `k'/k`, then `Spec(R ⊗_k k^sep)` is irreducible, where `k^sep = SeparableClosure k`.

INFORMAL ARGUMENT (rigorous; Stacks 037K, step (2)⇒(3)):

Write `K := k^sep = SeparableClosure k`. We must show `Spec(R ⊗_k K)` is irreducible, i.e.
(via `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`) that `nilradical (R ⊗_k K)` is
prime, equivalently that `R ⊗_k K` is nonempty as a spectrum and has a *unique minimal prime*.

* Nonemptiness / `R ⊗_k K ≠ 0`. Apply (2) to the trivial finite separable extension `k' = k`
  (`FiniteDimensional k k` and `Algebra.IsSeparable k k` both hold). This gives
  `IrreducibleSpace (PrimeSpectrum (R ⊗_k k))`, hence `R ⊗_k k ≠ 0` (irreducible ⇒ nonempty
  spectrum ⇒ nonzero ring), hence `R ≠ 0`. Since `K` is a nonzero free (in particular
  faithfully flat) `k`-module, `R ⊗_k K ≠ 0`, so `Spec(R ⊗_k K)` is nonempty.

* Unique minimal prime. `K = SeparableClosure k` is the *directed union* (filtered colimit)
  of its finite separable subextensions `k'/k` (every element of `K` is separable algebraic
  over `k`, so lies in a finite separable subextension; finitely many such elements generate a
  finite separable subextension — `IntermediateField.finiteDimensional_adjoin` /
  `Stacks 09GH`). Tensoring the directed system `{k'}` with `R` over `k` (tensor product
  commutes with filtered colimits) exhibits `R ⊗_k K` as the *filtered colimit* of the system
  `{R ⊗_k k'}` along the transition maps `R ⊗_k k' → R ⊗_k k''` (for `k' ⊆ k''`), and these
  transition maps as well as the maps `R ⊗_k k' → R ⊗_k K` are *injective* (base change of the
  injective, faithfully flat field inclusions `k' ↪ k''`, `k' ↪ K`).

  Suppose `q₁, q₂` are two minimal primes of `R ⊗_k K`. For each finite separable `k'`, the
  ring map `φ_{k'} : R ⊗_k k' → R ⊗_k K` is *flat* (it is `R`-base change of the flat — indeed
  free — map `k' → K`). By going-down for flat ring maps (Stacks 10.39.19; Mathlib via
  `Algebra.HasGoingDown` / flatness), the contraction `pᵢ(k') := φ_{k'}⁻¹(qᵢ)` is a *minimal*
  prime of `R ⊗_k k'`. By hypothesis (2), `Spec(R ⊗_k k')` is irreducible, so `R ⊗_k k'` has a
  unique minimal prime; hence `p₁(k') = p₂(k')` for every finite separable `k'`. Because
  `R ⊗_k K` is the filtered colimit of the `R ⊗_k k'` with injective transition maps, every
  element of `R ⊗_k K` lies in the image of some `R ⊗_k k'`, and membership in `qᵢ` is detected
  at that finite stage (i.e. `qᵢ = ⋃_{k'} φ_{k'}(pᵢ(k'))`, the colimit of the contractions).
  Since `p₁(k') = p₂(k')` at every stage, `q₁ = q₂`. Thus `R ⊗_k K` has a unique minimal prime.

  A nonzero ring with a unique minimal prime has prime nilradical (the nilradical is the
  intersection of the minimal primes, which here is the single minimal prime), so
  `nilradical (R ⊗_k K)` is prime and `Spec(R ⊗_k K)` is irreducible.

LEAN INPUTS: `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`; directed-union structure
of `SeparableClosure k` over finite separable subextensions (`IntermediateField`,
`separableClosure`, `IntermediateField.finiteDimensional_adjoin`); commutation of `⊗` with
filtered colimits; flatness/faithful-flatness of base change of field extensions
(`Module.Flat`, `Module.FaithfullyFlat`); going-down for flat maps
(`Algebra.HasGoingDown`/`RingHom.Flat`) giving minimal-prime contraction is minimal;
`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` (Stacks 00FK) for descent of minimal
primes along injective maps. -/
theorem geomIrred_step_2_3
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (h : GeomIrred2 k R) : GeomIrred3 k R := by
  classical
  change IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k))
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  -- Nontriviality of `R ⊗[k] SeparableClosure k`: from (2) at `k' = k` the spectrum of
  -- `R ⊗[k] k` is nonempty, hence `R ⊗[k] k` is nontrivial, hence `R` is, hence (faithful
  -- flatness of the field `SeparableClosure k`) `R ⊗[k] SeparableClosure k` is nontrivial.
  have hk : IrreducibleSpace (PrimeSpectrum (R ⊗[k] k)) := h k inferInstance inferInstance
  obtain ⟨p⟩ := hk.toNonempty
  have : Nontrivial (R ⊗[k] k) := p.nontrivial
  have hRnt : Nontrivial R :=
    (Algebra.TensorProduct.rid k k R).symm.toRingEquiv.toEquiv.nontrivial
  have : Nontrivial (R ⊗[k] SeparableClosure k) :=
    Module.FaithfullyFlat.lTensor_nontrivial k R (SeparableClosure k)
  refine ⟨?_, ?_⟩
  · -- `nilradical ≠ ⊤`: it is contained in any maximal (hence prime, proper) ideal.
    obtain ⟨q⟩ := (PrimeSpectrum.instNonemptyOfNontrivial (R := R ⊗[k] SeparableClosure k))
    exact ne_top_of_le_ne_top q.isPrime.ne_top (@nilradical_le_prime _ _ q.asIdeal q.isPrime)
  · -- Prime condition for the nilradical: capture `x` and `y` at a common finite separable
    -- stage `k' = adjoin k (finitely many separable elements) ⊆ SeparableClosure k`, where
    -- (2) gives `(nilradical (R ⊗[k] k')).IsPrime`, then push back up the injective base change.
    intro x y hxy
    obtain ⟨Sx, hSx⟩ := TensorProduct.exists_finset x
    obtain ⟨Sy, hSy⟩ := TensorProduct.exists_finset y
    set S : Finset (R × SeparableClosure k) := Sx ∪ Sy with hS
    set k' : IntermediateField k (SeparableClosure k) :=
      IntermediateField.adjoin k (↑(S.image Prod.snd) : Set (SeparableClosure k)) with hk'
    -- `k'/k` is finite (each generator is integral over `k`) and separable (subextension of the
    -- separable extension `SeparableClosure k / k`).
    have hfd : FiniteDimensional k k' :=
      IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
    have hsep : Algebra.IsSeparable k k' :=
      Algebra.isSeparable_tower_bot_of_isSeparable k (k' : Type u) (SeparableClosure k)
    -- The base-change map `ι : R ⊗[k] k' → R ⊗[k] SeparableClosure k` is injective.
    set ι := Algebra.TensorProduct.map (AlgHom.id k R) k'.val with hι
    have hinj : Function.Injective ι := fun _ _ hab =>
      TensorProduct.map_injective_of_flat_flat (AlgHom.id k R).toLinearMap k'.val.toLinearMap
        Function.injective_id k'.val.injective hab
    -- `nilradical (R ⊗[k] k')` is prime by hypothesis (2) on the finite separable `k'`.
    have hprime : (nilradical (R ⊗[k] (k' : Type u))).IsPrime :=
      PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp (h (k' : Type u) hfd hsep)
    -- A sum of pure tensors with second components in `S` lands in the image of `ι`.
    have hcap : ∀ (T : Finset (R × SeparableClosure k)), T ⊆ S →
        (∑ i ∈ T, i.fst ⊗ₜ[k] i.snd) ∈ ι.range := fun T hT =>
      tensor_mem_range_map (AlgHom.id k R) k'.val T fun i hi =>
        ⟨⟨i.1, rfl⟩, ⟨i.2, IntermediateField.subset_adjoin k _
          (by simpa using ⟨i.1, hT hi⟩)⟩, rfl⟩
    exact mem_or_mem_nilradical_of_mem_range ι.toRingHom hinj hprime
      (by rw [hSx]; exact hcap Sx Finset.subset_union_left)
      (by rw [hSy]; exact hcap Sy Finset.subset_union_right) hxy

/-- **Arrow `(3) ⇒ (4)`.** If `Spec(R ⊗_k k^sep)` is irreducible then so is `Spec(R ⊗_k k̄)`,
where `k^sep = SeparableClosure k` and `k̄ = AlgebraicClosure k`.

INFORMAL ARGUMENT (rigorous; Stacks 037K, step (3)⇒(4)):

Write `K := SeparableClosure k` and `L := AlgebraicClosure k`. There is a canonical
`k`-embedding `K ↪ L` (the separable closure sits inside the algebraic closure), and the
extension `L / K` is *purely inseparable*: `K` is precisely the separable closure of `k` in
`L`, and `L / k` is algebraic, so `L = (separableClosure k L)`'s purely inseparable closure —
Mathlib's `separableClosure.isPurelyInseparable (F := k) (E := L)` states
`IsPurelyInseparable ↥(separableClosure k L) L`, and `K ≃ ↥(separableClosure k L)` canonically.

Base change `R ⊗_k (·)` along `K ↪ L` gives a ring map
  `ψ : R ⊗_k K → R ⊗_k L`,
which is the `R`-base change of `K ↪ L`. We claim `Spec(ψ)` (i.e. `PrimeSpectrum.comap ψ`) is a
*homeomorphism*. Indeed:

* `L / K` purely inseparable ⇒ `L` is *integral* over `K` and the map `K → L` is *radicial*
  (universally injective): purely inseparable extensions are integral, and the relative
  Frobenius is bijective on points. Base change preserves these: `ψ : R ⊗_k K → R ⊗_k L` is
  integral (`RingHom.isIntegral_isStableUnderBaseChange`, Stacks 02JK) and radicial. A ring map
  that is integral and induces an injective and surjective (hence bijective and closed, as
  integral maps are closed on `Spec`) map on prime spectra is a *homeomorphism* on `Spec`
  (Stacks 037K cites Stacks 04XV / universal homeomorphism for purely inseparable; concretely:
  `PrimeSpectrum.comap ψ` is continuous, closed — integral ⇒ closed — bijective).

  More precisely, a purely inseparable extension induces a *universal homeomorphism* on spectra
  after any base change; in particular `Spec(R ⊗_k L) → Spec(R ⊗_k K)` is a homeomorphism.

* Transport irreducibility along the homeomorphism: `IrreducibleSpace` is a topological
  invariant, so from `IrreducibleSpace (PrimeSpectrum (R ⊗_k K))` (hypothesis (3)) we get
  `IrreducibleSpace (PrimeSpectrum (R ⊗_k L))` via `Homeomorph.irreducibleSpace_iff`.

LEAN INPUTS: `separableClosure.isPurelyInseparable`; `IsPurelyInseparable` ⇒ integral/radicial;
`RingHom.isIntegral_isStableUnderBaseChange` (02JK); integral ⇒ `Spec` closed map / closed
image; bijectivity of `Spec` of a radicial integral surjective map ⇒ homeomorphism
(build a `Homeomorph` on `PrimeSpectrum`); `Homeomorph.irreducibleSpace_iff`. Also need the
canonical `k`-algebra structure identifications `R ⊗_k K → R ⊗_k L`
(`Algebra.TensorProduct.map` of the inclusion `K → L`). -/
theorem geomIrred_step_3_4
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (h : GeomIrred3 k R) : GeomIrred4 k R := by
  -- Let `K = SeparableClosure k`, `L = AlgebraicClosure k`.  `L/K` is purely inseparable, so the
  -- base-change ring map `ψ : R ⊗[k] K → R ⊗[k] L` is injective (flat base change of an injective
  -- map) and every element of `R ⊗[k] L` has a `q`-power (`q = expChar`) in the image of `ψ`
  -- (Freshman's dream, using that `R ⊗[k] L` has exponential characteristic `q`).  Hence
  -- `PrimeSpectrum.comap ψ` is a homeomorphism and we transport `IrreducibleSpace`.
  obtain ⟨q, hq⟩ : ∃ q, ExpChar k q := ⟨ringExpChar k, ringExpChar.expChar k⟩
  -- Abstract core (stated for arbitrary intermediate `K`/`L` so the elaborator never has to
  -- unfold the noncomputable `SeparableClosure`/`AlgebraicClosure` instances while proving it).
  have H : ∀ (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L]
      [Algebra K L] [IsScalarTower k K L], IsPurelyInseparable K L → ExpChar K q →
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) →
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := by
    intro K L _ _ _ _ _ _ _ _ hKirr
    have hq0 : 0 < q := expChar_pos k q
    let f : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
    have hf : Function.Injective f := f.toRingHom.injective
    let ψ : (R ⊗[k] K) →ₐ[k] (R ⊗[k] L) := Algebra.TensorProduct.map (AlgHom.id k R) f
    have hψinj : Function.Injective ψ := fun _ _ hab =>
      Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.toLinearMap hf hab
    obtain ⟨p₀⟩ := hKirr.toNonempty
    have : Nontrivial (R ⊗[k] K) := p₀.nontrivial
    have : Nontrivial (R ⊗[k] L) := hψinj.nontrivial
    have hexpL : ExpChar (R ⊗[k] L) q :=
      expChar_of_injective_algebraMap (algebraMap k (R ⊗[k] L)).injective q
    have hpow_f : ∀ l : L, ∃ n : ℕ, l ^ q ^ n ∈ f.range := fun l => by
      obtain ⟨n, x, hx⟩ := IsPurelyInseparable.pow_mem K q l
      exact ⟨n, x, hx⟩
    have hcond1 : ∀ y : R ⊗[k] L, ∃ n : ℕ, n > 0 ∧ y ^ n ∈ (ψ.toRingHom).range := by
      intro y
      have key : ∃ n : ℕ, y ^ q ^ n ∈ ψ.range := by
        induction y using TensorProduct.inductionOn with
        | tmul r l =>
            obtain ⟨n, c, hc⟩ := hpow_f l
            refine ⟨n, ?_⟩
            rw [Algebra.TensorProduct.tmul_pow]
            refine ⟨(r ^ q ^ n) ⊗ₜ[k] c, ?_⟩
            change (Algebra.TensorProduct.map (AlgHom.id k R) f) _ = _
            rw [Algebra.TensorProduct.map_tmul]
            simp only [AlgHom.coe_id, id_eq]
            congr 1
        | add x z hx hz =>
            obtain ⟨n, hxn⟩ := hx
            obtain ⟨m, hzm⟩ := hz
            refine ⟨max n m, ?_⟩
            rw [add_pow_expChar_pow]
            apply Subalgebra.add_mem
            · have heq : x ^ q ^ (max n m) = (x ^ q ^ n) ^ (q ^ (max n m - n)) := by
                rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_max_left n m)]
              rw [heq]; exact pow_mem hxn _
            · have heq : z ^ q ^ (max n m) = (z ^ q ^ m) ^ (q ^ (max n m - m)) := by
                rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_max_right n m)]
              rw [heq]; exact pow_mem hzm _
      obtain ⟨n, a, ha⟩ := key
      exact ⟨q ^ n, pow_pos hq0 n, a, ha⟩
    have hcond2 : RingHom.ker (ψ.toRingHom) ≤ nilradical (R ⊗[k] K) := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx0 : x = 0 := hψinj (by simpa using hx)
      rw [hx0]; exact zero_mem _
    exact (((PrimeSpectrum.isHomeomorph_comap ψ.toRingHom hcond1 hcond2).homeomorph
      (PrimeSpectrum.comap ψ.toRingHom)).symm.irreducibleSpace_iff).mp hKirr
  -- Apply the core with `K = SeparableClosure k`, `L = AlgebraicClosure k`.
  exact H (SeparableClosure k) (AlgebraicClosure k)
    (separableClosure.isPurelyInseparable k (AlgebraicClosure k))
    (expChar_of_injective_algebraMap (algebraMap k (SeparableClosure k)).injective q) h

/- **Arrow `(4) ⇒ (1)`** (overview; the formal proof is `geomIrred_step_4_1` below, which is
fully wired modulo the five named helper lemmas that precede it). If `Spec(R ⊗_k k̄)` is
irreducible then for *every* field extension
`k'/k`, `Spec(R ⊗_k k')` is irreducible.

INFORMAL ARGUMENT (rigorous; Stacks 037K, step (4)⇒(1)):

Write `L := AlgebraicClosure k` (so `R ⊗_k L` has irreducible spectrum, i.e. a unique minimal
prime over the nonzero ring `R ⊗_k L`). Let `k'/k` be an arbitrary field extension. We must
show `Spec(R ⊗_k k')` is irreducible, i.e. `nilradical (R ⊗_k k')` is prime
(`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`).

Step A — pass to a common overfield. Choose a field `F` together with `k`-embeddings of both
`L` and `k'` into `F` (a *compositum*): e.g. let `m` be a maximal ideal of the nonzero ring
`L ⊗_k k'` and set `F := (L ⊗_k k') / m`, a field receiving both `L` and `k'` as `k`-subfields;
or take `F` to be an algebraically closed field containing `k'` of large enough cardinality and
embed `L` into it (`L/k` algebraic). Such `F` exists because `L ⊗_k k' ≠ 0` (tensor of nonzero
`k`-vector spaces over a field) and nonzero rings have maximal ideals.

Step B — `R ⊗_k F` has a unique minimal prime. There is a canonical iso of rings (tensor
reassociation / base change cancellation)
  `R ⊗_k F ≅ (R ⊗_k L) ⊗_L F`
(`Algebra.TensorProduct.cancelBaseChange` / `Algebra.TensorProduct.assoc`, using `L → F`).
Now `R ⊗_k L` has a unique minimal prime (hypothesis (4)) and `F` is an extension field of the
algebraically closed field `L`; by Stacks 030K-type input (Lemma 10.47.2: base change of a
ring with geometrically-irreducible-witness `Spec` along an extension of an algebraically
closed field preserves having a unique minimal prime), `(R ⊗_k L) ⊗_L F`, hence `R ⊗_k F`, has
a *unique minimal prime*. [This is the genuine analytic kernel: over an algebraically closed
base `L`, the geometric points are insensitive to enlarging `L`, so irreducibility of
`Spec(R ⊗_k L)` is preserved under `⊗_L F`.]

Step C — descend along `R ⊗_k k' → R ⊗_k F`. The inclusion `k' ↪ F` is a field extension,
hence *faithfully flat* and *injective*; its `R`-base change `j : R ⊗_k k' → R ⊗_k F` is
therefore injective (`R ⊗_k k' → R ⊗_k F` is injective: `k' → F` is split injective as
`k'`-modules / faithfully flat) and flat. By the minimal-prime descent for injective ring maps
(`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`, Stacks 00FK), every minimal prime
of `R ⊗_k k'` is the contraction `j⁻¹(Q)` of some minimal prime `Q` of `R ⊗_k F`; moreover, by
going-down for the flat map `j`, distinct minimal primes downstairs would lift to distinct
minimal primes upstairs. Since `R ⊗_k F` has a *unique* minimal prime, `R ⊗_k k'` has a unique
minimal prime. Combined with `R ⊗_k k' ≠ 0` (since `R ≠ 0`, from (4) giving `R ⊗_k L ≠ 0`, and
`k'` faithfully flat over `k`), `nilradical (R ⊗_k k')` is prime, so `Spec(R ⊗_k k')` is
irreducible.

LEAN INPUTS: existence of a common overfield `F` (maximal ideal of `L ⊗_k k'`,
`Ideal.exists_maximal`, `Ideal.Quotient.field`); the reassociation iso
`Algebra.TensorProduct.cancelBaseChange`/`assoc`; the unique-minimal-prime-preservation under
`⊗_L F` over algebraically closed `L` (Stacks 030K / Lemma 10.47.2 — NOT directly in Mathlib
under that tag; must be reconstructed, e.g. via geometric points / `IsAlgClosed` and the
nilradical characterization — the hard kernel); injectivity + flatness of base change of field
extensions; `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` (00FK) and going-down
(`Algebra.HasGoingDown`) for the descent; `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.
The unique-minimal-prime-preservation kernel is the crux. -/
/- **HARD KERNEL (Stacks 04KQ / 05DS, the core of Lemma 10.47.2).** Over an *algebraically
closed* field `L`, base change of a commutative `L`-algebra `A` with irreducible spectrum along
*any* field extension `F/L` keeps the spectrum irreducible.

This is the genuine analytic kernel of the `(4) ⇒ (1)` arrow. It is NOT pre-packaged in Mathlib
or `Stacks`/`StacksDraft` (the `@[stacks 030K]` declaration is a different lemma — unique
sep/purely-insep intermediate field). The standard proof runs as follows: reduce `A` to the
residue field `E = κ(nilradical A)` at the generic point, by localization and dense-image
transfer of irreducibility; reduce `E/L` and `F/L` to finitely generated subfields, by filtered
colimit and a nilradical-prime check; present `E = L(t₁..t_d)(θ)` via a separating
transcendence basis (`L` perfect) + primitive element; then `E ⊗_L F = R[X]/(g)` with
`R = L(t)⊗_L F` a domain, and the crux **Atom (Stacks 04KQ)**: `L(t)` is separably algebraically
closed in `Frac(L(t) ⊗_L F)` (so the separable irreducible `g` stays irreducible), proved by
specializing `t ↦ a ∈ Lᵈ` on a dense set and using `L` separably/algebraically closed.

Must be discharged from Mathlib primitives (`IsAlgClosed`/`IsSepClosed`, `MvPolynomial`/
`AdjoinRoot`, `IsLocalization`, Galois "natural irrationalities"). THE crux subgoal.

DECOMPOSITION: the kernel body below reduces to two named helper lemmas:
* `geomIrred_kernel_fields` — the **field Main Lemma** (the genuine analytic core: `E/L`, `F/L`
  field extensions of the algebraically closed `L`); and
* `geomIrred_kernel_residue_denseRange` — Lemma 1 (residue-field reduction) bookkeeping: the
  base change `A ⊗[L] F → E ⊗[L] F` of a map `A → E` with `ker ≤ nilradical A` has its kernel
  inside `nilradical (A ⊗[L] F)`, so its Spec-image is dense.
The reduction uses the transfer tool `irreducibleSpace_of_denseRange_comap`: passing `A`
to the residue field `E = Frac(A ⧸ nilradical A)` at the generic point. -/

/-- **Transfer of irreducibility along a ring map with dense Spec image.** If `f : R →+* S` has
`RingHom.ker f ≤ nilradical R` (equivalently `PrimeSpectrum.comap f` has dense range) and `Spec S`
is irreducible, then `Spec R` is irreducible. PROVED: `denseRange_comap_iff_ker_le_nilRadical` +
`IsIrreducible.image`/`IsIrreducible.closure`. -/
theorem irreducibleSpace_of_denseRange_comap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hker : RingHom.ker f ≤ nilradical R)
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum R) := by
  have hdense : DenseRange (PrimeSpectrum.comap f) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr hker
  have huniv : IsIrreducible (Set.univ : Set (PrimeSpectrum S)) :=
    (irreducibleSpace_def (PrimeSpectrum S)).mp hS
  have hirrImage : IsIrreducible (Set.range (PrimeSpectrum.comap f)) := by
    have := huniv.image (PrimeSpectrum.comap f) (by fun_prop)
    rwa [Set.image_univ] at this
  have hclo : IsIrreducible (closure (Set.range (PrimeSpectrum.comap f))) :=
    hirrImage.closure
  rw [hdense.closure_range] at hclo
  exact (irreducibleSpace_def (PrimeSpectrum R)).mpr hclo

/- **Field Main Lemma (the genuine analytic core, Stacks 04KQ / 05DS).** For `L` algebraically
closed and ANY field extensions `E/L`, `F/L`, the spectrum `Spec(E ⊗[L] F)` is irreducible.

This is the irreducible hard core of `geomIrred_kernel_baseChange_algClosed` after the
residue-field reduction. Proof outline:
  1. Reduce `E/L`, `F/L` to finitely generated subfields (tensor commutes with filtered colimits;
     nilradical-prime check survives — Sub-fact T2).
  2. Separating transcendence basis (`L` perfect, alg. closed) + primitive element ⟹
     `E = L(t₁..t_d)(θ)`, `θ` separable over `K = L(t)`; so `E ⊗_L F = R[X]/(g)` with
     `R = L(t) ⊗_L F` a domain (Step 3a: localization of `F[t]`).
  3. **Atom (Stacks 04KQ):** `K = L(t)` is separably algebraically closed in `M = Frac(R)`, so
     the separable irreducible `g` stays irreducible over `M`; dense-image transfer
     (`irreducibleSpace_of_denseRange_comap`) finishes.
Mathlib bricks: `IsSepClosed.of_isAlgClosed`, `MvPolynomial.algebraTensorAlgEquiv`,
`AdjoinRoot`, `Field.exists_primitive_element`, `IsGalois`/`IntermediateField` Galois corr.
THE crux subgoal; recommend its own AND node along the Stage-2 / Step-3a / Atom cut points. -/

/-- **Field Main Lemma, Stage 2 (filtered-colimit reduction).** To prove that `Spec (E ⊗[L] F)`
is irreducible for arbitrary field extensions `E/L`, `F/L` of an algebraically closed `L`, it
suffices to prove it for all *finitely generated* (as `L`-algebra) intermediate subfields
`E' ≤ E` and `F' ≤ F`.

*Proof.* Write `E = ⋃ E'` and `F = ⋃ F'` as directed unions of
their finitely generated subfields; tensor commutes with filtered colimits and the transition maps
`E' ⊗[L] F' → E ⊗[L] F` are injective (flatness of fields over `L`), so `E ⊗[L] F` is the directed
colimit of the `E' ⊗[L] F'`. For a directed colimit of rings with injective maps, if every
`Spec (E' ⊗ F')` is irreducible (equivalently each `nilradical (E' ⊗ F')` is prime) then
`nilradical (E ⊗ F)` is prime: any `x·y` nilpotent upstairs is witnessed at a finite stage where
primality of the nilradical applies. Nonemptiness is automatic (`E ⊗ F` is nontrivial).
Mathlib bricks: `IntermediateField` directed-union structure, `Algebra.TensorProduct`/`Module.Flat`
colimit compatibility, `Module.Flat.rTensor_exact`/injectivity of base change, the
`nilradical`-prime characterization `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.
[STAGE 2 — colimit transfer.] -/
theorem geomIrred_fields_colimit
    (L : Type u) [Field L] [IsAlgClosed L]
    (E : Type u) [Field E] [Algebra L E]
    (F : Type u) [Field F] [Algebra L F]
    (hfg : ∀ (E' : IntermediateField L E) (F' : IntermediateField L F),
        Algebra.EssFiniteType L E' → Algebra.EssFiniteType L F' →
        IrreducibleSpace (PrimeSpectrum (E' ⊗[L] F'))) :
    IrreducibleSpace (PrimeSpectrum (E ⊗[L] F)) := by
  -- irreducibility; an injective directed colimit preserves
  -- primality of the nilradical).
  classical
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  refine ⟨?_, ?_⟩
  · -- nilradical ≠ ⊤
    rw [Ideal.ne_top_iff_one]
    intro h
    rw [mem_nilradical] at h
    exact not_isNilpotent_one h
  · -- prime condition
    intro x y hxy
    -- capture x and y in a common finite stage
    obtain ⟨Sx, hSx⟩ := TensorProduct.exists_finset x
    obtain ⟨Sy, hSy⟩ := TensorProduct.exists_finset y
    set S : Finset (E × F) := Sx ∪ Sy with hS
    set E' : IntermediateField L E := IntermediateField.adjoin L (↑(S.image Prod.fst) : Set E) with
        hE'
    set F' : IntermediateField L F := IntermediateField.adjoin L (↑(S.image Prod.snd) : Set F) with
        hF'
    set ι := Algebra.TensorProduct.map E'.val F'.val with hι
    -- ι is injective
    have hinj : Function.Injective ι := fun _ _ hab =>
      TensorProduct.map_injective_of_flat_flat E'.val.toLinearMap F'.val.toLinearMap
        E'.val.injective F'.val.injective hab
    -- EssFiniteType instances
    have hEss : Algebra.EssFiniteType L E' :=
      IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_finset _)
    have hFss : Algebra.EssFiniteType L F' :=
      IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_finset _)
    -- nilradical of stage is prime
    have hprime : (nilradical (E' ⊗[L] F')).IsPrime :=
      PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp (hfg E' F' hEss hFss)
    -- capture membership helper
    have hcap : ∀ (T : Finset (E × F)), T ⊆ S → (∑ i ∈ T, i.fst ⊗ₜ[L] i.snd) ∈ ι.range :=
      fun T hT => tensor_mem_range_map E'.val F'.val T fun i hi =>
        ⟨⟨⟨i.1, IntermediateField.subset_adjoin L _ (by simpa using ⟨i.2, hT hi⟩)⟩, rfl⟩,
          ⟨⟨i.2, IntermediateField.subset_adjoin L _ (by simpa using ⟨i.1, hT hi⟩)⟩, rfl⟩⟩
    exact mem_or_mem_nilradical_of_mem_range ι.toRingHom hinj hprime
      (by rw [hSx]; exact hcap Sx Finset.subset_union_left)
      (by rw [hSy]; exact hcap Sy Finset.subset_union_right) hxy

/- **Field Main Lemma, finitely generated core (Stages 3 + Atom 04KQ)** — overview; the lemma
itself is now split into `geomIrred_fg_presentation` (structural) + `geomIrred_fg_core` (analytic
crux) below, with `geomIrred_fields_fg` wiring them. For `L` algebraically
closed, `E/L` a *finitely generated* (as `L`-algebra) field extension and `F/L` *any* field
extension, `Spec (E ⊗[L] F)` is irreducible.

*Proof.* `L` is perfect, being algebraically closed, so `E/L` has a separating
transcendence basis `t₁,…,t_d` with `E/K` finite separable, `K := L(t)`; by the primitive element
theorem `E = K(θ) = K[X]/(g)`, `g ∈ K[X]` separable irreducible. Base change:
`E ⊗[L] F = (K[X]/(g)) ⊗[K] R = R[X]/(g)` with `R := K ⊗[L] F`
(`Algebra.TensorProduct.quotientTensorEquiv` + base-change of the tower `L → K → E`). By Step 3a,
`R = L(t) ⊗[L] F` is a *domain* (localization of `F[t] ≅ L[t] ⊗[L] F`,
`MvPolynomial.algebraTensorAlgEquiv` + `MvPolynomial.isDomain`); let `M := Frac R`. The
localization `R[X]/(g) → M[X]/(g)` is injective (`R[X]/(g)` is `R`-free of rank `deg g`,
`AdjoinRoot.powerBasis`) with dense `Spec`-image, so by `irreducibleSpace_of_denseRange_comap` it
suffices that `M[X]/(g)` be a domain, i.e. `g` stays irreducible over `M`. **Atom (Stacks 04KQ):**
`K = L(t)` is separably algebraically closed in `M` (proved by specializing `t ↦ a ∈ Lᵈ` on a
dense set, using `L` separably/algebraically closed and infinite), so the separable irreducible
`g` stays irreducible over `M` (Galois "natural irrationalities":
`IntermediateField.LinearDisjoint.iff_inf_eq_bot`). Mathlib bricks:
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top` (0H71),
`Field.exists_primitive_element`, `AdjoinRoot.powerBasis`,
`Algebra.TensorProduct.quotientTensorEquiv`, `MvPolynomial.algebraTensorAlgEquiv`,
`Algebra.TensorProduct.isField_of_isAlgebraic`, `IntermediateField.LinearDisjoint.iff_inf_eq_bot`,
the PROVED `irreducibleSpace_of_denseRange_comap`. THE genuine analytic crux (Atom 04KQ); STRONGLY
recommend its own AND node along the Step-3a (purely transcendental ⟹ domain) / Atom cut points. -/
/-- **Field Main Lemma, Stage 3 structural presentation (separating transcendence basis +
primitive element).** For `L` algebraically closed (hence perfect) and `E/L` a finitely generated
field extension, there is a *purely transcendental* intermediate field `K = L(t₁,…,t_d)`, realized
as the fraction field of a polynomial ring `MvPolynomial σ L` over a finite index set `σ`, over
which `E` is *finite separable*. (By the primitive element theorem this is `E = K(θ) = K[X]/(g)`,
`g` separable irreducible; we only export the tower/finiteness/separability data, which is all the
core lemma needs.)

Proof: `L` algebraically closed ⟹ perfect; `E/L` finitely generated ⟹ it admits a separating
transcendence basis `t₁,…,t_d` with `E` finite separable over `K := L(t₁,…,t_d)` (Stacks 0H71 /
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top` in char `p`,
trivially in char `0` where every algebraic extension is separable). Present `K` as the fraction
field of `MvPolynomial σ L` (`IsFractionRing`), giving the scalar towers `L → K → E`.
[STAGE 3 — structural presentation.] -/
@[ega "IV 4.6.7" "special case", sga "1 II 5.6" "(iv)⇒(i), special case"]
theorem geomIrred_fg_presentation
    (L : Type u) [Field L] [IsAlgClosed L]
    (E : Type u) [Field E] [Algebra L E] [Algebra.EssFiniteType L E] :
    ∃ (σ : Type u) (_ : Finite σ)
      (K : Type u) (_ : Field K) (_ : Algebra L K)
      (_ : Algebra (MvPolynomial σ L) K) (_ : IsScalarTower L (MvPolynomial σ L) K)
      (_ : IsFractionRing (MvPolynomial σ L) K)
      (_ : Algebra K E) (_ : IsScalarTower L K E),
      FiniteDimensional K E ∧ Algebra.IsSeparable K E := by
  -- field L, and the top step is finite separable by construction).
  obtain ⟨s, htb, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField L E
  set σ := {x // x ∈ s} with hσ
  have hai : AlgebraicIndependent L (Subtype.val : σ → E) := htb.left
  set rg := Set.range (Subtype.val : σ → E) with hrg
  set C := Algebra.adjoin L rg with hC
  set K₀ := IntermediateField.adjoin L rg with hK₀
  -- Present `K₀ = L(t)` as the fraction field of the subalgebra `C = L[t]`.
  let alg : Algebra C K₀ :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin L rg)).toAlgebra
  have hcast : ∀ a : C, ((algebraMap C K₀ a : K₀) : E) = (a : E) := fun a => rfl
  have hsmul : FaithfulSMul C K₀ := by
    refine ⟨fun {a b} h => ?_⟩
    apply Subtype.ext
    have h2 := h (1 : K₀)
    simp only [Algebra.smul_def, mul_one] at h2
    have := congrArg (Subtype.val) h2
    rw [hcast, hcast] at this
    exact this
  have hfr : IsFractionRing C K₀ := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨r, hr, t, ht, hz⟩ := (IntermediateField.mem_adjoin_iff_div).mp z.property
    refine ⟨⟨r, hr⟩, ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    push_cast [hcast]
    exact hz
  -- `E` is finite separable over `K₀ = L(t)`.
  have hrange : rg = (↑s : Set E) := Subtype.range_coe
  have hsep' : Algebra.IsSeparable K₀ E := by rw [hK₀, hrange]; exact hsep
  -- Present `K₀` as `K = Frac (MvPolynomial σ L)` via the algebraic-independence equivalence.
  set K := FractionRing (MvPolynomial σ L) with hK
  let e : MvPolynomial σ L ≃ₐ[L] C := hai.aevalEquiv
  let φ : K ≃ₐ[L] K₀ := IsFractionRing.fieldEquivOfAlgEquiv L K K₀ e
  let algKE : Algebra K E := ((K₀.val.comp φ.toAlgHom).toRingHom).toAlgebra
  have hAM : (algebraMap K E) = (K₀.val.comp φ.toAlgHom).toRingHom := rfl
  have hst : IsScalarTower L K E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    have hx : (algebraMap K E) ((algebraMap L K) x) = K₀.val (φ ((algebraMap L K) x)) := by
      rw [hAM]; rfl
    rw [hx, AlgEquiv.commutes φ x, IntermediateField.coe_val]
    exact (IsScalarTower.algebraMap_apply L K₀ E x)
  -- Transport finiteness/separability across the isomorphism `φ : K ≃ₐ[L] K₀`.
  have hcompat : (algebraMap K E).comp (φ.symm.toRingEquiv.toRingHom) = (algebraMap K₀ E) := by
    refine RingHom.ext (fun y => ?_)
    have h1 : (algebraMap K E) (φ.symm y) = K₀.val (φ (φ.symm y)) := by rw [hAM]; rfl
    rw [RingHom.comp_apply, show (φ.symm.toRingEquiv.toRingHom) y = φ.symm y from rfl, h1,
      AlgEquiv.apply_symm_apply]
    rfl
  have hsepK : Algebra.IsSeparable K E := by
    refine Algebra.IsSeparable.of_equiv_equiv φ.symm.toRingEquiv (RingEquiv.refl E) ?_
    rw [RingEquiv.toRingHom_refl, RingHom.id_comp]
    exact hcompat
  have hfd : FiniteDimensional K E := by
    have : Algebra.EssFiniteType K E :=
      Algebra.EssFiniteType.of_comp L K E
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact ⟨σ, inferInstance, K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hst, hfd, hsepK⟩

/- **Field Main Lemma, finitely generated core (Step 3a + base change + Atom 04KQ).** Given the
structural presentation of `geomIrred_fg_presentation` — `K = L(t)` purely transcendental (as the
fraction field of `MvPolynomial σ L`, `σ` finite) and `E/K` finite separable, `L` algebraically
closed — and *any* field extension `F/L`, the spectrum `Spec (E ⊗[L] F)` is irreducible.

*Proof.*
  1. **Step 3a.** `R := K ⊗[L] F = L(t) ⊗[L] F` is an integral *domain*: it is a localization of
     `L[t] ⊗[L] F ≅ F[t] = MvPolynomial σ F` (`MvPolynomial.algebraTensorAlgEquiv`,
     `MvPolynomial.isDomain`) at the multiplicative set `L[t] ∖ {0}` (which avoids `0`); a
     localization of a domain at a set of nonzerodivisors is a domain. Let `M := Frac R`.
  2. **Base change.** Write `E = K[X]/(g)` (`Field.exists_primitive_element` + `AdjoinRoot`,
     `g` separable irreducible). Then `E ⊗[L] F = E ⊗[K] R = R[X]/(g)`
     (`Algebra.TensorProduct.quotientTensorEquiv` + `Algebra.TensorProduct.cancelBaseChange` for
     the tower `L → K → E`). `R[X]/(g)` is `R`-free of rank `deg g` (`AdjoinRoot.powerBasis`).
  3. **Localization transfer.** The localization `R[X]/(g) → M[X]/(g)` is injective (free module
     into its base change) with dense `Spec`-image, so by the PROVED
     `irreducibleSpace_of_denseRange_comap` it suffices that `M[X]/(g)` be a domain.
  4. **Atom (Stacks 04KQ).** `K = L(t)` is *separably algebraically closed* in `M = Frac R`
     (proved by specializing `t ↦ a ∈ Lᵈ` on a Zariski-dense set, using `L` separably/algebraically
     closed and infinite), so the separable irreducible `g` stays irreducible over `M` (Galois
     "natural irrationalities", `IntermediateField.LinearDisjoint.iff_inf_eq_bot`); hence
     `M[X]/(g)` is a field, a domain, and its Spec is a point.
Mathlib bricks: `MvPolynomial.algebraTensorAlgEquiv`, `MvPolynomial.isDomain`,
`IsFractionRing`/`IsLocalization`, `Field.exists_primitive_element`, `AdjoinRoot.powerBasis`,
`Algebra.TensorProduct.quotientTensorEquiv`, `Algebra.TensorProduct.cancelBaseChange`,
`Algebra.TensorProduct.isField_of_isAlgebraic`, `IntermediateField.LinearDisjoint.iff_inf_eq_bot`,
the PROVED `irreducibleSpace_of_denseRange_comap`. THE genuine analytic crux (Atom 04KQ). -/
/-- **[D] Step 3a: the purely transcendental base change is a domain.** For `K = L(t)` purely
transcendental (presented as the fraction field of `MvPolynomial σ L`, `σ` finite) and any field
extension `F/L`, `R := K ⊗[L] F` is an integral domain. Proof: `K ⊗[L] F` is a localization of
`L[t] ⊗[L] F ≅ F[t] = MvPolynomial σ F` (`MvPolynomial.algebraTensorAlgEquiv`,
`MvPolynomial.isDomain`) at the multiplicative set `L[t] ∖ {0}` (which avoids `0`); a localization
of a domain at a set of nonzerodivisors is a domain. -/
theorem geomIrred_fg_R_isDomain
    (L : Type u) [Field L]
    (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra L K]
    [Algebra (MvPolynomial σ L) K] [IsScalarTower L (MvPolynomial σ L) K]
    [IsFractionRing (MvPolynomial σ L) K]
    (F : Type u) [Field F] [Algebra L F] :
    IsDomain (K ⊗[L] F) := by
  -- D := MvPolynomial σ L ⊗[L] F ≅ MvPolynomial σ F is a domain.
  have hD : IsDomain (MvPolynomial σ L ⊗[L] F) := by
    have e : (MvPolynomial σ L ⊗[L] F) ≃+* MvPolynomial σ F :=
      (Algebra.TensorProduct.comm L (MvPolynomial σ L) F).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv L F).toRingEquiv
    exact MulEquiv.isDomain (MvPolynomial σ F) e.toMulEquiv
  -- algebraMap (MvPolynomial σ L) D is injective (base change of an injective field map).
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ L) (MvPolynomial σ L ⊗[L] F)) := by
    have : Function.Injective (algebraMap L F) := (algebraMap L F).injective
    exact Algebra.TensorProduct.includeLeft_injective (R := L)
      (A := MvPolynomial σ L) (B := F) (S := MvPolynomial σ L) this
  -- The image of the nonzerodivisors of MvPolynomial σ L lies in the nonzerodivisors of D.
  have hle : Algebra.algebraMapSubmonoid (MvPolynomial σ L ⊗[L] F)
      (nonZeroDivisors (MvPolynomial σ L)) ≤ nonZeroDivisors (MvPolynomial σ L ⊗[L] F) := by
    rintro x ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    have hm0 : (m : MvPolynomial σ L) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨m, hm⟩
    intro h
    exact hm0 (hinj (by rw [map_zero]; exact h))
  -- K ⊗[L] F is the localization of D at this submonoid, hence a domain.
  have hdom : IsDomain ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) hle
  -- Identify that localization (D ⊗[P] K) with K ⊗[L] F.
  have efin : ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) ≃+* (K ⊗[L] F) :=
    (Algebra.TensorProduct.comm (MvPolynomial σ L) (MvPolynomial σ L ⊗[L] F) K).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange L (MvPolynomial σ L) K K F).toRingEquiv
  exact MulEquiv.isDomain ((MvPolynomial σ L ⊗[L] F) ⊗[MvPolynomial σ L] K) efin.symm.toMulEquiv

/-- **[J] Localization base-change has nilpotent kernel.** For `E/K` finite (hence `K`-free,
`K`-flat), `R` a domain `K`-algebra and `M = Frac R` (an `IsFractionRing`), the base-changed
localization map `E ⊗[K] R → E ⊗[K] M`, i.e.
`Algebra.TensorProduct.map (AlgHom.id K E) (IsScalarTower.toAlgHom K R M)`, has kernel contained in
(in fact equal to) the nilradical of `E ⊗[K] R` — it is injective because `E` is `K`-flat and
`R → M` is injective (`Module.Flat.lTensor_preserves_injective_linearMap` / the
`rTensor`-exactness + nilpotent-pure-tensors pattern from `geomIrred_kernel_residue_denseRange`).
This feeds `irreducibleSpace_of_denseRange_comap` for the dense-image localization transfer. -/
theorem geomIrred_fg_baseChange_localization_ker
    (K : Type u) [Field K]
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra K R]
    (M : Type u) [Field M] [Algebra K M] [Algebra R M] [IsScalarTower K R M]
    [IsFractionRing R M] :
    RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id K E) (IsScalarTower.toAlgHom K R M)).toRingHom
      ≤ nilradical (E ⊗[K] R) := by
  -- E being K-flat; kernel is ⊥ ≤ nilradical).
  have hfinj : Function.Injective (IsScalarTower.toAlgHom K R M) := by
    change Function.Injective (algebraMap R M)
    exact IsFractionRing.injective R M
  have hlinj : Function.Injective
      (LinearMap.lTensor E (IsScalarTower.toAlgHom K R M).toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom K R M).toLinearMap hfinj
  have hψinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K E)
        (IsScalarTower.toAlgHom K R M)).toRingHom := fun _ _ hab => hlinj hab
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hx0 : x = 0 := hψinj (by rw [hx, map_zero])
  rw [hx0]
  exact zero_mem _
