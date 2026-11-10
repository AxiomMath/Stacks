module

public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced

/-!
# Spreading out a reducible generic fibre, and the irreducible half of Stacks 05FT

`StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut` proves the *bad* half of the
generic-fibre dichotomy for the geometrically reduced fibre locus — the affine case of Stacks 0577
at the generic point — and for the geometrically integral one, leaving the two *good* halves (the
affine cases of Stacks 0578 and Stacks 055A) as the only hypotheses of
`Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves`. The bad half for the
geometrically **irreducible** fibre locus was not among them, because the technique used there does
not reach it: a failure of irreducibility of `Spec (T ⊗[D] K)` is a pair of elements with nilpotent
product neither of which is nilpotent, and "not nilpotent" is not an equational condition that a
single coordinate functional of a free module can keep alive in a fibre.

**This file proves that bad half**, by replacing the functional with Chevalley's theorem. For an
element `a` of a finite type algebra `A` over a domain `E`, the set of primes `q` of `E` whose
fibre `κ(q) ⊗[E] A` still has `1 ⊗ₜ a` non-nilpotent is the image in `Spec E` of the basic open
`D(a) ⊆ Spec A`, which is constructible; and it contains the generic point of `Spec E` as soon as
`a` is non-nilpotent in `A` and `A` is free over `E`. So it contains a nonempty basic open of
`Spec E`. Running this for both elements of the pair and intersecting the two basic opens produces
a nonempty basic open of `Spec E` over which every fibre has non-prime nilradical, hence reducible
spectrum.

Two points make the argument work. That the generic point is in the image is elementary and uses
freeness only through `Module.Free.exists_linearMap_apply_ne_zero`: the set
`{e ⬝ aⁿ | e ≠ 0}` is a multiplicative subset of `A` avoiding `0`, so some prime of `A` misses it,
and such a prime misses `a` and contracts to `(0)`. And that a prime `P` of `A` over `q` with
`a ∉ P` keeps `1 ⊗ₜ a` non-nilpotent is
`Algebra.not_isNilpotent_one_tmul_of_comap_eq`: the residue field `κ(P)` is a `κ(q)`-algebra by
`Ideal.ResidueField.map`, so the fibre maps to it, and `a` has nonzero image there.

Note that the two witnesses necessarily come from *different* primes of `A` — their product is
nilpotent, so every prime of `A` contains one of them — which is why the fibre over `q`, and not
the residue field at a single prime of `A`, has to be the ring in which the failure is exhibited.

With this half proved, the good half for the geometrically irreducible fibre locus is equivalent to
constructibility of that locus, exactly as
`StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced` shows for the reduced one. So both
remaining gaps in Stacks 05FT are now gaps of the same kind, and
`Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_halves` records Stacks 05FT
as following from the affine cases of Stacks 0579 and Stacks 055B alone.

## Main results

* `Algebra.not_isNilpotent_one_tmul_of_comap_eq`: a prime of `A` over `q` avoiding `x` keeps
  `1 ⊗ₜ x` non-nilpotent in the fibre `κ(q) ⊗[E] A`.
* `Algebra.bot_mem_comap_image_basicOpen_of_free`: for `A` free over a domain `E` and `x : A`
  non-nilpotent, the generic point of `Spec E` lies under a prime of `A` avoiding `x`.
* `Algebra.exists_ne_zero_forall_not_mem_geometricallyIrreducibleFibreLocus_of_free`: **the
  spreading step.** If `E ⊗[D] T` is free over the Noetherian domain `E` and carries two
  non-nilpotent elements with nilpotent product, then some nonempty basic open of `Spec E` consists
  of primes contracting outside the geometrically irreducible fibre locus of `T`.
* `Algebra.exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus`: **the bad half of the
  generic-fibre dichotomy for geometric irreducibility**, the affine case at the generic point of
  the negative direction of Stacks 055A. If the generic point of `Spec D` is outside the
  geometrically irreducible fibre locus, some nonempty basic open of `Spec D` is disjoint from it.
* `Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_goodGeneric`: the affine case of
  the level set `n = 1` of Stacks 055B granted only the good half of Stacks 055A.
* `Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible`: that
  good half is *equivalent* to the constructibility it is used to prove.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_halves`: Stacks 05FT from
  the affine cases of Stacks 0579 and of the level set `n = 1` of Stacks 055B.

## Implementation notes

Constructibility of the image of a basic open is Chevalley's theorem,
`PrimeSpectrum.isConstructible_comap_image`, which needs `E → E ⊗[D] T` to be of finite
presentation; it is, because `E` is Noetherian and the base change of a finite type algebra is of
finite type. That is the only place the Noetherian hypothesis on `E` is used, and it is why the
spreading step asks for it where
`Algebra.exists_ne_zero_forall_not_mem_geometricallyReducedFibreLocus_of_free` does not.

The degenerate failure — `T ⊗[D] K` the zero ring, whose spectrum is empty and therefore not
irreducible — is carried along as the left alternative of the witness disjunction, exactly as in
the integral case, and is handled by
`Algebra.forall_not_mem_geometricallyIrreducibleFibreLocus_of_subsingleton`. Unlike for
reducedness it cannot be ignored: the zero ring is reduced but its spectrum is not irreducible.

Nothing here carries a `@[stacks 055A]` or `@[stacks 055B]` attribute. Only one half of Stacks 055A
is proved, and the statements about Stacks 055B remain conditional on the other half.

## References

* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 05DY](https://stacks.math.columbia.edu/tag/05DY)
-/

@[expose] public section

open PrimeSpectrum Topology

open scoped TensorProduct

universe u

namespace Algebra

section Fibre

variable {E A : Type u} [CommRing E] [CommRing A] [Algebra E A]

/-- **A point of a fibre away from `x` keeps `1 ⊗ₜ x` non-nilpotent.** Let `E → A` be a ring map,
let `q` be a prime of `E` and let `P` be a prime of `A` contracting to `q` and not containing
`x : A`. Then `1 ⊗ₜ x` is not nilpotent in the fibre `κ(q) ⊗[E] A`.

The residue field `κ(P)` is an algebra over `κ(q)` by `Ideal.ResidueField.map`, because `q` is the
contraction of `P`, and over `E` through `A`; so the fibre has an algebra map to `κ(P)` sending
`1 ⊗ₜ x` to the image of `x`, which is nonzero because `x ∉ P`. A field has no nonzero nilpotents,
so a nilpotent `1 ⊗ₜ x` would have zero image. -/
theorem not_isNilpotent_one_tmul_of_comap_eq (q : PrimeSpectrum E) (P : PrimeSpectrum A)
    (hPq : comap (algebraMap E A) P = q) {x : A} (hx : x ∉ P.asIdeal) :
    ¬ IsNilpotent ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] x) := by
  have hq : q.asIdeal = P.asIdeal.comap (algebraMap E A) := by rw [← hPq]; rfl
  let : Algebra E P.asIdeal.ResidueField :=
    ((algebraMap A P.asIdeal.ResidueField).comp (algebraMap E A)).toAlgebra
  have : IsScalarTower E A P.asIdeal.ResidueField := .of_algebraMap_eq' rfl
  let : Algebra q.asIdeal.ResidueField P.asIdeal.ResidueField :=
    (Ideal.ResidueField.map q.asIdeal P.asIdeal (algebraMap E A) hq).toAlgebra
  have : IsScalarTower E q.asIdeal.ResidueField P.asIdeal.ResidueField :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.map_algebraMap _ _ _ hq r).symm
  intro hnil
  refine hx (Ideal.algebraMap_residueField_eq_zero.mp ?_)
  have h0 := IsReduced.eq_zero _ (hnil.map
    ((IsScalarTower.toAlgHom E A P.asIdeal.ResidueField).liftEquiv E q.asIdeal.ResidueField A
      P.asIdeal.ResidueField))
  rwa [AlgHom.liftEquiv_tmul, one_smul, IsScalarTower.coe_toAlgHom'] at h0

/-- **A non-nilpotent element of a free algebra survives over the generic point.** Let `E` be a
domain, let `A` be an `E`-algebra which is free as an `E`-module and let `x : A` be non-nilpotent.
Then the generic point `(0)` of `Spec E` is the contraction of a prime of `A` not containing `x`.

The elements `e ⬝ xⁿ` with `e : E` nonzero form a multiplicative subset `S` of `A`, and `0 ∉ S`: a
nonzero coordinate functional `φ` of a basis of `A` at `xⁿ` exists because `A` is free and
`xⁿ ≠ 0`, and `φ (e ⬝ xⁿ) = e ⬝ φ xⁿ ≠ 0` because `E` is a domain. A prime of `A` disjoint from `S`
therefore exists, and it avoids `x` and meets `E` only in `0`. -/
theorem bot_mem_comap_image_basicOpen_of_free [IsDomain E] [Module.Free E A] {x : A}
    (hx : ¬ IsNilpotent x) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) ∈
      comap (algebraMap E A) '' (basicOpen x : Set (PrimeSpectrum A)) := by
  have hxn : ∀ n : ℕ, x ^ n ≠ 0 := fun n hn => hx ⟨n, hn⟩
  let S : Submonoid A :=
    { carrier := {y | ∃ e : E, e ≠ 0 ∧ ∃ n : ℕ, y = algebraMap E A e * x ^ n}
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨e₁, he₁, n₁, rfl⟩ ⟨e₂, he₂, n₂, rfl⟩
        exact ⟨e₁ * e₂, mul_ne_zero he₁ he₂, n₁ + n₂, by rw [map_mul, pow_add]; ring⟩ }
  have hS0 : (0 : A) ∉ S := by
    rintro ⟨e, he, n, hen⟩
    obtain ⟨φ, hφ⟩ := Module.Free.exists_linearMap_apply_ne_zero E (hxn n)
    refine mul_ne_zero he hφ ?_
    have h := congrArg φ hen.symm
    rwa [map_zero, ← Algebra.smul_def, map_smul, smul_eq_mul] at h
  obtain ⟨p, hp, -, hdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal A) S
    (Set.disjoint_left.mpr fun y hy => by
      rw [SetLike.mem_coe, Ideal.mem_bot] at hy
      exact hy ▸ hS0)
  refine ⟨⟨p, hp⟩, (mem_basicOpen _ _).mpr
    (fun hxp => Set.disjoint_left.mp hdisj hxp ⟨1, one_ne_zero, 1, by simp⟩),
    PrimeSpectrum.ext (le_antisymm (fun e he => ?_) bot_le)⟩
  rw [Ideal.mem_bot]
  by_contra he0
  exact Set.disjoint_left.mp hdisj he ⟨e, he0, 0, by simp⟩

end Fibre

section Spread

variable {D T : Type u} [CommRing D] [CommRing T] [Algebra D T]

/-- **Non-membership in the geometrically irreducible fibre locus, unfolded.** A prime `p` of `D`
lies outside the geometrically irreducible fibre locus of `T` exactly when some field `K` over `D`
with `ker (D → K) = p` has `Spec (T ⊗[D] K)` reducible. This is
`Algebra.not_mem_fibreLocus_iff` at irreducibility of the spectrum. -/
theorem not_mem_geometricallyIrreducibleFibreLocus_iff (p : PrimeSpectrum D) :
    p ∉ geometricallyIrreducibleFibreLocus D T ↔
      ∃ (K : Type u) (_ : Field K) (_ : Algebra D K),
        RingHom.ker (algebraMap D K) = p.asIdeal ∧
          ¬ IrreducibleSpace (PrimeSpectrum (T ⊗[D] K)) := by
  rw [geometricallyIrreducibleFibreLocus_eq_fibreLocus]
  exact not_mem_fibreLocus_iff p

variable (E : Type u) [CommRing E] [Algebra D E]

/-- `Algebra.not_mem_fibreLocus_comap` at irreducibility of the spectrum: a prime `q` of `E` whose
fibre `κ(q) ⊗[E] (E ⊗[D] T)` has reducible spectrum contracts outside the geometrically
irreducible fibre locus of `T`. -/
theorem not_mem_geometricallyIrreducibleFibreLocus_comap (q : PrimeSpectrum E)
    (hq : ¬ IrreducibleSpace (PrimeSpectrum (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T)))) :
    comap (algebraMap D E) q ∉ geometricallyIrreducibleFibreLocus D T :=
  geometricallyIrreducibleFibreLocus_eq_fibreLocus D T ▸
    not_mem_fibreLocus_comap E (fun _ _ _ _ e => irreducibleSpace_primeSpectrum_congr e) q hq

/-- **The degenerate case of the spreading step.** If the base change `E ⊗[D] T` is the zero ring
then so is every one of its fibres, and the spectrum of the zero ring is empty, hence not
irreducible; so no prime of `E` contracts into the geometrically irreducible fibre locus of `T`. -/
theorem forall_not_mem_geometricallyIrreducibleFibreLocus_of_subsingleton
    (h : Subsingleton (E ⊗[D] T)) (q : PrimeSpectrum E) :
    comap (algebraMap D E) q ∉ geometricallyIrreducibleFibreLocus D T := by
  refine not_mem_geometricallyIrreducibleFibreLocus_comap E q fun hirr => ?_
  have hsub : Subsingleton (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T)) := by
    have := h
    infer_instance
  exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr hsub).elim hirr.toNonempty.some

/-- **The spreading step for geometric irreducibility.** Let `E` be a Noetherian domain which is an
algebra over `D`, suppose the base change `E ⊗[D] T` is free as an `E`-module, and suppose it
carries two non-nilpotent elements `a`, `b` whose product is nilpotent. Then there is a nonzero
`h : E` such that every prime `q` of `E` with `h ∉ q` contracts to a prime of `D` outside the
geometrically irreducible fibre locus of `T`.

By Chevalley's theorem the set of primes of `E` under a prime of `E ⊗[D] T` avoiding `a` is
constructible, and it contains the generic point by
`Algebra.bot_mem_comap_image_basicOpen_of_free`, so it contains a nonempty basic open `D(h₁)`;
likewise `D(h₂)` for `b`. Take `h = h₁ ⬝ h₂`. For `q ∈ D(h)` the fibre `κ(q) ⊗[E] (E ⊗[D] T)` has
both `1 ⊗ₜ a` and `1 ⊗ₜ b` non-nilpotent, by
`Algebra.not_isNilpotent_one_tmul_of_comap_eq`, while their product `1 ⊗ₜ (a ⬝ b)` is nilpotent; so
the nilradical of that fibre is not prime and its spectrum is not irreducible. -/
theorem exists_ne_zero_forall_not_mem_geometricallyIrreducibleFibreLocus_of_free [IsDomain E]
    [IsNoetherianRing E] [Algebra.FiniteType D T] [Module.Free E (E ⊗[D] T)] {a b : E ⊗[D] T}
    (ha : ¬ IsNilpotent a) (hb : ¬ IsNilpotent b) (hab : IsNilpotent (a * b)) :
    ∃ h : E, h ≠ 0 ∧ ∀ q : PrimeSpectrum E, h ∉ q.asIdeal →
      comap (algebraMap D E) q ∉ geometricallyIrreducibleFibreLocus D T := by
  have hfp : (algebraMap E (E ⊗[D] T)).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
  have hcon : ∀ x : E ⊗[D] T, IsConstructible
      (comap (algebraMap E (E ⊗[D] T)) '' (basicOpen x : Set (PrimeSpectrum (E ⊗[D] T)))) :=
    fun _ => isConstructible_comap_image hfp isConstructible_basicOpen
  have key : ∀ x : E ⊗[D] T, ¬ IsNilpotent x → ∃ h : E, h ≠ 0 ∧ ∀ q : PrimeSpectrum E,
      h ∉ q.asIdeal → ¬ IsNilpotent ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] x) := fun x hx => by
    obtain ⟨h, h0, hsub⟩ := exists_ne_zero_basicOpen_subset_of_isConstructible (hcon x)
      (bot_mem_comap_image_basicOpen_of_free hx)
    refine ⟨h, h0, fun q hq => ?_⟩
    obtain ⟨P, hP, hPq⟩ := hsub ((mem_basicOpen h q).mpr hq)
    exact not_isNilpotent_one_tmul_of_comap_eq q P hPq ((mem_basicOpen x P).mp hP)
  obtain ⟨h₁, h₁0, h₁q⟩ := key a ha
  obtain ⟨h₂, h₂0, h₂q⟩ := key b hb
  refine ⟨h₁ * h₂, mul_ne_zero h₁0 h₂0, fun q hq => ?_⟩
  refine not_mem_geometricallyIrreducibleFibreLocus_comap E q fun hirr => ?_
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hirr
  obtain ⟨n, hn⟩ := hab
  have hprod : ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] a) *
      ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] b) ∈ nilradical _ := by
    rw [TensorProduct.tmul_mul_tmul, one_mul, mem_nilradical]
    exact ⟨n, by rw [TensorProduct.tmul_pow, one_pow, hn, _root_.TensorProduct.tmul_zero]⟩
  rcases hirr.mem_or_mem hprod with hmem | hmem
  · exact h₁q q (fun hh => hq (q.asIdeal.mul_mem_right _ hh)) (mem_nilradical.mp hmem)
  · exact h₂q q (fun hh => hq (q.asIdeal.mul_mem_left _ hh)) (mem_nilradical.mp hmem)

end Spread

section Bad

variable {D T : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]

/-- **The bad half of the generic-fibre dichotomy for geometric irreducibility, with the witness
field named.** Let `D` be a Noetherian domain and `T` a finite type `D`-algebra. If there is a
field `K` with `D → K` injective for which `Spec (T ⊗[D] K)` is not irreducible, then some nonempty
basic open of `Spec D` is disjoint from the geometrically irreducible fibre locus of `T`.

A reducible spectrum means a non-prime nilradical, which is either the whole ring — the degenerate
case where `K ⊗[D] T` vanishes — or a pair of non-nilpotent elements with nilpotent product. In the
second case the two elements are finite sums of pure tensors, and
`Algebra.exists_subalgebra_finiteType_free` provides a finite type `D`-subalgebra `E ⊆ K`
containing their left factors with `E ⊗[D] T` free over `E`. Freeness makes
`E ⊗[D] T → K ⊗[D] T` injective by `Algebra.subalgebraTensorMap_injective`, so the pair comes from
a pair in `E ⊗[D] T` with the same properties, and the spreading step
`Algebra.exists_ne_zero_forall_not_mem_geometricallyIrreducibleFibreLocus_of_free` followed by
`Algebra.exists_ne_zero_disjoint_of_forall_not_mem_comap` finishes. In the first case injectivity
makes `E ⊗[D] T` the zero ring and
`Algebra.forall_not_mem_geometricallyIrreducibleFibreLocus_of_subsingleton` applies to every prime
of `E`. -/
theorem exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus_of_not_irreducibleSpace
    [Algebra.FiniteType D T] (K : Type u) [Field K] [Algebra D K]
    (hDK : Function.Injective (algebraMap D K))
    (hK : ¬ IrreducibleSpace (PrimeSpectrum (T ⊗[D] K))) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyIrreducibleFibreLocus D T) := by
  classical
  have hK' : ¬ (nilradical (K ⊗[D] T)).IsPrime := by
    rw [← PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    exact fun h => hK ((irreducibleSpace_primeSpectrum_congr
      (TensorProduct.comm D T K).toRingEquiv).mpr h)
  -- the witnesses, and the finite set of elements of `K` they involve
  obtain ⟨c, hwit⟩ : ∃ c : Finset K, Subsingleton (K ⊗[D] T) ∨
      ∃ (x y : K ⊗[D] T) (s t : Finset (K × T)), ¬ IsNilpotent x ∧ ¬ IsNilpotent y ∧
        IsNilpotent (x * y) ∧ x = ∑ i ∈ s, i.1 ⊗ₜ i.2 ∧ y = ∑ i ∈ t, i.1 ⊗ₜ i.2 ∧
        s.image Prod.fst ⊆ c ∧ t.image Prod.fst ⊆ c := by
    by_cases htop : nilradical (K ⊗[D] T) = ⊤
    · refine ⟨∅, Or.inl (subsingleton_iff_zero_eq_one.mp ?_)⟩
      obtain ⟨n, hn⟩ : IsNilpotent (1 : K ⊗[D] T) :=
        mem_nilradical.mp (htop ▸ Submodule.mem_top)
      rw [one_pow] at hn
      exact hn.symm
    obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y : K ⊗[D] T, IsNilpotent (x * y) ∧ ¬ IsNilpotent x ∧
        ¬ IsNilpotent y := by
      by_contra hc
      refine hK' (Ideal.isPrime_iff.mpr ⟨htop, fun {u v} huv => ?_⟩)
      rw [mem_nilradical] at huv
      rw [mem_nilradical, mem_nilradical]
      by_cases hu : IsNilpotent u
      · exact Or.inl hu
      · exact Or.inr (by by_contra hv; exact hc ⟨u, v, huv, hu, hv⟩)
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset x
    obtain ⟨t, ht⟩ := TensorProduct.exists_finset y
    exact ⟨s.image Prod.fst ∪ t.image Prod.fst, Or.inr
      ⟨x, y, s, t, hx, hy, hxy, hs, ht, Finset.subset_union_left, Finset.subset_union_right⟩⟩
  obtain ⟨E, hft, hfree, hcE⟩ := exists_subalgebra_finiteType_free (T := T) K hDK c
  have hinj := subalgebraTensorMap_injective D T E
  have : IsNoetherianRing ↥E := Algebra.FiniteType.isNoetherianRing D ↥E
  obtain ⟨h, hh0, hh⟩ : ∃ h : ↥E, h ≠ 0 ∧ ∀ q : PrimeSpectrum ↥E, h ∉ q.asIdeal →
      comap (algebraMap D ↥E) q ∉ geometricallyIrreducibleFibreLocus D T := by
    rcases hwit with hsub | ⟨x, y, s, t, hx, hy, hxy, hxs, hyt, hsc, htc⟩
    · exact ⟨1, one_ne_zero, fun q _ =>
        forall_not_mem_geometricallyIrreducibleFibreLocus_of_subsingleton ↥E hinj.subsingleton q⟩
    obtain ⟨a, ha⟩ := mem_range_subalgebraTensorMap D T K
      (fun i hi => hcE _ (hsc (Finset.mem_image_of_mem _ hi))) hxs
    obtain ⟨b, hb⟩ := mem_range_subalgebraTensorMap D T K
      (fun i hi => hcE _ (htc (Finset.mem_image_of_mem _ hi))) hyt
    obtain ⟨n, hn⟩ := hxy
    exact exists_ne_zero_forall_not_mem_geometricallyIrreducibleFibreLocus_of_free ↥E
      (a := a) (b := b) (fun hnil => hx (ha ▸ hnil.map _)) (fun hnil => hy (hb ▸ hnil.map _))
      ⟨n, hinj (by rw [map_pow, map_mul, ha, hb, hn, map_zero])⟩
  exact exists_ne_zero_disjoint_of_forall_not_mem_comap ↥E
    (injective_algebraMap_subalgebra D K hDK E) hh0 hh

/-- **The bad half of the generic-fibre dichotomy for geometric irreducibility.** Let `D` be a
Noetherian domain and `T` a finite type `D`-algebra. If the generic point of `Spec D` does not lie
in the geometrically irreducible fibre locus of `T`, then some nonempty basic open of `Spec D` is
disjoint from that locus.

This is the affine case at the generic point of the negative direction of Stacks 055A, and the
companion of `Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`. The
hypothesis names a field `K` with `ker (D → K) = (0)` whose fibre has reducible spectrum, and
`Algebra.exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus_of_not_irreducibleSpace`
spreads that failure out. -/
theorem exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∉
      geometricallyIrreducibleFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyIrreducibleFibreLocus D T) := by
  obtain ⟨K, hfield, halg, hker, hnd⟩ :=
    (not_mem_geometricallyIrreducibleFibreLocus_iff _).mp hgen
  exact exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus_of_not_irreducibleSpace K
    ((RingHom.injective_iff_ker_eq_bot _).mpr hker) hnd

end Bad

/-- **The affine case of the level set `n = 1` of Stacks 055B from the good half of Stacks 055A.**
Over a Noetherian ring `A` the geometrically irreducible fibre locus of a finite type algebra `C`
is constructible, granted only that over a Noetherian domain whose generic fibre is geometrically
irreducible some nonempty basic open lies in the geometrically irreducible fibre locus.

This is `Algebra.isConstructible_geometricallyIrreducibleFibreLocus` with its dichotomy hypothesis
supplied by the hypothesis here together with the now-proved
`Algebra.exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus`. -/
theorem isConstructible_geometricallyIrreducibleFibreLocus_of_goodGeneric
    (hgood : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIrreducibleFibreLocus A C) := by
  refine isConstructible_geometricallyIrreducibleFibreLocus (fun D T _ _ _ _ _ _ => ?_) A C
  by_cases hgen :
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T
  · obtain ⟨f, hf0, hf⟩ := hgood D T hgen
    exact ⟨f, hf0, Or.inl hf⟩
  · obtain ⟨f, hf0, hf⟩ := exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus hgen
    exact ⟨f, hf0, Or.inr hf⟩

/-- **The affine case of Stacks 055A at the generic point is the affine case of Stacks 055B.** The
good half of the generic-fibre dichotomy for geometric irreducibility — over a Noetherian domain
`D` with a finite type algebra `T`, a geometrically irreducible generic fibre forces a nonempty
basic open of `Spec D` inside `Algebra.geometricallyIrreducibleFibreLocus D T` — holds for all
Noetherian domains if and only if that locus is constructible over every Noetherian ring.

This is `Algebra.exists_basicOpen_subset_fibreLocus_iff_isConstructible` at irreducibility of the
spectrum, whose bad half is
`Algebra.exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus`. Together with
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` it says that
both statements still missing from Stacks 05FT are equivalent to the constructibility results they
are invoked to prove, so neither can be obtained from constructible sets alone. -/
theorem exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible :
    (∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
        [Algebra.FiniteType D T],
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
          ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyIrreducibleFibreLocus D T) ↔
      ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
        [Algebra.FiniteType A C], IsConstructible (geometricallyIrreducibleFibreLocus A C) :=
  exists_basicOpen_subset_fibreLocus_iff_isConstructible
    (fun _ _ _ _ e => irreducibleSpace_primeSpectrum_congr e)
    fun _ _ _ _ _ _ _ _ hgen => exists_ne_zero_disjoint_geometricallyIrreducibleFibreLocus hgen

/-- **Stacks 05FT from the affine cases of Stacks 0579 and Stacks 055B.** Let `R → S` be flat of
finite presentation and suppose `S ⊗[R] κ(p)` is geometrically integral over `κ(p)` for every prime
`p` of `R`. Then `S` is a projective `R`-module, provided that over every Noetherian ring the
geometrically reduced fibre locus and the geometrically irreducible fibre locus of a finite type
algebra are constructible.

By Stacks 05DY the geometrically integral fibre locus is the intersection of those two, so
`Algebra.isConstructible_geometricallyIntegralFibreLocus` discharges the single hypothesis of
`Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible`. By
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` and
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible` the two
hypotheses are interchangeable with the good halves of Stacks 0578 and Stacks 055A, which is the
form `Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves` takes them in. -/
theorem projective_of_geometricallyIntegral_fibres_of_isConstructible_halves
    (hred : ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
      [Algebra.FiniteType A C], IsConstructible (geometricallyReducedFibreLocus A C))
    (hirr : ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
      [Algebra.FiniteType A C], IsConstructible (geometricallyIrreducibleFibreLocus A C))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_isConstructible
    (fun R₀ S₀ _ _ _ _ _ _ =>
      isConstructible_geometricallyIntegralFibreLocus R₀ S₀ (hirr R₀ S₀) (hred R₀ S₀)) h

end Algebra

end
