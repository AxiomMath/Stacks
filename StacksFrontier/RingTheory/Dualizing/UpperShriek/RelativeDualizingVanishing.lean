module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Bounded
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Surjective

/-!
# Vanishing of the low cohomology of the relative dualizing complex

Let `φ : R →+* A` be a homomorphism of finite type and let `p` be a polynomial presentation of
`φ` in `n` variables.  The relative dualizing complex of `φ` is `ω^•_{A/R} = φ^!(R)`, the value
of algebraic upper shriek at the base ring placed in cohomological degree zero.  This file proves
that it has no cohomology below degree `-n`:

`H^i(ω^•_{A/R}) = 0` for `i < -n` ,

that the same therefore holds after localizing at any multiplicative subset of `A`, and — at the
bound the source actually asserts — that `H^i(ω^•_{A/R})_𝔭 = 0` for `i < -r` whenever every
fibre of `Spec(A) → Spec(R)` meeting the primes below `𝔭` has dimension at most `r`.

## Main results

* `Dualizing.PolynomialPresentation.isGE_relativeDualizingComplex` — `ω^•_{A/R}` lies in
  `D^{≥ -n}(A)`.
* `Dualizing.PolynomialPresentation.isZero_homology_relativeDualizingComplex` and
  `Dualizing.PolynomialPresentation.subsingleton_localizedModule_homology_relativeDualizingComplex`
  — that vanishing, before and after localization.
* `subsingleton_localizedModule_homology_relativeDualizingComplex_of_relativeDimensionAt_le`,
  in the namespace `Dualizing` — the conclusion of clause (1) of [Stacks, Tag 0E9R] at the
  sharp bound `-r`, from a bound `r` on the fibre dimensions.
* `Dualizing.subsingleton_localizedModule_homology_relativeDualizingComplex_ofSurjective` — the
  vanishing for a surjective `φ`, where the bound is `0`.

## Relation to the source

[Stacks, Tag 0E9R] assumes `R → A` of finite type between Noetherian rings and a prime
`𝔭 ⊂ R` with (1) `R_𝔭` Cohen–Macaulay and (2) `trdeg_{κ(R ∩ 𝔮)} κ(𝔮) ≤ r` at every minimal
prime `𝔮 ⊂ A`, and concludes that `H^i(ω^•_{A/R})_𝔭 ≠ 0 → -r ≤ i` and that `H^{-r}(ω^•_{A/R})_𝔭`
is `(S_2)` as an `A_𝔭`-module.  Both clauses are proved in full, for a general finite type `φ`,
in `StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay`:
`Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex` and
`Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex`.  The results of
this file are special cases or variants of the vanishing clause and carry no Tag 0E9R attribute.

**The bound `-n` is not the tag's bound.**  The number of variables `n` of a presentation is a
different quantity from `r`: it is larger, and it depends on the presentation rather than on `φ`.

**The fibre-dimension variant.**  The vanishing at a single prime `𝔮 ⊂ A` below minus the
dimension of the fibre through `𝔮` is [Stacks, Tag 0E9P], proved in
`StacksFrontier/RingTheory/Dualizing/UpperShriek/FibreDimensionBound.lean`; what is added here is
the
passage from the primes of `A` to the localization at the image of `R ∖ 𝔭`.  A bound on the fibre
dimensions is a different hypothesis from the source's (1) and (2), and neither implies the other.

**The surjective case.**  For a surjective `φ` the canonical presentation has no variables, so
`n = 0`; and `A` is a quotient of `R`, so `κ(𝔮) = κ(R ∩ 𝔮)` at every prime of `A` and `r = 0` is
the sharp admissible value in hypothesis (2).  The vanishing below `0` then holds without
hypothesis (1).

## Implementation notes

Upper shriek depends on the presentation and is well defined only up to isomorphism, that
independence being [stacks 0BZJ].  This library has Tag 0BZJ as
`Dualizing.PolynomialPresentation.upperShriekFunctor_iso`, but only conditionally on the
undischarged hypothesis `Dualizing.PolynomialEvalDuality`.  Every statement below is therefore
made for an arbitrary polynomial presentation rather than for one chosen by `Classical.choice`;
being `≥ -n` in the canonical t-structure is invariant under isomorphism, so this is the
strongest reading and it does not depend on Tag 0BZJ at all, conditional or otherwise.

The argument is the trivial half of the source's: `φ^!(K) = RHom_P(A, K ⊗_R^L P)[n]`, derived
base change along the flat map `R → P` is exact and so preserves the lower bound `0` of a module
placed in degree zero, derived coextension of scalars `RHom_P(A, -)` is right adjoint to an exact
functor and so preserves lower bounds, and the shift by `n` moves the bound to `-n`.

## References

* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- Localizing a zero module in `ModuleCat A` gives a subsingleton. -/
private theorem subsingleton_localizedModule_of_isZero (S : Submonoid A)
    {M : ModuleCat.{max v u} A} (h : Limits.IsZero M) : Subsingleton (LocalizedModule S M) := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

namespace PolynomialPresentation

/-- Derived base change along the polynomial algebra of a presentation carries a module placed in
cohomological degree zero to a complex with no cohomology in negative degrees: it is the derived
functor of an exact functor. -/
private theorem isGE_derivedExtension_singleFunctor_obj (p : PolynomialPresentation f)
    (M : ModuleCat.{max v u} R) :
    (p.derivedExtension.{u, v}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)).IsGE 0 := by
  have hflat : (MvPolynomial.C : R →+* p.Poly).Flat := p.flat_C
  let _ : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ hflat
  exact mapDerivedCategory_isGE
    (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly))
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M) 0

/-- **The relative dualizing complex lies in `D^{≥ -n}(A)`.**  For a polynomial presentation `p`
of `f` in `n` variables, `φ^!` of a module placed in cohomological degree zero — in particular
`ω^•_{A/R} = φ^!(R)` — has no cohomology below degree `-n`. -/
theorem isGE_relativeDualizingComplex (p : PolynomialPresentation f)
    (M : ModuleCat.{max v u} R) :
    (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)).IsGE
      (-(p.variableCount : ℤ)) := by
  have hext : (p.derivedExtension.{u, v}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)).IsGE 0 :=
    p.isGE_derivedExtension_singleFunctor_obj.{u, v} M
  have hhom : ((derivedHom.{u, v, u} p.toRingHom).obj (p.derivedExtension.{u, v}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M))).IsGE 0 :=
    isGE_derivedHom_obj.{u, v} p.toRingHom _ 0 hext
  rw [p.upperShriekFunctor_obj.{u, v}
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)]
  have hhom' : DerivedCategory.TStructure.t.IsGE
      ((derivedHom.{u, v, u} p.toRingHom).obj (p.derivedExtension.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M))) 0 := hhom
  exact DerivedCategory.TStructure.t.isGE_shift
    ((derivedHom.{u, v, u} p.toRingHom).obj (p.derivedExtension.{u, v}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)))
    0 (p.variableCount : ℤ) (-(p.variableCount : ℤ)) (by omega)

/-- **The relative dualizing complex has no cohomology below minus the number of variables.**
For a polynomial presentation of `f` in `n` variables, `ω^•_{A/R} = φ^!(R)` has no cohomology in
degrees below `-n`.

This is *not* [Stacks, Tag 0E9R]: the tag's bound is `-r` with `r` the transcendence-degree bound
of its hypothesis (2), and `n` is a different quantity — a larger one, and one that depends on
the presentation rather than on `f`.  The tag's bound, in the sharp form the source states it, is
`subsingleton_localizedModule_homology_relativeDualizingComplex_of_relativeDimensionAt_le` below;
see the module docstring. -/
theorem isZero_homology_relativeDualizingComplex (p : PolynomialPresentation f)
    (i : ℤ) (hi : i < -(p.variableCount : ℤ)) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  have : (p.upperShriekFunctor.{u, v}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (ULift.{v} R)))).IsGE (-(p.variableCount : ℤ)) :=
    p.isGE_relativeDualizingComplex.{u, v} (ModuleCat.of R (ULift.{v} R))
  exact DerivedCategory.isZero_of_isGE _ (-(p.variableCount : ℤ)) i hi

/-- **The vanishing below minus the number of variables, localized.**  The shape in which the
source states its vanishing, `H^i(ω^•_{A/R})_𝔭 = 0`, but at the bound `-n` rather than at the
source's `-r`; stated at an arbitrary multiplicative subset of `A`, which covers every
localization of `A`.

As for `Dualizing.PolynomialPresentation.isZero_homology_relativeDualizingComplex`, this is not
[Stacks, Tag 0E9R]: the bound is a different quantity from the tag's. -/
theorem subsingleton_localizedModule_homology_relativeDualizingComplex
    (p : PolynomialPresentation f) (S : Submonoid A) (i : ℤ)
    (hi : i < -(p.variableCount : ℤ)) :
    Subsingleton (LocalizedModule S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        (p.upperShriekFunctor.{u, v}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
            (ModuleCat.of R (ULift.{v} R)))))) := by
  exact subsingleton_localizedModule_of_isZero S
    (p.isZero_homology_relativeDualizingComplex.{u, v} i hi)

end PolynomialPresentation

/-! ### Clause (1) of Tag 0E9R at the sharp bound, from a bound on the fibre dimensions -/

/-- The local topological Krull dimension of a space at a point is nonnegative: the dimension is
computed by some open neighbourhood of the point, and such a neighbourhood is nonempty. -/
private theorem nonneg_topologicalKrullDimAt_aux {Y : Type*} [TopologicalSpace Y] (y : Y) :
    0 ≤ topologicalKrullDimAt Y y := by
  obtain ⟨⟨U, hy, _, hd⟩, _⟩ := topologicalKrullDimAt_isLeast Y y
  rw [hd]
  cases h : topologicalKrullDim U with
  | bot => exact False.elim (((topologicalKrullDim_eq_bot_iff_isEmpty U).mp h).false ⟨y, hy⟩)
  | coe n => simp

/-- The relative dimension at a prime is never `-∞`: the fibre through the prime contains it, so
it is nonempty. -/
private theorem nonneg_relativeDimensionAt (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔮 : Ideal S) [𝔮.IsPrime] : 0 ≤ Algebra.relativeDimensionAt R 𝔮 := by
  rw [Algebra.relativeDimensionAt]
  exact nonneg_topologicalKrullDimAt_aux _

/-- A relative dimension bounded above by a natural number is a natural number. -/
private theorem exists_eq_coe_of_relativeDimensionAt_le (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (𝔮 : Ideal S) [𝔮.IsPrime] {r : ℕ}
    (h : Algebra.relativeDimensionAt R 𝔮 ≤ (r : WithBot ℕ∞)) :
    ∃ d : ℕ, d ≤ r ∧ Algebra.relativeDimensionAt R 𝔮 = (d : WithBot ℕ∞) := by
  have h0 := nonneg_relativeDimensionAt R 𝔮
  obtain ⟨x, hx⟩ : ∃ x : ℕ∞, Algebra.relativeDimensionAt R 𝔮 = (x : WithBot ℕ∞) := by
    have hne : Algebra.relativeDimensionAt R 𝔮 ≠ ⊥ := by
      intro hb
      rw [hb] at h0
      exact absurd (le_bot_iff.mp h0) (by simp)
    obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hne
    exact ⟨x, hx.symm⟩
  rw [hx] at h ⊢
  have hxr : x ≤ (r : ℕ∞) := by exact_mod_cast h
  lift x to ℕ using (lt_of_le_of_lt hxr (by simp)).ne
  exact ⟨x, by exact_mod_cast hxr, rfl⟩

/-- A module killed by localizing at every prime disjoint from `S` is killed by localizing at
`S`: an element surviving the localization at `S` has an annihilator disjoint from `S`, hence
contained in a prime disjoint from `S`, and the element then survives at that prime. -/
private theorem subsingleton_localizedModule_of_forall_prime_disjoint {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] (S : Submonoid A)
    (h : ∀ 𝔮 : PrimeSpectrum A, Disjoint (𝔮.asIdeal : Set A) (S : Set A) →
      Subsingleton (LocalizedModule 𝔮.asIdeal.primeCompl M)) :
    Subsingleton (LocalizedModule S M) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  by_contra hm
  push Not at hm
  have hker : ∀ a : A, a ∈ LinearMap.ker (LinearMap.toSpanSingleton A M m) ↔ a • m = 0 := by
    intro a
    simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint ((LinearMap.ker (LinearMap.toSpanSingleton A M m) : Ideal A) : Set A)
      (S : Set A) := by
    rw [Set.disjoint_left]
    intro a ha haS
    exact hm a haS ((hker a).mp ha)
  obtain ⟨𝔮, h𝔮, hle, hd⟩ := Ideal.exists_le_prime_disjoint _ S hdisj
  have hsub := h ⟨𝔮, h𝔮⟩ hd
  rw [LocalizedModule.subsingleton_iff] at hsub
  obtain ⟨t, ht, htm⟩ := hsub m
  exact ht (hle ((hker t).mpr htm))

/-- **Clause (1) of [Stacks, Tag 0E9R] at the sharp bound `r`, from a bound on the fibre
dimensions.**  Let `R → A` be a finite type homomorphism of Noetherian rings presented by `p`,
let `𝔭 ⊂ R` be a prime and let `r : ℕ`.  If the fibre of `Spec(A) → Spec(R)` has dimension at
most `r` at every prime `𝔮 ⊂ A` whose contraction is contained in `𝔭`, then

`H^i(ω^•_{A/R})_𝔭 = 0` for `i < -r` .

This is the conclusion of clause (1) of the source at the source's own bound.  It is *not* the
tag: the source's hypotheses are (1) `R_𝔭` Cohen–Macaulay and (2)
`trdeg_{κ(R ∩ 𝔮)} κ(𝔮) ≤ r` at the minimal primes `𝔮` of `A`, and the fibre-dimension bound
stands in for them here, so it is a hypothesis the source does not have.  The tag itself, under
the source's hypotheses, is
`Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex`.

The vanishing at a single prime of `A` is [Stacks, Tag 0E9P], available as
`Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology`; what
is done here is the passage from the primes of `A` to the multiplicative set `φ(R ∖ 𝔭)`, which is
the localization the source's statement uses. -/
theorem subsingleton_localizedModule_homology_relativeDualizingComplex_of_relativeDimensionAt_le
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (𝔭 : Ideal R) [𝔭.IsPrime]
    (r : ℕ)
    (hr : ∀ 𝔮 : PrimeSpectrum A, Ideal.comap (algebraMap R A) 𝔮.asIdeal ≤ 𝔭 →
      Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (r : WithBot ℕ∞))
    (i : ℤ) (hi : i < -(r : ℤ)) :
    Subsingleton (LocalizedModule (Submonoid.map (algebraMap R A) 𝔭.primeCompl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  refine subsingleton_localizedModule_of_forall_prime_disjoint _ fun 𝔮 hd => ?_
  have hcomap : Ideal.comap (algebraMap R A) 𝔮.asIdeal ≤ 𝔭 := by
    intro a ha
    by_contra haP
    exact Set.disjoint_left.mp hd (Ideal.mem_comap.mp ha)
      (Submonoid.mem_map.mpr ⟨a, haP, rfl⟩)
  obtain ⟨d, hdr, hdeq⟩ := exists_eq_coe_of_relativeDimensionAt_le R 𝔮.asIdeal (hr 𝔮 hcomap)
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  have hbound := upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
    p 𝔮 d hdeq i hnt
  omega

/-- **The vanishing of [Stacks, Tag 0E9R] for a surjective `φ`, at the presentation with no
variables.**  For a surjective `φ`
the canonical presentation has no variables, so the bound of
`Dualizing.PolynomialPresentation.isZero_homology_relativeDualizingComplex` is `0`; and `A` is a
quotient of `R`, so `κ(𝔮) = κ(R ∩ 𝔮)` at every prime `𝔮` of `A` and `r = 0` is the sharp value
admitted by hypothesis (2) of the source.  The conclusion below is therefore the vanishing
asserted by Tag 0E9R in this special case, without hypothesis (1); the general statement is
`Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex`. -/
theorem isZero_homology_relativeDualizingComplex_ofSurjective
    (f : R →+* A) (hf : Function.Surjective f) (i : ℤ) (hi : i < 0) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      ((PolynomialPresentation.ofSurjective f hf).upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  have hcount : ((PolynomialPresentation.ofSurjective f hf).variableCount : ℤ) = 0 := by
    norm_num [PolynomialPresentation.ofSurjective]
  refine (PolynomialPresentation.ofSurjective f hf).isZero_homology_relativeDualizingComplex.{u, v}
    i ?_
  rw [hcount]
  simpa using hi

/-- **The vanishing of [Stacks, Tag 0E9R] for a surjective `φ`, localized.**  The localized
form of `Dualizing.isZero_homology_relativeDualizingComplex_ofSurjective`, which is the shape in
which the source states the clause. -/
theorem subsingleton_localizedModule_homology_relativeDualizingComplex_ofSurjective
    (f : R →+* A) (hf : Function.Surjective f) (S : Submonoid A) (i : ℤ) (hi : i < 0) :
    Subsingleton (LocalizedModule S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        ((PolynomialPresentation.ofSurjective f hf).upperShriekFunctor.{u, v}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
            (ModuleCat.of R (ULift.{v} R)))))) := by
  exact subsingleton_localizedModule_of_isZero S
    (isZero_homology_relativeDualizingComplex_ofSurjective.{u, v} f hf i hi)

end Dualizing

end
