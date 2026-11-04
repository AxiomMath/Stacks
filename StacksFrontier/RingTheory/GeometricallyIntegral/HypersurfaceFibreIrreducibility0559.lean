module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.PolynomialIrreducibility
public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible
public import StacksFrontier.RingTheory.GeometricallyIntegral.SmoothGenericFibre
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometrically irreducible fibres of a hypersurface, the last step of Stacks 0559

The First proof of Stacks 0559 ends by replacing the given morphism `X → Y = Spec A` with the
hypersurface `X' = Spec (A[x_1, …, x_{r+1}]/(P))` cut out by the minimal polynomial of a
primitive element of the function field of the generic fibre, and then says *"it suffices to
prove the lemma for `X' → Y`, which is the content of Lemma 0557"*.

**This file proves that last step**, unconditionally, in the ring-theoretic form the
constructibility chain consumes. For a domain `D` and a polynomial `P ∈ D[x_i : i ∈ ι]` in
finitely many variables which is irreducible over an algebraic closure of the fraction field of
`D`, there is a nonzero `f : D` such that every prime in the basic open `D(f)` lies in the
geometrically irreducible fibre locus of `D[x_i]/(P)`. That is exactly the conclusion of the
irreducible good half `hirr` — the hypothesis of
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_irreducible_goodGeneric` — for the
hypersurface algebras.

The two ingredients are Stacks 0557, `MvPolynomial.exists_away_irreducible_map`, which produces
`f` together with the irreducibility of every field-valued specialization of `P` over `D(f)`, and
the base change `MvPolynomial.quotientSpanTensorRingEquiv`, which identifies the fibre of a
hypersurface with the hypersurface cut out by the specialized polynomial.

## Main results

* `MvPolynomial.quotientSpanTensorRingEquiv`: the fibre of a hypersurface is a hypersurface,
  `(D[x_i]/(P)) ⊗[D] k ≃+* k[x_i]/(P^k)`.
* `MvPolynomial.isDomain_quotient_span_of_irreducible`: a hypersurface over a field, cut out by an
  irreducible polynomial, is a domain.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`:
  **the main result.** The conclusion of the irreducible good half of the generic-fibre dichotomy
  for a hypersurface whose defining polynomial is absolutely irreducible over the fraction field.
* `Algebra.bot_mem_geometricallyIrreducibleFibreLocus_of_irreducible_mvPolynomial`: in that
  situation the generic point itself lies in the locus, so the hypothesis of the good half holds
  as well as its conclusion.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_integral_generic`:
  the same conclusion from the hypothesis in the shape the First proof has it after the cover of
  Stacks 0550, namely that the generic fibre is geometrically *integral*. Absolute irreducibility
  of the defining polynomial is then a consequence rather than an assumption.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIntegralFibreLocus_of_mvPolynomial`: the
  good half of the generic-fibre dichotomy for the geometrically integral fibre locus of a
  hypersurface, obtained by intersecting the previous result with the reduced half.

## Implementation notes

No declaration here carries a `@[stacks 0559]` or `@[stacks 055A]` attribute. The tagged
statements are about an arbitrary morphism of finite type, and the hypersurface case is one step
of their proof; a tag on it would over-claim. What remains of the First proof is named in
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`'s
docstring.

Non-degeneracy is witnessed inside the same family of algebras, and the witnesses are theorems of
this file rather than remarks. `Algebra.geometricallyIrreducibleFibreLocus_quotient_span_zero`
gives a hypersurface whose locus is all of `Spec D`, and
`Algebra.geometricallyIrreducibleFibreLocus_quotient_span_X_mul_X_eq_empty` one whose locus is
empty, so the predicate the main result lands in takes both extremes. The second is sharper than
a mere extreme: `Algebra.not_exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus`
turns it into a proof that the *conclusion* of the main result is false for `P = x₀x₁`, whose
specializations are reducible over every field, so the absolute-irreducibility hypothesis cannot
be dropped. Note that the companion degeneration `P = x₀²` would not serve: the dual numbers
`k[x]/(x²)` are geometrically irreducible
(`Algebra.isGeometricallyIrreducible_quotient_span_X_sq`), which is why the witness has to be
reducible rather than merely non-reduced.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 0557](https://stacks.math.columbia.edu/tag/0557)
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u

namespace MvPolynomial

/-- **The fibre of a hypersurface is a hypersurface.** For a polynomial `P` over a commutative
ring `D` in a family of variables `ι` and a `D`-algebra `k`, base change along `D → k` carries
`D[x_i : i ∈ ι]/(P)` to `k[x_i : i ∈ ι]/(P^k)`, where `P^k` is the image of `P` under the
coefficientwise map. -/
noncomputable def quotientSpanTensorRingEquiv (D : Type*) [CommRing D] (ι : Type*) (k : Type*)
    [CommRing k] [Algebra D k] (P : MvPolynomial ι D) :
    (MvPolynomial ι D ⧸ Ideal.span {P}) ⊗[D] k ≃+*
      MvPolynomial ι k ⧸ Ideal.span {P.map (algebraMap D k)} :=
  let e : MvPolynomial ι D ⊗[D] k ≃+* MvPolynomial ι k :=
    (Algebra.TensorProduct.comm D (MvPolynomial ι D) k).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv D k).toRingEquiv
  have hmap : Ideal.span {P.map (algebraMap D k)} =
      ((Ideal.span {P}).map
        (algebraMap (MvPolynomial ι D) (MvPolynomial ι D ⊗[D] k))).map (e : _ →+* _) := by
    rw [Ideal.map_map, Ideal.map_span]
    congr 1
    simp only [Set.image_singleton, Set.singleton_eq_singleton_iff]
    change _ = e (algebraMap (MvPolynomial ι D) (MvPolynomial ι D ⊗[D] k) P)
    simp [e, Algebra.TensorProduct.algebraMap_apply]
  (Algebra.TensorProduct.quotientTensorEquiv (R := D) D k (MvPolynomial ι D)
    (Ideal.span {P})).toRingEquiv.trans (Ideal.quotientEquiv _ _ e hmap)

/-- A hypersurface over a field, cut out by an irreducible polynomial, is a domain: the
polynomial ring is a unique factorisation domain, so an irreducible element generates a prime
ideal. No finiteness of the family of variables is needed. -/
@[sga "3 III 4.6.6" "partial"]
theorem isDomain_quotient_span_of_irreducible (k : Type*) [Field k] (ι : Type*)
    {Q : MvPolynomial ι k} (hQ : Irreducible Q) :
    IsDomain (MvPolynomial ι k ⧸ Ideal.span {Q}) :=
  have : (Ideal.span {Q}).IsPrime := (Ideal.span_singleton_prime hQ.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hQ)
  Ideal.Quotient.isDomain _

end MvPolynomial

namespace Algebra

/-- A field-valued point of `Spec D` lying in the basic open `D(f)` factors through the
localization of `D` away from `f`. -/
theorem exists_ringHom_localizationAway_comp_eq (D : Type u) [CommRing D] (f : D)
    (κ : Type u) [Field κ] [Algebra D κ] (hf : algebraMap D κ f ≠ 0) :
    ∃ φ : Localization.Away f →+* κ,
      φ.comp (algebraMap D (Localization.Away f)) = algebraMap D κ :=
  ⟨IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr hf),
    IsLocalization.Away.lift_comp f (isUnit_iff_ne_zero.mpr hf)⟩

/-- If the specialization of a hypersurface over a field `κ` is a domain, the fibre of the
hypersurface over `κ` has irreducible spectrum. -/
private theorem irreducibleSpace_tensor_of_isDomain_map (D : Type*) [CommRing D] (ι : Type*)
    (κ : Type*) [Field κ] [Algebra D κ] (P : MvPolynomial ι D)
    [IsDomain (MvPolynomial ι κ ⧸ Ideal.span {P.map (algebraMap D κ)})] :
    IrreducibleSpace (PrimeSpectrum ((MvPolynomial ι D ⧸ Ideal.span {P}) ⊗[D] κ)) :=
  have e := MvPolynomial.quotientSpanTensorRingEquiv D ι κ P
  have : IsDomain ((MvPolynomial ι D ⧸ Ideal.span {P}) ⊗[D] κ) :=
    Function.Injective.isDomain e e.injective
  PrimeSpectrum.irreducibleSpace

/-- **The irreducible good half of the generic-fibre dichotomy for a hypersurface.** Let `D` be a
domain with fraction field `K` and let `Kbar` be an algebraically closed extension of `K`. Let
`P ∈ D[x_i : i ∈ ι]`, in finitely many variables, be irreducible over `Kbar`. Then there is a
nonzero `f : D` such that every prime of the basic open `D(f)` lies in the geometrically
irreducible fibre locus of the hypersurface `D[x_i]/(P)`: for every field `κ` whose structure map
has that prime as kernel, `Spec ((D[x_i]/(P)) ⊗[D] κ)` is irreducible.

This is the conclusion of the hypothesis `hirr` of
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_irreducible_goodGeneric`, proved for
the hypersurface algebras, and it is the final step of the First proof of Stacks 0559: there the
general morphism of finite type is replaced, after the cover of Stacks 0550, the separating
transcendence basis of Stacks 030Q and the birational identification of Stacks 0552, by exactly
such a hypersurface, and the source then invokes Stacks 0557.

What is **not** proved here is that replacement: passing from an arbitrary finite type algebra to
a hypersurface with the same fibres over a nonempty open requires Stacks 0550 (formalized as
`Stacks.Cover0550.exists_finiteUniversalHomeomorphism_geometricallyReduced_genericFiber`),
Stacks 0552 and Stacks 054X, all three of which are statements about schemes, together with the
field theory that produces `P` from the function field of the generic fibre. Accordingly nothing
here carries a tag of Stacks 0559 or of Stacks 055A. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible
    (D : Type u) [CommRing D] [IsDomain D] (ι : Type u) [Finite ι] (P : MvPolynomial ι D)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (hP : Irreducible (P.map ((algebraMap K Kbar).comp (algebraMap D K)))) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {P}) := by
  obtain ⟨f, hf0, hf⟩ := MvPolynomial.exists_away_irreducible_map D K Kbar ι P hP
  refine ⟨f, hf0, fun p hp κ _ _ hker => ?_⟩
  have hfκ : algebraMap D κ f ≠ 0 := fun h =>
    (mem_basicOpen f p).mp hp (hker ▸ RingHom.mem_ker.mpr h)
  obtain ⟨φ, hφ⟩ := exists_ringHom_localizationAway_comp_eq D f κ hfκ
  have hirr : Irreducible (P.map (algebraMap D κ)) := hφ ▸ hf κ φ
  have : IsDomain (MvPolynomial ι κ ⧸ Ideal.span {P.map (algebraMap D κ)}) :=
    MvPolynomial.isDomain_quotient_span_of_irreducible κ ι hirr
  exact irreducibleSpace_tensor_of_isDomain_map D ι κ P

/-- In the situation of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible` the
generic point of `Spec D` lies in the geometrically irreducible fibre locus, so the *hypothesis*
of the irreducible good half holds for a hypersurface with absolutely irreducible defining
polynomial, as well as its conclusion. -/
theorem bot_mem_geometricallyIrreducibleFibreLocus_of_irreducible_mvPolynomial
    (D : Type u) [CommRing D] [IsDomain D] (ι : Type u) [Finite ι] (P : MvPolynomial ι D)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (hP : Irreducible (P.map ((algebraMap K Kbar).comp (algebraMap D K)))) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
      geometricallyIrreducibleFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {P}) := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible
      D ι P K Kbar hP
  exact hf ((mem_basicOpen f _).mpr (by simpa using hf0))

/-- **The locus takes the value `Set.univ`.** The hypersurface cut out by the zero polynomial is
the polynomial ring itself, whose fibres are polynomial rings over fields, hence domains; so every
prime of `Spec D` lies in the geometrically irreducible fibre locus. -/
theorem geometricallyIrreducibleFibreLocus_quotient_span_zero (D : Type u) [CommRing D]
    (ι : Type u) :
    geometricallyIrreducibleFibreLocus D
        (MvPolynomial ι D ⧸ Ideal.span {(0 : MvPolynomial ι D)}) = Set.univ := by
  refine Set.eq_univ_of_forall fun p κ _ _ _ => ?_
  have hp : (Ideal.span {(0 : MvPolynomial ι D).map (algebraMap D κ)}).IsPrime := by
    rw [Ideal.span_singleton_eq_bot.mpr (by simp)]
    exact Ideal.isPrime_bot
  have : IsDomain
      (MvPolynomial ι κ ⧸ Ideal.span {(0 : MvPolynomial ι D).map (algebraMap D κ)}) :=
    Ideal.Quotient.isDomain _
  exact irreducibleSpace_tensor_of_isDomain_map D ι κ 0

/-- **The irreducible good half for a hypersurface with geometrically integral generic fibre.**
This is the hypothesis in the shape the First proof of Stacks 0559 has it after the cover of
Stacks 0550 has made the generic fibre geometrically reduced as well as geometrically irreducible.

Over an algebraically closed field the fibre of the hypersurface is `Kbar[x_i]/(Q^{Kbar})`, and it
is a domain exactly when the ideal `(Q^{Kbar})` is prime, i.e. when `Q^{Kbar}` is zero or
irreducible. The first case is `Q = 0`, where the locus is everything; the second is the
hypothesis of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`.

Note that geometric irreducibility of the generic fibre alone would not do: it says only that
`(Q^{Kbar})` has prime radical, so `Q^{Kbar}` may be a proper power of an irreducible, and
spreading that case out is exactly what the reduction of Stacks 0550 is for. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_integral_generic
    (D : Type u) [CommRing D] [IsDomain D] (ι : Type u) [Finite ι] (Q : MvPolynomial ι D)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar] [Algebra D Kbar]
    [IsScalarTower D K Kbar]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
      geometricallyIntegralFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {Q})) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {Q}) := by
  have htower : algebraMap D Kbar = (algebraMap K Kbar).comp (algebraMap D K) :=
    IsScalarTower.algebraMap_eq D K Kbar
  have hinj : Function.Injective (algebraMap D Kbar) := by
    rw [htower]
    exact (algebraMap K Kbar).injective.comp (IsFractionRing.injective D K)
  have e := MvPolynomial.quotientSpanTensorRingEquiv D ι Kbar Q
  have : IsDomain ((MvPolynomial ι D ⧸ Ideal.span {Q}) ⊗[D] Kbar) :=
    hgen Kbar ((RingHom.injective_iff_ker_eq_bot _).mp hinj)
  have hdom : IsDomain (MvPolynomial ι Kbar ⧸ Ideal.span {Q.map (algebraMap D Kbar)}) :=
    Function.Injective.isDomain e.symm e.symm.injective
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  rcases eq_or_ne (Q.map (algebraMap D Kbar)) 0 with h0 | h0
  · have hQ : Q = 0 := MvPolynomial.map_injective _ hinj (by simpa using h0)
    subst hQ
    exact ⟨1, one_ne_zero, by
      rw [geometricallyIrreducibleFibreLocus_quotient_span_zero D ι]; exact Set.subset_univ _⟩
  · refine exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible
      D ι Q K Kbar ?_
    rw [← htower]
    exact ((Ideal.span_singleton_prime h0).mp hprime).irreducible

/-- **The good half of the generic-fibre dichotomy for the geometrically integral fibre locus of a
hypersurface.** Over a Noetherian domain `D`, if the generic fibre of `D[x_i]/(Q)` is geometrically
integral then so is every fibre over a nonempty basic open of `Spec D`.

The irreducible half is
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_integral_generic`
and the reduced half is the unconditional
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus`; the two basic opens are
intersected, which is a basic open of the product of the two witnesses, and
`Algebra.geometricallyIntegralFibreLocus_eq_inter` is Stacks 05DY. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIntegralFibreLocus_of_mvPolynomial
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] (ι : Type u) [Finite ι]
    (Q : MvPolynomial ι D)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar] [Algebra D Kbar]
    [IsScalarTower D K Kbar]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
      geometricallyIntegralFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {Q})) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIntegralFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {Q}) := by
  have hsplit := geometricallyIntegralFibreLocus_eq_inter D (MvPolynomial ι D ⧸ Ideal.span {Q})
  obtain ⟨f₁, hf₁0, hf₁⟩ :=
    exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_integral_generic
      D ι Q K Kbar hgen
  obtain ⟨f₂, hf₂0, hf₂⟩ :=
    exists_basicOpen_subset_geometricallyReducedFibreLocus D (MvPolynomial ι D ⧸ Ideal.span {Q})
      (hsplit.subset hgen).2
  refine ⟨f₁ * f₂, mul_ne_zero hf₁0 hf₂0, ?_⟩
  rw [hsplit]
  intro x hx
  rw [PrimeSpectrum.basicOpen_mul] at hx
  exact ⟨hf₁ hx.1, hf₂ hx.2⟩

end Algebra

/-! ## Non-degeneracy

Both extremes of `Algebra.geometricallyIrreducibleFibreLocus`, realised by hypersurfaces, and the
consequence that the absolute-irreducibility hypothesis of the main result cannot be dropped. -/

namespace Algebra

/-- In `k[x₀, x₁]/(x₀x₁)` the class of a variable is not nilpotent: the `k`-algebra map sending
that variable to the indeterminate of `k[t]` and the other one to zero kills `x₀x₁`, and so
factors through the quotient, where it sends the class to a non-nilpotent element. -/
theorem not_isNilpotent_mk_X_quotient_span_X_mul_X (κ : Type u) [Field κ] (i : Fin 2) :
    ¬ IsNilpotent (Ideal.Quotient.mk
      (Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) κ)})
      (MvPolynomial.X i)) := by
  classical
  set g : Fin 2 → Polynomial κ := fun l => if l = i then Polynomial.X else 0 with hg
  set ψ : MvPolynomial (Fin 2) κ →+* Polynomial κ := (MvPolynomial.aeval g).toRingHom with hψ
  have hgi : g i = Polynomial.X := by simp [hg]
  have hzero : ψ (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
    have : g 0 * g 1 = 0 := by fin_cases i <;> simp [hg]
    simpa [hψ] using this
  have hker : Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) κ)} ≤
      RingHom.ker ψ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hzero))
  intro hnil
  have hX : IsNilpotent (Polynomial.X : Polynomial κ) := by
    have := hnil.map (Ideal.Quotient.lift _ ψ fun a ha => RingHom.mem_ker.mp (hker ha))
    rwa [Ideal.Quotient.lift_mk, hψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X, hgi] at this
  exact Polynomial.X_ne_zero hX.eq_zero

/-- **The locus takes the value `∅`.** The hypersurface `D[x₀, x₁]/(x₀x₁)` has no geometrically
irreducible fibre at all: over any field the classes of `x₀` and `x₁` are non-nilpotent elements
with zero product, so the nilradical of the fibre is not prime. -/
theorem geometricallyIrreducibleFibreLocus_quotient_span_X_mul_X_eq_empty (D : Type u)
    [CommRing D] :
    geometricallyIrreducibleFibreLocus D
        (MvPolynomial (Fin 2) D ⧸
          Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) D)}) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  have hfib := hp p.asIdeal.ResidueField (Ideal.ker_algebraMap_residueField p.asIdeal)
  set κ := p.asIdeal.ResidueField with hκ
  have hmap : (MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) D).map (algebraMap D κ) =
      MvPolynomial.X 0 * MvPolynomial.X 1 := by simp
  set Q : MvPolynomial (Fin 2) κ := MvPolynomial.X 0 * MvPolynomial.X 1 with hQ
  have hirr : IrreducibleSpace (PrimeSpectrum (MvPolynomial (Fin 2) κ ⧸ Ideal.span {Q})) := by
    have e := (MvPolynomial.quotientSpanTensorRingEquiv D (Fin 2) κ
      (MvPolynomial.X 0 * MvPolynomial.X 1)).trans (Ideal.quotEquivOfEq (by rw [hmap]))
    refine irreducibleSpace_primeSpectrum_of_injective e.symm.toRingHom ?_
    exact e.symm.injective
  have hprime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  have hzero : Ideal.Quotient.mk (Ideal.span {Q}) (MvPolynomial.X 0) *
      Ideal.Quotient.mk (Ideal.span {Q}) (MvPolynomial.X 1) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rcases hprime.mem_or_mem
      (show _ ∈ nilradical (MvPolynomial (Fin 2) κ ⧸ Ideal.span {Q}) from
        hzero ▸ IsNilpotent.zero) with h | h
  · exact not_isNilpotent_mk_X_quotient_span_X_mul_X κ 0 h
  · exact not_isNilpotent_mk_X_quotient_span_X_mul_X κ 1 h

/-- **The absolute-irreducibility hypothesis of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible` is not
removable.** For `P = x₀x₁` over any domain the conclusion is false: the locus is empty, while a
basic open attached to a nonzero element of a domain is not. -/
theorem not_exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus (D : Type u)
    [CommRing D] [IsDomain D] :
    ¬ ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D
        (MvPolynomial (Fin 2) D ⧸
          Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) D)}) := by
  rintro ⟨f, hf0, hf⟩
  rw [geometricallyIrreducibleFibreLocus_quotient_span_X_mul_X_eq_empty D,
    Set.subset_empty_iff] at hf
  exact hf0 ((PrimeSpectrum.basicOpen_eq_bot_iff f).mp
    (TopologicalSpace.Opens.ext (by simpa using hf))).eq_zero

end Algebra

end
