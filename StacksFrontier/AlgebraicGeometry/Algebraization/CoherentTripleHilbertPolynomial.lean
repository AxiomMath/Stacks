module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparation
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hilbert polynomial of a coherent triple

Let `A` be a Noetherian local ring, let `f` lie in its maximal ideal and act regularly, and let
`(F, F₀, α)` be a coherent triple for `(A, f)`. A prepared extension of the triple exists and
all of them compute the same cokernel-minus-kernel length, so that number is an invariant of the
triple: its *Euler characteristic* `χ(F, F₀, α)`.

Twisting a coherent triple by the integer tensor powers of an invertible coherent triple
`(L, L₀, λ)` produces a function `ℤ → ℤ`, `n ↦ χ((F, F₀, α) ⊗ (L, L₀, λ)^{⊗ n})`, and the
source's proposition is that this function is given by a polynomial of degree at most
`dim(Supp F)`. This file sets up the Euler characteristic of the triple itself, the notion of an
invertible coherent triple, and the discrete-calculus step with which the source closes that
proof: a function on all of `ℤ` whose first difference is given by a rational polynomial of
degree at most `d` is itself given by one of degree at most `d + 1`.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic`: the Euler characteristic of a
  coherent triple.
* `Stacks.Algebraization.IsInvertibleTriple`: both members of the triple are invertible.

## Main results

* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_preparedExtension`: every
  prepared extension computes it.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`: an isomorphism of
  coherent triples preserves it.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_add_of_shortExact`: it is additive
  along a short exact sequence of coherent triples.
* `Stacks.Algebraization.exists_polynomial_natDegree_le_of_forall_sub_eq`: the discrete-calculus
  step described above.
* `Stacks.Algebraization.exists_polynomial_eulerCharacteristic_of_shortExact_succ`: additivity
  and that step combined into the induction step of the source's proof.
* `Stacks.Algebraization.isQuasiAffine_puncturedSpectrum`: the punctured spectrum of a Noetherian
  local ring is quasi-affine.

## Implementation notes

The Euler characteristic is `(cokernel length) - (kernel length)` of the closed-fibre map of a
prepared extension, read off a prepared extension produced by
`Stacks.Algebraization.nonempty_preparedExtension`. Both of the source's inputs for this to be
well posed are available: that theorem for existence, and
`Stacks.Algebraization.PreparedExtension.eulerCharacteristic_eq` for independence of the choice,
which is recorded below as `eulerCharacteristic_eq_of_preparedExtension` so that no consumer has
to know which prepared extension was taken.

Invertibility of a module on a scheme is the repository's `Stacks.Ample.IsInvertibleModule`,
which is Tag 01CS's "tensoring by it is an equivalence" condition with the sheaf condition on the
structure presheaf supplied.

The discrete-calculus step is the "variant of Algebra, Lemma 10.58.5 for functions defined for
all integers" which the source leaves to the reader. It is proved from
`Polynomial.exists_antidifference`, which produces an antidifference vanishing at `0`: the
difference between the function and that antidifference has vanishing first difference at every
integer, hence is constant in both directions, and adding the constant does not raise the degree.
Note that the conclusion holds at *every* integer, not merely for large ones, which is what
distinguishes it from `IsNumericalPolynomial`.

## References

* [Stacks Project, Tag 0F24](https://stacks.math.columbia.edu/tag/0F24)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 00JZ](https://stacks.math.columbia.edu/tag/00JZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### The Euler characteristic of a coherent triple -/

/-- **The Euler characteristic of a coherent triple**: the length of the cokernel minus the
length of the kernel of the closed-fibre map of a prepared extension. Prepared extensions exist
by `Stacks.Algebraization.nonempty_preparedExtension`, and the number does not depend on the one
chosen by `Stacks.Algebraization.PreparedExtension.eulerCharacteristic_eq`. -/
@[stacks 0F24 "the Euler characteristic of the triple itself"]
public noncomputable def CoherentTriple.eulerCharacteristic {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsRegular f) (T : CoherentTriple A f) : ℤ :=
  (nonempty_preparedExtension A f hf hreg T).some.eulerCharacteristic

/-- **Every prepared extension computes the Euler characteristic of its triple.** -/
public theorem CoherentTriple.eulerCharacteristic_eq_of_preparedExtension {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
    (hf : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsRegular f) (T : CoherentTriple A f)
    (P : PreparedExtension A f T) :
    T.eulerCharacteristic hf hreg = P.eulerCharacteristic :=
  PreparedExtension.eulerCharacteristic_eq A f hf T _ P

/-! ### Transport along a morphism of coherent triples -/

/-- **A prepared extension of a coherent triple is one of any triple it maps to isomorphically
over the punctured spectrum.** The module on `Spec A` is unchanged; the two comparison data are
composed with the components of the morphism of triples. -/
public noncomputable def PreparedExtension.ofHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : CoherentTriple.Hom T S) [IsIso φ.onPunctured]
    (P : PreparedExtension A f T) : PreparedExtension A f S where
  F' := P.F'
  coherent := P.coherent
  regular := P.regular
  alpha' := P.alpha' ≪≫ asIso φ.onPunctured
  alpha₀' := P.alpha₀' ≫ φ.onClosedFibre
  compatible := by
    have hφ := φ.compatible
    have hP := P.compatible
    simp only [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc] at hφ hP ⊢
    rw [hφ]
    simp only [← Category.assoc] at hP ⊢
    rw [hP]

/-- The closed-fibre map of a transported prepared extension is the original one followed by the
global sections of the closed-fibre component of the morphism. -/
public theorem PreparedExtension.closedFibreMap_ofHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : CoherentTriple.Hom T S) [IsIso φ.onPunctured]
    (P : PreparedExtension A f T) :
    (P.ofHom φ).closedFibreMap = P.closedFibreMap ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).map
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).map φ.onClosedFibre) := by
  simp only [PreparedExtension.closedFibreMap, PreparedExtension.ofHom, Functor.map_comp]
  rfl

/-- **The Euler characteristic of a coherent triple depends only on its isomorphism class.** A
morphism of coherent triples whose two components are isomorphisms preserves it. -/
public theorem CoherentTriple.eulerCharacteristic_eq_of_hom {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsRegular f) {T S : CoherentTriple A f} (φ : CoherentTriple.Hom T S)
    [IsIso φ.onPunctured] [IsIso φ.onClosedFibre] :
    T.eulerCharacteristic hf hreg = S.eulerCharacteristic hf hreg := by
  obtain ⟨P⟩ := nonempty_preparedExtension A f hf hreg T
  rw [T.eulerCharacteristic_eq_of_preparedExtension hf hreg P,
    S.eulerCharacteristic_eq_of_preparedExtension hf hreg (P.ofHom φ)]
  have hmap := PreparedExtension.closedFibreMap_ofHom φ P
  have ek : kernel (P.ofHom φ).closedFibreMap ≅ kernel P.closedFibreMap :=
    kernelIsoOfEq hmap ≪≫ kernelCompMono P.closedFibreMap _
  have ec : cokernel (P.ofHom φ).closedFibreMap ≅ cokernel P.closedFibreMap :=
    cokernelIsoOfEq hmap ≪≫ cokernelCompIsIso P.closedFibreMap _
  unfold PreparedExtension.eulerCharacteristic
  rw [ModuleCat.length_eq_of_iso ek, ModuleCat.length_eq_of_iso ec]

/-- **Stacks Project, Tag 0F26 for the triples themselves.** The Euler characteristic of a
coherent triple is additive along a short exact sequence of coherent triples. -/
@[stacks 0F26 "additivity for the Euler characteristics of the triples themselves"]
public theorem CoherentTriple.eulerCharacteristic_add_of_shortExact {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsRegular f) {T S R : CoherentTriple A f} {φ : CoherentTriple.Hom T S}
    {ψ : CoherentTriple.Hom S R} (hse : CoherentTriple.ShortExact φ ψ) :
    S.eulerCharacteristic hf hreg =
      T.eulerCharacteristic hf hreg + R.eulerCharacteristic hf hreg := by
  obtain ⟨P⟩ := nonempty_preparedExtension A f hf hreg T
  obtain ⟨Q⟩ := nonempty_preparedExtension A f hf hreg S
  obtain ⟨N⟩ := nonempty_preparedExtension A f hf hreg R
  rw [T.eulerCharacteristic_eq_of_preparedExtension hf hreg P,
    S.eulerCharacteristic_eq_of_preparedExtension hf hreg Q,
    R.eulerCharacteristic_eq_of_preparedExtension hf hreg N]
  exact Stacks.Algebraization.eulerCharacteristic_add_of_shortExact A f hf hse P Q N

/-! ### Invertible coherent triples -/

/-- **The punctured spectrum of a Noetherian local ring is quasi-affine**, being a quasi-compact
open subscheme of an affine scheme. This is what makes [Stacks, Tag 0F20] -- a finite subset of
an open lies in an affine nonvanishing locus of a global section of an invertible module --
applicable to the punctured-spectrum member of a coherent triple. -/
public instance isQuasiAffine_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : (Stacks.Divisors.puncturedSpectrum A).toScheme.IsQuasiAffine := by
  have : NoetherianSpace (PrimeSpectrum A) := inferInstance
  have : CompactSpace (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    @NoetherianSpace.compactSpace _ _
      (NoetherianSpace.set ((Stacks.Divisors.puncturedSpectrum A).1 : Set (PrimeSpectrum A)))
  exact Scheme.IsQuasiAffine.of_isImmersion (Stacks.Divisors.puncturedSpectrum A).ι

/-- **An invertible coherent triple**: a coherent triple whose module on the punctured spectrum
and whose module on the closed fibre are both invertible. -/
public structure IsInvertibleTriple {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (L : CoherentTriple A f) : Prop where
  /-- The module on the punctured spectrum is invertible. -/
  invertible_F : Stacks.Ample.IsInvertibleModule
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F
  /-- The module on the closed fibre is invertible. -/
  invertible_F₀ : Stacks.Ample.IsInvertibleModule (closedFibre A f) L.F₀

/-! ### Polynomiality on all of `ℤ` from the first difference -/

/-- **A function on all of `ℤ` whose first difference is a polynomial is a polynomial.** If
`g : ℤ → ℤ` satisfies `g (n + 1) - g n = Q(n)` at every integer `n`, with `Q` a rational
polynomial of degree at most `d`, then `g` agrees at every integer with a rational polynomial of
degree at most `d + 1`.

This is the variant of [Stacks, Tag 00JZ] for functions defined on all integers with which the
proof of [Stacks, Tag 0F27] concludes, and unlike `IsNumericalPolynomial` it constrains the
function at every integer rather than only at large ones. -/
@[stacks 0F27 "the concluding step: polynomiality on ℤ from the first difference"]
public theorem exists_polynomial_natDegree_le_of_forall_sub_eq {g : ℤ → ℤ} {d : ℕ}
    {Q : Polynomial ℚ} (hQ : Q.natDegree ≤ d)
    (hg : ∀ n : ℤ, (g (n + 1) : ℚ) - (g n : ℚ) = Q.eval (n : ℚ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d + 1 ∧ ∀ n : ℤ, (g n : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P₀, hP₀deg, hP₀zero, hP₀⟩ := Polynomial.exists_antidifference d Q hQ
  have step : ∀ m : ℤ, (g (m + 1) : ℚ) - P₀.eval ((m + 1 : ℤ) : ℚ)
      = (g m : ℚ) - P₀.eval (m : ℚ) := by
    intro m
    have h1 := hg m
    have h2 := hP₀ ((m : ℤ) : ℚ)
    have e : ((m + 1 : ℤ) : ℚ) = ((m : ℤ) : ℚ) + 1 := by push_cast; ring
    rw [e]
    linarith
  have key : ∀ n : ℤ, (g n : ℚ) - P₀.eval (n : ℚ) = (g 0 : ℚ) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [hP₀zero]
    | succ k ih => linarith [step (k : ℤ)]
    | pred k ih =>
      have h := step (-(k : ℤ) - 1)
      have e : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
      rw [e] at h
      linarith
  refine ⟨P₀ + Polynomial.C (g 0 : ℚ), ?_, fun n => ?_⟩
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le hP₀deg (by simp))
  · have := key n
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    linarith

/-- **The induction step of [Stacks, Tag 0F27], assembled.** Suppose each member of a family of
coherent triples sits in a short exact sequence over the previous one, and the Euler
characteristics of the quotients are given at every integer by a rational polynomial of degree at
most `d`. Then the Euler characteristics of the family are given at every integer by a rational
polynomial of degree at most `d + 1`. -/
public theorem exists_polynomial_eulerCharacteristic_of_shortExact_succ {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsRegular f) (twist quot : ℤ → CoherentTriple A f)
    (φ : ∀ n : ℤ, CoherentTriple.Hom (twist n) (twist (n + 1)))
    (ψ : ∀ n : ℤ, CoherentTriple.Hom (twist (n + 1)) (quot n))
    (hse : ∀ n : ℤ, CoherentTriple.ShortExact (φ n) (ψ n))
    {d : ℕ} {Q : Polynomial ℚ} (hQ : Q.natDegree ≤ d)
    (hquot : ∀ n : ℤ, (((quot n).eulerCharacteristic hf hreg : ℤ) : ℚ) = Q.eval (n : ℚ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d + 1 ∧
      ∀ n : ℤ, (((twist n).eulerCharacteristic hf hreg : ℤ) : ℚ) = P.eval (n : ℚ) := by
  refine exists_polynomial_natDegree_le_of_forall_sub_eq hQ fun n => ?_
  have h := CoherentTriple.eulerCharacteristic_add_of_shortExact hf hreg (hse n)
  have h' : (twist (n + 1)).eulerCharacteristic hf hreg - (twist n).eulerCharacteristic hf hreg
      = (quot n).eulerCharacteristic hf hreg := by omega
  rw [← hquot n, ← h']
  push_cast
  ring

end Stacks.Algebraization

end
