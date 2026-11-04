module

public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Algebra
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Algebra
public import StacksFrontier.LinearAlgebra.SymmetricPower.MonomialBasis
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of the conormal module of a quasi-regular sequence

Let `R` be a commutative ring, let `f : Fin c → R` be a finite sequence and let
`J = (f₀, …, f_{c-1})` be the ideal it generates.  Quasi-regularity of `f`
(`RingTheory.Sequence.IsQuasiRegular`, Stacks tag 061P) is *by definition* bijectivity of the
canonical map

`Φ : (R/J)[T₀, …, T_{c-1}] → ⨁_d J^d/J^{d+1}`

of Stacks tag 061N, in the polynomial-source form `Stacks.RingTheory.QuasiRegular.
associatedGradedMap`.  This file converts that polynomial-algebra statement into the
**symmetric-algebra** statement

`Sym_{R/J}(J/J²) ≅ ⨁_d J^d/J^{d+1}`, degreewise `Symᵈ_{R/J}(J/J²) ≅ J^d/J^{d+1}`,

which is the shape in which the comparison map of Stacks tag 0632 is phrased.  The bridge is the
degree-one half of quasi-regularity: the classes `f̄₀, …, f̄_{c-1}` of the generators form a
*basis* of `J/J²` over `R/J`, so `Sym_{R/J}(J/J²)` is a polynomial algebra in `c` variables and
`Φ` becomes the comparison map out of the symmetric algebra.

## Main definitions

* `Stacks.RingTheory.QuasiRegular.generatorClass`: the class of `f i` in `J/J²`, i.e. in the
  degree-one piece `Tcomp R f 1` of the associated graded module.
* `Stacks.RingTheory.QuasiRegular.basisGeneratorClass`: **the classes of the generators are a
  basis of `J/J²` over `R/J`**, for a sequence whose quasi-regularity map is injective.
* `Stacks.RingTheory.QuasiRegular.homogeneousToTcomp`: the restriction of the quasi-regularity
  map to the degree-`d` homogeneous polynomials, landing in `J^d/J^{d+1}`.
* `Stacks.RingTheory.QuasiRegular.symmetricAlgebraEquivTarget`: **the identification
  `Sym_{R/J}(J/J²) ≅ ⨁_d J^d/J^{d+1}`** for a quasi-regular sequence.
* `Stacks.RingTheory.QuasiRegular.symPowEquivTcomp`: **its degree-`d` part,
  `Symᵈ_{R/J}(J/J²) ≅ J^d/J^{d+1}`.**

## Main results

* `Stacks.RingTheory.QuasiRegular.span_generatorClass` and
  `Stacks.RingTheory.QuasiRegular.linearIndependent_generatorClass`: the two halves of
  `basisGeneratorClass`.  Spanning holds for any sequence; independence is exactly the
  degree-one injectivity of the quasi-regularity map.
* `Stacks.RingTheory.QuasiRegular.free_Tcomp_one` and
  `Stacks.RingTheory.QuasiRegular.finite_Tcomp_one`: `J/J²` is a finite free `R/J`-module.
* `Stacks.RingTheory.QuasiRegular.free_Tcomp` and
  `Stacks.RingTheory.QuasiRegular.finite_Tcomp`: **every graded piece `J^d/J^{d+1}` of a
  quasi-regular ideal is a finite free `R/J`-module**, being a symmetric power of `J/J²`.
* `Stacks.RingTheory.QuasiRegular.symmetricAlgebraEquivTarget_ι`,
  `Stacks.RingTheory.QuasiRegular.symmetricAlgebraEquivTarget_one` and
  `Stacks.RingTheory.QuasiRegular.symmetricAlgebraEquivTarget_prod_ι`: the identification is the
  *canonical* map — it is the identity on degree-one generators, it is unital, and it sends the
  monomial `∏ᵢ (f̄ᵢ)^{eᵢ}` of degree-one generators to the class of `f^e` in degree `|e|`.
* `Stacks.RingTheory.QuasiRegular.lof_symPowEquivTcomp`: the degree-`d` identification is the
  restriction of the total one to the degree-`d` symmetric power, landing in the degree-`d`
  summand; `Stacks.RingTheory.QuasiRegular.symPowEquivTcomp_basisSymmetricPower` reads off its
  value on the monomial basis of `Symᵈ`.
* `Stacks.RingTheory.QuasiRegular.tcomp_eq_associatedGradedPiece`: the graded pieces used here
  are the `AssociatedGraded.piece` of `J`.
* `Stacks.RingTheory.QuasiRegular.bijective_associatedGradedMap_of_isQuasiRegular`: the
  hypothesis used throughout is quasi-regularity in the sense of Stacks tag 061P.

## Implementation notes

The hypothesis of every statement below is bijectivity (or injectivity, where that suffices) of
`Stacks.RingTheory.QuasiRegular.associatedGradedMap`, rather than
`RingTheory.Sequence.IsQuasiRegular` itself.  The two are the same condition, by
`Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff`, and
`bijective_associatedGradedMap_of_isQuasiRegular` records the direction needed here; working
with the map keeps the reindexing of `List.ofFn` out of the proofs.

The degree-one basis is obtained without a graded splitting of the quasi-regularity map:
independence of the generator classes is read off by evaluating the map on the linear polynomial
`∑ᵢ āᵢ Tᵢ`, whose image lies in the single summand `J/J²`, and extracting a coefficient from the
monomial basis of the polynomial ring.

Degree `d` is isolated by composing the quasi-regularity map with the projection
`DirectSum.component` onto the degree-`d` summand.  That projection kills the image of a
homogeneous polynomial of any other degree, by
`associatedGradedMap_mem_range_lof`, so surjectivity in degree `d` follows from surjectivity of
the whole map after replacing a preimage by its degree-`d` homogeneous component.

The symmetric algebra is Mathlib's `SymmetricAlgebra`, whose degree-`d` piece is the repo's
`SymPow.symmetricPower`; the comparison with a polynomial algebra over a basis is Mathlib's
`SymmetricAlgebra.equivMvPolynomial`, refined degreewise by
`SymPow.symmetricPowerEquivHomogeneousSubmodule`.

`tcomp_eq_associatedGradedPiece` records that the graded pieces used here are *definitionally*
`AssociatedGraded.piece`, the model carrying the graded ring structure and the one the conormal
algebra of an immersion is built from, so the results below transfer to that model without
further work.

### What is *not* here

The target is the quasi-regularity development's own model `RingTheory.Sequence.Target` of
`⨁_d J^d/J^{d+1}`, which carries only a `(R/J)[T]`-module structure; the direct sums themselves
are *not* compared, and no graded *ring* structure on the target is used.  Consequently the
identification above is stated as a *linear* equivalence pinned down by its values on monomials
of degree-one generators, not as an isomorphism of graded rings, and the sheaf-level statement of
Stacks tag 0632 — that `Sym*(C_{Z/X}) → C_{Z/X,*}` is an isomorphism for a quasi-regular
immersion — is not derived from it.

## References

* [Stacks Project, Tag 061N](https://stacks.math.columbia.edu/tag/061N)
* [Stacks Project, Tag 061P](https://stacks.math.columbia.edu/tag/061P)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 063B](https://stacks.math.columbia.edu/tag/063B)
-/

@[expose] public section

namespace Stacks.RingTheory.QuasiRegular

variable {R : Type*} [CommRing R] {c : ℕ}

/-! ### Elementary lemmas on the associated graded module -/

/-- The total degree `|e| = ∑ᵢ eᵢ` used by the quasi-regularity map is `Finsupp.degree`, the
index of the monomial basis of a homogeneous part of a polynomial ring. -/
theorem qrMdeg_eq_degree (e : Fin c →₀ ℕ) : qrMdeg e = Finsupp.degree e :=
  (Finsupp.degree_eq_sum e).symm

/-- An element of `R` lies in `J^1 R` exactly when it lies in `J`. -/
private theorem mem_JpowM_one_iff {f : Fin c → R} {x : R} : x ∈ JpowM R f 1 ↔ x ∈ Jid f := by
  rw [mem_JpowM_iff, pow_one]

/-- A generator `f i` lies in `J^1 R = J`. -/
theorem mem_JpowM_one (f : Fin c → R) (i : Fin c) : f i ∈ JpowM R f 1 :=
  mem_JpowM_one_iff.mpr (Ideal.subset_span (Set.mem_range_self i))

/-- `1` lies in `J^0 R = R`. -/
theorem one_mem_JpowM_zero (f : Fin c → R) : (1 : R) ∈ JpowM R f 0 := by
  rw [mem_JpowM_iff, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- The monomial `f^e` lies in `J^d` whenever `|e| = d`. -/
theorem fpow_mem_JpowM (f : Fin c → R) {e : Fin c →₀ ℕ} {d : ℕ} (hd : qrMdeg e = d) :
    fpow f e ∈ JpowM R f d :=
  mem_JpowM_iff.mpr (hd ▸ fpow_mem f e)

/-- Graded classes in equal degrees of elements with equal underlying values agree.  This moves
the degree of a class past the dependency of `J^d/J^{d+1}` on `d`. -/
theorem gradedClass_congr (f : Fin c → R) {d d' : ℕ} (h : d = d') (a : JpowM R f d)
    (a' : JpowM R f d') (ha : (a : R) = (a' : R)) :
    gradedClass f d a = gradedClass f d' a' := by
  subst h
  rw [show a = a' from Subtype.ext ha]

/-- A graded class of degree `d` lies in the image of the degree-`d'` summand whenever
`d = d'`. -/
theorem gradedClass_mem_range_lof (f : Fin c → R) {d d' : ℕ} (h : d = d') (a : JpowM R f d) :
    gradedClass f d a ∈
      LinearMap.range (DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d') := by
  subst h
  exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- The graded class of `a ∈ J^d` is the image of its class in `J^d/J^{d+1}` under the inclusion
of the degree-`d` summand. -/
theorem gradedClass_eq_lof (f : Fin c → R) (d : ℕ) (a : JpowM R f d) :
    gradedClass f d a
      = DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d (Submodule.Quotient.mk a) :=
  rfl

/-! ### Degree one: the conormal module `J/J²` -/

/-- The class `f̄ᵢ` of the generator `f i` in the conormal module `J/J²`, the degree-one piece of
the associated graded module. -/
noncomputable def generatorClass (f : Fin c → R) (i : Fin c) : Tcomp R f 1 :=
  Submodule.Quotient.mk ⟨f i, mem_JpowM_one f i⟩

/-- The quasi-regularity map sends the variable `Tᵢ` to the class `f̄ᵢ` in the degree-one
summand. -/
theorem associatedGradedMap_X_eq (f : Fin c → R) (i : Fin c) :
    associatedGradedMap f (MvPolynomial.X i)
      = DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) 1 (generatorClass f i) := by
  rw [associatedGradedMap_X, imgTargetLin_eq_gradedClass,
    gradedClass_congr f (show qrMdeg (Finsupp.single i 1) = 1 by
      simp [qrMdeg, Finsupp.single_apply]) _ ⟨f i, mem_JpowM_one f i⟩
      (by simp [fpow, Finsupp.single_apply])]
  rfl

/-- The scalar `a mod J` acts on the generator class `f̄ᵢ` as the class of `a · f i`. -/
theorem smul_generatorClass (f : Fin c → R) (a : R) (i : Fin c)
    (hmem : a * f i ∈ JpowM R f 1) :
    (Ideal.Quotient.mk (Jid f) a) • generatorClass f i
      = Submodule.Quotient.mk ⟨a * f i, hmem⟩ := by
  have h : (Ideal.Quotient.mk (Jid f) a) • generatorClass f i = a • generatorClass f i := by
    rw [show (Ideal.Quotient.mk (Jid f) a) = a • (1 : qrRbar f) by
      simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq], smul_assoc, one_smul]
  rw [h, generatorClass, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, ← map_smul]
  rfl

/-- **The classes of the generators span `J/J²` over `R/J`**, for any finite sequence: an element
of `J` is a combination `∑ᵢ aᵢ f i`, and its class is the matching combination of the classes. -/
theorem span_generatorClass (f : Fin c → R) :
    Submodule.span (qrRbar f) (Set.range (generatorClass f)) = ⊤ := by
  refine top_unique fun x _ => ?_
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (mem_JpowM_one_iff.mp z.2)
    have hmem : ∀ i, a i * f i ∈ JpowM R f 1 := fun i =>
      mem_JpowM_one_iff.mpr (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))
    have hsum : ∑ i, (⟨a i * f i, hmem i⟩ : JpowM R f 1) = z := by
      refine Subtype.ext ?_
      rw [AddSubmonoidClass.coe_finsetSum]
      simpa [smul_eq_mul] using ha
    have key : ∑ i, (Ideal.Quotient.mk (Jid f) (a i)) • generatorClass f i
        = (Submodule.Quotient.mk z : Tcomp R f 1) :=
      calc ∑ i, (Ideal.Quotient.mk (Jid f) (a i)) • generatorClass f i
          = ∑ i, (Tsub R f 1).mkQ ⟨a i * f i, hmem i⟩ :=
            Finset.sum_congr rfl fun i _ => smul_generatorClass f (a i) i (hmem i)
        _ = (Tsub R f 1).mkQ (∑ i, (⟨a i * f i, hmem i⟩ : JpowM R f 1)) := (map_sum _ _ _).symm
        _ = (Submodule.Quotient.mk z : Tcomp R f 1) := by rw [hsum]; rfl
    rw [← key]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The classes of the generators are linearly independent in `J/J²` over `R/J`** when the
quasi-regularity map is injective. -/
theorem linearIndependent_generatorClass (f : Fin c → R)
    (h : Function.Injective (associatedGradedMap f)) :
    LinearIndependent (qrRbar f) (generatorClass f) := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  have hp : associatedGradedMap f
        (∑ j, g j • (MvPolynomial.X j : MvPolynomial (Fin c) (qrRbar f)))
      = DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) 1
          (∑ j, g j • generatorClass f j) := by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, map_smul, associatedGradedMap_X_eq]
  rw [hg, map_zero] at hp
  have hzero : (∑ j, g j • (MvPolynomial.X j : MvPolynomial (Fin c) (qrRbar f))) = 0 :=
    h (hp.trans (map_zero _).symm)
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) hzero
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hc
  have hco : ∀ j : Fin c, MvPolynomial.coeff (Finsupp.single i 1)
      (g j • (MvPolynomial.X j : MvPolynomial (Fin c) (qrRbar f)))
      = if j = i then g j else 0 := by
    intro j
    rw [show g j • (MvPolynomial.X j : MvPolynomial (Fin c) (qrRbar f))
        = MvPolynomial.monomial (Finsupp.single j 1) (g j) by
      rw [MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      MvPolynomial.coeff_monomial]
    exact if_congr (Finsupp.single_left_inj one_ne_zero) rfl rfl
  rw [Finset.sum_congr rfl fun j _ => hco j] at hc
  simpa using hc

/-- **The conormal module `J/J²` of a quasi-regular sequence is free on the classes of the
generators**, over `R/J`. -/
@[ega "IV 16.9.3" "(i), special case", sga "1 II 4.14" "(ii)", sga "7 VI 4.14" "more general"]
noncomputable def basisGeneratorClass (f : Fin c → R)
    (h : Function.Injective (associatedGradedMap f)) :
    Module.Basis (Fin c) (qrRbar f) (Tcomp R f 1) :=
  Module.Basis.mk (linearIndependent_generatorClass f h) (span_generatorClass f).ge

/-- The `i`-th vector of `basisGeneratorClass f h` is the class `generatorClass f i`. -/
@[simp]
theorem basisGeneratorClass_apply (f : Fin c → R)
    (h : Function.Injective (associatedGradedMap f)) (i : Fin c) :
    basisGeneratorClass f h i = generatorClass f i :=
  Module.Basis.mk_apply _ _ i

/-- The conormal module of a quasi-regular sequence is a free `R/J`-module. -/
@[sga "7 VI 4.14" "J/J² is a free A₀-module"]
theorem free_Tcomp_one (f : Fin c → R) (h : Function.Injective (associatedGradedMap f)) :
    Module.Free (qrRbar f) (Tcomp R f 1) :=
  Module.Free.of_basis (basisGeneratorClass f h)

/-- The conormal module of a quasi-regular sequence is a finite `R/J`-module. -/
theorem finite_Tcomp_one (f : Fin c → R) (h : Function.Injective (associatedGradedMap f)) :
    Module.Finite (qrRbar f) (Tcomp R f 1) :=
  Module.Finite.of_basis (basisGeneratorClass f h)

/-! ### Degree `d`: the homogeneous part of the quasi-regularity map -/

/-- The projection of `⨁_d J^d/J^{d+1}` onto its degree-`d` summand `J^d/J^{d+1}`. -/
noncomputable abbrev targetComponent (f : Fin c → R) (d : ℕ) :
    Target R f →ₗ[qrRbar f] Tcomp R f d :=
  DirectSum.component (qrRbar f) ℕ (fun n => Tcomp R f n) d

/-- **The quasi-regularity map is graded**: it carries a homogeneous polynomial of degree `d`
into the degree-`d` summand `J^d/J^{d+1}`, since it sends the monomial `T^e` into degree
`|e|`. -/
theorem associatedGradedMap_mem_range_lof (f : Fin c → R) (d : ℕ)
    {p : MvPolynomial (Fin c) (qrRbar f)}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) d) :
    associatedGradedMap f p ∈
      LinearMap.range (DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d) := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  have hps : associatedGradedMap f p = ∑ e ∈ p.support,
      associatedGradedMap f (MvPolynomial.monomial e (MvPolynomial.coeff e p)) := by
    rw [← map_sum, ← MvPolynomial.as_sum p]
  rw [hps]
  refine Submodule.sum_mem _ fun e he => ?_
  have hdeg : qrMdeg e = d := by
    rw [qrMdeg_eq_degree]
    simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (MvPolynomial.mem_support_iff.mp he)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.coeff e p)
  rw [← ha, associatedGradedMap_monomial, imgTargetLin_eq_gradedClass]
  exact gradedClass_mem_range_lof f hdeg _

/-- The degree-`d` part of the quasi-regularity map: the `R/J`-linear map from the degree-`d`
homogeneous polynomials to `J^d/J^{d+1}`, obtained by projecting the quasi-regularity map onto
the degree-`d` summand. -/
noncomputable def homogeneousToTcomp (f : Fin c → R) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) d →ₗ[qrRbar f] Tcomp R f d :=
  (targetComponent f d).comp
    ((associatedGradedMap f).comp
      (MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) d).subtype)

/-- The degree-`d` part of the quasi-regularity map, applied to a homogeneous polynomial. -/
private theorem homogeneousToTcomp_apply (f : Fin c → R) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) d) :
    homogeneousToTcomp f d p = targetComponent f d (associatedGradedMap f p) := rfl

/-- On a homogeneous polynomial of degree `d` the quasi-regularity map is the degree-`d` part
followed by the inclusion of the degree-`d` summand. -/
theorem lof_homogeneousToTcomp (f : Fin c → R) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) d) :
    DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d (homogeneousToTcomp f d p)
      = associatedGradedMap f (p : MvPolynomial (Fin c) (qrRbar f)) := by
  obtain ⟨t, ht⟩ := associatedGradedMap_mem_range_lof f d p.2
  rw [homogeneousToTcomp_apply, ← ht, DirectSum.component.lof_self]

/-- The degree-`d` part of an injective quasi-regularity map is injective. -/
theorem injective_homogeneousToTcomp (f : Fin c → R)
    (h : Function.Injective (associatedGradedMap f)) (d : ℕ) :
    Function.Injective (homogeneousToTcomp f d) := fun p q hpq =>
  Subtype.ext (h (by
    rw [← lof_homogeneousToTcomp f d p, ← lof_homogeneousToTcomp f d q, hpq]))

/-- The degree-`d` part of a surjective quasi-regularity map is surjective: a preimage of a
degree-`d` class may be replaced by its degree-`d` homogeneous component, because the images of
the other components lie in other summands. -/
theorem surjective_homogeneousToTcomp (f : Fin c → R)
    (h : Function.Surjective (associatedGradedMap f)) (d : ℕ) :
    Function.Surjective (homogeneousToTcomp f d) := by
  intro x
  obtain ⟨q, hq⟩ := h (DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d x)
  have hzero : ∀ k : ℕ, k ≠ d → targetComponent f d
      (associatedGradedMap f (MvPolynomial.homogeneousComponent k q)) = 0 := by
    intro k hk
    obtain ⟨t, ht⟩ := associatedGradedMap_mem_range_lof f k
      (MvPolynomial.homogeneousComponent_mem k q)
    rw [← ht, DirectSum.component.of (qrRbar f) d k t]
    exact dite_eq_right_iff.mpr fun hcon => absurd hcon hk
  have hx : x = ∑ k ∈ Finset.range (q.totalDegree + 1),
      targetComponent f d (associatedGradedMap f (MvPolynomial.homogeneousComponent k q)) := by
    rw [← map_sum, ← map_sum, MvPolynomial.sum_homogeneousComponent, hq]
    exact (DirectSum.component.lof_self (qrRbar f) d x).symm
  refine ⟨⟨MvPolynomial.homogeneousComponent d q,
    MvPolynomial.homogeneousComponent_mem d q⟩, ?_⟩
  by_cases hd : d ∈ Finset.range (q.totalDegree + 1)
  · rw [Finset.sum_eq_single_of_mem d hd fun k _ hk => hzero k hk] at hx
    exact hx.symm
  · rw [Finset.sum_eq_zero fun k hk => hzero k fun hcon => hd (hcon ▸ hk)] at hx
    change targetComponent f d (associatedGradedMap f (MvPolynomial.homogeneousComponent d q)) = x
    rw [MvPolynomial.homogeneousComponent_eq_zero d q
      (by simpa [Nat.lt_succ_iff] using hd), map_zero, map_zero, ← hx]

/-- The degree-`d` part of a bijective quasi-regularity map is bijective. -/
theorem bijective_homogeneousToTcomp (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (d : ℕ) :
    Function.Bijective (homogeneousToTcomp f d) :=
  ⟨injective_homogeneousToTcomp f h.injective d, surjective_homogeneousToTcomp f h.surjective d⟩

/-! ### The symmetric algebra of the conormal module -/

/-- **`Sym_{R/J}(J/J²) ≅ ⨁_d J^d/J^{d+1}` for a quasi-regular sequence.** The conormal module is
free on the classes of the generators, so its symmetric algebra is the polynomial algebra
`(R/J)[T₀, …, T_{c-1}]`, and the quasi-regularity map is an isomorphism out of it. -/
noncomputable def symmetricAlgebraEquivTarget (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) :
    SymmetricAlgebra (qrRbar f) (Tcomp R f 1) ≃ₗ[qrRbar f] Target R f :=
  (SymmetricAlgebra.equivMvPolynomial (basisGeneratorClass f h.injective)).toLinearEquiv.trans
    (LinearEquiv.ofBijective (associatedGradedMap f) h)

/-- The identification `Sym_{R/J}(J/J²) ≅ ⨁_d J^d/J^{d+1}` is the quasi-regularity map read
through the polynomial presentation of the symmetric algebra. -/
theorem symmetricAlgebraEquivTarget_apply (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f))
    (x : SymmetricAlgebra (qrRbar f) (Tcomp R f 1)) :
    symmetricAlgebraEquivTarget f h x
      = associatedGradedMap f
          (SymmetricAlgebra.equivMvPolynomial (basisGeneratorClass f h.injective) x) := rfl

/-- The polynomial presentation of `Sym_{R/J}(J/J²)` sends the degree-one generator `f̄ᵢ` to the
variable `Tᵢ`. -/
theorem equivMvPolynomial_ι_generatorClass (f : Fin c → R)
    (h : Function.Injective (associatedGradedMap f)) (i : Fin c) :
    SymmetricAlgebra.equivMvPolynomial (basisGeneratorClass f h)
        (SymmetricAlgebra.ι (qrRbar f) (Tcomp R f 1) (generatorClass f i))
      = MvPolynomial.X i := by
  rw [← basisGeneratorClass_apply f h i]
  exact SymmetricAlgebra.equivMvPolynomial_ι_apply _ i

/-- **The identification is the identity on degree-one generators**: it carries the generator
`ι x` of the symmetric algebra, for `x ∈ J/J²`, to `x` itself in the degree-one summand.  This
is the defining property of the comparison map of Stacks tag 0632. -/
theorem symmetricAlgebraEquivTarget_ι (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (x : Tcomp R f 1) :
    symmetricAlgebraEquivTarget f h (SymmetricAlgebra.ι (qrRbar f) (Tcomp R f 1) x)
      = DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) 1 x := by
  have key : (symmetricAlgebraEquivTarget f h).toLinearMap ∘ₗ
      SymmetricAlgebra.ι (qrRbar f) (Tcomp R f 1)
      = DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) 1 := by
    refine (basisGeneratorClass f h.injective).ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, basisGeneratorClass_apply]
    rw [LinearEquiv.coe_coe, symmetricAlgebraEquivTarget_apply,
      equivMvPolynomial_ι_generatorClass, associatedGradedMap_X_eq]
  exact LinearMap.congr_fun key x

/-- **The identification sends a monomial in the degree-one generators to the class of the
corresponding monomial in the `f i`**: `∏ᵢ f̄ᵢ^{eᵢ}` goes to the class of `f^e` in degree
`|e|`. -/
theorem symmetricAlgebraEquivTarget_prod_ι (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (e : Fin c →₀ ℕ) :
    symmetricAlgebraEquivTarget f h
        (∏ i ∈ e.support, SymmetricAlgebra.ι (qrRbar f) (Tcomp R f 1) (generatorClass f i) ^ e i)
      = gradedClass f (qrMdeg e) ⟨fpow f e, mem_JpowM_iff.mpr (fpow_mem f e)⟩ := by
  rw [symmetricAlgebraEquivTarget_apply, map_prod,
    Finset.prod_congr rfl fun i (_ : i ∈ e.support) => by
      rw [map_pow, equivMvPolynomial_ι_generatorClass],
    MvPolynomial.prod_X_pow_eq_monomial,
    congrArg (MvPolynomial.monomial e)
      (map_one (Ideal.Quotient.mk (Jid f))).symm,
    associatedGradedMap_monomial, imgTargetLin_eq_gradedClass]
  exact gradedClass_congr f rfl _ _ (mul_one _)

/-- **The identification is unital**: it carries `1` to the class of `1` in degree zero. -/
theorem symmetricAlgebraEquivTarget_one (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) :
    symmetricAlgebraEquivTarget f h 1 = gradedClass f 0 ⟨1, one_mem_JpowM_zero f⟩ := by
  have hz := symmetricAlgebraEquivTarget_prod_ι f h 0
  rw [Finsupp.support_zero, Finset.prod_empty] at hz
  rw [hz]
  exact gradedClass_congr f (by simp [qrMdeg]) _ _ (by simp [fpow])

/-- **`Symᵈ_{R/J}(J/J²) ≅ J^d/J^{d+1}` for a quasi-regular sequence**: the degree-`d` part of
the identification `Sym_{R/J}(J/J²) ≅ ⨁_d J^d/J^{d+1}`.  This is the affine shadow of the
assertion that the comparison map of Stacks tag 0632 is an isomorphism in every degree. -/
noncomputable def symPowEquivTcomp (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (d : ℕ) :
    SymPow.symmetricPower d (qrRbar f) (Tcomp R f 1) ≃ₗ[qrRbar f] Tcomp R f d :=
  (SymPow.symmetricPowerEquivHomogeneousSubmodule (basisGeneratorClass f h.injective) d).trans
    (LinearEquiv.ofBijective (homogeneousToTcomp f d) (bijective_homogeneousToTcomp f h d))

/-- The degree-`d` identification is the restriction of the total one to the degree-`d` symmetric
power, landing in the degree-`d` summand. -/
theorem lof_symPowEquivTcomp (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (d : ℕ)
    (x : SymPow.symmetricPower d (qrRbar f) (Tcomp R f 1)) :
    DirectSum.lof (qrRbar f) ℕ (fun n => Tcomp R f n) d (symPowEquivTcomp f h d x)
      = symmetricAlgebraEquivTarget f h (x : SymmetricAlgebra (qrRbar f) (Tcomp R f 1)) := by
  have h1 : symPowEquivTcomp f h d x
      = homogeneousToTcomp f d (SymPow.symmetricPowerEquivHomogeneousSubmodule
          (basisGeneratorClass f h.injective) d x) := rfl
  rw [h1, lof_homogeneousToTcomp, SymPow.coe_symmetricPowerEquivHomogeneousSubmodule_apply,
    symmetricAlgebraEquivTarget_apply]

/-- The degree-`d` identification sends the monomial basis element of `Symᵈ_{R/J}(J/J²)` indexed
by a multi-index `e` of degree `d` to the class of `f^e` in `J^d/J^{d+1}`. -/
theorem symPowEquivTcomp_basisSymmetricPower (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (d : ℕ)
    (e : {e : Fin c →₀ ℕ | Finsupp.degree e = d}) :
    symPowEquivTcomp f h d (SymPow.basisSymmetricPower (basisGeneratorClass f h.injective) d e)
      = Submodule.Quotient.mk
          ⟨fpow f (e : Fin c →₀ ℕ),
            fpow_mem_JpowM f ((qrMdeg_eq_degree (e : Fin c →₀ ℕ)).trans e.2)⟩ := by
  have hd : qrMdeg (e : Fin c →₀ ℕ) = d := (qrMdeg_eq_degree _).trans e.2
  have key := lof_symPowEquivTcomp f h d
    (SymPow.basisSymmetricPower (basisGeneratorClass f h.injective) d e)
  rw [SymPow.coe_basisSymmetricPower_apply] at key
  simp only [basisGeneratorClass_apply] at key
  rw [symmetricAlgebraEquivTarget_prod_ι,
    gradedClass_congr f hd _ ⟨fpow f (e : Fin c →₀ ℕ), fpow_mem_JpowM f hd⟩ rfl,
    gradedClass_eq_lof] at key
  have key2 := congrArg (targetComponent f d) key
  rwa [DirectSum.component.lof_self, DirectSum.component.lof_self] at key2

/-- **Every graded piece `J^d/J^{d+1}` of a quasi-regular ideal is a free `R/J`-module**, being
the `d`-th symmetric power of the free module `J/J²`. -/
theorem free_Tcomp (f : Fin c → R) (h : Function.Bijective (associatedGradedMap f)) (d : ℕ) :
    Module.Free (qrRbar f) (Tcomp R f d) :=
  have := free_Tcomp_one f h.injective
  Module.Free.of_equiv (symPowEquivTcomp f h d)

/-- **Every graded piece `J^d/J^{d+1}` of a quasi-regular ideal is a finite `R/J`-module**, being
the `d`-th symmetric power of the finite module `J/J²`. -/
@[ega "0 19.5.8" "special case"]
theorem finite_Tcomp (f : Fin c → R) (h : Function.Bijective (associatedGradedMap f)) (d : ℕ) :
    Module.Finite (qrRbar f) (Tcomp R f d) :=
  have := finite_Tcomp_one f h.injective
  Module.Finite.equiv (symPowEquivTcomp f h d)

/-! ### Comparison with the `AssociatedGraded` model -/

/-- **The two models of `J^n` agree.** The quasi-regularity development's `JpowM` is the `n`-th
term of the `J`-adic filtration in the sense of `AssociatedGraded.power`. -/
theorem jpowM_eq_associatedGradedPower (f : Fin c → R) (n : ℕ) :
    JpowM R f n = AssociatedGraded.power (M := R) (Jid f) n := rfl

/-- **The two models of `J^n/J^{n+1}` agree.** The quasi-regularity development's `Tcomp` is the
degree-`n` piece of the associated graded ring of `J` in the sense of `AssociatedGraded.piece`,
which is the model carrying the graded ring structure and the one the conormal algebra of an
immersion is built from: the two are the same quotient of the same submodule. -/
theorem tcomp_eq_associatedGradedPiece (f : Fin c → R) (n : ℕ) :
    Tcomp R f n = AssociatedGraded.piece (M := R) (Jid f) n := rfl

/-! ### The hypothesis is quasi-regularity -/

/-- The hypothesis used throughout this file is quasi-regularity of the sequence in the sense of
Stacks tag 061P, by `Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff`. -/
theorem bijective_associatedGradedMap_of_isQuasiRegular (f : Fin c → R)
    (h : RingTheory.Sequence.IsQuasiRegular R (List.ofFn f)) :
    Function.Bijective (associatedGradedMap f) :=
  (Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff f).mp h

end Stacks.RingTheory.QuasiRegular

end
