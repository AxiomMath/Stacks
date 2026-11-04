module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentConditionSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPolynomialLocus
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFiniteProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional

/-!
# The substack of coherent sheaves with fixed Hilbert polynomial

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `P : ℤ → ℤ`.  The substack `Coh^P_{X/B} = Coh^{P, L}_{X/B} ⊆ Coh_{X/B}` consists
of the objects `(T ⟶ B, 𝓕)` with

`P(n) = χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n})`  for all `n ∈ ℤ` and `t ∈ T`.

It is the special case `I = ℤ`, `E_n = L^{⊗ n}` of Situation 0DNC.  Each function
`t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant on the test schemes (Stacks 0A1Q, 0D1Z), and
the degrees of the numerical polynomials `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are locally bounded
(Stacks 0DN4), so near every point only finitely many of the conditions matter and the condition
is open and closed (Stacks 0DNE).  Hence `Coh^P_{X/B} ⟶ Coh_{X/B}` is representable by open and
closed immersions, `Coh^P_{X/B}` is algebraic whenever `Coh_{X/B}` is, and since every
`n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a numerical polynomial (Stacks 0DN4),

`Coh_{X/B} = ∐_{P numerical polynomial} Coh^P_{X/B}`

is a disjoint union decomposition: on every object `(T, 𝓕)` the loci of the numerical polynomials
are open and closed, pairwise disjoint and cover `T`, and a morphism `(T', 𝓕') ⟶ (T, 𝓕)` has its
source in `Coh^P_{X/B}` exactly when `T' ⟶ T` lands in the locus of `P`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.hilbertPolynomialCFG`: the substack
  `Coh^{P, L}_{X/B}`, and `AlgebraicGeometry.Space.CoherentSituation.hilbertPolynomialι` its
  inclusion into `Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_hilbertPolynomialι_obj_eq_iff`: the objects of
  `Coh_{X/B}` lying in `Coh^{P, L}_{X/B}` are those with `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`.
* `AlgebraicGeometry.Space.CoherentSituation.hilbertPolynomialι_isOpenAndClosedImmersion`: the
  inclusion is representable by algebraic spaces, an open immersion and a closed immersion.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_hilbertPolynomialCFG`:
  `Coh^{P, L}_{X/B}` is an algebraic stack for `f` separated, `Coh_{X/B}` being algebraic
  (Stacks 09DS).
* `AlgebraicGeometry.Space.CoherentSituation.hilbertPolynomialLocus_decomposition`: the disjoint
  union decomposition `Coh_{X/B} = ∐_P Coh^P_{X/B}`, read on each object.

## Implementation notes

The source does not use that `P` is a numerical polynomial for the open and closed substack: for
any `P : ℤ → ℤ` the condition is open and closed (and empty unless `P` is a numerical polynomial),
so the statements here are made for every function `P`.  The disjoint union decomposition is
stated on each object `(T, 𝓕)` of `Coh_{X/B}`: the open and closed subschemes of `T` cut out by the
loci of the numerical polynomials partition `T`, and the locus of `P` is the 2-fibre product
`T ×_{Coh_{X/B}} Coh^P_{X/B}`.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
  (P : ℤ → ℤ)

/-- **The substack `Coh^{P, L}_{X/B}` of coherent sheaves with Hilbert polynomial `P`** with
respect to `L`: the full subcategory of `Coh_{X/B}` of the objects `(T, 𝓕)` with
`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for all `n ∈ ℤ` and `t ∈ T`, a category fibred in groupoids over
the big fppf site of `S`.  The condition is inherited along the morphisms of `Coh_{X/B}`, the
twisted Euler characteristics being constant along them
(`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`). -/
def hilbertPolynomialCFG : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  D.conditionCFG (CoherentObject.HasHilbertPolynomial L P)
    (fun φ h t n => (h (φ.baseScheme t) n).trans (φ.twistedEuler_eq L t n).symm)

/-- **The inclusion `Coh^{P, L}_{X/B} ⟶ Coh_{X/B}`**, a 1-morphism of categories fibred in
groupoids. -/
def hilbertPolynomialι : D.hilbertPolynomialCFG L P ⟶ coherentCFG D :=
  D.conditionι (CoherentObject.HasHilbertPolynomial L P)
    (fun φ h t n => (h (φ.baseScheme t) n).trans (φ.twistedEuler_eq L t n).symm)

/-- An object `(T ⟶ B, 𝓕)` of `Coh_{X/B}` lies in `Coh^P_{X/B} = Coh^{P, L}_{X/B}` (is the image of
an object of it) exactly when `P(n) = χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n})` for every `n ∈ ℤ` and
every `t ∈ T`. -/
@[stacks 0DNF "an object `(T ⟶ B, 𝓕)` of `Coh_{X/B}` lies in `Coh^P_{X/B}` iff
`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for all `n ∈ ℤ` and `t ∈ T`"]
theorem exists_hilbertPolynomialι_obj_eq_iff (A : CoherentObject D) :
    (∃ X, (CatFiberedInGroupoids.homFunctor (D.hilbertPolynomialι L P)).obj X = A) ↔
      ∀ (n : ℤ) (t : A.testScheme), P n = CoherentObject.twistedEuler L A t n :=
  ⟨by rintro ⟨X, rfl⟩ n t; exact X.property t n, fun h => ⟨⟨A, fun t n => h n t⟩, rfl⟩⟩

/-- Every object of `Coh^{P, L}_{X/B}` has Hilbert polynomial `P`. -/
theorem hasHilbertPolynomial_hilbertPolynomialι_obj (X : (D.hilbertPolynomialCFG L P).val.obj) :
    CoherentObject.HasHilbertPolynomial L P
      ((CatFiberedInGroupoids.homFunctor (D.hilbertPolynomialι L P)).obj X) :=
  X.property

/-- `Coh^P_{X/B} ⊆ Coh_{X/B}` is an open and closed substack: the inclusion
`Coh^{P, L}_{X/B} ⟶ Coh_{X/B}` is representable by algebraic spaces, an open immersion and a closed
immersion (Stacks 0DNE for `I = ℤ` and `E_n = L^{⊗ n}`). -/
@[stacks 0DNF "`Coh^P_{X/B} = Coh^{P,L}_{X/B} ⊂ Coh_{X/B}` is an open and closed substack"]
theorem hilbertPolynomialι_isOpenAndClosedImmersion :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.hilbertPolynomialι L P).hom ∧
      Stack.IsOpenImmersion B S hS (D.hilbertPolynomialι L P) ∧
      Stack.IsClosedImmersion B S hS (D.hilbertPolynomialι L P) :=
  conditionι_isOpenAndClosedImmersion
    (fun φ h t n => (h (φ.baseScheme t) n).trans (φ.twistedEuler_eq L t n).symm)
    (isOpenAndClosedCondition_hasHilbertPolynomial L P)

/-- **`Coh^{P, L}_{X/B}` is algebraic when `Coh_{X/B}` is** (Stacks 05UM along the inclusion,
which is representable by algebraic spaces). -/
theorem isAlgebraicStack_hilbertPolynomialCFG_of_isAlgebraicStack
    (hcoh : Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS (D.hilbertPolynomialCFG L P).val :=
  isAlgebraicStack_conditionCFG
    (fun φ h t n => (h (φ.baseScheme t) n).trans (φ.twistedEuler_eq L t n).symm)
    (isOpenAndClosedCondition_hasHilbertPolynomial L P).isFlatClosedCondition hcoh

/-- For a separated morphism `f : X ⟶ B` of finite presentation, `Coh^{P, L}_{X/B}` is an algebraic
stack: `Coh_{X/B}` is algebraic (Stacks 09DS, with Grothendieck's existence theorem Stacks 0CXB),
and the inclusion of `Coh^{P, L}_{X/B}` is representable by algebraic spaces (Stacks 05UM). -/
@[stacks 0DNF "for `f : X ⟶ B` separated and of finite presentation, `Coh^P_{X/B}` is an
algebraic stack"]
theorem isAlgebraicStack_hilbertPolynomialCFG (hsep : IsSeparated B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS (D.hilbertPolynomialCFG L P).val :=
  D.isAlgebraicStack_hilbertPolynomialCFG_of_isAlgebraicStack L P
    (isAlgebraicStack_coherentCFG D hsep)

variable {D} in
/-- The disjoint union decomposition `Coh_{X/B} = ∐_P Coh^P_{X/B}`, read on each object
`A = (T, 𝓕)` of `Coh_{X/B}`: the loci of the functions `P : ℤ → ℤ`
(`AlgebraicGeometry.Space.CoherentObject.hilbertPolynomialLocus`) are open and closed in `T`,
pairwise disjoint, and those of the numerical polynomials cover `T` (Stacks 0DN4); a morphism
`A' ⟶ A` of `Coh_{X/B}` has its source in `Coh^{P, L}_{X/B}` exactly when its map of test schemes
lands in the locus of `P`. -/
@[stacks 0DNF "`Coh_{X/B} = ∐_{P numerical polynomial} Coh^P_{X/B}` is a disjoint union
decomposition, read on each object `(T, 𝓕)`: the loci of the numerical polynomials are open and
closed, pairwise disjoint, cover `T`, and the locus of `P` cuts out `Coh^P_{X/B}`"]
theorem hilbertPolynomialLocus_decomposition (A : CoherentObject D) :
    (∀ P : ℤ → ℤ, IsClopen (A.hilbertPolynomialLocus L P)) ∧
      (⋃ P : {P : ℤ → ℤ // ∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)},
        A.hilbertPolynomialLocus L P.1) = Set.univ ∧
      Pairwise (fun P Q : ℤ → ℤ =>
        Disjoint (A.hilbertPolynomialLocus L P) (A.hilbertPolynomialLocus L Q)) ∧
      ∀ (P : ℤ → ℤ) (A' : CoherentObject D) (φ : CoherentHom A' A),
        CoherentObject.HasHilbertPolynomial L P A' ↔
          Set.range φ.baseScheme ⊆ A.hilbertPolynomialLocus L P := by
  refine ⟨fun P => ?_, A.iUnion_hilbertPolynomialLocus L,
    A.pairwise_disjoint_hilbertPolynomialLocus L, fun P A' φ => ?_⟩
  · exact isClopen_setOf_forall_eq_of_locally_isPolynomialOfDegreeLE
      (fun n => CoherentObject.isLocallyConstant_twistedEuler L A n)
      (fun t => A.exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler L t) P
  · rw [CoherentObject.hasHilbertPolynomial_iff_hilbertPolynomialLocus_eq_univ,
      ← φ.preimage_hilbertPolynomialLocus L P, Set.range_subset_iff, Set.eq_univ_iff_forall]
    rfl

end AlgebraicGeometry.Space.CoherentSituation

end
