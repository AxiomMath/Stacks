module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection

/-!
# The numerical polynomial of the twisted Euler characteristics (Stacks 0DN4)

Let `k` be a field, let `X` be a proper algebraic space over `k`, let `F` be a coherent
`𝒪_X`-module and let `L₁, …, L_r` be invertible `𝒪_X`-modules.  Stacks 0DN4 says that

`(n₁, …, n_r) ↦ χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`

is a numerical polynomial in `n₁, …, n_r` of total degree at most the dimension of the scheme
theoretic support of `F`.

This file writes that statement over the library's own names — the twist
`AlgebraicGeometry.Space.twistedModuleUlift`, the Euler characteristic
`AlgebraicGeometry.Space.eulerCharacteristic` of Stacks 0DN1 and the dimension
`AlgebraicGeometry.Space.dimension` of Stacks 04N6, all of them the spellings that the
intersection number of Stacks 0EDF already uses in
`StacksFrontier/AlgebraicGeometry/Spaces/NumericalIntersection.lean` — and proves the parts of it
that are formal.  The tag is **not** delivered: the dévissage its proof runs is absent from this
library, and the inputs that are missing are named in the implementation notes.  The only
`@[stacks 0DN4 …]` attribute is a keyed one, on the case `r = 0` of no invertible modules.

## Main definitions

* `AlgebraicGeometry.Space.RepresentsTwistedEuler`: a rational polynomial in `r` variables takes
  the twisted Euler characteristics `χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` as its values at
  the integral tuples.  This is the `hP` hypothesis of
  `AlgebraicGeometry.Space.intersectionNumber_eq_coeff`, named.
* `AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE`: there is such a polynomial, of
  total degree at most a given bound.
* `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial`: **Stacks 0DN4 over library
  names**, the above with the bound taken to be the dimension of a closed subspace carrying `F`.
  Nothing proves this, and it carries no attribute.
* `AlgebraicGeometry.Space.HasAdditiveTwistedEuler`: the additivity of the twisted Euler
  characteristics along a short exact sequence, as a named hypothesis.  It packages Stacks 0DN2
  at the twists together with the exactness of the twisted sequences.

## Main results

* `AlgebraicGeometry.Space.eq_of_representsTwistedEuler`: **the polynomial is unique**,
  unconditionally, because a rational polynomial is determined by its values at integral tuples.
  This is what makes "*the* numerical polynomial" of the source a definite description.
* `AlgebraicGeometry.Space.exists_intCast_eq_eval_of_representsTwistedEuler`: a representing
  polynomial is *numerical* in the sense of Stacks 027X on the integral tuples — its values
  there are integers, being Euler characteristics.  This is the "numerical" half of the phrase
  "numerical polynomial" of the source, and it is formal once a representing polynomial is in
  hand; the existence of one is the content of the tag and is not proved here.
* `AlgebraicGeometry.Space.zero_le_dimension`: the dimension of Stacks 04N6 of an algebraic
  space with at least one point is at least `0`.
* `AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_fin_zero`: **Stacks 0DN4 for
  `r = 0`**, the case of no invertible modules, for a closed subspace with a point.
* `AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_fin_zero_iff`: the same case
  decided in both directions — for `r = 0` the conclusion of the tag holds for a bound `d`
  exactly when `0 ≤ d` or `χ(X, F) = 0` — which measures precisely what the hypothesis of the
  previous result costs.
* `AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_middle`, `…_left` and `…_right`:
  **two out of three along a short exact sequence**, granted the additivity of the twisted Euler
  characteristics.  This is condition (1) of the dévissage of Stacks 08AN which the source's
  proof verifies, and it is the one step of that proof which is pure polynomial arithmetic.

## What is and is not proved

**What is not proved, and why.**  The source proves Stacks 0DN4 by reducing to the scheme
theoretic support and then running the dévissage of Stacks 08AN, the base case of which is the
scheme-level statement Stacks 0BEM obtained through a finite cover by a scheme (Stacks 09YC) or
through Chow's lemma (Stacks 089J).  In this library, for
the tags cited by Stacks 0DN4:

* **Stacks 0BEM, the scheme case, is not proved.**  It is stated over library names as
  `Stacks.TwistedSheafEuler.IsEulerNumericalPolynomial`
  (`../TwistedSheafEuler/Basic.lean`), whose module documentation records that the additivity of
  the Euler characteristic in a short exact sequence (Stacks 08AA) and the embedded-points
  reduction (Stacks 02OM, 02OZ, 02P2) are all absent, so its induction cannot be run either.
  No `@[stacks 0BEM]` attribute exists anywhere in the library.
* **The dévissage of Stacks 08AN, the finite cover of Stacks 09YC and Chow's lemma for
  algebraic spaces, Stacks 089J, have no occurrence**, so neither of the two constructions the
  source offers for the irreducible case is available.
* The additivity of `χ` the dévissage is run with is present, as
  `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer` (Stacks 0DN2), but
  only with the finiteness of Stacks 08AS and the vanishing in large degrees of Stacks 072C
  carried as hypotheses.  Stacks 08AS is
  `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper` (`./ProperCohomologyFinite.lean`),
  for modules at the universe of the schemes, whereas `AlgebraicGeometry.Space.cohomologyOverBase`
  is taken at a module universe containing the universe of the small étale site; and
  `Space.exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isQuasiCompactSpace`
  (`./CohomologicalDimension.lean`) is stated for modules at the universe of the schemes as
  well.  So the two facts that make `χ` an integer are not available at the module universe
  used here; see the implementation notes of `./EulerCharacteristic.lean`.

Accordingly `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial` is a statement and not a
theorem, and no attribute is attached to it.

**What is proved.**  The uniqueness and the numericality of a representing polynomial, the case
`r = 0` in both directions, the nonnegativity of the dimension of a space with a point, and the
two-out-of-three property of the conclusion along a short exact sequence granted the additivity
of the twisted Euler characteristics — that is, condition (1) of the dévissage of Stacks 08AN.
What remains is conditions (2) and (3) of that dévissage, the dévissage itself, and the scheme
case Stacks 0BEM; those are the whole geometric content of the tag.

## Implementation notes

**How the scheme theoretic support is expressed.**  There is no scheme theoretic support of a
module on an algebraic space in this library: `AlgebraicGeometry.Scheme.Modules`
`.schemeTheoreticSupport` (`../Morphisms/Support/SchemeTheoretic.lean`) is for schemes only.  The
degree bound is therefore quantified over *every* closed subspace `i : Z ⟶ X` with `F ≅ i_*G`
for a coherent `𝒪_Z`-module `G`.  That is not a weakening: the source's own first step is that
the scheme theoretic support is such a `Z`, so the quantified form specialises to the sharp
bound, while conversely the scheme theoretic support is contained in every such `Z`, whose
dimension is therefore at least its own.  The two forms are equivalent, and the quantified one
is writable here.

**The module universes.**  As in `./NumericalIntersection.lean`, the twist is formed at
`AlgebraicGeometry.Space.Modules.{u, u}`, where the tensor product and the tensor powers of
Stacks 01CU live, and the universe of its sections is raised once by
`AlgebraicGeometry.Space.twistedModuleUlift` immediately before the Euler characteristic is
taken, that being available only at `Modules.{u, max (u + 1) w}`.  Coherence of each twist is an
instance hypothesis here, and for a different reason than in that file: the module `F` being
twisted is arbitrary — not even coherence of `F` itself is assumed, the statements below being
about an arbitrary `𝒪_X`-module — so there is nothing to derive coherence of the twists from.
When `F` is coherent they *are* coherent, by
`AlgebraicGeometry.Space.isCoherent_twistedModuleUlift` of
`StacksFrontier/AlgebraicGeometry/Spaces/TwistedModuleCoherent.lean`, which is what discharges the
same instance for the intersection number of Stacks 0EDF.

**The `r = 0` case and the empty support.**  With no invertible modules the function is the
constant `χ(X, F)`, so a constant polynomial represents it and the bound to be checked is
`0 ≤ dim Z`.  That holds as soon as `Z` has a point
(`AlgebraicGeometry.Space.zero_le_dimension`), and a point of `Z` is exactly what has to be
assumed: a space with no points has dimension `⊥` in `WithBot ℕ∞`, and then the source's bound
forces the representing polynomial to be `0`, hence `χ(X, F) = 0`, which needs an empty scheme
theoretic support to force `F ≅ 0` — a statement this library does not have, exactly as recorded
for the scheme-level `Stacks.TwistedSheafEuler.isEulerNumericalPolynomial_fin_zero`.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 027X](https://stacks.math.columbia.edu/tag/027X)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

/-! ### The dimension of a space with a point -/

/-- **The dimension of Stacks 04N6 of an algebraic space with at least one point is at least
`0`.**  The dimension is the supremum of the dimensions at points, and the dimension at a point
is nonnegative by `AlgebraicGeometry.Space.zero_le_dimensionAtPoint`.  Without a point the
supremum is empty and the dimension is `⊥`. -/
theorem zero_le_dimension (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y) : 0 ≤ dimension B S hS Y hY :=
  (zero_le_dimensionAtPoint B S hS hY y).trans (le_iSup _ y)

/-! ### The twisted Euler characteristics as the values of a polynomial -/

section Twisted

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **A rational polynomial represents the twisted Euler characteristics of `F`**: at every
integral tuple `n` its value is `χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`.

Coherence of each twist is an instance hypothesis, as it is for
`AlgebraicGeometry.Space.eulerCharacteristic`, so no proof term occurs in the statement; `F` is
an arbitrary `𝒪_X`-module here, so there is nothing to derive it from.  This is the hypothesis
`hP` of `AlgebraicGeometry.Space.intersectionNumber_eq_coeff`, named — there the module is
`i_*𝒪_Z` and the instance is discharged. -/
def RepresentsTwistedEuler {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)]
    (P : MvPolynomial (Fin r) ℚ) : Prop :=
  ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
    ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n) : ℤ) : ℚ)

/-- **The twisted Euler characteristics of `F` are the values of a rational polynomial of total
degree at most `d`.**  This is the conclusion of Stacks 0DN4 with the degree bound left as a
parameter; the tag takes `d` to be the dimension of the scheme theoretic support of `F`, which
is `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial`.

The disjunct `P = 0` is the convention that the zero polynomial has degree `⊥`, and it is not a
weakening: without it the statement would be *false* whenever `d = ⊥`, since
`MvPolynomial.totalDegree` is a natural number and its cast is never below `⊥`, whereas the
source's assertion in that case is that the function vanishes identically.  This is the encoding
the scheme-level `Stacks.TwistedSheafEuler.IsEulerNumericalPolynomial` uses for Stacks 0BEM. -/
def HasTwistedEulerPolynomialOfDegreeLE {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)]
    (d : WithBot ℕ∞) : Prop :=
  ∃ P : MvPolynomial (Fin r) ℚ, RepresentsTwistedEuler.{u, w} k B hk X f hf F L P ∧
    (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ d)

/-- **Stacks 0DN4 over library names.**  For every closed subspace `i : Z ⟶ X` carrying `F`,
that is with `F ≅ i_*G` for a coherent `𝒪_Z`-module `G`, the twisted Euler characteristics
`χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` are the values at the integral tuples of a rational
polynomial of total degree at most the dimension of `Z`.

Quantifying over all such `Z` is how the dimension of the *scheme theoretic support* of the
source is expressed, there being no scheme theoretic support of a module on an algebraic space
in this library; the two forms are equivalent, for the reason given in the implementation notes.
The polynomial is automatically numerical, by
`AlgebraicGeometry.Space.exists_intCast_eq_eval_of_representsTwistedEuler`, and unique, by
`AlgebraicGeometry.Space.eq_of_representsTwistedEuler`.

**This is not proved here**, and no Stacks 0DN4 attribute is attached to it; the implementation
notes name every missing input. -/
def IsTwistedEulerNumericalPolynomial {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)] : Prop :=
  ∀ (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X),
    IsClosedImmersion B (Spec (.of k)) hk i.hom →
    ∀ G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2,
      IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G →
      (F ≅ (modulePushforward B (Spec (.of k)) hk i).obj G) →
      HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F L
        (dimension B (Spec (.of k)) hk Z.1 Z.2)

/-! ### Uniqueness and numericality of the representing polynomial -/

section Uniqueness

variable {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)]

/-- **A polynomial representing the twisted Euler characteristics is unique.**  Two rational
polynomials whose values at every integral tuple are `χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` are
equal, because a rational polynomial in finitely many variables is determined by its values at
the integral tuples (`MvPolynomial.eq_of_eval_intCast_eq`).

This is unconditional: the existence of a representing polynomial, which is Stacks 0DN4, is not
assumed.  It is what makes "*the* numerical polynomial" of the source a definite description,
and in particular what makes the intersection number of Stacks 0EDF independent of the
polynomial chosen. -/
theorem eq_of_representsTwistedEuler {P Q : MvPolynomial (Fin r) ℚ}
    (hP : RepresentsTwistedEuler.{u, w} k B hk X f hf F L P)
    (hQ : RepresentsTwistedEuler.{u, w} k B hk X f hf F L Q) : P = Q :=
  MvPolynomial.eq_of_eval_intCast_eq fun n => (hP n).trans (hQ n).symm

/-- **A polynomial representing the twisted Euler characteristics takes integer values at the
integral tuples**, those values being Euler characteristics.  This is the "numerical" half of
the phrase "numerical polynomial in `n₁, …, n_r`" of Stacks 0DN4, in the sense of Stacks 027X;
it is formal once a representing polynomial is in hand, and the existence of one is the content
of the tag and is not proved in this library. -/
theorem exists_intCast_eq_eval_of_representsTwistedEuler {P : MvPolynomial (Fin r) ℚ}
    (hP : RepresentsTwistedEuler.{u, w} k B hk X f hf F L P) (n : Fin r → ℤ) :
    ∃ m : ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P = (m : ℚ) :=
  ⟨_, hP n⟩

/-- **A larger bound on the total degree is a weaker conclusion.** -/
theorem HasTwistedEulerPolynomialOfDegreeLE.mono {d e : WithBot ℕ∞} (hde : d ≤ e)
    (h : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F L d) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F L e :=
  let ⟨P, hP, hdeg⟩ := h
  ⟨P, hP, hdeg.imp id fun h' => h'.trans hde⟩

end Uniqueness

/-! ### Stacks 0DN4 with no invertible modules -/

section FinZero

/-- A rational polynomial in no variables has total degree `0`: the only exponent vector in
`Fin 0 →₀ ℕ` is the empty one, whose sum is `0`. -/
private theorem totalDegree_fin_zero (P : MvPolynomial (Fin 0) ℚ) : P.totalDegree = 0 := by
  refine Nat.le_zero.1 (Finset.sup_le fun i _ => ?_)
  obtain rfl : i = 0 := Finsupp.ext fun j => j.elim0
  simp

variable (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin 0 → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin 0 → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)]

/-- With no invertible modules the twisted Euler characteristics are the constant `χ(X, F)`, so
the constant polynomial of that value represents them. -/
theorem representsTwistedEuler_C_fin_zero :
    RepresentsTwistedEuler.{u, w} k B hk X f hf F L
      (MvPolynomial.C ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L fun _ => 0) : ℤ) : ℚ)) := by
  intro n
  obtain rfl : n = fun _ => 0 := funext fun j => j.elim0
  simp

/-- **The case `r = 0` of Stacks 0DN4, exactly.**  With no invertible modules every polynomial
in sight is a constant, and the only one representing the function is the constant `χ(X, F)`; so
the conclusion of the tag holds for a bound `d` precisely when `0 ≤ d`, that is when the
subspace carrying `F` has a point, or else when `χ(X, F) = 0`, which is the case the `P = 0`
convention of `AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE` covers.

This measures exactly what the hypothesis of
`AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_fin_zero` costs. -/
theorem hasTwistedEulerPolynomialOfDegreeLE_fin_zero_iff (d : WithBot ℕ∞) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F L d ↔
      (0 ≤ d ∨ eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L fun _ => 0) = 0) := by
  constructor
  · rintro ⟨P, hP, hP0 | hdeg⟩
    · refine Or.inr ?_
      have h := hP fun _ => 0
      rw [hP0] at h
      simpa using h.symm
    · exact Or.inl (by simpa [totalDegree_fin_zero P] using hdeg)
  · rintro (h0 | hχ)
    · refine ⟨_, representsTwistedEuler_C_fin_zero.{u, w} k B hk X f hf F L, Or.inr ?_⟩
      rw [MvPolynomial.totalDegree_C]
      simpa using h0
    · refine ⟨_, representsTwistedEuler_C_fin_zero.{u, w} k B hk X f hf F L, Or.inl ?_⟩
      simp [hχ]

/-- **Stacks 0DN4 in the case `r = 0`.**  With no invertible modules to twist by, the function
on `ℤ ^ 0` is the constant `χ(X, F)`, so it is represented by a constant polynomial, whose total
degree is `0`; and `0` is at most the dimension of the closed subspace `Z` carrying `F` as soon
as `Z` has a point, by `AlgebraicGeometry.Space.zero_le_dimension`.  Taking `Z` to be the scheme
theoretic support of `F` gives the source's statement for `r = 0`.

The point of `Z` is the one hypothesis beyond the source's, and it is the empty-support case
that it excludes: a space with no points has dimension `⊥`, the bound then forces the
representing polynomial to be `0`, hence `χ(X, F) = 0`, and that needs an empty scheme theoretic
support to force `F ≅ 0`, which this library does not provide.  The closed immersion `i`, the
module `G` and the isomorphism `F ≅ i_*G` are the source's hypotheses, carried so that the
statement is the one of the tag; the constant polynomial does not use them. -/
@[stacks 0DN4 "the case r = 0 of no invertible modules: the constant function χ(X, F) is
represented by a constant polynomial, of total degree 0, which is at most the dimension of the
closed subspace carrying F whenever that subspace has a point.  The empty-support case, and
every case with invertible modules present, is not proved"]
theorem hasTwistedEulerPolynomialOfDegreeLE_fin_zero
    (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
    (_hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2)
    (_hG : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G)
    (_hF : F ≅ (modulePushforward B (Spec (.of k)) hk i).obj G)
    (z : points B (Spec (.of k)) hk Z.1) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F L
      (dimension B (Spec (.of k)) hk Z.1 Z.2) :=
  (hasTwistedEulerPolynomialOfDegreeLE_fin_zero_iff.{u, w} k B hk X f hf F L _).2
    (Or.inl (zero_le_dimension B (Spec (.of k)) hk Z.2 z))

end FinZero

/-! ### Two out of three along a short exact sequence -/

section Devissage

/-- A total degree bounded by the maximum of two total degrees each at most `d` is at most `d`. -/
private theorem cast_totalDegree_le_of_le_max {r : ℕ} {P Q R : MvPolynomial (Fin r) ℚ}
    {d : WithBot ℕ∞} (h : R.totalDegree ≤ max P.totalDegree Q.totalDegree)
    (hP : (P.totalDegree : WithBot ℕ∞) ≤ d) (hQ : (Q.totalDegree : WithBot ℕ∞) ≤ d) :
    (R.totalDegree : WithBot ℕ∞) ≤ d := by
  rcases le_total P.totalDegree Q.totalDegree with hle | hle
  · rw [max_eq_right hle] at h
    exact le_trans (by exact_mod_cast h) hQ
  · rw [max_eq_left hle] at h
    exact le_trans (by exact_mod_cast h) hP

/-- The bound of `AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE`, in the
convention under which the zero polynomial has degree `⊥`, is stable under addition. -/
private theorem degreeLE_add {r : ℕ} {P Q : MvPolynomial (Fin r) ℚ} {d : WithBot ℕ∞}
    (hP : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ d)
    (hQ : Q = 0 ∨ (Q.totalDegree : WithBot ℕ∞) ≤ d) :
    P + Q = 0 ∨ ((P + Q).totalDegree : WithBot ℕ∞) ≤ d := by
  rcases hP with rfl | hP
  · simpa using hQ
  rcases hQ with rfl | hQ
  · simpa using Or.inr hP
  exact Or.inr (cast_totalDegree_le_of_le_max (MvPolynomial.totalDegree_add P Q) hP hQ)

/-- The same bound is stable under subtraction. -/
private theorem degreeLE_sub {r : ℕ} {P Q : MvPolynomial (Fin r) ℚ} {d : WithBot ℕ∞}
    (hP : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ d)
    (hQ : Q = 0 ∨ (Q.totalDegree : WithBot ℕ∞) ≤ d) :
    P - Q = 0 ∨ ((P - Q).totalDegree : WithBot ℕ∞) ≤ d := by
  rcases hP with rfl | hP
  · rcases hQ with rfl | hQ
    · simp
    · exact Or.inr (by simpa [MvPolynomial.totalDegree_neg] using hQ)
  rcases hQ with rfl | hQ
  · simpa using Or.inr hP
  exact Or.inr (cast_totalDegree_le_of_le_max (MvPolynomial.totalDegree_sub P Q) hP hQ)

variable {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F₁ F₂ F₃ : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₁ L n)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₂ L n)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₃ L n)]
    (d : WithBot ℕ∞)

/-- **Additivity of the twisted Euler characteristics**, as a named hypothesis: at every
integral tuple the Euler characteristic of the middle twist is the sum of the Euler
characteristics of the outer two.

This is Stacks 0DN2, the additivity of `χ` along a short exact sequence, applied to the twists
of a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of coherent modules.  Two inputs are packaged
in it, neither available in this library: Stacks 0DN2 itself holds here only with the finiteness
of Stacks 08AS and the vanishing of Stacks 072C as hypotheses
(`AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer`), and the exactness of
the *twisted* sequences — tensoring with an invertible module is exact — has no counterpart for
modules on an algebraic space here. -/
def HasAdditiveTwistedEuler : Prop :=
  ∀ n : Fin r → ℤ,
    eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₂ L n) =
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₁ L n) +
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F₃ L n)

/-- **Two out of three, the middle term.**  Granted the additivity of the twisted Euler
characteristics, if the outer two modules of a short exact sequence satisfy the conclusion of
Stacks 0DN4 with bound `d` then so does the middle one, the representing polynomial being the
sum of theirs.

This is condition (1) of the dévissage of Stacks 08AN which the source's proof of Stacks 0DN4
verifies.  It cannot be chained into a proof of the tag: the dévissage itself has no occurrence
in this library, and neither does its base case Stacks 0BEM. -/
theorem hasTwistedEulerPolynomialOfDegreeLE_middle
    (hadd : HasAdditiveTwistedEuler.{u, w} k B hk X f hf F₁ F₂ F₃ L)
    (h₁ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₁ L d)
    (h₃ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₃ L d) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₂ L d := by
  obtain ⟨P₁, hP₁, hd₁⟩ := h₁
  obtain ⟨P₃, hP₃, hd₃⟩ := h₃
  refine ⟨P₁ + P₃, fun n => ?_, degreeLE_add hd₁ hd₃⟩
  rw [MvPolynomial.eval_add, hP₁ n, hP₃ n, hadd n]
  push_cast
  ring

/-- **Two out of three, the first outer term.**  Granted the additivity of the twisted Euler
characteristics, if the middle and the third module satisfy the conclusion of Stacks 0DN4 with
bound `d` then so does the first, the representing polynomial being the difference of theirs. -/
theorem hasTwistedEulerPolynomialOfDegreeLE_left
    (hadd : HasAdditiveTwistedEuler.{u, w} k B hk X f hf F₁ F₂ F₃ L)
    (h₂ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₂ L d)
    (h₃ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₃ L d) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₁ L d := by
  obtain ⟨P₂, hP₂, hd₂⟩ := h₂
  obtain ⟨P₃, hP₃, hd₃⟩ := h₃
  refine ⟨P₂ - P₃, fun n => ?_, degreeLE_sub hd₂ hd₃⟩
  rw [MvPolynomial.eval_sub, hP₂ n, hP₃ n, hadd n]
  push_cast
  ring

/-- **Two out of three, the third outer term.**  Granted the additivity of the twisted Euler
characteristics, if the first and the middle module satisfy the conclusion of Stacks 0DN4 with
bound `d` then so does the third, the representing polynomial being the difference of theirs. -/
theorem hasTwistedEulerPolynomialOfDegreeLE_right
    (hadd : HasAdditiveTwistedEuler.{u, w} k B hk X f hf F₁ F₂ F₃ L)
    (h₁ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₁ L d)
    (h₂ : HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₂ L d) :
    HasTwistedEulerPolynomialOfDegreeLE.{u, w} k B hk X f hf F₃ L d := by
  obtain ⟨P₁, hP₁, hd₁⟩ := h₁
  obtain ⟨P₂, hP₂, hd₂⟩ := h₂
  refine ⟨P₂ - P₁, fun n => ?_, degreeLE_sub hd₂ hd₁⟩
  rw [MvPolynomial.eval_sub, hP₂ n, hP₁ n, hadd n]
  push_cast
  ring

end Devissage

end Twisted

end AlgebraicGeometry.Space

end
