module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The residue degree of an affine morphism at a closed point

Let `psi : R ⟶ A` be a map of rings. This file computes the residue degree of
`Spec psi : Spec A ⟶ Spec R` at a point `x` of `Spec A` whose prime is maximal, in the case where
`R` is a field: it is the dimension of `A ⧸ x` as an `R`-vector space.

The application is the affine line over a field. A closed point of `Spec k[T]` is cut out by a
monic irreducible polynomial `p`, and the residue degree of `Spec k[T] ⟶ Spec k` there is the
degree of `p`. That is the local input to the degree computation for a principal divisor on
`ℙ¹_k`: the degree of the divisor of a rational function is a sum over closed points of the
affine line of the order of vanishing weighted by exactly this residue degree.

## Main definitions

* `Stacks.Chow.specEvaluation` — evaluation of a global section of `Spec A` at a point, as a
  bundled ring homomorphism `A →+* κ(x)` rather than through an `Algebra` instance.
* `Stacks.Chow.quotientEquivResidueFieldSpec` — at a maximal point `x` of `Spec A` the residue
  field `κ(x)` is the quotient `A ⧸ x`.

## Main results

* `Stacks.Chow.ker_specEvaluation` and `Stacks.Chow.specEvaluation_surjective` — evaluation at
  `x` has kernel `x` and, when `x` is maximal, is surjective.
* `Stacks.Chow.specEvaluation_naturality` — evaluation commutes with the residue field map of
  `Spec psi`.
* `Stacks.Chow.residueDegree_specMap_of_isField` — **the residue degree of `Spec A ⟶ Spec R` over
  a field `R` at a maximal point `x` is `finrank R (A ⧸ x)`.**
* `Stacks.Chow.residueDegree_specMap_polynomialC` — **on the affine line over a field the residue
  degree at the point of a monic irreducible polynomial is its degree.**

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.residueDegree` is a `Module.finrank` of residue fields of schemes,
for the algebra structure supplied by `AlgebraicGeometry.Scheme.Hom.residueFieldMap`. Transporting
it to a `Module.finrank` of rings is `Algebra.finrank_eq_of_equiv_equiv`, which asks for a ring
equivalence on each of the two levels together with the commuting square between them. This file
therefore builds

* `eK : R ≃+* κ((Spec psi) x)`, which is evaluation itself: it is injective because its kernel is
  the prime of the image point, which is `⊥` as `R` is a field, and surjective because that prime
  is then maximal;
* `eL : A ⧸ x ≃+* κ(x)`, which is evaluation passed to the quotient by its kernel;

and the square is the naturality of global evaluation, `Stacks.Chow.specEvaluation_naturality`.
The same two equivalences appear inline in the proof of
`Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite`, where the base is a one-dimensional local
ring rather than a field and they are built out of localizations.

Both statements take the ring map as a genuine morphism `psi : R ⟶ A` of `CommRingCat` together
with the hypothesis `psi.hom = algebraMap R A`, rather than as
`CommRingCat.ofHom (algebraMap R A)`. The reason is that `CommRingCat.ofHom f` has type
`CommRingCat.of ↑R ⟶ CommRingCat.of ↑A`, which is only definitionally and not syntactically the
type `R ⟶ A`, so rewriting under it fails. This is the same device as
`Stacks.Chow.trdeg_residueField_genericPoint_eq_trdeg`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Evaluation of a global section at a point of an affine scheme -/

/-- Evaluation of a global section of `Spec A` at a point `x`, as a ring map `A →+* κ(x)`.

This is the composite of the identification `A ≅ Γ(Spec A, ⊤)` with the global evaluation map
`AlgebraicGeometry.Scheme.Γevaluation`. -/
def specEvaluation (A : CommRingCat.{u}) (x : Spec A) : ↑A →+* (Spec A).residueField x :=
  ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation x).hom

/-- Evaluation at a point of `Spec A` is the structure map of `Ideal.ResidueField`, read through
the identification `AlgebraicGeometry.Scheme.Spec.residueFieldIso` of the residue field of
`Spec A` at `x` with the residue field of the prime of `x`. -/
theorem ofHom_specEvaluation (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsPrime] :
    CommRingCat.ofHom (specEvaluation A x) =
      CommRingCat.ofHom (algebraMap ↑A x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso A x).inv :=
  (Scheme.Spec.algebraMap_residueFieldIso_inv A x).symm

/-- `Stacks.Chow.ofHom_specEvaluation` as a factorization of ring homomorphisms. -/
theorem specEvaluation_eq_comp (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsPrime] :
    specEvaluation A x =
      (Scheme.Spec.residueFieldIso A x).inv.hom.comp
        (algebraMap ↑A x.asIdeal.ResidueField) :=
  congrArg CommRingCat.Hom.hom (ofHom_specEvaluation A x)

/-- The identification of `κ(x)` with the residue field of the prime of `x` is bijective. -/
theorem bijective_residueFieldIso_inv (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsPrime] :
    Function.Bijective (Scheme.Spec.residueFieldIso A x).inv.hom :=
  ConcreteCategory.bijective_of_isIso (C := CommRingCat) _

/-- A global section of `Spec A` vanishes at `x` exactly when it lies in the prime of `x`. -/
theorem ker_specEvaluation (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsPrime] :
    RingHom.ker (specEvaluation A x) = x.asIdeal := by
  rw [specEvaluation_eq_comp,
    RingHom.ker_comp_of_injective _ (bijective_residueFieldIso_inv A x).injective]
  exact Ideal.ker_algebraMap_residueField _

/-- At a point whose prime is maximal, every element of the residue field is the value of a
global section. -/
theorem specEvaluation_surjective (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsMaximal] :
    Function.Surjective (specEvaluation A x) := by
  rw [specEvaluation_eq_comp]
  exact (bijective_residueFieldIso_inv A x).surjective.comp
    (Ideal.algebraMap_residueField_surjective x.asIdeal)

/-- **Evaluation is natural.** The value at `x` of the image of a global section of `Spec R` under
`psi` is the image under the residue field map of `Spec psi` of its value at `(Spec psi) x`. -/
theorem specEvaluation_naturality {R A : CommRingCat.{u}} (psi : R ⟶ A) (x : Spec A) (r : ↑R) :
    ((Spec.map psi).residueFieldMap x).hom (specEvaluation R ((Spec.map psi).base x) r) =
      specEvaluation A x (psi.hom r) := by
  have h : ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map psi).base x)) ≫
        (Spec.map psi).residueFieldMap x =
      psi ≫ ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation x) := by
    rw [Category.assoc, Scheme.Γevaluation_naturality, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) r

/-- **The residue field at a maximal point of `Spec A` is the quotient of `A` by its prime.**
Evaluation at `x` is surjective with kernel `x`. -/
def quotientEquivResidueFieldSpec (A : CommRingCat.{u}) (x : Spec A) [x.asIdeal.IsMaximal] :
    (↑A ⧸ x.asIdeal) ≃+* (Spec A).residueField x :=
  (Ideal.quotEquivOfEq (ker_specEvaluation A x).symm).trans
    (RingHom.quotientKerEquivOfSurjective (specEvaluation_surjective A x))

/-- `Stacks.Chow.quotientEquivResidueFieldSpec` sends the class of `a` in `A ⧸ x` to the value of
`a` at `x`. -/
@[simp]
theorem quotientEquivResidueFieldSpec_mk (A : CommRingCat.{u}) (x : Spec A)
    [x.asIdeal.IsMaximal] (a : ↑A) :
    quotientEquivResidueFieldSpec A x (Ideal.Quotient.mk x.asIdeal a) = specEvaluation A x a := by
  show (RingHom.quotientKerEquivOfSurjective (specEvaluation_surjective A x))
      (Ideal.quotEquivOfEq (ker_specEvaluation A x).symm (Ideal.Quotient.mk x.asIdeal a))
    = specEvaluation A x a
  rw [Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk (specEvaluation_surjective A x) a]

/-! ### The residue degree over a field -/

/-- **The residue degree of `Spec A ⟶ Spec R` at a closed point.** For `R` a field and
`psi : R ⟶ A` a ring map, the degree of the residue-field extension at a maximal point `x` of
`Spec A` is the `R`-dimension of the quotient `A ⧸ x`. -/
theorem residueDegree_specMap_of_isField {R A : CommRingCat.{u}} [Algebra ↑R ↑A]
    (psi : R ⟶ A) (hpsi : psi.hom = algebraMap ↑R ↑A) (hR : IsField ↑R)
    (x : Spec A) (hx : x.asIdeal.IsMaximal) :
    (Spec.map psi).residueDegree x = Module.finrank ↑R (↑A ⧸ x.asIdeal) := by
  have _ := hx
  let _ := hR.toField
  set y := (Spec.map psi).base x
  have _ := y.isPrime
  have hybot : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime y.asIdeal
  have hymax : y.asIdeal.IsMaximal := hybot ▸ Ideal.bot_isMaximal
  let eK : ↑R ≃+* (Spec R).residueField y :=
    RingEquiv.ofBijective (specEvaluation R y)
      ⟨(RingHom.injective_iff_ker_eq_bot _).mpr (by rw [ker_specEvaluation, hybot]),
        specEvaluation_surjective R y⟩
  let eL : (↑A ⧸ x.asIdeal) ≃+* (Spec A).residueField x := quotientEquivResidueFieldSpec A x
  let _ : Algebra ((Spec R).residueField y) ((Spec A).residueField x) :=
    ((Spec.map psi).residueFieldMap x).hom.toAlgebra
  have hcompat : (algebraMap ((Spec R).residueField y) ((Spec A).residueField x)).comp
      eK.toRingHom = eL.toRingHom.comp (algebraMap ↑R (↑A ⧸ x.asIdeal)) := by
    refine RingHom.ext fun r => ?_
    show ((Spec.map psi).residueFieldMap x).hom (specEvaluation R y r) =
      quotientEquivResidueFieldSpec A x (Ideal.Quotient.mk x.asIdeal (algebraMap ↑R ↑A r))
    rw [quotientEquivResidueFieldSpec_mk, ← hpsi]
    exact specEvaluation_naturality psi x r
  simpa only [Scheme.Hom.residueDegree] using
    (Algebra.finrank_eq_of_equiv_equiv eK eL hcompat).symm

/-- **The residue degree of the affine line over a field at a closed point** is the degree of the
monic irreducible polynomial cutting that point out. -/
theorem residueDegree_specMap_polynomialC (k : Type u) [Field k] {p : Polynomial k}
    (hp : Irreducible p) (hpm : p.Monic) (x : Spec (CommRingCat.of (Polynomial k)))
    (hx : x.asIdeal = Ideal.span {p}) :
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))).residueDegree x
      = p.natDegree := by
  have hmax : x.asIdeal.IsMaximal := hx ▸ PrincipalIdealRing.isMaximal_of_irreducible hp
  rw [residueDegree_specMap_of_isField (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    Polynomial.algebraMap_eq.symm (Field.toIsField k) x hmax, hx]
  exact ((AdjoinRoot.powerBasis' hpm).finrank).trans (AdjoinRoot.powerBasis'_dim hpm)

end Stacks.Chow

end
