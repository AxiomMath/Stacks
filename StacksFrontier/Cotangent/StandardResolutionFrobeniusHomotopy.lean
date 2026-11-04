module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialSet.KanFibration
public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality

/-!
# Frobenius on the standard resolution in positive characteristic

Let `p` be a prime with `p = 0` in `A`, and let `B` be an `A`-algebra. The Frobenius maps
`F_A : A → A` and `F_B : B → B` form a commutative square of ring maps, so they induce an
endomorphism of the standard resolution `P_•` of `B` over `A`. That endomorphism is homotopic
to the endomorphism given by the Frobenius of each term `P_n`.

## Main definitions

* `CommAlgCat.frobeniusHom` is the Frobenius ring endomorphism of a commutative semiring in
  which the prime `p` vanishes.
* `CommAlgCat.frobeniusSquare` is the commutative square `(F_A, F_B)` of ring maps.
* `CommAlgCat.resolutionRing` is the standard resolution viewed as a simplicial commutative ring.
* `CommAlgCat.squareEndo` is the endomorphism of `P_•` induced by `frobeniusSquare`, and
  `CommAlgCat.frobeniusEndo` is the endomorphism given by Frobenius on each term.

## Main results

* `CommAlgCat.nonempty_homotopy_frobeniusEndo_squareEndo` is the asserted homotopy.
* `CommAlgCat.exists_frobeniusHomotopyCylinder` repackages the same construction as
  `CommAlgCat.FrobeniusHomotopyCylinder`, the family of ring endomorphisms of the terms of `P_•`
  indexed by the simplices of the interval, together with the compatibilities — semilinearity over
  the Frobenius of `A` and multiplicativity of degree `p` on the augmentation — that a map of
  cotangent complexes needs in order to be induced by such a family.

## Implementation notes

Neither of the two compared endomorphisms is a map of `A`-algebras, since `F_B` is semilinear
over `F_A` rather than `A`-linear; both are maps of simplicial *rings*, which is why
`resolutionRing` forgets the `A`-algebra structure along `forget₂ (CommAlgCat A) CommRingCat`.
The square-induced map is the one of Section 08QL, supplied by
`CommAlgCat.squareFunctoriality`.

`frobeniusHom` is Mathlib's `frobenius` with the `ExpChar` typeclass replaced by the source's
hypothesis `(p : R) = 0`; the two agree whenever both apply, and the weaker hypothesis also
covers the zero ring, which `ExpChar R p` excludes for prime `p`.

Simplicial, Lemma 0G5S (`CategoryTheory.Godement.exists_homotopy_whiskerLeft_whiskerRight`)
gives the homotopy the source's proof appeals to, but it lives in the category of endofunctors of
the category of `F_p`-algebra maps, in which Frobenius is an endomorphism of the identity functor;
reaching it would require that category to be built. The homotopy here is constructed directly
instead, and runs from the termwise Frobenius to the square-induced map.

The homotopy is built by induction on the relative skeleta of the simplicial cylinder
`P_• × Δ[1]` over its two end faces. A cell of the cylinder is a pair `(x, t)` with
`t : ⦋n⦌ ⟶ ⦋1⦌`, and the homotopy is a ring map `P_n → P_n` for each `t`, extending the already
chosen maps on the boundary. The extension exists because `P_n` is a polynomial algebra over `A`,
so a ring map out of it compatible with `A → P_n` may be prescribed freely on the variables; and
the prescribed boundary values are compatible because the augmented standard resolution satisfies
the horn-filling condition in every degree, which here is supplied by
`SimplicialObject.fibration_whiskerRight_forget_of_surjective` together with an explicit filler
built from one extra variable.

## References

* [Stacks Project, Tag 0G5Y](https://stacks.math.columbia.edu/tag/0G5Y)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CommAlgCat

/-- The Frobenius endomorphism `x ↦ x ^ p` of a commutative semiring in which the prime `p`
vanishes. -/
public def frobeniusHom {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.pos.ne'
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, hR]
    ring

/-- Frobenius is the `p`-th power map. -/
@[simp]
public theorem frobeniusHom_apply {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) (x : R) : frobeniusHom hp hR x = x ^ p := rfl

/-- If the prime `p` vanishes in the base ring, it vanishes in every algebra over it. -/
public theorem natCast_eq_zero_of_algebra {p : ℕ} {A : Type*} [CommRing A] (R : Type*)
    [CommRing R] [Algebra A R] (hA : (p : A) = 0) : (p : R) = 0 := by
  rw [← map_natCast (algebraMap A R) p, hA, map_zero]

variable (p : ℕ)

/-- The commutative square of ring maps given by the Frobenius endomorphisms of `A` and of `B`.
This is the square of Section 08QL whose induced map on cotangent complexes the source
studies. -/
public def frobeniusSquare (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    AlgebraSquare.{u, v, u} A A B B where
  base := frobeniusHom hp hA
  map := frobeniusHom hp (natCast_eq_zero_of_algebra (p := p) B hA)
  map_algebraMap a := by
    change (algebraMap A B a) ^ p = algebraMap A B (a ^ p)
    rw [map_pow]

/-- The standard resolution of `B` over `A`, viewed as a simplicial commutative ring. The two
endomorphisms compared by the source are ring maps but not `A`-algebra maps, so this is the
category in which they live. -/
public noncomputable def resolutionRing (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : SimplicialObject CommRingCat.{max u v} :=
  (standardResolution.{u, max u v} A B).left ⋙
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}

/-- The endomorphism of the standard resolution given by the Frobenius of each term `P_n`. -/
public noncomputable def frobeniusEndo (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    resolutionRing.{u, v} A B ⟶ resolutionRing.{u, v} A B where
  app n := CommRingCat.ofHom (frobeniusHom hp
    (natCast_eq_zero_of_algebra (p := p)
      ((standardResolution.{u, max u v} A B).left.obj n) hA))
  naturality {i j} f := by
    ext x
    exact (map_pow ((standardResolution.{u, max u v} A B).left.map f).hom x p).symm

/-- The endomorphism of the standard resolution induced by the square of Frobenius maps, i.e.
the map `P_• → P_•` of Section 08QL attached to `frobeniusSquare`. -/
public noncomputable def squareEndo (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    resolutionRing.{u, v} A B ⟶ resolutionRing.{u, v} A B where
  app n := CommRingCat.ofHom
    ((squareFunctoriality (frobeniusSquare.{u, v} p hp A B hA)).resolution n)
  naturality {i j} f := by
    ext x
    exact (squareFunctoriality
      (frobeniusSquare.{u, v} p hp A B hA)).resolution_naturality f x

/-- The degree-`n + 1` term of the standard resolution, with the right-hand side of
`CommAlgCat.standardResolution_obj_succ` written as the polynomial comonad applied to the
degree-`n` term. This is the form which composes with `polynomialComonad.map` without the
composite having to be retyped. -/
private theorem standardResolution_obj_succ_comonad (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌) =
      (polynomialComonad.{u, v} A).obj ((standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) :=
  standardResolution_obj_succ.{u, v} A B n

/-- The degree-zero term of the standard resolution, with the right-hand side of
`CommAlgCat.standardResolution_zero` written as the polynomial comonad applied to `B`. -/
private theorem standardResolution_zero_comonad (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution.{u, v} A B).left.obj (op ⦋0⦌) = (polynomialComonad.{u, v} A).obj B :=
  standardResolution_zero.{u, v} A B

/-- Polynomial evaluation at the identity deletes a variable: `[q] ↦ q`. The two presentations of
the algebra as a polynomial algebra are supplied as equations, so that the statement applies to
the terms of the standard resolution, where they hold only propositionally. -/
private theorem polynomial_evaluation_X_of_eq (A : Type u) [CommRing A]
    (P Q R : CommAlgCat.{max u v} A)
    (hP : P = CommAlgCat.of A (MvPolynomial Q A)) (hQ : Q = R)
    (hP' : P = CommAlgCat.of A (MvPolynomial R A)) (q : Q) :
    (eqToHom hP' ≫ CommAlgCat.ofHom (MvPolynomial.aeval (id : R → R)) ≫
        eqToHom hQ.symm).hom
      ((CommAlgCat.algEquivOfIso (eqToIso hP)).symm (MvPolynomial.X q)) = q := by
  subst R P
  simp [CommAlgCat.algEquivOfIso]

/-- The zeroth face of the standard resolution deletes the outermost bracket: `d^n_0 [q] = q`. -/
private theorem standardResolution_δ_zero_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ)
    (q : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.δ (0 : Fin (n + 2))
      (standardResolutionX A B n q) = q := by
  rw [standardResolution_face, Godement.Prep.face_zero]
  exact polynomial_evaluation_X_of_eq A _ _ _
    (standardResolution_obj_succ A B n)
    (standardResolution_obj A B n)
    (standardResolution_obj A B (n + 1)) q

/-- Every face of the standard resolution other than the zeroth is the polynomial comonad applied
to a face one degree down. -/
private theorem standardResolution_δ_succ (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 2)) :
    (standardResolution A B).left.δ i.succ =
      eqToHom (standardResolution_obj_succ_comonad A B (n + 1)) ≫
        (polynomialComonad A).toFunctor.map
          ((standardResolution A B).left.δ i) ≫
        eqToHom (standardResolution_obj_succ_comonad A B n).symm := by
  rw [standardResolution_face, Godement.Prep.face_succ,
    standardResolution_face, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- The polynomial comonad applied to `f` renames variables: `[r] ↦ [f r]`. As in
`polynomial_evaluation_X_of_eq`, the two presentations are supplied as equations. -/
private theorem polynomial_map_X_of_eq (A : Type u) [CommRing A]
    (P Q R S : CommAlgCat.{max u v} A)
    (hP : P = (polynomialComonad A).obj R)
    (hQ : Q = (polynomialComonad A).obj S) (f : R ⟶ S) (r : R) :
    (eqToHom hP ≫ (polynomialComonad A).toFunctor.map f ≫
        eqToHom hQ.symm).hom
      ((CommAlgCat.algEquivOfIso (eqToIso hP)).symm (MvPolynomial.X r)) =
      (CommAlgCat.algEquivOfIso (eqToIso hQ)).symm (MvPolynomial.X (f r)) := by
  subst P Q
  show MvPolynomial.rename f.hom (MvPolynomial.X r) = MvPolynomial.X (f r)
  exact MvPolynomial.rename_X _ _

/-- Every face other than the zeroth takes variables to variables:
`d^{n+1}_{i+1} [q] = [d^n_i q]`. -/
private theorem standardResolution_δ_succ_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 2))
    (q : (standardResolution A B).left.obj (op ⦋n + 1⦌)) :
    (standardResolution A B).left.δ i.succ
      (standardResolutionX A B (n + 1) q) =
      standardResolutionX A B n
        ((standardResolution A B).left.δ i q) := by
  rw [standardResolution_δ_succ]
  exact polynomial_map_X_of_eq A _ _ _ _
    (standardResolution_obj_succ_comonad A B (n + 1))
    (standardResolution_obj_succ_comonad A B n) _ q

/-- Every degeneracy of the standard resolution other than the zeroth is the polynomial comonad
applied to a degeneracy one degree down. -/
private theorem standardResolution_σ_succ (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 1)) :
    (standardResolution A B).left.σ i.succ =
      eqToHom (standardResolution_obj_succ_comonad A B n) ≫
        (polynomialComonad A).toFunctor.map
          ((standardResolution A B).left.σ i) ≫
        eqToHom (standardResolution_obj_succ_comonad A B (n + 1)).symm := by
  rw [standardResolution_degeneracy, Godement.Prep.degeneracy_succ,
    standardResolution_degeneracy, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- Every degeneracy other than the zeroth takes variables to variables:
`s^{n+1}_{i+1} [q] = [s^n_i q]`. -/
private theorem standardResolution_σ_succ_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 1))
    (q : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.σ i.succ
      (standardResolutionX A B n q) =
      standardResolutionX A B (n + 1)
        ((standardResolution A B).left.σ i q) := by
  rw [standardResolution_σ_succ]
  exact polynomial_map_X_of_eq A _ _ _ _
    (standardResolution_obj_succ_comonad A B n)
    (standardResolution_obj_succ_comonad A B (n + 1)) _ q

/-- The face `d^0_1 : P_1 → P_0` is the polynomial comonad applied to the augmentation. -/
private theorem standardResolution_δ_one (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.δ (1 : Fin 2) =
      eqToHom (standardResolution_obj_succ_comonad A B 0) ≫
        (polynomialComonad A).toFunctor.map
          ((standardResolution A B).hom.app (op ⦋0⦌)) ≫
        eqToHom (standardResolution_zero_comonad A B).symm := by
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    standardResolution_face]
  rw [Godement.Prep.face_succ,
    Godement.Prep.face_zero, standardResolution_augmentation,
    Functor.map_comp, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

/-- The face `d^0_1` takes a variable to the variable indexed by the augmentation of its index:
`d^0_1 [q] = [ε q]`. -/
private theorem standardResolution_δ_one_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A)
    (q : (standardResolution A B).left.obj (op ⦋0⦌)) :
    (standardResolution A B).left.δ (1 : Fin 2)
      (standardResolutionX A B 0 q) =
      (standardResolutionZeroAlgEquiv A B).symm
        (MvPolynomial.X (standardResolutionAugmentationHom A B (op ⦋0⦌) q)) := by
  rw [standardResolution_δ_one]
  exact polynomial_map_X_of_eq A _ _ _ _
    (standardResolution_obj_succ_comonad A B 0)
    (standardResolution_zero_comonad A B) _ q

/-- Two elements of `P_0` with the same augmentation are the two faces of a single element of
`P_1`: the one-dimensional case of horn filling, proved directly from the extra variable. -/
private theorem standardResolution_edge_filler (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A)
    (x₀ x₁ : (standardResolution A B).left.obj (op ⦋0⦌))
    (hx : standardResolutionAugmentationHom A B (op ⦋0⦌) x₀ =
      standardResolutionAugmentationHom A B (op ⦋0⦌) x₁) :
    ∃ y : (standardResolution A B).left.obj (op ⦋1⦌),
      (standardResolution A B).left.δ 0 y = x₀ ∧
      (standardResolution A B).left.δ 1 y = x₁ := by
  let P := (standardResolution A B).left
  refine ⟨(standardResolution A B).left.σ (0 : Fin 1) x₁ +
    standardResolutionX A B 0 (x₀ - x₁) -
    standardResolutionX A B 0 0, ?_, ?_⟩
  · show (P.δ (0 : Fin 2)).hom (_ + _ - _) = x₀
    rw [map_sub, map_add, standardResolution_δ_zero_X, standardResolution_δ_zero_X]
    have hs := congrArg (fun f : P.obj (op ⦋0⦌) ⟶ P.obj (op ⦋0⦌) => f.hom x₁)
      (P.δ_comp_σ_self (i := (0 : Fin 1)))
    change P.δ 0 (P.σ 0 x₁) = x₁ at hs
    rw [hs]
    abel
  · show (P.δ (1 : Fin 2)).hom (_ + _ - _) = x₁
    rw [map_sub, map_add, standardResolution_δ_one_X, standardResolution_δ_one_X,
      map_sub, hx, sub_self, map_zero]
    have hs := congrArg (fun f : P.obj (op ⦋0⦌) ⟶ P.obj (op ⦋0⦌) => f.hom x₁)
      (P.δ_comp_σ_succ (i := (0 : Fin 1)))
    change P.δ 1 (P.σ 0 x₁) = x₁ at hs
    rw [hs]
    abel

/-- The extra variable, with its value at zero subtracted, fills a normalized cycle. -/
private theorem standardResolution_cycle_filler (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ)
    (q : (standardResolution A B).left.obj (op ⦋n + 1⦌))
    (hq : ∀ i : Fin (n + 2), (standardResolution A B).left.δ i q = 0) :
    ∃ r : (standardResolution A B).left.obj (op ⦋n + 2⦌),
      (standardResolution A B).left.δ (0 : Fin (n + 3)) r = q ∧
      ∀ i : Fin (n + 2), (standardResolution A B).left.δ i.succ r = 0 := by
  refine ⟨standardResolutionX A B (n + 1) q -
    standardResolutionX A B (n + 1) 0, ?_, ?_⟩
  · show ((standardResolution A B).left.δ (0 : Fin (n + 3))).hom
      (_ - _) = q
    rw [map_sub, standardResolution_δ_zero_X, standardResolution_δ_zero_X, sub_zero]
  · intro i
    show ((standardResolution A B).left.δ i.succ).hom (_ - _) = 0
    rw [map_sub, standardResolution_δ_succ_X, standardResolution_δ_succ_X, hq i,
      map_zero, sub_self]

open SSet.modelCategoryQuillen in
/-- Horn filling in a simplicial commutative ring: a family of `(n + 1)`-simplices indexed by the
vertices other than the zeroth, compatible under the faces, extends over the missing face. The
underlying simplicial abelian group is a Kan complex because the map to the point is surjective in
every degree. -/
private theorem exists_horn_filler_commRing (P : SimplicialObject CommRingCat.{v}) (n : ℕ)
    (x : Fin (n + 3) → P.obj (op ⦋n + 1⦌))
    (hx : ∀ (j k : Fin (n + 3)) (hjk : j < k),
      P.δ (k.pred (Fin.ne_zero_of_lt hjk)) (x j) =
        P.δ (j.castPred (Fin.ne_last_of_lt hjk)) (x k)) :
    ∃ y : P.obj (op ⦋n + 2⦌), ∀ i : Fin (n + 2), P.δ i.succ y = x i.succ := by
  let W := forget₂ CommRingCat.{v} RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
    forget₂ AddCommGrpCat AddGrpCat
  let Z : SimplicialObject AddGrpCat.{v} := P ⋙ W
  let Y := (SimplicialObject.const AddGrpCat.{v}).obj (AddGrpCat.of (PUnit : Type v))
  let f : Z ⟶ Y :=
    { app := fun _ => AddGrpCat.ofHom 0
      naturality := by intros; ext; rfl }
  have hf : ∀ k, Function.Surjective (f.app k).hom := by
    intro k y
    refine ⟨0, ?_⟩
    show (PUnit.unit : PUnit) = _
    exact Subsingleton.elim _ _
  have hfib : HomotopicalAlgebra.Fibration (Functor.whiskerRight f (forget AddGrpCat)) :=
    SimplicialObject.fibration_whiskerRight_forget_of_surjective f hf
  have hc : SSet.horn.IsCompatible (i := (0 : Fin (n + 3)))
      (fun j _ => (SimplicialObject.yonedaEquivObj Z (n + 1)).symm (x j)) := by
    rw [SSet.horn.isCompatible_iff]
    intro j k _ _ hjk
    apply (SimplicialObject.yonedaEquivObj Z n).injective
    simp only [← SimplicialObject.δ_yonedaEquivObj, Equiv.apply_symm_apply]
    show (P.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom (x j) =
      (P.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom (x k)
    exact hx j k hjk
  obtain ⟨g, hg, _⟩ := hc.exists_lift (Functor.whiskerRight f (forget AddGrpCat))
    ((SimplicialObject.yonedaEquivObj Y (n + 2)).symm 0) (by
      intro j hj
      ext k y
      show (PUnit.unit : PUnit) = _
      exact Subsingleton.elim _ _)
  refine ⟨SimplicialObject.yonedaEquivObj Z (n + 2) g, fun i => ?_⟩
  show (Z.δ i.succ).hom (SimplicialObject.yonedaEquivObj Z (n + 2) g) = _
  rw [SimplicialObject.δ_yonedaEquivObj, hg i.succ (Fin.succ_ne_zero i),
    Equiv.apply_symm_apply]

/-- Boundary filling in the standard resolution: a compatible family of all `n + 3` faces is the
boundary of an `(n + 2)`-simplex. The horn is filled first, then the remaining discrepancy in the
zeroth face is a cycle, which the extra variable fills. -/
private theorem standardResolution_boundary_filler (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ)
    (x : Fin (n + 3) → (resolutionRing A B).obj (op ⦋n + 1⦌))
    (hx : ∀ (j k : Fin (n + 3)) (hjk : j < k),
      (resolutionRing A B).δ (k.pred (Fin.ne_zero_of_lt hjk)) (x j) =
        (resolutionRing A B).δ (j.castPred (Fin.ne_last_of_lt hjk)) (x k)) :
    ∃ y : (resolutionRing A B).obj (op ⦋n + 2⦌),
      ∀ i : Fin (n + 3), (resolutionRing A B).δ i y = x i := by
  let P := resolutionRing A B
  obtain ⟨y, hy⟩ := exists_horn_filler_commRing P n x hx
  have hq : ∀ i : Fin (n + 2), P.δ i (x 0 - P.δ 0 y) = 0 := by
    intro i
    show (P.δ i).hom (_ - _) = 0
    rw [map_sub]
    have hi := hx 0 i.succ (Fin.succ_pos i)
    simp only [Fin.pred_succ, Fin.castPred_zero] at hi
    rw [hi]
    have hh := congrArg (fun t : P.obj (op ⦋n + 2⦌) ⟶ P.obj (op ⦋n⦌) => t.hom y)
      (P.δ_comp_δ (i := (0 : Fin (n + 2))) (j := i) (Fin.zero_le i))
    change P.δ 0 (P.δ i.succ y) = P.δ i (P.δ 0 y) at hh
    rw [← hh, hy, sub_self]
  obtain ⟨q, hq₀, hqδ⟩ := standardResolution_cycle_filler A B n (x 0 - P.δ 0 y) hq
  change P.obj (op ⦋n + 2⦌) at q
  change P.δ (0 : Fin (n + 3)) q = x 0 - P.δ 0 y at hq₀
  change ∀ i : Fin (n + 2), P.δ i.succ q = 0 at hqδ
  refine ⟨y + q, fun i => ?_⟩
  cases i using Fin.cases with
  | zero =>
      show (P.δ 0).hom (_ + _) = _
      rw [map_add, hq₀]
      abel
  | succ i =>
      show (P.δ i.succ).hom (_ + _) = _
      rw [map_add, hy i, hqδ i, add_zero]

/-- The index set of the polynomial presentation of `P_n`: the `n`-fold iterate of `C ↦ A[C]`
applied to `B`. -/
private noncomputable abbrev resolutionVariables (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :=
  ((polynomialComonad.{u, max u v} A).toFunctor.iterate n).obj B

/-- The presentation of `P_n` as the polynomial algebra on `resolutionVariables A B n`. -/
private noncomputable abbrev resolutionPolynomialEquiv (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) ≃ₐ[A]
      MvPolynomial (resolutionVariables A B n) A :=
  CommAlgCat.algEquivOfIso (eqToIso (standardResolution_obj A B n))

/-- The variable of `P_n` indexed by an element of `resolutionVariables A B n`. -/
private noncomputable def resolutionVariable (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (x : resolutionVariables A B n) :
    (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) :=
  (resolutionPolynomialEquiv A B n).symm (MvPolynomial.X x)

/-- Godement's degeneracies take a polynomial variable to a polynomial variable. -/
private theorem polynomial_degeneracy_mem_range_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 1))
    (x : resolutionVariables A B n) :
    ((Godement.degeneracy (polynomialComonad A).δ n i).app B).hom
      (MvPolynomial.X x) ∈ Set.range
        (MvPolynomial.X : resolutionVariables A B (n + 1) →
          MvPolynomial (resolutionVariables A B (n + 1)) A) := by
  cases i using Fin.cases with
  | zero =>
      rw [Godement.Prep.degeneracy_zero]
      exact ⟨MvPolynomial.X x, (MvPolynomial.rename_X _ _).symm⟩
  | succ i =>
      cases n with
      | zero => exact i.elim0
      | succ n =>
          rw [Godement.Prep.degeneracy_succ]
          exact ⟨((Godement.degeneracy (polynomialComonad A).δ n i).app B).hom x,
            (MvPolynomial.rename_X _ _).symm⟩

/-- Every degeneracy of the standard resolution takes a variable of `P_n` to a variable of
`P_{n+1}`. -/
private theorem resolutionVariable_degeneracy (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (i : Fin (n + 1))
    (x : resolutionVariables A B n) :
    ∃ y : resolutionVariables A B (n + 1),
      (standardResolution.{u, max u v} A B).left.σ i (resolutionVariable A B n x) =
        resolutionVariable A B (n + 1) y := by
  obtain ⟨y, hy⟩ := polynomial_degeneracy_mem_range_X A B n i x
  refine ⟨y, ?_⟩
  rw [standardResolution_degeneracy]
  show ((CommAlgCat.algEquivOfIso
      (eqToIso (standardResolution_obj A B (n + 1)))).symm)
      (((Godement.degeneracy (polynomialComonad A).δ n i).app B).hom
        ((resolutionPolynomialEquiv A B n) (resolutionVariable A B n x))) = _
  simp only [resolutionVariable, AlgEquiv.apply_symm_apply, ← hy]
  rfl

/-- Every surjection of the simplex category acts on the standard resolution by taking variables to
variables, since it is a composite of degeneracies. -/
private theorem resolutionVariable_map_epi (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : resolutionVariables A B m) :
    ∃ y : resolutionVariables A B n,
      (standardResolution.{u, max u v} A B).left.map f.op (resolutionVariable A B m x) =
        resolutionVariable A B n y := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero (SimplexCategory.len_le_of_epi f)
      subst m
      rw [SimplexCategory.eq_id_of_epi f]
      exact ⟨x, by simp⟩
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        rw [SimplexCategory.eq_id_of_epi f]
        exact ⟨x, by simp⟩
      · have hn : ¬ Function.Injective f.toOrderHom := by
          intro hf
          have : Mono f := SimplexCategory.mono_iff_injective.mpr hf
          have hnm : n + 1 ≤ m := SimplexCategory.len_le_of_mono f
          have hmn : m ≤ n + 1 := SimplexCategory.len_le_of_epi f
          omega
        obtain ⟨i, g, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hn
        have : Epi g := epi_of_epi (SimplexCategory.σ i) g
        obtain ⟨z, hz⟩ := ih g x
        obtain ⟨y, hy⟩ := resolutionVariable_degeneracy A B n i z
        refine ⟨y, ?_⟩
        simp only [op_comp, Functor.map_comp, CommAlgCat.comp_apply, hz]
        exact hy

/-- The cylinder of a simplicial algebra, displayed using ordinal maps for the
simplices of the interval. -/
private def algebraCylinder (A : Type u) [CommRing A]
    (P : SimplicialObject (CommAlgCat.{v} A)) : SSet.{v} where
  obj n := P.obj n × (n.unop ⟶ ⦋1⦌)
  map f := ↾fun x => (P.map f x.1, f.unop ≫ x.2)
  map_id n := by ext x <;> simp
  map_comp f g := by ext x <;> simp [Category.assoc]

/-- The boundary of the cylinder: the simplices whose interval coordinate is one of the two
constants, that is, the two end faces. -/
private def algebraCylinderBoundary (A : Type u) [CommRing A]
    (P : SimplicialObject (CommAlgCat.{v} A)) : (algebraCylinder A P).Subcomplex where
  obj n := {x | ∃ b : Fin 2, x.2 = SimplexCategory.const n.unop ⦋1⦌ b}
  map := by
    intro n m f x hx
    obtain ⟨b, hb⟩ := hx
    refine ⟨b, ?_⟩
    change f.unop ≫ x.2 = SimplexCategory.const m.unop ⦋1⦌ b
    rw [hb]
    ext j
    rfl

/-- The cylinder on the standard resolution of `B` over `A`. -/
private noncomputable abbrev resolutionCylinder (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :=
  algebraCylinder A (standardResolution.{u, max u v} A B).left

/-- The boundary of the cylinder on the standard resolution. -/
private noncomputable abbrev resolutionCylinderBoundary (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :=
  algebraCylinderBoundary A (standardResolution.{u, max u v} A B).left

/-- The relative skeleta of the cylinder over its boundary: stage `d` consists of the boundary
together with every simplex of dimension below `d`. -/
private noncomputable abbrev resolutionCylinderFiltration (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (d : ℕ) :=
  SSet.skeletonOfMono (resolutionCylinderBoundary A B).ι d

/-- The endomorphism of `P_•` attached to an endpoint of the interval: termwise Frobenius at `0`
and the square-induced map at `1`. -/
private noncomputable def endpointEndo (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (b : Fin 2) :
    resolutionRing A B ⟶ resolutionRing A B :=
  if b = 0 then frobeniusEndo p hp A B hA else squareEndo p hp A B hA

/-- Both endpoint endomorphisms restrict to Frobenius on the image of the base ring `A`. -/
private theorem endpointEndo_algebraMap (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (b : Fin 2)
    (n : SimplexCategoryᵒᵖ) (a : A) :
    (endpointEndo p hp A B hA b).app n
      (algebraMap A ((standardResolution.{u, max u v} A B).left.obj n) a) =
      algebraMap A ((standardResolution.{u, max u v} A B).left.obj n)
        (frobeniusHom hp hA a) := by
  by_cases hb : b = 0
  · simp only [endpointEndo, ite_eq_left hb]
    exact (map_pow _ a p).symm
  · simp only [endpointEndo, ite_eq_right hb]
    exact (squareFunctoriality (frobeniusSquare p hp A B hA)).resolution_algebraMap n a

/-- Both endpoint endomorphisms are compatible with the augmentation, where they induce the
`p`-th power map on `B`. -/
private theorem endpointEndo_augmentation (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (b : Fin 2)
    (n : SimplexCategoryᵒᵖ) (x : (standardResolution.{u, max u v} A B).left.obj n) :
    standardResolutionAugmentationHom A B n ((endpointEndo p hp A B hA b).app n x) =
      (standardResolutionAugmentationHom A B n x) ^ p := by
  by_cases hb : b = 0
  · simp only [endpointEndo, ite_eq_left hb]
    exact map_pow _ x p
  · simp only [endpointEndo, ite_eq_right hb]
    exact (squareFunctoriality (frobeniusSquare p hp A B hA)).resolution_augmentation n x

/-- The map out of the boundary of the cylinder given by the two endpoint endomorphisms, one on
each end face. -/
private noncomputable def cylinderBoundaryEvaluation (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    (resolutionCylinderBoundary.{u, v} A B : SSet.{max u v}) ⟶
      (standardResolution.{u, max u v} A B).left ⋙ forget (CommAlgCat.{max u v} A) where
  app n := ↾fun x => (endpointEndo p hp A B hA (x.1.2.toOrderHom 0)).app n x.1.1
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨⟨x, t⟩, hz⟩
    obtain ⟨b, hb⟩ := hz
    change t = SimplexCategory.const n.unop ⦋1⦌ b at hb
    change (endpointEndo p hp A B hA (t.toOrderHom (f.unop.toOrderHom 0))).app m
      ((standardResolution.{u, max u v} A B).left.map f x) =
      (standardResolution.{u, max u v} A B).left.map f
        ((endpointEndo p hp A B hA (t.toOrderHom 0)).app n x)
    rw [hb]
    exact congrArg (fun q => q.hom x) ((endpointEndo p hp A B hA b).naturality f)

/-- A simplex of the cylinder whose interval coordinate is constant lies in every stage, being part
of the boundary. -/
private theorem cylinder_constant_mem (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (d : ℕ) (n : SimplexCategoryᵒᵖ)
    (x : (standardResolution.{u, max u v} A B).left.obj n) (b : Fin 2) :
    (x, SimplexCategory.const n.unop ⦋1⦌ b) ∈ (resolutionCylinderFiltration A B d).obj n :=
  Or.inl ⟨⟨(x, SimplexCategory.const n.unop ⦋1⦌ b), b, rfl⟩, rfl⟩

/-- Every simplex of the cylinder of dimension below `d` lies in stage `d`. -/
private theorem cylinder_low_mem (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (d n : ℕ) (hn : n < d)
    (x : (resolutionCylinder A B).obj (op ⦋n⦌)) :
    x ∈ (resolutionCylinderFiltration A B d).obj _ :=
  Or.inr ((resolutionCylinder A B).mem_skeleton x hn)

/-- A homotopy over stage `d` only: a map out of stage `d` of the cylinder which is the two
endpoint endomorphisms on the boundary, and which in each degree below `d` is given, for each
simplex `t` of the interval, by a ring map `P_n → P_n` over Frobenius on the base. -/
private structure PolynomialHomotopyStage (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (d : ℕ) where
  /-- The map out of stage `d` of the cylinder. -/
  hom : (resolutionCylinderFiltration.{u, v} A B d : SSet.{max u v}) ⟶
    (standardResolution.{u, max u v} A B).left ⋙ forget (CommAlgCat.{max u v} A)
  /-- On each end face of the cylinder the map is the corresponding endpoint endomorphism. -/
  endpoint : ∀ (n : SimplexCategoryᵒᵖ)
      (x : (standardResolution.{u, max u v} A B).left.obj n) (b : Fin 2),
    hom.app n ⟨(x, SimplexCategory.const n.unop ⦋1⦌ b), cylinder_constant_mem A B d n x b⟩ =
      (endpointEndo p hp A B hA b).app n x
  /-- In each degree below `d`, and for each simplex `t` of the interval, the ring map `P_n → P_n`
  carrying the map. -/
  ringMap : ∀ (n : ℕ) (_hn : n < d) (_t : ⦋n⦌ ⟶ ⦋1⦌),
    (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) →+*
      (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)
  /-- Each of those ring maps restricts to Frobenius on the image of the base ring `A`. -/
  ringMap_base : ∀ (n : ℕ) (hn : n < d) (t : ⦋n⦌ ⟶ ⦋1⦌) (a : A),
    ringMap n hn t (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a)
  /-- Each of those ring maps computes the map on the cell `(-, t)` of the cylinder. -/
  ringMap_apply : ∀ (n : ℕ) (hn : n < d) (t : ⦋n⦌ ⟶ ⦋1⦌)
      (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)),
    hom.app _ ⟨(x, t), cylinder_low_mem A B d n hn (x, t)⟩ = ringMap n hn t x

/-- A subset of simplices reflected by degeneracies inherits the nondegenerate
factorization of the ambient simplicial set. -/
private theorem exists_nonDegenerate_mem_of_degeneracy
    (X : SSet.{v}) (T : ∀ n : ℕ, Set (X.obj (op ⦋n⦌)))
    (hT : ∀ (n : ℕ) (i : Fin (n + 1)) (x : X.obj (op ⦋n⦌)),
      X.σ i x ∈ T (n + 1) → x ∈ T n)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) (hx : x ∈ T n) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y ∧ (y : X.obj (op ⦋m⦌)) ∈ T m := by
  induction n with
  | zero => exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp, hx⟩
  | succ n ih =>
      by_cases hnd : x ∈ X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hnd⟩, by simp, hx⟩
      · simp only [← SSet.mem_degenerate_iff_notMem_nonDegenerate,
          SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hnd
        obtain ⟨i, y, rfl⟩ := hnd
        obtain ⟨m, f, hf, z, rfl, hz⟩ := ih y (hT n i y hx)
        exact ⟨m, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl, hz⟩

/-- A simplex of the `d`-skeleton is a degeneracy of a simplex of dimension below `d`. -/
private theorem exists_epi_low_of_mem_skeleton (X : SSet.{v}) {d n : ℕ}
    (x : X.obj (op ⦋n⦌)) (hx : x ∈ (X.skeleton d).obj _) :
    ∃ (m : ℕ) (_hm : m < d) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.obj (op ⦋m⦌)), x = X.map f.op y := by
  have hT (k : ℕ) (i : Fin (k + 1)) (z : X.obj (op ⦋k⦌))
      (hz : X.σ i z ∈ (X.skeleton d).obj _) : z ∈ (X.skeleton d).obj _ := by
    have hh := (X.skeleton d).map (SimplexCategory.δ i.castSucc).op hz
    have he := congrArg (fun q => q.hom z) (X.δ_comp_σ_self (i := i))
    change X.δ i.castSucc (X.σ i z) = z at he
    change X.δ i.castSucc (X.σ i z) ∈ (X.skeleton d).obj _ at hh
    rwa [he] at hh
  obtain ⟨m, f, hf, y, he, hy⟩ := exists_nonDegenerate_mem_of_degeneracy X
    (fun k => (X.skeleton d).obj (op ⦋k⦌)) hT x hx
  exact ⟨m, (X.mem_skeleton_obj_iff_of_nonDegenerate y d).mp hy, f, hf, y, he⟩

/-- Two ring maps out of a polynomial algebra over `R` which agree on the image of `R` and on every
variable are equal. -/
private theorem ringHom_ext_of_polynomialEquiv {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] {V : Type*}
    (e : S ≃ₐ[R] MvPolynomial V R) (f g : S →+* T)
    (hR : ∀ a : R, f (algebraMap R S a) = g (algebraMap R S a))
    (hV : ∀ v : V, f (e.symm (MvPolynomial.X v)) = g (e.symm (MvPolynomial.X v))) :
    f = g := by
  have he : f.comp e.symm.toRingEquiv.toRingHom =
      g.comp e.symm.toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) hV
    show f (e.symm (MvPolynomial.C a)) = g (e.symm (MvPolynomial.C a))
    rw [show e.symm (MvPolynomial.C a) = algebraMap R S a from e.symm.commutes a]
    exact hR a
  ext x
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply] using
    RingHom.congr_fun he (e x)

/-- The faces of an `(n + 2)`-simplex, pushed through a map defined on a subcomplex which contains
all of them, form a family compatible under the faces. -/
private theorem subcomplex_face_images_compatible (X Y : SSet.{v}) (U : X.Subcomplex)
    (h : (U : SSet) ⟶ Y) (n : ℕ) (x : X.obj (op ⦋n + 2⦌))
    (hx : ∀ i : Fin (n + 3), X.δ i x ∈ U.obj _) :
    ∀ (j k : Fin (n + 3)) (hjk : j < k),
      Y.δ (k.pred (Fin.ne_zero_of_lt hjk)) (h.app _ ⟨X.δ j x, hx j⟩) =
        Y.δ (j.castPred (Fin.ne_last_of_lt hjk)) (h.app _ ⟨X.δ k x, hx k⟩) := by
  intro j k hjk
  have hm (i : Fin (n + 2)) (r : Fin (n + 3)) :
      Y.δ i (h.app _ ⟨X.δ r x, hx r⟩) =
        h.app _ ⟨X.δ i (X.δ r x), U.map (SimplexCategory.δ i).op (hx r)⟩ :=
    (congrArg (fun q => q.hom ⟨X.δ r x, hx r⟩)
      (h.naturality (SimplexCategory.δ i).op)).symm
  rw [hm, hm]
  apply congrArg (h.app _)
  apply Subtype.ext
  have he := congrArg (fun q => q.hom x)
    (X.δ_comp_δ' (i := j.castPred (Fin.ne_last_of_lt hjk)) (j := k)
      (by simpa only [Fin.castSucc_castPred] using hjk))
  simpa only [ConcreteCategory.comp_apply, Fin.castSucc_castPred] using he.symm

/-- Naturality of a stage, read on elements. -/
private theorem PolynomialHomotopyStage.naturality_apply
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {d : ℕ} (h : PolynomialHomotopyStage.{u, v} p hp A B hA d)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (resolutionCylinder A B).obj n)
    (hx : x ∈ (resolutionCylinderFiltration A B d).obj n) :
    (standardResolution.{u, max u v} A B).left.map f (h.hom.app n ⟨x, hx⟩) =
      h.hom.app m ⟨(resolutionCylinder A B).map f x,
        (resolutionCylinderFiltration A B d).map f hx⟩ :=
  (congrArg (fun q => q.hom ⟨x, hx⟩) (h.hom.naturality f)).symm

/-- The augmentation of the standard resolution commutes with its structure maps, on elements. -/
private theorem augmentation_map_apply (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
    {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (x : (standardResolution.{u, max u v} A B).left.obj i) :
    standardResolutionAugmentationHom A B j ((standardResolution.{u, max u v} A B).left.map f x) =
      standardResolutionAugmentationHom A B i x :=
  RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) x

/-- A stage is compatible with the augmentation: the augmentation of a value is the `p`-th power of
the augmentation of the underlying element of `P_•`. This holds because the stage agrees with an
endpoint endomorphism after restricting along the map to degree zero. -/
private theorem PolynomialHomotopyStage.augmentation_apply
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {d : ℕ} (h : PolynomialHomotopyStage.{u, v} p hp A B hA d)
    (n : SimplexCategoryᵒᵖ) (x : (resolutionCylinderFiltration A B d).obj n) :
    standardResolutionAugmentationHom A B n (h.hom.app n x) =
      (standardResolutionAugmentationHom A B n x.1.1) ^ p := by
  let f : n ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ n.unop 0).op
  have ht : (resolutionCylinder A B).map f x.1 =
      ((standardResolution.{u, max u v} A B).left.map f x.1.1,
        SimplexCategory.const ⦋0⦌ ⦋1⦌ (x.1.2.toOrderHom 0)) := by
    show (_, (SimplexCategory.const ⦋0⦌ n.unop 0) ≫ x.1.2) = (_, _)
    exact congrArg (fun t =>
      ((standardResolution.{u, max u v} A B).left.map f x.1.1, t))
      (SimplexCategory.const_comp ⦋0⦌ x.1.2 0)
  have he : (standardResolution.{u, max u v} A B).left.map f (h.hom.app n x) =
      (endpointEndo p hp A B hA (x.1.2.toOrderHom 0)).app (op ⦋0⦌)
        ((standardResolution.{u, max u v} A B).left.map f x.1.1) := by
    rw [h.naturality_apply p f x.1 x.2]
    have heq : (⟨(resolutionCylinder A B).map f x.1,
        (resolutionCylinderFiltration A B d).map f x.2⟩ :
        (resolutionCylinderFiltration A B d).obj (op ⦋0⦌)) =
      ⟨((standardResolution.{u, max u v} A B).left.map f x.1.1,
        SimplexCategory.const ⦋0⦌ ⦋1⦌ (x.1.2.toOrderHom 0)),
        cylinder_constant_mem A B d _ _ _⟩ := Subtype.ext ht
    rw [heq, h.endpoint]
  rw [← augmentation_map_apply A B f, he, endpointEndo_augmentation, augmentation_map_apply]

/-- Every `(n + 1)`-simplex of the cylinder has a value compatible with the values a stage of
degree `n + 1` already assigns to its faces: the compatible family of faces is filled. -/
private theorem PolynomialHomotopyStage.exists_simplex_filler
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {n : ℕ}
    (h : PolynomialHomotopyStage.{u, v} p hp A B hA (n + 1))
    (x : (resolutionCylinder A B).obj (op ⦋n + 1⦌)) :
    ∃ y : (standardResolution.{u, max u v} A B).left.obj (op ⦋n + 1⦌),
      (∀ hx : x ∈ (resolutionCylinderFiltration A B (n + 1)).obj _,
        y = h.hom.app _ ⟨x, hx⟩) ∧
      ∀ i : Fin (n + 2), (standardResolution.{u, max u v} A B).left.δ i y =
        h.hom.app _ ⟨(resolutionCylinder A B).δ i x,
          cylinder_low_mem A B (n + 1) n (Nat.lt_succ_self n) _⟩ := by
  classical
  by_cases hx : x ∈ (resolutionCylinderFiltration A B (n + 1)).obj _
  · exact ⟨h.hom.app _ ⟨x, hx⟩, fun _ => rfl,
      fun i => h.naturality_apply p (SimplexCategory.δ i).op x hx⟩
  · cases n with
    | zero =>
        let y₀ := h.hom.app _ ⟨(resolutionCylinder A B).δ (0 : Fin 2) x,
          cylinder_low_mem A B 1 0 (by omega) _⟩
        let y₁ := h.hom.app _ ⟨(resolutionCylinder A B).δ (1 : Fin 2) x,
          cylinder_low_mem A B 1 0 (by omega) _⟩
        have he : standardResolutionAugmentationHom A B (op ⦋0⦌) y₀ =
            standardResolutionAugmentationHom A B (op ⦋0⦌) y₁ := by
          dsimp only [y₀, y₁]
          rw [h.augmentation_apply p, h.augmentation_apply p]
          exact congrArg (· ^ p) ((augmentation_map_apply A B (SimplexCategory.δ 0).op x.1).trans
            (augmentation_map_apply A B (SimplexCategory.δ 1).op x.1).symm)
        obtain ⟨y, hy₀, hy₁⟩ := standardResolution_edge_filler A B y₀ y₁ he
        refine ⟨y, fun hxx => (hx hxx).elim, fun i => ?_⟩
        fin_cases i
        · exact hy₀
        · exact hy₁
    | succ n =>
        let y (i : Fin (n + 3)) := h.hom.app _ ⟨(resolutionCylinder A B).δ i x,
          cylinder_low_mem A B (n + 2) (n + 1) (by omega) _⟩
        have hy := subcomplex_face_images_compatible (resolutionCylinder A B)
          ((standardResolution.{u, max u v} A B).left ⋙
            forget (CommAlgCat.{max u v} A))
          (resolutionCylinderFiltration A B (n + 2)) h.hom n x
          (fun i => cylinder_low_mem A B (n + 2) (n + 1) (by omega) _)
        obtain ⟨z, hz⟩ := standardResolution_boundary_filler A B n y hy
        exact ⟨z, fun hxx => (hx hxx).elim, hz⟩

/-- A family of ring maps, one for each simplex `t` of the interval, which agrees with a stage of
degree `d` on the boundary and on the variables of `P_d`, agrees with it on all of stage `d`. -/
private theorem PolynomialHomotopyStage.ringMaps_agree_on_filtration
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {d : ℕ} (h : PolynomialHomotopyStage.{u, v} p hp A B hA d)
    (F : (⦋d⦌ ⟶ ⦋1⦌) →
      ((standardResolution.{u, max u v} A B).left.obj (op ⦋d⦌) →+*
        (standardResolution.{u, max u v} A B).left.obj (op ⦋d⦌)))
    (hR : ∀ t a, F t (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a))
    (hX : ∀ t v (hv : (resolutionVariable A B d v, t) ∈
        (resolutionCylinderFiltration A B d).obj _),
      F t (resolutionVariable A B d v) = h.hom.app _ ⟨(resolutionVariable A B d v, t), hv⟩) :
    ∀ z : (resolutionCylinderFiltration A B d).obj (op ⦋d⦌),
      F z.1.2 z.1.1 = h.hom.app _ z := by
  rintro ⟨⟨x, t⟩, hx⟩
  change (x, t) ∈ Set.range ((resolutionCylinderBoundary A B).ι.app _) ∨
    (x, t) ∈ ((resolutionCylinder A B).skeleton d).obj _ at hx
  rcases hx with hx | hx
  · obtain ⟨z, hz⟩ := hx
    have hb : ∃ b : Fin 2, t = SimplexCategory.const ⦋d⦌ ⦋1⦌ b := by
      obtain ⟨b, hb⟩ : ∃ b : Fin 2, z.1.2 = SimplexCategory.const ⦋d⦌ ⦋1⦌ b := z.2
      exact ⟨b, (congrArg Prod.snd hz).symm.trans hb⟩
    obtain ⟨b, rfl⟩ := hb
    have he : F (SimplexCategory.const ⦋d⦌ ⦋1⦌ b) =
        ((endpointEndo p hp A B hA b).app (op ⦋d⦌)).hom := by
      apply ringHom_ext_of_polynomialEquiv (resolutionPolynomialEquiv A B d)
      · intro a
        exact (hR _ a).trans (endpointEndo_algebraMap p hp A B hA b _ a).symm
      · intro v
        exact (hX _ v (cylinder_constant_mem A B d _ _ b)).trans (h.endpoint _ _ b)
    exact (RingHom.congr_fun he x).trans (h.endpoint _ x b).symm
  · obtain ⟨m, hm, f, hf, ⟨y, s⟩, he⟩ :=
      exists_epi_low_of_mem_skeleton (resolutionCylinder A B) (x, t) hx
    let P := (standardResolution.{u, max u v} A B).left
    have hcomp : (F (f ≫ s)).comp (P.map f.op).hom.toRingHom =
        (P.map f.op).hom.toRingHom.comp (h.ringMap m hm s) := by
      apply ringHom_ext_of_polynomialEquiv (resolutionPolynomialEquiv A B m)
      · intro a
        show F (f ≫ s) ((P.map f.op).hom (algebraMap A _ a)) =
          (P.map f.op).hom (h.ringMap m hm s (algebraMap A _ a))
        rw [(P.map f.op).hom.commutes, hR, h.ringMap_base, (P.map f.op).hom.commutes]
      · intro v
        obtain ⟨w, hw⟩ := resolutionVariable_map_epi A B f v
        let z := (resolutionVariable A B m v, s)
        have hz : (resolutionCylinder A B).map f.op z =
            (resolutionVariable A B d w, f ≫ s) := Prod.ext hw rfl
        have hzmem := (resolutionCylinderFiltration A B d).map f.op
          (cylinder_low_mem A B d m hm z)
        change (resolutionCylinder A B).map f.op z ∈
          (resolutionCylinderFiltration A B d).obj _ at hzmem
        rw [hz] at hzmem
        show F (f ≫ s) (P.map f.op (resolutionVariable A B m v)) =
          P.map f.op (h.ringMap m hm s (resolutionVariable A B m v))
        rw [hw, hX _ _ hzmem, ← h.ringMap_apply]
        have hn := (h.naturality_apply p f.op z (cylinder_low_mem A B d m hm z)).symm
        refine (congrArg (h.hom.app _) (Subtype.ext hz.symm)).trans hn
    calc
      F t x = F (f ≫ s) (P.map f.op y) :=
        congrArg (fun z : (resolutionCylinder A B).obj (op ⦋d⦌) => F z.2 z.1) he
      _ = P.map f.op (h.ringMap m hm s y) := RingHom.congr_fun hcomp y
      _ = h.hom.app _ ⟨(resolutionCylinder A B).map f.op (y, s),
          (resolutionCylinderFiltration A B d).map f.op
            (cylinder_low_mem A B d m hm (y, s))⟩ := by
        rw [← h.ringMap_apply]
        exact h.naturality_apply p f.op (y, s) (cylinder_low_mem A B d m hm (y, s))
      _ = _ := congrArg (h.hom.app _) (Subtype.ext he.symm)

/-- A stage of degree `n + 1` extends to a family of ring maps in degree `n + 1`: choose a filler
for each variable and extend freely over the polynomial algebra. -/
private theorem PolynomialHomotopyStage.exists_degree_ringMaps_succ
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {n : ℕ}
    (h : PolynomialHomotopyStage.{u, v} p hp A B hA (n + 1)) :
    ∃ F : (⦋n + 1⦌ ⟶ ⦋1⦌) →
      ((standardResolution.{u, max u v} A B).left.obj (op ⦋n + 1⦌) →+*
        (standardResolution.{u, max u v} A B).left.obj (op ⦋n + 1⦌)),
      (∀ t a, F t (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a)) ∧
      (∀ t v (hv : (resolutionVariable A B (n + 1) v, t) ∈
          (resolutionCylinderFiltration A B (n + 1)).obj _),
        F t (resolutionVariable A B (n + 1) v) =
          h.hom.app _ ⟨(resolutionVariable A B (n + 1) v, t), hv⟩) ∧
      ∀ (i : Fin (n + 2)) (t : ⦋n + 1⦌ ⟶ ⦋1⦌)
        (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n + 1⦌)),
        (standardResolution.{u, max u v} A B).left.δ i (F t x) =
          h.ringMap n (Nat.lt_succ_self n) (SimplexCategory.δ i ≫ t)
            ((standardResolution.{u, max u v} A B).left.δ i x) := by
  classical
  let P := (standardResolution.{u, max u v} A B).left
  let a (t : ⦋n + 1⦌ ⟶ ⦋1⦌) (v : resolutionVariables A B (n + 1)) :=
    Classical.choose (h.exists_simplex_filler p (resolutionVariable A B (n + 1) v, t))
  have ha t v := Classical.choose_spec
    (h.exists_simplex_filler p (resolutionVariable A B (n + 1) v, t))
  let F (t : ⦋n + 1⦌ ⟶ ⦋1⦌) : P.obj (op ⦋n + 1⦌) →+* P.obj (op ⦋n + 1⦌) :=
    (MvPolynomial.eval₂Hom ((algebraMap A _).comp (frobeniusHom hp hA)) (a t)).comp
      (resolutionPolynomialEquiv A B (n + 1)).toRingEquiv.toRingHom
  have hFX (t) (v) : F t (resolutionVariable A B (n + 1) v) = a t v := by
    show MvPolynomial.eval₂Hom _ _ ((resolutionPolynomialEquiv A B (n + 1))
      ((resolutionPolynomialEquiv A B (n + 1)).symm (MvPolynomial.X v))) = _
    rw [AlgEquiv.apply_symm_apply]
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hFR t a : F t (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a) := by
    show MvPolynomial.eval₂Hom _ _
      ((resolutionPolynomialEquiv A B (n + 1)) (algebraMap A _ a)) = _
    rw [AlgEquiv.commutes]
    exact MvPolynomial.eval₂Hom_C _ _ _
  refine ⟨F, hFR, ?_, ?_⟩
  · intro t v hv
    exact (hFX t v).trans ((ha t v).1 hv)
  · intro i t x
    have he : (P.δ i).hom.toRingHom.comp (F t) =
        (h.ringMap n (Nat.lt_succ_self n) (SimplexCategory.δ i ≫ t)).comp
          (P.δ i).hom.toRingHom := by
      apply ringHom_ext_of_polynomialEquiv (resolutionPolynomialEquiv A B (n + 1))
      · intro b
        show (P.δ i).hom (F t (algebraMap A _ b)) =
          h.ringMap n _ _ ((P.δ i).hom (algebraMap A _ b))
        rw [hFR, (P.δ i).hom.commutes, (P.δ i).hom.commutes, h.ringMap_base]
      · intro v
        show P.δ i (F t (resolutionVariable A B (n + 1) v)) = _
        rw [hFX]
        exact ((ha t v).2 i).trans
          (h.ringMap_apply n (Nat.lt_succ_self n) (SimplexCategory.δ i ≫ t)
            (P.δ i (resolutionVariable A B (n + 1) v)))
    exact RingHom.congr_fun he x

/-- The initial stage: the map out of the boundary given by the two endpoint endomorphisms. There
is no degree below `0`, so the ring-map fields are empty. -/
private noncomputable def initialPolynomialHomotopyStage (hp : p.Prime)
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    PolynomialHomotopyStage.{u, v} p hp A B hA 0 where
  hom := SSet.Subcomplex.homOfLE (show resolutionCylinderFiltration.{u, v} A B 0 ≤
      resolutionCylinderBoundary.{u, v} A B by
        simp [resolutionCylinderFiltration, SSet.skeletonOfMono]) ≫
    cylinderBoundaryEvaluation p hp A B hA
  endpoint n x b := rfl
  ringMap n hn := False.elim ((Nat.not_lt_zero n) hn)
  ringMap_base n hn := False.elim ((Nat.not_lt_zero n) hn)
  ringMap_apply n hn := False.elim ((Nat.not_lt_zero n) hn)

open SSet.relativeCellComplexOfMono CategoryTheory.Limits in
/-- Extension over one round of relative cell attachment: a map out of the `d`-th relative skeleton
and a prescription on the `d`-simplices of the ambient complex, agreeing on the skeleton and
compatible on the boundaries of the attached cells, extend to the `(d + 1)`-st skeleton. -/
private theorem exists_skeleton_extension (X Y : SSet.{v}) (U : X.Subcomplex) (d : ℕ)
    (h : (SSet.skeletonOfMono U.ι d : SSet) ⟶ Y)
    (F : X.obj (op ⦋d⦌) → Y.obj (op ⦋d⦌))
    (hF : ∀ (x : X.obj (op ⦋d⦌)) (hx : x ∈ (SSet.skeletonOfMono U.ι d).obj _),
      h.app _ ⟨x, hx⟩ = F x)
    (hbd : ∀ c : Cell U.ι d,
      c.ιSigmaBoundary ≫ t U.ι d ≫ h =
        (SSet.boundary d).ι ≫ SSet.yonedaEquiv.symm (F c.simplex)) :
    ∃ H : (SSet.skeletonOfMono U.ι (d + 1) : SSet) ⟶ Y,
      r U.ι d ≫ H = h ∧
      ∀ x : (SSet.skeletonOfMono U.ι (d + 1)).obj (op ⦋d⦌), H.app _ x = F x.1 := by
  classical
  let k : sigmaStdSimplex U.ι d ⟶ Y :=
    Sigma.desc (fun c : Cell U.ι d => SSet.yonedaEquiv.symm (F c.simplex))
  have hw : t U.ι d ≫ h = l U.ι d ≫ k := by
    ext c : 1
    simpa [k] using hbd c
  let H := (isPushout U.ι d).desc h k hw
  have hr : r U.ι d ≫ H = h := (isPushout U.ι d).inl_desc h k hw
  refine ⟨H, hr, ?_⟩
  rintro ⟨x, hx⟩
  by_cases hx₀ : x ∈ (SSet.skeletonOfMono U.ι d).obj _
  · exact (congrArg (fun q => q.app (op ⦋d⦌) ⟨x, hx₀⟩) hr).trans (hF x hx₀)
  · have hnd : x ∈ X.nonDegenerate d := by
      by_contra hn
      obtain ⟨m, hm, f, hf, y, rfl⟩ := (X.mem_degenerate_iff x).1
        ((X.mem_degenerate_iff_notMem_nonDegenerate x).2 hn)
      exact hx₀ (Or.inr ((X.skeleton d).map f.op (X.mem_skeleton y hm)))
    let c : Cell U.ι d := ⟨x, hnd, fun hx => hx₀ (Or.inl hx)⟩
    have hc : (c.ιSigmaStdSimplex ≫ b U.ι d) ≫ H =
        SSet.yonedaEquiv.symm (F x) := by
      rw [Category.assoc, (isPushout U.ι d).inr_desc h k hw]
      simp [k, c]
    have hv : SSet.yonedaEquiv (c.ιSigmaStdSimplex ≫ b U.ι d) = ⟨x, hx⟩ := by
      apply Subtype.ext
      show ((b U.ι d).app _ (c.ιSigmaStdSimplex.app _
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋d⦌)))).val = x
      exact (c.b_app_ι_app_objEquiv_symm_val (𝟙 ⦋d⦌)).trans (by simp [c])
    simpa only [SSet.yonedaEquiv_comp, hv, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hc

open SSet.relativeCellComplexOfMono in
/-- The `i`-th face of the attaching map of a cell is the `i`-th face of its simplex. -/
private theorem cell_boundary_face (X : SSet.{v}) (U : X.Subcomplex) (n : ℕ)
    (c : Cell U.ι (n + 1)) (i : Fin (n + 2)) :
    SSet.yonedaEquiv (SSet.boundary.ι i ≫ c.ιSigmaBoundary ≫ t U.ι (n + 1)) =
      ⟨X.δ i c.simplex, Or.inr (X.mem_skeleton _ (Nat.lt_succ_self n))⟩ := by
  apply Subtype.ext
  have he := congrArg SSet.yonedaEquiv
    (show (SSet.boundary.ι i ≫ c.ιSigmaBoundary ≫ t U.ι (n + 1)) ≫
        (SSet.skeletonOfMono U.ι (n + 1)).ι = SSet.stdSimplex.δ i ≫ c.map by
      simp [t])
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp,
    show SSet.yonedaEquiv c.map = c.simplex from Equiv.apply_symm_apply _ _,
    SSet.yonedaEquiv_comp] at he
  exact he

open SSet.relativeCellComplexOfMono in
/-- A stage of degree `d` together with a compatible family of ring maps in degree `d` extends to a
stage of degree `d + 1`. -/
private theorem PolynomialHomotopyStage.exists_succ_of_degree_ringMaps
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {d : ℕ} (h : PolynomialHomotopyStage.{u, v} p hp A B hA d)
    (F : (⦋d⦌ ⟶ ⦋1⦌) →
      ((standardResolution.{u, max u v} A B).left.obj (op ⦋d⦌) →+*
        (standardResolution.{u, max u v} A B).left.obj (op ⦋d⦌)))
    (hR : ∀ t a, F t (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a))
    (hX : ∀ t v (hv : (resolutionVariable A B d v, t) ∈
        (resolutionCylinderFiltration A B d).obj _),
      F t (resolutionVariable A B d v) = h.hom.app _ ⟨(resolutionVariable A B d v, t), hv⟩)
    (hbd : ∀ c : Cell (resolutionCylinderBoundary A B).ι d,
      c.ιSigmaBoundary ≫ t (resolutionCylinderBoundary A B).ι d ≫ h.hom =
        (SSet.boundary d).ι ≫ SSet.yonedaEquiv.symm (F c.simplex.2 c.simplex.1)) :
    ∃ H : PolynomialHomotopyStage.{u, v} p hp A B hA (d + 1),
      r (resolutionCylinderBoundary A B).ι d ≫ H.hom = h.hom := by
  classical
  obtain ⟨H, hr, hH⟩ := exists_skeleton_extension (resolutionCylinder A B)
    ((standardResolution.{u, max u v} A B).left ⋙
      forget (CommAlgCat.{max u v} A)) (resolutionCylinderBoundary A B) d h.hom
    (fun z => F z.2 z.1)
    (fun z hz => (h.ringMaps_agree_on_filtration p F hR hX ⟨z, hz⟩).symm) hbd
  have hmaps (n : ℕ) (hn : n < d + 1) (t : ⦋n⦌ ⟶ ⦋1⦌) :
      ∃ φ : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) →+*
          (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌),
        (∀ a, φ (algebraMap A _ a) = algebraMap A _ (frobeniusHom hp hA a)) ∧
        ∀ x, H.app _ ⟨(x, t), cylinder_low_mem A B (d + 1) n hn _⟩ = φ x := by
    by_cases hnd : n < d
    · refine ⟨h.ringMap n hnd t, h.ringMap_base n hnd t, fun x => ?_⟩
      exact (congrArg (fun q => q.app (op ⦋n⦌)
        ⟨(x, t), cylinder_low_mem A B d n hnd _⟩) hr).trans (h.ringMap_apply n hnd t x)
    · obtain rfl : n = d := by omega
      exact ⟨F t, hR t, fun x => hH ⟨(x, t), cylinder_low_mem A B (n + 1) n hn _⟩⟩
  refine ⟨{
    hom := H
    endpoint := fun n x b => ?_
    ringMap := fun n hn t => Classical.choose (hmaps n hn t)
    ringMap_base := fun n hn t => (Classical.choose_spec (hmaps n hn t)).1
    ringMap_apply := fun n hn t => (Classical.choose_spec (hmaps n hn t)).2
  }, hr⟩
  exact (congrArg (fun q => q.app n
    ⟨(x, SimplexCategory.const n.unop ⦋1⦌ b), cylinder_constant_mem A B d n x b⟩) hr).trans
      (h.endpoint n x b)

/-- Every map `⦋0⦌ ⟶ ⦋1⦌` is constant. -/
private theorem simplex_zero_eq_const (t : ⦋0⦌ ⟶ ⦋1⦌) :
    t = SimplexCategory.const ⦋0⦌ ⦋1⦌ (t.toOrderHom 0) := by
  ext i
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  rw [hi]
  rfl

open SSet.relativeCellComplexOfMono in
/-- Every stage extends to the next one. In degree zero the extension is given by the endpoint
endomorphisms, and in higher degree by `exists_degree_ringMaps_succ`. -/
private theorem PolynomialHomotopyStage.exists_succ
    {hp : p.Prime} {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
    {hA : (p : A) = 0} {d : ℕ} (h : PolynomialHomotopyStage.{u, v} p hp A B hA d) :
    ∃ H : PolynomialHomotopyStage.{u, v} p hp A B hA (d + 1),
      r (resolutionCylinderBoundary A B).ι d ≫ H.hom = h.hom := by
  classical
  cases d with
  | zero =>
      let F (t : ⦋0⦌ ⟶ ⦋1⦌) :=
        ((endpointEndo p hp A B hA (t.toOrderHom 0)).app (op ⦋0⦌)).hom
      apply h.exists_succ_of_degree_ringMaps p F
        (fun t a => endpointEndo_algebraMap p hp A B hA (t.toOrderHom 0) _ a)
      · intro t v hv
        have ht := simplex_zero_eq_const t
        have he := h.endpoint (op ⦋0⦌) (resolutionVariable A B 0 v) (t.toOrderHom 0)
        exact he.symm.trans (congrArg (h.hom.app _) (Subtype.ext (Prod.ext rfl ht.symm)))
      · intro c
        exact (c.notMem ⟨⟨c.simplex, c.simplex.2.toOrderHom 0,
          simplex_zero_eq_const c.simplex.2⟩, rfl⟩).elim
  | succ n =>
      obtain ⟨F, hR, hX, hfaces⟩ := h.exists_degree_ringMaps_succ p
      apply h.exists_succ_of_degree_ringMaps p F hR hX
      intro c
      apply SSet.boundary.hom_ext
      intro i
      apply SSet.yonedaEquiv.injective
      have hl : SSet.yonedaEquiv
          ((SSet.boundary.ι i ≫ c.ιSigmaBoundary ≫
            t (resolutionCylinderBoundary A B).ι (n + 1)) ≫ h.hom) =
          h.hom.app _ ⟨(resolutionCylinder A B).δ i c.simplex,
            cylinder_low_mem A B (n + 1) n (Nat.lt_succ_self n) _⟩ := by
        rw [SSet.yonedaEquiv_comp, cell_boundary_face]
      have hr : SSet.yonedaEquiv (X :=
          (standardResolution.{u, max u v} A B).left ⋙
            forget (CommAlgCat.{max u v} A))
          ((SSet.boundary.ι i ≫ (SSet.boundary (n + 1)).ι) ≫
            SSet.yonedaEquiv.symm (F c.simplex.2 c.simplex.1)) =
          (standardResolution.{u, max u v} A B).left.δ i
            (F c.simplex.2 c.simplex.1) := by
        rw [SSet.boundary.ι_ι, SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        rfl
      have he := hl.trans ((h.ringMap_apply n (Nat.lt_succ_self n)
        (SimplexCategory.δ i ≫ c.simplex.2)
        ((standardResolution.{u, max u v} A B).left.δ i c.simplex.1)).trans
          ((hfaces i c.simplex.2 c.simplex.1).symm.trans hr.symm))
      simpa only [Category.assoc] using he

/-- The tower of stages: stage `0` is the boundary evaluation, and each later stage is a chosen
extension of the one before it. -/
private noncomputable def polynomialHomotopyStages (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    (d : ℕ) → PolynomialHomotopyStage.{u, v} p hp A B hA d
  | 0 => initialPolynomialHomotopyStage p hp A B hA
  | d + 1 => Classical.choose ((polynomialHomotopyStages hp A B hA d).exists_succ p)

/-- Each stage of the tower restricts to the one before it. -/
private theorem polynomialHomotopyStages_succ (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (d : ℕ) :
    SSet.relativeCellComplexOfMono.r (resolutionCylinderBoundary A B).ι d ≫
      (polynomialHomotopyStages p hp A B hA (d + 1)).hom =
        (polynomialHomotopyStages p hp A B hA d).hom :=
  Classical.choose_spec ((polynomialHomotopyStages p hp A B hA d).exists_succ p)

/-- Any two stages of the tower agree on the smaller of their filtrations. -/
private theorem polynomialHomotopyStages_hom_eq (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) {d e : ℕ} (hde : d ≤ e)
    (n : SimplexCategoryᵒᵖ) (x : (resolutionCylinder A B).obj n)
    (hx : x ∈ (resolutionCylinderFiltration A B d).obj n) :
    (polynomialHomotopyStages p hp A B hA e).hom.app n
        ⟨x, (SSet.skeletonOfMono (resolutionCylinderBoundary A B).ι).monotone hde n hx⟩ =
      (polynomialHomotopyStages p hp A B hA d).hom.app n ⟨x, hx⟩ := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih =>
      exact (congrArg (fun q => q.app n
        ⟨x, (SSet.skeletonOfMono (resolutionCylinderBoundary A B).ι).monotone hde n hx⟩)
          (polynomialHomotopyStages_succ p hp A B hA e)).trans ih

/-- The ring map `P_n → P_n` attached to a simplex `t : ⦋n⦌ ⟶ ⦋1⦌` of the interval: the value of
the homotopy on the cell `(-, t)` of the cylinder. -/
private noncomputable abbrev comparisonRingMap (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (n : ℕ) (t : ⦋n⦌ ⟶ ⦋1⦌) :
    (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) →+*
      (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) :=
  (polynomialHomotopyStages p hp A B hA (n + 1)).ringMap n (Nat.lt_succ_self n) t

/-- The comparison map is computed by any stage of the tower whose degree exceeds `n`. -/
private theorem comparisonRingMap_eq_stage (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) {n d : ℕ} (hn : n < d)
    (t : ⦋n⦌ ⟶ ⦋1⦌)
    (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    comparisonRingMap p hp A B hA n t x =
      (polynomialHomotopyStages p hp A B hA d).hom.app _
        ⟨(x, t), cylinder_low_mem A B d n hn _⟩ :=
  ((polynomialHomotopyStages p hp A B hA (n + 1)).ringMap_apply n
    (Nat.lt_succ_self n) t x).symm.trans
      (polynomialHomotopyStages_hom_eq p hp A B hA (Nat.succ_le_of_lt hn) _ (x, t)
        (cylinder_low_mem A B (n + 1) n (Nat.lt_succ_self n) _)).symm

/-- The comparison maps are natural in the simplex category: a simplicial operator carries the map
attached to `t` to the map attached to the restricted simplex. -/
private theorem comparisonRingMap_naturality (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) {n m : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (t : ⦋n⦌ ⟶ ⦋1⦌)
    (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    (standardResolution.{u, max u v} A B).left.map f.op
        (comparisonRingMap p hp A B hA n t x) =
      comparisonRingMap p hp A B hA m (f ≫ t)
        ((standardResolution.{u, max u v} A B).left.map f.op x) := by
  let d := n + m + 1
  have hn : n < d := by omega
  have hm : m < d := by omega
  rw [comparisonRingMap_eq_stage p hp A B hA hn,
    comparisonRingMap_eq_stage p hp A B hA hm]
  exact (polynomialHomotopyStages p hp A B hA d).naturality_apply p f.op (x, t)
    (cylinder_low_mem A B d n hn _)

/-- Naturality of the comparison maps, with the restricted simplex of the interval given by an
equation. -/
private theorem comparisonRingMap_naturality_of_eq (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    {t : ⦋n⦌ ⟶ ⦋1⦌} {t' : ⦋m⦌ ⟶ ⦋1⦌} (ht : f ≫ t = t')
    (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    (standardResolution.{u, max u v} A B).left.map f.op
        (comparisonRingMap p hp A B hA n t x) =
      comparisonRingMap p hp A B hA m t'
        ((standardResolution.{u, max u v} A B).left.map f.op x) := by
  subst ht
  exact comparisonRingMap_naturality p hp A B hA f t x

/-- At a constant simplex of the interval the comparison map is the corresponding endpoint
endomorphism. -/
private theorem comparisonRingMap_const (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) (n : ℕ) (b : Fin 2)
    (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    comparisonRingMap p hp A B hA n (SimplexCategory.const ⦋n⦌ ⦋1⦌ b) x =
      (endpointEndo p hp A B hA b).app (op ⦋n⦌) x :=
  ((polynomialHomotopyStages p hp A B hA (n + 1)).ringMap_apply n
    (Nat.lt_succ_self n) _ x).symm.trans
      ((polynomialHomotopyStages p hp A B hA (n + 1)).endpoint _ x b)

/-- The simplex of the interval attached to the index `0` is constant at `1`. -/
theorem toMk₁_zero_eq_const (n : ℕ) :
    SimplexCategory.toMk₁ (0 : Fin (n + 2)) = SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
  ext j
  apply congrArg Fin.val
  show (if j.castSucc < 0 then (0 : Fin 2) else 1) = 1
  simp

/-- The simplex of the interval attached to the last index is constant at `0`. -/
theorem toMk₁_last_eq_const (n : ℕ) :
    SimplexCategory.toMk₁ (Fin.last (n + 1)) = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
  ext j
  apply congrArg Fin.val
  show (if j.castSucc < Fin.last (n + 1) then (0 : Fin 2) else 1) = 0
  simp

/-- **Stacks Project, Tag 0G5Y.** Let `A → B` be a ring map with `p = 0` in `A` for a prime `p`,
and let `P_•` be the standard resolution of `B` over `A`. The endomorphism of `P_•` induced by
the commutative square of Frobenius maps `F_A` and `F_B` is homotopic to the endomorphism given
by Frobenius on each term `P_n`. The homotopy produced here runs from the termwise Frobenius to
the square-induced map; the source states the relation without an orientation. -/
@[stacks 0G5Y]
public theorem nonempty_homotopy_frobeniusEndo_squareEndo (hp : p.Prime) (A : Type u)
    [CommRing A] (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    Nonempty (SimplicialObject.Homotopy
      (frobeniusEndo.{u, v} p hp A B hA) (squareEndo.{u, v} p hp A B hA)) := by
  let H (n : ℕ) (i : Fin (n + 2)) :
      (resolutionRing.{u, v} A B).obj (op ⦋n⦌) ⟶
        (resolutionRing.{u, v} A B).obj (op ⦋n⦌) :=
    CommRingCat.ofHom (comparisonRingMap p hp A B hA n (SimplexCategory.toMk₁ i))
  refine ⟨Godement.Prep.homotopyOfRel _ _ H ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro n
    apply CommRingCat.hom_ext
    ext x
    show comparisonRingMap p hp A B hA n (SimplexCategory.toMk₁ 0) x = _
    rw [toMk₁_zero_eq_const]
    refine (comparisonRingMap_const p hp A B hA n 1 x).trans ?_
    simp only [endpointEndo]
    rfl
  · intro n
    apply CommRingCat.hom_ext
    ext x
    show comparisonRingMap p hp A B hA n (SimplexCategory.toMk₁ (Fin.last (n + 1))) x = _
    rw [toMk₁_last_eq_const]
    refine (comparisonRingMap_const p hp A B hA n 0 x).trans ?_
    simp only [endpointEndo]
    rfl
  · intro n j i hji
    apply CommRingCat.hom_ext
    ext x
    exact comparisonRingMap_naturality_of_eq p hp A B hA _ (by
      simp only [SimplexCategory.δ_comp_toMk₁_of_lt _ _ (Fin.castSucc_lt_succ_iff.2 hji),
        Fin.pred_succ]) x
  · intro n j i hij
    apply CommRingCat.hom_ext
    ext x
    exact comparisonRingMap_naturality_of_eq p hp A B hA _ (by
      simp only [SimplexCategory.δ_comp_toMk₁_of_le _ _ (Fin.castSucc_le_castSucc_iff.2 hij),
        Fin.castPred_castSucc]) x
  · intro n j i hji
    apply CommRingCat.hom_ext
    ext x
    exact comparisonRingMap_naturality_of_eq p hp A B hA _
      (SimplexCategory.σ_comp_toMk₁_of_lt _ _ (Fin.castSucc_lt_succ_iff.2 hji)) x
  · intro n j i hij
    apply CommRingCat.hom_ext
    ext x
    exact comparisonRingMap_naturality_of_eq p hp A B hA _
      (SimplexCategory.σ_comp_toMk₁_of_le _ _ hij) x

/-- The homotopy of Tag 0G5Y, in the form that its globalisation to cotangent complexes consumes:
the family of ring endomorphisms of the terms of the standard resolution carried by the cylinder
`P_• × Δ[1]`, one for each simplex `t : ⦋n⦌ ⟶ ⦋1⦌` of the interval.

Each member is semilinear over the Frobenius of `A` and raises the augmentation to the `p`-th
power — the two conditions under which a ring endomorphism of `P_n` induces a map
`Ω[P_n⁄A] ⊗[P_n] B → Ω[P_n⁄A] ⊗[P_n] B` semilinear over the Frobenius of `B`. The family is
natural in the simplex category, and at the two constant simplices of the interval it is the
Frobenius of `P_n` and the degreewise map of Section 08QL attached to the Frobenius square. -/
public structure FrobeniusHomotopyCylinder (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) where
  /-- The ring endomorphism of `P_n` attached to a simplex `t` of the interval. -/
  map (n : ℕ) (t : ⦋n⦌ ⟶ ⦋1⦌) :
    (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌) →+*
      (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)
  /-- Each map is semilinear over the Frobenius of the base ring. -/
  map_algebraMap (n : ℕ) (t : ⦋n⦌ ⟶ ⦋1⦌) (a : A) :
    map n t (algebraMap A ((standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) a) =
      algebraMap A ((standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) (a ^ p)
  /-- Each map raises the augmentation to the `p`-th power. -/
  map_augmentation (n : ℕ) (t : ⦋n⦌ ⟶ ⦋1⦌)
      (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    standardResolutionAugmentationHom.{u, max u v} A B (op ⦋n⦌) (map n t x) =
      standardResolutionAugmentationHom.{u, max u v} A B (op ⦋n⦌) x ^ p
  /-- The family is natural in the simplex category: a simplicial operator carries the map
  attached to `t` to the map attached to the restricted simplex. -/
  map_naturality {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (t : ⦋n⦌ ⟶ ⦋1⦌)
      (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    (standardResolution.{u, max u v} A B).left.map f.op (map n t x) =
      map m (f ≫ t) ((standardResolution.{u, max u v} A B).left.map f.op x)
  /-- At the constant simplex `0` the map is the Frobenius of `P_n`. -/
  map_const_zero (n : ℕ) (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    map n (SimplexCategory.const ⦋n⦌ ⦋1⦌ 0) x = x ^ p
  /-- At the constant simplex `1` the map is the degreewise map of standard resolutions induced by
  the Frobenius square. -/
  map_const_one (n : ℕ) (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    map n (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1) x =
      standardResolutionSquareMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA) (op ⦋n⦌) x

/-- **Stacks Project, Tag 0G5Y**, in the form consumed by the globalisation to cotangent
complexes: the cylinder of ring endomorphisms built above is a `FrobeniusHomotopyCylinder`. -/
public theorem exists_frobeniusHomotopyCylinder (hp : p.Prime) (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hA : (p : A) = 0) :
    Nonempty (FrobeniusHomotopyCylinder.{u, v} p hp A B hA) :=
  ⟨{ map := fun n t => comparisonRingMap p hp A B hA n t
     map_algebraMap := fun n t a =>
       (polynomialHomotopyStages p hp A B hA (n + 1)).ringMap_base n (Nat.lt_succ_self n) t a
     map_augmentation := fun n t x => by
       rw [comparisonRingMap_eq_stage p hp A B hA (Nat.lt_succ_self n) t x]
       exact (polynomialHomotopyStages p hp A B hA (n + 1)).augmentation_apply p _ _
     map_naturality := fun f t x => comparisonRingMap_naturality p hp A B hA f t x
     map_const_zero := fun n x => by
       refine (comparisonRingMap_const p hp A B hA n 0 x).trans ?_
       simp only [endpointEndo]
       rfl
     map_const_one := fun n x => by
       refine (comparisonRingMap_const p hp A B hA n 1 x).trans ?_
       simp only [endpointEndo]
       rfl }⟩

end CommAlgCat

end
