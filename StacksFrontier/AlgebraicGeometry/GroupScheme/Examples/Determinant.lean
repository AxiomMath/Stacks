module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative

/-!
# The determinant as a morphism of group schemes over the integers

The determinant gives a morphism from the general linear group scheme to the multiplicative
group scheme over `Spec ℤ`. On coordinate rings its pullback sends the Laurent variable to the
determinant of the generic matrix.

## Main definitions

* `AlgebraicGeometry.generalLinearStructureMorphismOverIntegers` is the structure morphism of the
  general linear scheme to `Spec ℤ`, and
  `AlgebraicGeometry.generalLinearTensorSquareOverIntegers` the tensor square of its coordinate
  ring over `ℤ`.
* `AlgebraicGeometry.determinantCoordinateRingHom` is the ring homomorphism sending the Laurent
  variable to the generic determinant.
* `AlgebraicGeometry.determinantGroupSchemeMorphismOverIntegers` is the determinant morphism of
  group schemes over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.generalLinearSchemeGrpObjOverIntegers` is the group-scheme structure of
  `GLₙ` over `Spec ℤ`, and
  `AlgebraicGeometry.generalLinearSchemeGrpObjOverIntegers_mul` identifies its multiplication on
  generic matrix entries.
* `AlgebraicGeometry.determinantGroupSchemeMorphismOverIntegers_spec` identifies the determinant
  on coordinate rings.

## Implementation notes

Group schemes over `Spec ℤ` are group objects in the category of schemes over `Spec ℤ`. The
coordinate ring used for the general linear scheme has integer coefficients represented via a
universe lift, while its structure morphism here lands in `Spec ℤ` itself; this is the reason
the integral model is pinned to universe `0` and carries its own structure morphism and
representability datum, distinct from the universe-polymorphic ones. The coordinate-ring
specification singles out the determinant. All assertions also hold at `n = 0`, where the
determinant is one.

## References

* [Stacks Project, Tag 022X](https://stacks.math.columbia.edu/tag/022X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
  CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The integer-base structure morphism of the general linear scheme. -/
noncomputable abbrev generalLinearStructureMorphismOverIntegers (n : ℕ) :
    generalLinearScheme.{0} n ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (generalLinearCoordinateRing.{0} n)))

/-- The tensor square over `ℤ` of the general linear coordinate ring. -/
abbrev generalLinearTensorSquareOverIntegers (n : ℕ) : Type :=
  @TensorProduct ℤ CommRing.toCommSemiring
    (generalLinearCoordinateRing.{0} n) (generalLinearCoordinateRing.{0} n)
    CommRing.toCommSemiring.toAddCommMonoid CommRing.toCommSemiring.toAddCommMonoid
    Algebra.toModule Algebra.toModule

/-- The matrix-point equivalence for schemes over the integers. -/
noncomputable def generalLinearOverRepresentableByOverIntegers (n : ℕ) :
    (((Over.forget (Spec (.of ℤ))).op ⋙ generalLinearGroupFunctor.{0} n) ⋙
        forget GrpCat).RepresentableBy
      (Over.mk (generalLinearStructureMorphismOverIntegers n)) := by
  let h := generalLinearRepresentableBy n
  refine ⟨?_, ?_⟩
  · intro X
    let e : (X ⟶ Over.mk (generalLinearStructureMorphismOverIntegers n)) ≃
        (X.left ⟶ generalLinearScheme.{0} n) :=
      { toFun f := (Over.forget (Spec (.of ℤ))).map f
        invFun f := Over.homMk f (specZIsTerminal.hom_ext _ _)
        left_inv f := by ext; rfl
        right_inv f := rfl }
    exact e.trans h.homEquiv
  · intro X Y f g
    change h.homEquiv ((Over.forget (Spec (.of ℤ))).map (f ≫ g)) =
      (generalLinearGroupFunctor.{0} n ⋙ forget GrpCat).map
          ((Over.forget (Spec (.of ℤ))).map f).op
          (h.homEquiv ((Over.forget (Spec (.of ℤ))).map g))
    exact h.homEquiv_comp ((Over.forget (Spec (.of ℤ))).map f)
      ((Over.forget (Spec (.of ℤ))).map g)

/-- The group scheme structure of `GLₙ` over the integers. -/
@[stacks 022X "det_over_integers"]
noncomputable instance generalLinearSchemeGrpObjOverIntegers (n : ℕ) :
    GrpObj (Over.mk (generalLinearStructureMorphismOverIntegers n)) :=
  GrpObj.ofRepresentableBy (Over.mk (generalLinearStructureMorphismOverIntegers n))
    ((Over.forget (Spec (.of ℤ))).op ⋙ generalLinearGroupFunctor.{0} n)
    (generalLinearOverRepresentableByOverIntegers n)

private lemma generalLinearRepresentability_symm_appTop (n : ℕ) {X : Over (Spec (.of ℤ))}
    (z : Matrix.GeneralLinearGroup (Fin n) (Scheme.Γ.obj (op X.left))) :
    (Scheme.ΓSpecIso (.of (generalLinearCoordinateRing.{0} n))).inv ≫
        (Over.Hom.left
          (((generalLinearOverRepresentableByOverIntegers n).homEquiv' (X := X)).symm z)).appTop =
      CommRingCat.ofHom
        (localizedPolynomialHomOfGeneralLinear n (Scheme.Γ.obj (op X.left)) z) := by
  change (Scheme.ΓSpecIso (.of (generalLinearCoordinateRing.{0} n))).inv ≫
      (ΓSpec.adjunction.homEquiv X.left
        (op (CommRingCat.of (generalLinearCoordinateRing.{0} n)))
        (CommRingCat.ofHom
          (localizedPolynomialHomOfGeneralLinear n (Scheme.Γ.obj (op X.left)) z)).op).appTop = _
  exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The ring homomorphism sending the Laurent variable to the generic determinant. -/
noncomputable def determinantCoordinateRingHom (n : ℕ) :
    LaurentPolynomial ℤ →+* generalLinearCoordinateRing.{0} n :=
  LaurentPolynomial.eval₂ (algebraMap ℤ (generalLinearCoordinateRing.{0} n))
    (IsLocalization.Away.algebraMap_isUnit (generalLinearDeterminant.{0} n)).unit

private lemma determinantCoordinateRingHom_T (n : ℕ) :
    determinantCoordinateRingHom n (LaurentPolynomial.T 1) =
      algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
        (generalLinearCoordinateRing.{0} n) (generalLinearDeterminant.{0} n) := by
  simp [determinantCoordinateRingHom, LaurentPolynomial.eval₂_T]

private lemma generalLinearDeterminant_eval (n : ℕ) {A : Type} [CommRing A]
    (c : ULift.{0} ℤ →+* A) (v : Fin n × Fin n → A) :
    MvPolynomial.eval₂ c v (generalLinearDeterminant.{0} n) =
      Matrix.det (Matrix.of fun i j => v (i, j)) := by
  simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] using
    localizedPolynomial_det_eval (n := n) (MvPolynomial.eval₂Hom c v)

/-- Global sections of `Spec.map φ` commute with the inverse of `Scheme.ΓSpecIso`. -/
private lemma Scheme.specMap_appTop_ΓSpecIso_inv_apply {R S : CommRingCat} (φ : R ⟶ S)
    (x : R) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) =
      (Scheme.ΓSpecIso S).inv.hom (φ.hom x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality φ)).symm

private lemma specMap_counit_apply_single_one :
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
      (Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom))))
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (LaurentPolynomial ℤ))).inv) (AddMonoidAlgebra.single 1 1)) = 1 := by
  have hc : (Bialgebra.counitAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom
      (AddMonoidAlgebra.single 1 1) = 1 := by
    change Coalgebra.counit (R := ℤ) (A := LaurentPolynomial ℤ) (LaurentPolynomial.T 1) = 1
    simp
  rw [Scheme.specMap_appTop_ΓSpecIso_inv_apply, CommRingCat.hom_ofHom, hc, map_one]

/-- The multiplication of the integral general linear group object, read off through the
representing equivalence as the product of the two projections. -/
private lemma generalLinearMulOverIntegers_homEquiv (n : ℕ) :
    (generalLinearOverRepresentableByOverIntegers n).homEquiv'
        (μ[Over.mk (generalLinearStructureMorphismOverIntegers n)]) =
      (generalLinearOverRepresentableByOverIntegers n).homEquiv'
          (fst (Over.mk (generalLinearStructureMorphismOverIntegers n))
            (Over.mk (generalLinearStructureMorphismOverIntegers n))) *
        (generalLinearOverRepresentableByOverIntegers n).homEquiv'
          (snd (Over.mk (generalLinearStructureMorphismOverIntegers n))
            (Over.mk (generalLinearStructureMorphismOverIntegers n))) :=
  Equiv.apply_symm_apply _ _

private lemma eq_specMap_schemeHomRingHomEquiv (n : ℕ)
    (h : Spec (.of (generalLinearTensorSquareOverIntegers n)) ⟶ generalLinearScheme.{0} n) :
    h = Spec.map (CommRingCat.ofHom
      ((Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))).hom.hom.comp
        (schemeHomRingHomEquiv n h))) := by
  let : CommRing (Scheme.Γ.obj
      (op (Spec (.of (generalLinearTensorSquareOverIntegers n))))) := CommRingCat.commRing _
  let g := schemeHomRingHomEquiv n h
  let gcat : CommRingCat.of (generalLinearCoordinateRing.{0} n) ⟶
      Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))) :=
    @CommRingCat.ofHom (generalLinearCoordinateRing.{0} n)
      (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))) : Type)
      inferInstance ‹CommRing (Scheme.Γ.obj
        (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))› g
  let iso := Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))
  apply ext_to_Spec
  rw [Scheme.Γ_map_op]
  trans gcat
  · change (Scheme.ΓSpecIso (.of (generalLinearCoordinateRing.{0} n))).inv ≫ h.appTop = gcat
    have hh : ΓSpec.adjunction.homEquiv (Spec (.of (generalLinearTensorSquareOverIntegers n)))
        (op (CommRingCat.of (generalLinearCoordinateRing.{0} n))) gcat.op = h := by
      rw [show gcat.op = (ΓSpec.adjunction.homEquiv
          (Spec (.of (generalLinearTensorSquareOverIntegers n)))
          (op (CommRingCat.of (generalLinearCoordinateRing.{0} n)))).symm h from
        Opposite.unop_injective (CommRingCat.hom_ext rfl)]
      exact Equiv.apply_symm_apply _ h
    rw [← hh]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (X := Spec (.of (generalLinearTensorSquareOverIntegers n)))
      (B := CommRingCat.of (generalLinearCoordinateRing.{0} n)) gcat
  · have hgcat : gcat = CommRingCat.ofHom (iso.hom.hom.comp g) ≫ iso.inv := by
      symm
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x => Iso.hom_inv_id_apply iso (g x)
    exact hgcat.trans (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (iso.hom.hom.comp g)))

private lemma generalLinearOverIntegers_homEquiv'_comp_mul (n : ℕ) {X : Over (Spec (.of ℤ))}
    (k : X ⟶ Over.mk (generalLinearStructureMorphismOverIntegers n) ⊗
      Over.mk (generalLinearStructureMorphismOverIntegers n)) :
    (generalLinearOverRepresentableByOverIntegers n).homEquiv'
        (k ≫ μ[Over.mk (generalLinearStructureMorphismOverIntegers n)]) =
      (generalLinearOverRepresentableByOverIntegers n).homEquiv'
          (k ≫ fst (Over.mk (generalLinearStructureMorphismOverIntegers n))
            (Over.mk (generalLinearStructureMorphismOverIntegers n))) *
        (generalLinearOverRepresentableByOverIntegers n).homEquiv'
          (k ≫ snd (Over.mk (generalLinearStructureMorphismOverIntegers n))
            (Over.mk (generalLinearStructureMorphismOverIntegers n))) := by
  rw [(generalLinearOverRepresentableByOverIntegers n).homEquiv'_comp,
    (generalLinearOverRepresentableByOverIntegers n).homEquiv'_comp,
    (generalLinearOverRepresentableByOverIntegers n).homEquiv'_comp,
    generalLinearMulOverIntegers_homEquiv]
  exact map_mul _ _ _

private lemma generalLinearOverIntegers_homEquiv'_of_left_eq_specMap (n : ℕ)
    (ψ : generalLinearCoordinateRing.{0} n →+* generalLinearTensorSquareOverIntegers n)
    (f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap ℤ (generalLinearTensorSquareOverIntegers n)))) ⟶
        Over.mk (generalLinearStructureMorphismOverIntegers n))
    (hf : f.left = Spec.map (CommRingCat.ofHom ψ)) :
    (generalLinearOverRepresentableByOverIntegers n).homEquiv' f =
      localizedPolynomialHomEquiv n
        (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))
        ((Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))).inv.hom.comp ψ) := by
  change localizedPolynomialHomEquiv n _ (schemeHomRingHomEquiv n f.left) = _
  rw [hf]
  exact congrArg (localizedPolynomialHomEquiv n
    (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n))))))
    (schemeHomRingHomEquiv_specMap (n := n) (B := generalLinearTensorSquareOverIntegers n) ψ)

private lemma generalLinearTensorSquareOverIntegers_mul_entry (n : ℕ) (i j : Fin n) :
    (Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))).hom.hom
      (((localizedPolynomialHomEquiv n
        (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))).inv.hom.comp
            Algebra.TensorProduct.includeLeftRingHom) *
        localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))).inv.hom.comp
            Algebra.TensorProduct.includeRight.toRingHom) :
        Matrix.GeneralLinearGroup (Fin n)
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))) :
        Matrix (Fin n) (Fin n)
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))) i j) =
      ∑ k : Fin n,
        @TensorProduct.tmul ℤ CommRing.toCommSemiring
          (generalLinearCoordinateRing.{0} n) (generalLinearCoordinateRing.{0} n)
          CommRing.toCommSemiring.toAddCommMonoid CommRing.toCommSemiring.toAddCommMonoid
          Algebra.toModule Algebra.toModule
          (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
            (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, k)))
          (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
            (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (k, j))) := by
  let iso := Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))
  let φL := iso.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom
  let φR := iso.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom
  refine (congrArg iso.hom.hom
    (localizedPolynomialHomEquiv_mul_entry n _ φL φR i j)).trans ?_
  refine (map_sum iso.hom.hom _ Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
  refine (map_mul iso.hom.hom _ _).trans ?_
  have hA : iso.hom.hom (φL (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
        (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, k)))) =
      Algebra.TensorProduct.includeLeftRingHom
        (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
          (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, k))) :=
    Iso.inv_hom_id_apply iso _
  have hB : iso.hom.hom (φR (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
        (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (k, j)))) =
      Algebra.TensorProduct.includeRight.toRingHom
        (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
          (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (k, j))) :=
    Iso.inv_hom_id_apply iso _
  refine (congrArg₂ (· * ·) hA hB).trans ?_
  simp [Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- Multiplication on `GLₙ` is matrix multiplication, on generic matrix entries. -/
@[stacks 022X "det_over_integers"]
theorem generalLinearSchemeGrpObjOverIntegers_mul (n : ℕ) :
    ∃ m : generalLinearCoordinateRing.{0} n →+* generalLinearTensorSquareOverIntegers n,
      (pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
        (generalLinearCoordinateRing.{0} n)).inv ≫
          μ[Over.mk (generalLinearStructureMorphismOverIntegers n)].left =
            Spec.map (CommRingCat.ofHom m) ∧
      (∀ i j : Fin n,
        m (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
          (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, j))) =
          ∑ k : Fin n,
          @TensorProduct.tmul ℤ CommRing.toCommSemiring
              (generalLinearCoordinateRing.{0} n) (generalLinearCoordinateRing.{0} n)
              CommRing.toCommSemiring.toAddCommMonoid CommRing.toCommSemiring.toAddCommMonoid
              Algebra.toModule Algebra.toModule
              (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
                (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, k)))
                (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
                  (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (k, j)))) := by
  let h := (pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
      (generalLinearCoordinateRing.{0} n)).inv ≫
    μ[Over.mk (generalLinearStructureMorphismOverIntegers n)].left
  let g := schemeHomRingHomEquiv n h
  let iso := Scheme.ΓSpecIso (.of (generalLinearTensorSquareOverIntegers n))
  let X : Over (Spec (.of ℤ)) := Over.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap ℤ (generalLinearTensorSquareOverIntegers n))))
  let k : X ⟶ Over.mk (generalLinearStructureMorphismOverIntegers n) ⊗
      Over.mk (generalLinearStructureMorphismOverIntegers n) :=
    Over.homMk (pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
      (generalLinearCoordinateRing.{0} n)).inv (by
        rw [Over.tensorObj_hom]
        exact AlgebraicGeometry.specZIsTerminal.hom_ext _ _)
  refine ⟨iso.hom.hom.comp g, eq_specMap_schemeHomRingHomEquiv n h, fun i j => ?_⟩
  have hα : (generalLinearOverRepresentableByOverIntegers n).homEquiv'
      (k ≫ μ[Over.mk (generalLinearStructureMorphismOverIntegers n)]) =
        localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n))))) g := rfl
  have hfst := generalLinearOverIntegers_homEquiv'_of_left_eq_specMap n
    Algebra.TensorProduct.includeLeftRingHom
    (k ≫ fst (Over.mk (generalLinearStructureMorphismOverIntegers n))
      (Over.mk (generalLinearStructureMorphismOverIntegers n)))
    (pullbackSpecIso_inv_fst _ _ _)
  have hsnd := generalLinearOverIntegers_homEquiv'_of_left_eq_specMap n
    Algebra.TensorProduct.includeRight.toRingHom
    (k ≫ snd (Over.mk (generalLinearStructureMorphismOverIntegers n))
      (Over.mk (generalLinearStructureMorphismOverIntegers n)))
    (pullbackSpecIso_inv_snd _ _ _)
  have hval := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n)
      (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n))))) =>
        iso.hom.hom ((z : Matrix (Fin n) (Fin n)
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquareOverIntegers n)))))) i j))
    (generalLinearOverIntegers_homEquiv'_comp_mul n k)
  rw [hα, hfst, hsnd] at hval
  change iso.hom.hom
    (g (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
      (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, j)))) = _
  exact hval.trans (generalLinearTensorSquareOverIntegers_mul_entry n i j)

private lemma includeLeft_mul_includeRight {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] (x : A) (y : B) :
    (Algebra.TensorProduct.includeLeftRingHom x : TensorProduct R A B) *
      Algebra.TensorProduct.includeRight y = x ⊗ₜ[R] y := by
  simp

private lemma determinant_mul_coordinate_hom (n : ℕ)
    (m : generalLinearCoordinateRing.{0} n →+* generalLinearTensorSquareOverIntegers n)
    (hentry : ∀ i j : Fin n,
      m (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
        (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, j))) =
        ∑ k : Fin n,
          @TensorProduct.tmul ℤ CommRing.toCommSemiring
            (generalLinearCoordinateRing.{0} n) (generalLinearCoordinateRing.{0} n)
            CommRing.toCommSemiring.toAddCommMonoid
            CommRing.toCommSemiring.toAddCommMonoid
            Algebra.toModule Algebra.toModule
            (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
              (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (i, k)))
            (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
              (generalLinearCoordinateRing.{0} n) (MvPolynomial.X (k, j)))) :
    m ((algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
      (generalLinearCoordinateRing.{0} n)) (generalLinearDeterminant.{0} n)) =
      Algebra.TensorProduct.includeLeftRingHom
          ((algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
            (generalLinearCoordinateRing.{0} n)) (generalLinearDeterminant.{0} n)) *
        Algebra.TensorProduct.includeRight.toRingHom
          ((algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
            (generalLinearCoordinateRing.{0} n)) (generalLinearDeterminant.{0} n)) := by
  let P := MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ)
  let R := generalLinearCoordinateRing.{0} n
  let B := generalLinearTensorSquareOverIntegers n
  let φ : P →+* B := m.comp (algebraMap P R)
  let inclL : P →+* B := Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap P R)
  let inclR : P →+* B := Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap P R)
  let X : Matrix (Fin n) (Fin n) P := Matrix.mvPolynomialX (Fin n) (Fin n) (ULift.{0} ℤ)
  let A : Matrix (Fin n) (Fin n) B := inclL.mapMatrix X
  let C : Matrix (Fin n) (Fin n) B := inclR.mapMatrix X
  have hmat : φ.mapMatrix X = A * C := by
    ext i j
    change m (algebraMap P R (MvPolynomial.X (i, j))) =
      ∑ k : Fin n, inclL (MvPolynomial.X (i, k)) * inclR (MvPolynomial.X (k, j))
    exact (hentry i j).trans (Finset.sum_congr rfl fun k _ =>
      (includeLeft_mul_includeRight (R := ℤ) (algebraMap P R (MvPolynomial.X (i, k)))
        (algebraMap P R (MvPolynomial.X (k, j)))).symm)
  have hA : A.det = inclL (generalLinearDeterminant.{0} n) := (inclL.map_det X).symm
  have hC : C.det = inclR (generalLinearDeterminant.{0} n) := (inclR.map_det X).symm
  calc
    m (algebraMap P R (generalLinearDeterminant.{0} n)) = Matrix.det (φ.mapMatrix X) :=
      φ.map_det X
    _ = A.det * C.det := by rw [hmat, Matrix.det_mul]
    _ = Algebra.TensorProduct.includeLeftRingHom
          (algebraMap P R (generalLinearDeterminant.{0} n)) *
        Algebra.TensorProduct.includeRight.toRingHom
          (algebraMap P R (generalLinearDeterminant.{0} n)) := by
      rw [hA, hC]
      rfl

/-- The determinant, as a morphism of schemes over `Spec ℤ` from the general linear scheme to
the multiplicative group. -/
noncomputable def determinantOverIntegersHom (n : ℕ) :
    Over.mk (generalLinearStructureMorphismOverIntegers n) ⟶
      multiplicativeGroup.asOver (Spec (.of ℤ)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)))
    (specZIsTerminal.hom_ext _ _)

/-- The unit section of the integral general linear group scheme, as a morphism of schemes. -/
noncomputable def generalLinearUnitSection (n : ℕ) :
    Spec (.of ℤ) ⟶ generalLinearScheme.{0} n :=
  Over.Hom.left
    (((generalLinearOverRepresentableByOverIntegers n).homEquiv'
      (X := 𝟙_ (Over (Spec (.of ℤ))))).symm 1)

/-- The determinant of the generic matrix evaluated at the identity point is one. -/
lemma determinantOverIntegers_one_left (n : ℕ) :
    generalLinearUnitSection n ≫
        Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)) =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom) := by
  apply ext_to_Spec
  dsimp only [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
  ext
  case h₁ x =>
    exact congrArg (fun φ : ℤ →+* _ => φ x) (RingHom.ext_int _ _)
  case h_of =>
    have hpoint := congrArg
      (fun q : CommRingCat.of (generalLinearCoordinateRing.{0} n) ⟶
          Scheme.Γ.obj (op ((𝟙_ (Over (Spec (.of ℤ)))).left)) =>
        CommRingCat.Hom.hom q
          (determinantCoordinateRingHom n (LaurentPolynomial.T 1)))
      (generalLinearRepresentability_symm_appTop n
        (X := 𝟙_ (Over (Spec (.of ℤ)))) (z := 1))
    change (CommRingCat.Hom.hom (Scheme.Hom.appTop (generalLinearUnitSection n)))
        ((CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)))))
          ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of (LaurentPolynomial ℤ))).inv)
            (LaurentPolynomial.T 1))) =
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Spec.map (CommRingCat.ofHom
            (Bialgebra.counitAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom))))
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of (LaurentPolynomial ℤ))).inv)
          (AddMonoidAlgebra.single 1 1))
    rw [specMap_counit_apply_single_one, Scheme.specMap_appTop_ΓSpecIso_inv_apply,
      CommRingCat.hom_ofHom]
    apply hpoint.trans
    change localizedPolynomialHomOfGeneralLinear n _ 1
      (determinantCoordinateRingHom n (LaurentPolynomial.T 1)) = 1
    rw [determinantCoordinateRingHom_T]
    simp only [localizedPolynomialHomOfGeneralLinear, polynomialEvalOfGeneralLinear,
      algebraMap_int_eq, RingEquiv.toRingHom_eq_coe, Units.val_one,
      IsLocalization.Away.lift_eq, MvPolynomial.coe_eval₂Hom, generalLinearDeterminant_eval]
    change Matrix.det
      (1 : Matrix (Fin n) (Fin n) (Scheme.Γ.obj (op (Spec (.of ℤ))))) = 1
    exact Matrix.det_one

/-- The underlying morphism of multiplication on the integral general linear group scheme. -/
noncomputable def generalLinearMulOverIntegersLeft (n : ℕ) :
    pullback (generalLinearStructureMorphismOverIntegers n)
        (generalLinearStructureMorphismOverIntegers n) ⟶ generalLinearScheme.{0} n :=
  μ[Over.mk (generalLinearStructureMorphismOverIntegers n)].left

/-- The underlying morphism of the product of the determinant with itself. -/
noncomputable def determinantOverIntegersTensorLeft (n : ℕ) :
    pullback (generalLinearStructureMorphismOverIntegers n)
        (generalLinearStructureMorphismOverIntegers n) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ)))) :=
  (determinantOverIntegersHom n ⊗ₘ determinantOverIntegersHom n).left

private noncomputable def determinantCoordinateAlgHom (n : ℕ) :
    LaurentPolynomial ℤ →ₐ[ℤ] generalLinearCoordinateRing.{0} n :=
  { __ := determinantCoordinateRingHom n, commutes' z := by simp }

private lemma pullbackSpecIso_inv_comp_determinantOverIntegersTensorLeft (n : ℕ) :
    ((pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
        (generalLinearCoordinateRing.{0} n)).inv ≫ determinantOverIntegersTensorLeft n) ≫
      (pullbackSpecIso ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)).hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (determinantCoordinateAlgHom n)
        (determinantCoordinateAlgHom n)).toRingHom) := by
  rw [← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · change ((pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
          (generalLinearCoordinateRing.{0} n)).inv ≫
        (determinantOverIntegersHom n ⊗ₘ determinantOverIntegersHom n).left) ≫
      pullback.fst _ _ = _
    simp only [Category.assoc]
    rw [Over.tensorHom_left_fst]
    simp only [Over.mk_hom]
    rw [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_fst]
    change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      generalLinearCoordinateRing.{0} n →+*
        generalLinearTensorSquareOverIntegers n)) ≫
      Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (Algebra.TensorProduct.map_comp_includeLeftRingHom (determinantCoordinateAlgHom n)
        (determinantCoordinateAlgHom n)).symm)
  · change ((pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
          (generalLinearCoordinateRing.{0} n)).inv ≫
        (determinantOverIntegersHom n ⊗ₘ determinantOverIntegersHom n).left) ≫
      pullback.snd _ _ = _
    simp only [Category.assoc]
    rw [Over.tensorHom_left_snd]
    simp only [Over.mk_hom]
    rw [pullbackSpecIso_inv_snd_assoc, pullbackSpecIso_inv_snd]
    change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      generalLinearCoordinateRing.{0} n →+*
        generalLinearTensorSquareOverIntegers n)) ≫
      Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight
        (determinantCoordinateAlgHom n) (determinantCoordinateAlgHom n))).symm)

/-- Composing the determinant with itself on a product of generic matrices multiplies the two
determinants. -/
lemma determinantOverIntegers_mul_left (n : ℕ) :
    generalLinearMulOverIntegersLeft n ≫
        Spec.map (CommRingCat.ofHom (determinantCoordinateRingHom n)) =
      determinantOverIntegersTensorLeft n ≫
        (pullbackSpecIso ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)).hom ≫
          Spec.map (CommRingCat.ofHom
            (Bialgebra.comulAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom) := by
  obtain ⟨m, hm, hentry⟩ := generalLinearSchemeGrpObjOverIntegers_mul n
  let g := determinantCoordinateRingHom n
  let p := pullbackSpecIso ℤ (generalLinearCoordinateRing.{0} n)
    (generalLinearCoordinateRing.{0} n)
  let q := pullbackSpecIso ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)
  let t := Algebra.TensorProduct.map (determinantCoordinateAlgHom n)
    (determinantCoordinateAlgHom n)
  have hmul : p.inv ≫ generalLinearMulOverIntegersLeft n = Spec.map (CommRingCat.ofHom m) := hm
  have ht : (p.inv ≫ determinantOverIntegersTensorLeft n) ≫ q.hom =
      Spec.map (CommRingCat.ofHom t.toRingHom) :=
    pullbackSpecIso_inv_comp_determinantOverIntegersTensorLeft n
  apply (cancel_epi p.inv).mp
  rw [← Category.assoc, hmul, ← Category.assoc, ← Category.assoc, ht, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext
  · simp
  · change m (g (LaurentPolynomial.T 1)) =
      t (Coalgebra.comul (R := ℤ) (LaurentPolynomial.T 1))
    rw [LaurentPolynomial.comul_T, Algebra.TensorProduct.map_tmul]
    change m (determinantCoordinateRingHom n (LaurentPolynomial.T 1)) =
      @TensorProduct.tmul ℤ CommRing.toCommSemiring
        (generalLinearCoordinateRing.{0} n) (generalLinearCoordinateRing.{0} n)
        CommRing.toCommSemiring.toAddCommMonoid CommRing.toCommSemiring.toAddCommMonoid
        Algebra.toModule Algebra.toModule
        (determinantCoordinateRingHom n (LaurentPolynomial.T 1))
        (determinantCoordinateRingHom n (LaurentPolynomial.T 1))
    rw [determinantCoordinateRingHom_T, determinant_mul_coordinate_hom n m hentry]
    exact includeLeft_mul_includeRight (R := ℤ) _ _

/-- The determinant as a morphism of group schemes over `Spec ℤ`. -/
@[stacks 022X "det_over_integers"]
noncomputable def determinantGroupSchemeMorphismOverIntegers (n : ℕ) :
    Grp.mk (Over.mk (generalLinearStructureMorphismOverIntegers n)) ⟶
      Grp.mk (multiplicativeGroup.asOver (Spec (.of ℤ))) :=
  Grp.homMk'' (determinantOverIntegersHom n)
    (Over.OverMorphism.ext (determinantOverIntegers_one_left n))
    (Over.OverMorphism.ext (determinantOverIntegers_mul_left n))

/-- On coordinate rings, determinant sends the Laurent variable to the generic determinant. -/
@[stacks 022X "det_over_integers"]
theorem determinantGroupSchemeMorphismOverIntegers_spec (n : ℕ) :
    ∃ g : LaurentPolynomial ℤ →+* generalLinearCoordinateRing.{0} n,
      (determinantGroupSchemeMorphismOverIntegers n).hom.hom.left =
        Spec.map (CommRingCat.ofHom g) ∧
        g (LaurentPolynomial.T 1) =
          algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{0} ℤ))
            (generalLinearCoordinateRing.{0} n) (generalLinearDeterminant.{0} n) :=
  ⟨determinantCoordinateRingHom n, rfl, determinantCoordinateRingHom_T n⟩

end AlgebraicGeometry
