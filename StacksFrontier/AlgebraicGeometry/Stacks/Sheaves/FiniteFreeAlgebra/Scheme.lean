module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# The scheme of finite free algebra structures

For a positive integer `d`, the structure constants of a commutative, associative
multiplication on a free module of rank `d`, with its first basis vector as unit, are
represented by an affine scheme. Its points over an arbitrary scheme are naturally the
corresponding algebra structures over the ring of global sections.

The representing ring is the polynomial ring on the structure constants `a i j k`, modulo the
associativity, commutativity and unit relations.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra`: a free `d`-dimensional commutative algebra, recorded
  by its structure constants.
* `AlgebraicGeometry.FiniteFreeAlgebra.map`: extension of scalars of structure constants.
* `AlgebraicGeometry.FiniteFreeAlgebra.CoeffIndex`: the index type of a structure constant.
* `AlgebraicGeometry.FiniteFreeAlgebra.universalCoeff`: a universal structure constant, as a
  polynomial variable.
* `AlgebraicGeometry.FiniteFreeAlgebra.universalRelations`: the defining polynomial relations.
* `AlgebraicGeometry.FiniteFreeAlgebra.universalRing`: the universal ring.
* `AlgebraicGeometry.FiniteFreeAlgebra.scheme`: the spectrum of the universal ring.
* `AlgebraicGeometry.FiniteFreeAlgebra.Representation`: the pointwise identification together
  with its naturality.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.representation`: points of the universal scheme over `T`
  are free `d`-dimensional algebras over `Γ(T, 𝒪_T)`, naturally in `T`.

## Implementation notes

A free algebra structure is recorded by coefficients `a i j k`; its multiplication sends the
pair of basis vectors `(i, j)` to `∑ k, a i j k e k`. The universal ring is lifted into the
universe of the test schemes before applying `Spec`, so the representation applies in any scheme
universe.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The structure constants of a commutative, associative algebra on `R ^ d` whose first
standard basis vector is the multiplicative unit. -/
structure FiniteFreeAlgebra (R : Type*) [CommRing R] (d : ℕ) [NeZero d] where
  /-- The coefficient of the `k`th basis vector in the product of the `i`th and `j`th basis
  vectors. -/
  coeff : Fin d → Fin d → Fin d → R
  /-- The multiplication is associative. -/
  assoc : ∀ i j k m,
    ∑ l, coeff i j l * coeff l k m = ∑ l, coeff i l m * coeff j k l
  /-- The multiplication is commutative. -/
  comm : ∀ i j k, coeff i j k = coeff j i k
  /-- The first basis vector is the multiplicative unit. -/
  unit_coeff : ∀ i j, coeff i 0 j = if i = j then 1 else 0

namespace FiniteFreeAlgebra

/-- Extension of scalars of structure constants along a ring homomorphism. -/
@[simps]
def map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (m : FiniteFreeAlgebra R d) : FiniteFreeAlgebra S d where
  coeff i j k := f (m.coeff i j k)
  assoc i j k n := by
    simpa only [map_sum, map_mul] using congrArg f (m.assoc i j k n)
  comm i j k := congrArg f (m.comm i j k)
  unit_coeff i j := by simp [m.unit_coeff]

variable (d : ℕ) [NeZero d]

/-- An index for a universal structure coefficient `a i j k`. -/
abbrev CoeffIndex := Fin d × Fin d × Fin d

/-- A variable in the polynomial ring of universal structure constants. -/
abbrev universalCoeff (i j k : Fin d) : MvPolynomial (CoeffIndex d) ℤ :=
  MvPolynomial.X (i, j, k)

/-- The polynomial relations expressing associativity, commutativity, and that the first basis
vector is the unit. -/
def universalRelations : Set (MvPolynomial (CoeffIndex d) ℤ) :=
  {p | ∃ i j k m, p =
      (∑ l, universalCoeff d i j l * universalCoeff d l k m) -
        ∑ l, universalCoeff d i l m * universalCoeff d j k l} ∪
  {p | ∃ i j k, p = universalCoeff d i j k - universalCoeff d j i k} ∪
  {p | ∃ i j, p = universalCoeff d i 0 j -
      MvPolynomial.C (if i = j then 1 else 0)}

/-- The universal ring carrying a free `d`-dimensional commutative algebra structure with the
first basis vector as unit. -/
abbrev universalRing :=
  MvPolynomial (CoeffIndex d) ℤ ⧸ Ideal.span (universalRelations d)

/-- The affine scheme representing free `d`-dimensional algebra structures. -/
abbrev scheme : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (.of (ULift.{u} (universalRing d)))

/-- The natural form of the equation identifying points of the universal scheme with free
algebra structures over global sections. -/
structure Representation where
  /-- The identification on a scheme `T`. -/
  equiv (T : AlgebraicGeometry.Scheme.{u}) :
    (T ⟶ scheme d) ≃ FiniteFreeAlgebra Γ(T, ⊤) d
  /-- The identification commutes with pullback along morphisms of schemes. -/
  naturality {T U : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ U) (x : U ⟶ scheme d) :
    FiniteFreeAlgebra.map f.appTop.hom (equiv U x) = equiv T (f ≫ x)

/-- Points of the scheme of structure constants over `T` are naturally free
`d`-dimensional algebras over `Γ(T, 𝒪_T)`. -/
@[stacks 05YM]
noncomputable def representation : Representation.{u} d := by
  classical
  let relIdeal : Ideal (MvPolynomial (CoeffIndex d) ℤ) := Ideal.span (universalRelations d)
  let mkStructure (R : Type u) [CommRing R] (m : FiniteFreeAlgebra R d) :
      universalRing d →+* R := by
    let e : MvPolynomial (CoeffIndex d) ℤ →+* R :=
      MvPolynomial.eval₂Hom (algebraMap ℤ R) (fun q => m.coeff q.1 q.2.1 q.2.2)
    have he : ∀ a ∈ relIdeal, e a = 0 := by
      change Ideal.span (universalRelations d) ≤ RingHom.ker e
      refine Ideal.span_le.2 fun p hp => ?_
      rcases hp with (⟨i, j, k, n, rfl⟩ | ⟨i, j, k, rfl⟩) | ⟨i, j, rfl⟩
      · change e ((∑ l, universalCoeff d i j l * universalCoeff d l k n) -
          ∑ l, universalCoeff d i l n * universalCoeff d j k l) = 0
        simpa [e, universalCoeff] using sub_eq_zero.mpr (m.assoc i j k n)
      · change e (universalCoeff d i j k - universalCoeff d j i k) = 0
        simpa [e, universalCoeff] using sub_eq_zero.mpr (m.comm i j k)
      · change e (universalCoeff d i 0 j - MvPolynomial.C (if i = j then 1 else 0)) = 0
        dsimp [e]
        rcases eq_or_ne i j with rfl | hij
        · simpa [e, universalCoeff, MvPolynomial.eval₂Hom] using
            sub_eq_zero.mpr (m.unit_coeff i i)
        · simpa [hij, e, universalCoeff, MvPolynomial.eval₂Hom] using
            sub_eq_zero.mpr (m.unit_coeff i j)
    exact Ideal.Quotient.lift relIdeal e he
  let toStructure (T : AlgebraicGeometry.Scheme.{u}) (x : T ⟶ scheme d) :
      FiniteFreeAlgebra Γ(T, ⊤) d := by
    let φ : universalRing d →+* Γ(T, ⊤) :=
      x.appTop.hom.comp
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of
          (ULift.{u} (universalRing d)))).inv.hom.comp ULift.ringEquiv.symm.toRingHom)
    refine {
      coeff := fun i j k => φ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j, k)))
      assoc := ?_
      comm := ?_
      unit_coeff := ?_ }
    · intro i j k n
      have h : Ideal.Quotient.mk relIdeal
          ((∑ l, universalCoeff d i j l * universalCoeff d l k n) -
            ∑ l, universalCoeff d i l n * universalCoeff d j k l) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Or.inl (Or.inl ⟨i, j, k, n, rfl⟩)))
      exact sub_eq_zero.mp (by simpa [φ, universalRing, universalCoeff] using congrArg φ h)
    · intro i j k
      have h : Ideal.Quotient.mk relIdeal
          (universalCoeff d i j k - universalCoeff d j i k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Or.inl (Or.inr ⟨i, j, k, rfl⟩)))
      exact sub_eq_zero.mp (by simpa [φ, universalRing, universalCoeff] using congrArg φ h)
    · intro i j
      have h : Ideal.Quotient.mk relIdeal
          (universalCoeff d i 0 j - MvPolynomial.C (if i = j then 1 else 0)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨i, j, rfl⟩))
      exact sub_eq_zero.mp (by simpa [φ, universalRing, universalCoeff] using congrArg φ h)
  have ext_coeff : ∀ {R : Type u} [CommRing R] {m n : FiniteFreeAlgebra R d},
      (∀ i j k, m.coeff i j k = n.coeff i j k) → m = n := by
    intro R _ m n h
    cases m; cases n; congr 1; funext i j k; exact h i j k
  refine {
    equiv := fun T => {
      toFun := fun x => toStructure T x
      invFun := fun m =>
        (AlgebraicGeometry.ΓSpec.adjunction.homEquiv T
          (Opposite.op (CommRingCat.of (ULift.{u} (universalRing d)))))
          ((CommRingCat.ofHom ((mkStructure _ m).comp ULift.ringEquiv.toRingHom)).op)
      left_inv := ?_
      right_inv := ?_ }
    naturality := ?_ }
  · intro x
    let E := AlgebraicGeometry.ΓSpec.adjunction.homEquiv T
      (Opposite.op (CommRingCat.of (ULift.{u} (universalRing d))))
    rw [← E.apply_symm_apply x]
    let q : CommRingCat.of (ULift.{u} (universalRing d)) ⟶ CommRingCat.of Γ(T, ⊤) :=
      CommRingCat.ofHom ((mkStructure _ (toStructure T (E (E.symm x)))).comp
        ULift.ringEquiv.toRingHom)
    change E q.op = E (E.symm x)
    congr 1
    apply Quiver.Hom.unop_inj
    apply CommRingCat.hom_ext
    have hup : Function.Surjective (ULift.ringEquiv.symm.toRingHom :
        universalRing d →+* ULift.{u} (universalRing d)) := by
      rintro ⟨x⟩
      exact ⟨x, rfl⟩
    apply (RingHom.cancel_right hup).mp
    apply Ideal.Quotient.ringHom_ext
    have h := AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (X := T) (B := CommRingCat.of (ULift.{u} (universalRing d)))
      (φ := (E.symm x).unop)
    have hh := congrArg (fun g => g.hom) h
    dsimp [q]
    change (mkStructure _ (toStructure T (E (E.symm x)))).comp
      (Ideal.Quotient.mk relIdeal) = _
    calc
      _ = _ := Ideal.Quotient.lift_comp_mk relIdeal _ _
      _ = _ := by
        apply MvPolynomial.ringHom_ext
        · intro z
          simp
        · intro q'
          simpa [toStructure, universalCoeff, universalRing, E, ULift.ringEquiv] using
            congrArg (fun g => g (ULift.up (Ideal.Quotient.mk relIdeal (MvPolynomial.X q')))) hh
  · intro m
    let E := AlgebraicGeometry.ΓSpec.adjunction.homEquiv T
      (Opposite.op (CommRingCat.of (ULift.{u} (universalRing d))))
    apply ext_coeff
    intro i j k
    change (toStructure T
      (E (CommRingCat.ofHom ((mkStructure _ m).comp ULift.ringEquiv.toRingHom)).op)).coeff
        i j k = m.coeff i j k
    have h := AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (X := T) (B := CommRingCat.of (ULift.{u} (universalRing d)))
      (φ := CommRingCat.ofHom ((mkStructure _ m).comp ULift.ringEquiv.toRingHom))
    have hx := congrArg (fun g => g.hom
      (ULift.up (Ideal.Quotient.mk relIdeal (MvPolynomial.X (i, j, k))))) h
    simpa [toStructure, mkStructure, universalRing, E, ULift.ringEquiv] using hx
  · exact fun f x => ext_coeff fun i j k => rfl

end FiniteFreeAlgebra

end

end AlgebraicGeometry

end
