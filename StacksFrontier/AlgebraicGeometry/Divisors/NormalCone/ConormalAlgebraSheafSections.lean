module

public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedAlgebra
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading

/-!
# The sections of the conormal algebra sheaf over an affine chart

Let `i : Z ⟶ X` be an immersion of schemes and let `U = Spec R ⊆ X` be an affine open over
which `i` restricts to a closed immersion, with `I ⊆ R` the kernel of `R ⟶ Γ(Z, i⁻¹U)`. The
degree-`n` sections of the conormal algebra `𝒞_{Z/X,*}` over `i⁻¹U` are `Iⁿ/Iⁿ⁺¹`
(Stacks 0633, `AlgebraicGeometry.affineSectionsEquiv`). This file assembles the degrees: the ring
of sections over `i⁻¹U` of the sheaf of commutative `𝒪_Z`-algebras
`Stacks.Conormal.conormalAlgebraSheaf i`, the ungraded realization of `𝒞_{Z/X,*}`, is the
associated graded ring

`Gr_I(R) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹ ≅ Γ(i⁻¹U, 𝒞_{Z/X,*})`,

carrying the class of `a ∈ Iⁿ` to the homogeneous section it names, the degree-zero class of
`r ∈ R` to the image of `r` under `𝒪_X(U) ⟶ 𝒪_Z(i⁻¹U) ⟶ 𝒞_{Z/X,*}(i⁻¹U)`, and the map of
associated graded rings induced by a restriction `R = Γ(X, U) ⟶ Γ(X, V)` to the restriction of
sections from `i⁻¹U` to `i⁻¹V`.

## Main definitions

* `AssociatedGraded.gradedRingMapOfRingHom`: the map `Gr_I(A) ⟶ Gr_{I'}(B)` of associated graded
  rings induced by a ring homomorphism `f : A ⟶ B` with `f(I) ⊆ I'`.
* `Stacks.Conormal.gradedSectionsHom`: the ring homomorphism from `Gr_I(R)` to the direct sum of
  the sections over `i⁻¹U` of the homogeneous pieces of `𝒞_{Z/X,*}`, which is
  `AlgebraicGeometry.affineSectionsEquiv` in each degree.
* `Stacks.Conormal.conormalAlgebraSheafSectionsEquiv`: **the identification
  `Gr_I(R) ≅ Γ(i⁻¹U, 𝒞_{Z/X,*})` as rings.**

## Main results

* `Stacks.Conormal.bijective_gradedSectionsHom`: `gradedSectionsHom` is bijective.
* `Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_mk`: on homogeneous classes the
  identification is the canonical local map of Stacks 0630.
* `Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_gradeZeroMk`: on degree-zero classes it is
  the structure map of `𝒞_{Z/X,*}` composed with the map on sections of `i`.
* `Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_restrict`: it commutes with restriction to a
  smaller chart.

## Implementation notes

Three identifications are composed. In each degree, `AlgebraicGeometry.affineSectionsEquiv`
identifies `Iⁿ/Iⁿ⁺¹` with the sections of the degree-`n` piece; over the degrees, the sections
of the ungraded realization over an affine open are the direct sum of the sections of the pieces,
which is `Stacks.RelativeSpec.totalSectionsRingEquiv`, applicable because `i⁻¹U` is affine; and
the negative pieces of `𝒞_{Z/X,*}` vanish, so that the direct sum over `ℕ` is the direct sum over
`ℤ` (`Stacks.bijective_directSumNatToIntApp`). Multiplicativity is proved on the source by
`DirectSum.toSemiring`, from the multiplicativity and unitality of the degreewise identification.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-! ### The map of associated graded rings induced by a ring homomorphism -/

namespace AssociatedGraded

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The map of associated graded rings `Gr_I(A) ⟶ Gr_{I'}(B)` induced by a ring homomorphism
`f : A ⟶ B` carrying `I` into `I'`**: in degree `n` it is `AssociatedGraded.pieceMapOfRingHom`,
the class of `a ∈ Iⁿ` going to the class of `f a ∈ I'ⁿ`. -/
def gradedRingMapOfRingHom (f : A →+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map f ≤ I') :
    gradedRing I →+* gradedRing I' :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun m => piece (M := B) I' m) n).comp (pieceMapOfRingHom f hI n))
    (congrArg (DirectSum.of (fun m => piece (M := B) I' m) 0)
      (pieceMapOfRingHom_homogeneousOne f hI))
    (fun {i j} x y =>
      (congrArg (DirectSum.of (fun m => piece (M := B) I' m) (i + j))
        (pieceMapOfRingHom_homogeneousMul f hI i j x y)).trans
        (of_mul_of I' (pieceMapOfRingHom f hI i x) (pieceMapOfRingHom f hI j y)).symm)

/-- On the degree-`n` summand, `gradedRingMapOfRingHom f hI` is `pieceMapOfRingHom f hI n`. -/
@[simp]
theorem gradedRingMapOfRingHom_of (f : A →+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map f ≤ I')
    (n : ℕ) (x : piece (M := A) I n) :
    gradedRingMapOfRingHom f hI (DirectSum.of (fun m => piece (M := A) I m) n x) =
      DirectSum.of (fun m => piece (M := B) I' m) n (pieceMapOfRingHom f hI n x) :=
  DirectSum.toSemiring_of _ _ _ n x

end AssociatedGraded

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
  (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))

/-- **Restriction to a smaller affine chart carries the kernel ideal into the kernel ideal**, in
the form `I_U · Γ(X, V) ⊆ I_V` of an inclusion of ideals. -/
theorem map_chartIdeal_le {U V : X.affineOpens} (hVU : V.1 ≤ U.1) :
    (chartIdeal i U).map (X.presheaf.map (homOfLE hVU).op).hom ≤ chartIdeal i V :=
  Ideal.map_le_iff_le_comap.2 fun _ hx => map_mem_chartIdeal i hVU hx

/-! ### The direct sum of the sections of the homogeneous pieces -/

/-- The degree-`n` identification `Iⁿ/Iⁿ⁺¹ ≅ 𝒞_{Z/X,n}(i⁻¹U)` followed by the inclusion of the
degree-`n` summand of the direct sum of the sections of the homogeneous pieces. -/
def pieceSectionIncl (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) n →+
      (conormalAlgebra i).algebra.toPresheafGradedAlgebra.Total (op (i ⁻¹ᵁ U.1)) :=
  (DirectSum.of (fun m : ℤ =>
      (((conormalAlgebra i).algebra.piece m).val.obj (op (i ⁻¹ᵁ U.1)) : Type u)) (n : ℤ)).comp
    ((affineSectionsEquiv i U hU).equiv n).toAddMonoidHom

/-- `pieceSectionIncl` sends `x ∈ Iⁿ/Iⁿ⁺¹` to the degree-`n` inclusion of its image under the
degree-`n` identification. -/
theorem pieceSectionIncl_apply (n : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) n) :
    pieceSectionIncl i U hU n x =
      (conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl (n : ℤ)
        ((affineSectionsEquiv i U hU).equiv n x) :=
  rfl

/-- **The degreewise identification, as a ring homomorphism** out of the associated graded ring
`Gr_I(Γ(X, U))` into the direct sum of the sections over `i⁻¹U` of the homogeneous pieces of the
conormal algebra. -/
def gradedSectionsHom : AssociatedGraded.gradedRing (chartIdeal i U) →+*
    (conormalAlgebra i).algebra.toPresheafGradedAlgebra.Total (op (i ⁻¹ᵁ U.1)) :=
  DirectSum.toSemiring (pieceSectionIncl i U hU)
    ((congrArg (DirectSum.of (fun m : ℤ =>
        (((conormalAlgebra i).algebra.piece m).val.obj (op (i ⁻¹ᵁ U.1)) : Type u)) 0)
        (affineSectionsEquiv i U hU).map_one).trans
      ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.one_eq_incl (op (i ⁻¹ᵁ U.1))).symm)
    (fun {n m} a b =>
      ((congrArg (DirectSum.of (fun k : ℤ =>
          (((conormalAlgebra i).algebra.piece k).val.obj (op (i ⁻¹ᵁ U.1)) : Type u)) _)
          ((affineSectionsEquiv i U hU).map_mul n m a b)).trans
        ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl_mul_incl (n : ℤ) (m : ℤ)
          _ _).symm))

/-- On the degree-`n` summand of `Gr_I(Γ(X, U))`, `gradedSectionsHom` is `pieceSectionIncl`. -/
theorem gradedSectionsHom_of (n : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) n) :
    gradedSectionsHom i U hU
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) n x) =
      pieceSectionIncl i U hU n x :=
  DirectSum.toSemiring_of _ _ _ n x

/-- `gradedSectionsHom` is the degreewise identification over the nonnegative degrees, followed
by the inclusion of the nonnegative degrees into all degrees. -/
theorem gradedSectionsHom_apply_eq (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    gradedSectionsHom i U hU z =
      directSumNatToIntApp (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val)
        (op (i ⁻¹ᵁ U.1))
        (DFinsupp.mapRange.addEquiv (fun n => (affineSectionsEquiv i U hU).equiv n) z) := by
  induction z using DirectSum.induction_on with
  | zero =>
      exact (map_zero (gradedSectionsHom i U hU)).trans
        ((congrArg (directSumNatToIntApp (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val)
            (op (i ⁻¹ᵁ U.1))) (map_zero _)).trans (map_zero _)).symm
  | of n x =>
      have hmap : DFinsupp.mapRange.addEquiv (fun n => (affineSectionsEquiv i U hU).equiv n)
          (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) n x) =
          DirectSum.of (fun k : ℕ =>
            (((conormalAlgebra i).algebra.piece (k : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) : Type u)) n
            ((affineSectionsEquiv i U hU).equiv n x) :=
        DFinsupp.mapRange_single (hf := fun k => ((affineSectionsEquiv i U hU).equiv k).map_zero)
      exact (gradedSectionsHom_of i U hU n x).trans
        ((directSumNatToIntApp_of (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val)
          (op (i ⁻¹ᵁ U.1)) n ((affineSectionsEquiv i U hU).equiv n x)).symm.trans
          (congrArg (directSumNatToIntApp (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val)
            (op (i ⁻¹ᵁ U.1))) hmap.symm))
  | add z z' hz hz' =>
      exact (map_add (gradedSectionsHom i U hU) z z').trans
        ((congrArg₂ (· + ·) hz hz').trans
          ((congrArg (directSumNatToIntApp (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val)
              (op (i ⁻¹ᵁ U.1))) (map_add _ z z')).trans (map_add _ _ _)).symm)

/-- **The associated graded ring is the direct sum of the sections of the homogeneous pieces**:
the degreewise identification is bijective, and the negative degrees contribute nothing because
the negative pieces of the conormal algebra vanish. -/
theorem bijective_gradedSectionsHom : Function.Bijective (gradedSectionsHom i U hU) := by
  have hzero : ∀ n : ℤ, n < 0 →
      Subsingleton (((conormalAlgebra i).algebra.piece n).val.obj (op (i ⁻¹ᵁ U.1))) :=
    fun n hn => ⟨fun a b => ((conormalAlgebra i).eq_zero_of_neg n hn _ a).trans
      ((conormalAlgebra i).eq_zero_of_neg n hn _ b).symm⟩
  have hcomp := (bijective_directSumNatToIntApp
      (fun m : ℤ => ((conormalAlgebra i).algebra.piece m).val) (op (i ⁻¹ᵁ U.1)) hzero).comp
    (DFinsupp.mapRange.addEquiv (fun n => (affineSectionsEquiv i U hU).equiv n)).bijective
  exact (funext fun z => gradedSectionsHom_apply_eq i U hU z) ▸ hcomp

/-! ### The ring of sections over the chart -/

/-- **The ring of sections of the conormal algebra sheaf over an affine closed-immersion chart is
the associated graded ring**: for `U ⊆ X` an affine open over which the immersion `i` restricts to
a closed immersion, with `I` the kernel of `Γ(X, U) ⟶ Γ(Z, i⁻¹U)`,
`Gr_I(Γ(X, U)) ≅ Γ(i⁻¹U, 𝒞_{Z/X,*})` as rings. -/
def conormalAlgebraSheafSectionsEquiv :
    AssociatedGraded.gradedRing (chartIdeal i U) ≃+*
      (conormalAlgebraSheaf i).right.obj.obj (op (i ⁻¹ᵁ U.1)) :=
  (RingEquiv.ofBijective (gradedSectionsHom i U hU) (bijective_gradedSectionsHom i U hU)).trans
    (Stacks.RelativeSpec.totalSectionsRingEquiv Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int
      (coborderAffineChart_preimage i U hU ▸
        (coborderAffineChart i U hU).2.preimage i.liftCoborder))

/-- **On homogeneous classes the identification is the canonical local map** of Stacks 0630: the
class of `a ∈ Iⁿ` goes to the homogeneous section of degree `n` it names, viewed in the ungraded
realization. -/
theorem conormalAlgebraSheafSectionsEquiv_of_mk (n : ℕ) (a : Γ(X, U))
    (ha : a ∈ chartIdeal i U ^ n) :
    conormalAlgebraSheafSectionsEquiv i U hU
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) n
          (AssociatedGraded.mk (chartIdeal i U) n ⟨a, by simpa using ha⟩)) =
      (conormalAlgebra i).algebra.ungradedIncl (n : ℤ)
        ((conormalAlgebra i).localMap U hU n ⟨a, ha⟩) :=
  congrArg ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.totalUnit
      (Opens.grothendieckTopology Z) (op (i ⁻¹ᵁ U.1)))
    ((gradedSectionsHom_of i U hU n _).trans
      (congrArg ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl (n : ℤ))
        ((affineSectionsEquiv i U hU).map_mk n ⟨a, by simpa using ha⟩)))

/-- **On degree-zero classes the identification is the structure map**: the class of
`r ∈ Γ(X, U)` in `I⁰/I¹` goes to the image of `r` under
`𝒪_X(U) ⟶ 𝒪_Z(i⁻¹U) ⟶ 𝒞_{Z/X,*}(i⁻¹U)`. -/
theorem conormalAlgebraSheafSectionsEquiv_of_gradeZeroMk (r : Γ(X, U)) :
    conormalAlgebraSheafSectionsEquiv i U hU
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) 0
          (AssociatedGraded.gradeZeroMk (chartIdeal i U) r)) =
      ((conormalAlgebraSheaf i).hom.hom.app (op (i ⁻¹ᵁ U.1))).hom ((i.app U).hom r) := by
  have hmk : AssociatedGraded.gradeZeroMk (chartIdeal i U) r =
      r • (GradedMonoid.GOne.one :
        AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) 0) :=
    congrArg (AssociatedGraded.mk (chartIdeal i U) 0) (Subtype.ext (mul_one r).symm)
  have h : gradedSectionsHom i U hU
      (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) 0
        (AssociatedGraded.gradeZeroMk (chartIdeal i U) r)) =
      (conormalAlgebra i).algebra.toPresheafGradedAlgebra.structureMap (op (i ⁻¹ᵁ U.1))
        ((i.app U).hom r) :=
    ((gradedSectionsHom_of i U hU 0 _).trans (pieceSectionIncl_apply i U hU 0 _)).trans
      ((congrArg ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl (0 : ℤ))
        ((congrArg ((affineSectionsEquiv i U hU).equiv 0) hmk).trans
          (((affineSectionsEquiv i U hU).map_smul 0 r _).trans
            (congrArg (fun y => (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from
              (i.app U).hom r) • y) (affineSectionsEquiv i U hU).map_one)))).trans
        ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl_smul (0 : ℤ) _ _))
  exact congrArg ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.totalUnit
    (Opens.grothendieckTopology Z) (op (i ⁻¹ᵁ U.1))) h

/-- **The identification commutes with restriction between charts**: for affine charts
`V ⊆ U`, restricting sections of the conormal algebra sheaf from `i⁻¹U` to `i⁻¹V` corresponds to
the map `Gr_{I_U}(Γ(X, U)) ⟶ Gr_{I_V}(Γ(X, V))` induced by the restriction
`Γ(X, U) ⟶ Γ(X, V)`. -/
theorem conormalAlgebraSheafSectionsEquiv_restrict (V : X.affineOpens)
    (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) (hVU : V.1 ≤ U.1)
    (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    ((conormalAlgebraSheaf i).right.obj.map (homOfLE (i.preimage_mono hVU)).op).hom
        (conormalAlgebraSheafSectionsEquiv i U hU z) =
      conormalAlgebraSheafSectionsEquiv i V hV
        (AssociatedGraded.gradedRingMapOfRingHom (X.presheaf.map (homOfLE hVU).op).hom
          (map_chartIdeal_le i hVU) z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      induction x using Submodule.Quotient.induction_on with
      | _ a =>
        have ha : (a : Γ(X, U)) ∈ chartIdeal i U ^ n := by simpa using a.2
        have hb : X.presheaf.map (homOfLE hVU).op (a : Γ(X, U)) ∈ chartIdeal i V ^ n :=
          map_mem_chartIdeal_pow i hVU n ha
        have hl := conormalAlgebraSheafSectionsEquiv_of_mk i U hU n a ha
        have hr := conormalAlgebraSheafSectionsEquiv_of_mk i V hV n _ hb
        rw [AssociatedGraded.gradedRingMapOfRingHom_of]
        refine Eq.trans ?_ ((congrArg (conormalAlgebraSheafSectionsEquiv i V hV) rfl).trans hr).symm
        refine (congrArg _ hl).trans ?_
        refine ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.totalSheafRestrict_inclSheaf
          (Opens.grothendieckTopology Z) (homOfLE (i.preimage_mono hVU)).op (n : ℤ) _).trans ?_
        exact congrArg ((conormalAlgebra i).algebra.toPresheafGradedAlgebra.inclSheaf
          (Opens.grothendieckTopology Z) (n : ℤ))
          ((conormalAlgebra i).localMap_naturality U V hVU (i.preimage_mono hVU) hU hV n
            ⟨a, ha⟩ ⟨_, hb⟩ rfl)
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Stacks.Conormal

end
