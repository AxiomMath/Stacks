module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.Vanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.DegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.DirectImageAcyclic

/-!
# Gabber's theorem for the direct image of a finite constant sheaf from an absolutely integrally
closed cover

Let `(A, I)` be a henselian pair, `X = Spec A`, `i : Z = Spec (A ⧸ I) ⟶ X`, and let `C` be an
absolutely integrally closed ring which is integral over `A`, with `g : Spec C ⟶ X`. For a finite
abelian group `M` the restriction map

`H^q(X, g_* M) → H^q(Z, (g_* M)|_Z)`

is bijective in every degree.

## Main results

* `Stacks.EtaleCohomology.isAbsolutelyIntegrallyClosed_tensor_quotient`: `C ⊗_A A/I` is absolutely
  integrally closed when `C` is.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_constant`: the
  restriction map `H^q(X, g_* M) → H^q(Z, (g_* M)|_Z)` is bijective for every `q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.EtaleCohomology

/-- `C ⊗_A A/I` is absolutely integrally closed when `C` is. -/
theorem isAbsolutelyIntegrallyClosed_tensor_quotient {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (I : Ideal A) (hC : IsAbsolutelyIntegrallyClosed C) :
    IsAbsolutelyIntegrallyClosed (C ⊗[A] (A ⧸ I)) :=
  isAbsolutelyIntegrallyClosed_of_surjective
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingHom.comp
      (Ideal.Quotient.mk (I.map (algebraMap A C))))
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).surjective.comp
      Ideal.Quotient.mk_surjective) hC

/-- **Gabber's theorem for the direct image of a finite constant sheaf from an absolutely
integrally closed integral cover.** For a henselian pair `(A, I)`, an absolutely integrally closed
ring `C` integral over `A` with `g : Spec C ⟶ Spec A`, and a finite abelian group `M`, the
restriction map `H^q(Spec A, g_* M) → H^q(Spec (A ⧸ I), (g_* M)|_{Spec (A ⧸ I)})` is bijective for
every `q`. -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_constant
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (hC : IsAbsolutelyIntegrallyClosed C) (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj
        ((constantSheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair A I hI _
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
    IsIntegralHom.SpecMap_iff.mpr fun x ↦ Algebra.IsIntegral.isIntegral (R := A) x
  exact bijective_etaleCohomologyRestrictionMap_directImage_of_subsingleton _ _ _ _
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct A C (A ⧸ I))).flip _ q
    (AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf_smallEtale hC M q hq)
    (subsingleton_sheafH_iso (((etaleAbelianInverseImageConstantIso.{u, 0} _).app M).symm) q
      (AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf_smallEtale
        (R := C ⊗[A] (A ⧸ I)) (isAbsolutelyIntegrallyClosed_tensor_quotient I hC) M q hq))

end Stacks.EtaleCohomology
