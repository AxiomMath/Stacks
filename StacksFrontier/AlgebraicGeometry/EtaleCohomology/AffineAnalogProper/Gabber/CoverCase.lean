module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.CellCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurve

/-!
# Gabber's theorem for piecewise constant sheaves on an absolutely integrally closed cover

Let `(A, I)` be a henselian pair and `C` an absolutely integrally closed ring integral over `A`,
with `f : Spec C ⟶ Spec A`. If an abelian sheaf `G` on `(Spec C)_étale` is constant with finite
value on each of finitely many basic locally closed sets `V(Lₖ) ∩ D(gₖ)` covering `Spec C`, then
restriction `H^q(Spec A, f_* G) → H^q(Spec (A ⧸ I), (f_* G)|)` is bijective in every degree.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_of_cover`: the
  restriction map on the étale cohomology of `f_* G` is bijective in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
include hI

/-- **Gabber's theorem for the direct image of a piecewise constant sheaf on an absolutely
integrally closed cover.** -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_of_cover
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (hC : IsAbsolutelyIntegrallyClosed C)
    (G : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (pieces : List (List C × C × AddCommGrpCat.{u + 1}))
    (hcover : ∀ x : Spec (.of C), ∃ p ∈ pieces, x ∈ cellSet p.1 p.2.1)
    (hconst : ∀ p ∈ pieces, Finite p.2.2 ∧ IsConstantOnSet G (cellSet p.1 p.2.1) p.2.2)
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj G)
      q) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  have : IsIntegralHom f :=
    IsIntegralHom.SpecMap_iff.mpr fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, 0} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, 0} f
  have : (etaleAbelianDirectImage.{u, 0} f).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).isRightAdjoint
  refine prop_of_isConstantOnSet_cover
    (fun H => ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} f).obj H) q))
    (fun H hH q => bijective_etaleCohomologyRestrictionMap_of_isZero _
      (Functor.map_isZero (etaleAbelianDirectImage.{u, 0} f) hH) q)
    (fun S hS h₁ h₃ q => etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, 0, u + 1} _
      (hS.map_of_exact (etaleAbelianDirectImage.{u, 0} f)) h₁ h₃ q)
    (fun B c E _ H hv hc q =>
      bijective_etaleCohomologyRestrictionMap_directImage_of_cellSet A I hI C hC B c E H hv hc q)
    (piecesMeasure pieces) pieces le_rfl [] 1 G ?_ ?_ q
  · intro p hp
    exact ⟨(hconst p hp).1, (hconst p hp).2.mono Set.inter_subset_right⟩
  · intro W ι _ hd
    have : IsEmpty W := by
      refine ⟨fun w => ?_⟩
      obtain ⟨p, hp, hx⟩ := hcover (ι.base w)
      refine Set.disjoint_left.mp hd ⟨w, rfl⟩ ⟨?_, p, hp, hx⟩
      exact ⟨fun b hb => absurd hb List.not_mem_nil, (ι.base w).isPrime.ne_top ∘
        (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)⟩
    exact isZero_of_isEmpty.{u, 0} _

end Stacks.EtaleCohomology
