module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.BasePointIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DiscreteValuationStalk

/-!
# Smoothness over an affine base from a formally smooth localization of the base ring

`AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_localRingHom` asks for a model `A_p → B_q` of
the stalk map of `f` at `x`, and therefore for the prime `p` of `A`, for an identification of the
local ring of the base, and for a compatibility between the two identifications.  **Over an
affine base all three are determined by the identification upstairs**: `p` is the contraction of
`q`, the local ring of `Spec R` at the image point is the localization of `R` there, and the
compatibility is the statement — already part of the identification upstairs — that the germ of
a section of `R` is the image of its value.

So the criterion takes the shape used at a generic point of a fibre in the reduced fibre
theorem: a morphism to an affine scheme, a presentation of the local ring upstairs as a
localization of a ring `T` over `R` compatible with the germ, and adic formal smoothness of
`R_{q ∩ R} → T_q`.

## Main results

* `AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ`: the affine-base
  form of the local smoothness criterion.

## Implementation notes

The identification of the local ring downstairs is the composite of
`IsLocalization.algEquiv` — available because the contraction of `q` has the same complement as
the prime of the image point, by
`AlgebraicGeometry.asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime` — with
`AlgebraicGeometry.Spec.stalkIso`.  Both commute with the structure map of `R`, which is what
makes the compatibility hypothesis `hbase` of the general criterion a consequence of the one
compatibility hypothesis here.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **Smoothness at a point of a scheme over an affine base, from an adically formally smooth
localization of the base ring.**  Let `g : Y ⟶ Spec R` be flat and locally of finite
presentation, let `y` be a point at which both local rings are discrete valuation rings, and
suppose `𝒪_{Y, y}` is identified with the localization of an `R`-algebra `T` at a prime `q`, by
an isomorphism carrying the germ of a section of `R` to the image of its value.  If
`R_{q ∩ R} → T_q` is formally smooth for the maximal-ideal-adic topology of `T_q`, then `g` is
smooth at `y`.

This is `AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_localRingHom` with the data about the
base supplied: the prime below is the contraction of `q`
(`AlgebraicGeometry.asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime`), and the local ring
of `Spec R` there is the localization of `R`. -/
theorem smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ {R : CommRingCat.{u}}
    {Y : Scheme.{u}} (g : Y ⟶ Spec R) [LocallyOfFinitePresentation g] [Flat g] (y : Y)
    [IsDomain ((Spec R).presheaf.stalk (g.base y))]
    [IsDiscreteValuationRing ((Spec R).presheaf.stalk (g.base y))]
    [IsDomain (Y.presheaf.stalk y)] [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    {T : Type v} [CommRing T] [Algebra R T] {q : Ideal T} [q.IsPrime]
    (φ : Y.presheaf.stalk y ≃+* Localization.AtPrime q)
    (hφ : ∀ r : R, φ (((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫
        Y.presheaf.germ ⊤ y trivial).hom r) =
      algebraMap T (Localization.AtPrime q) (algebraMap R T r))
    (hsm : RingHom.FormallySmoothNAdic.{u, u, v}
      (Localization.localRingHom (q.comap (algebraMap R T)) q (algebraMap R T) rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    InfinitesimalLifting.SmoothAt g y := by
  have : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
  have : (q.comap (algebraMap R T)).IsPrime := Ideal.IsPrime.comap _
  have hp : (g.base y).asIdeal = q.comap (algebraMap R T) :=
    asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime g y q (algebraMap R T) φ hφ
  have hpc : (q.comap (algebraMap R T)).primeCompl = (g.base y).asIdeal.primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hp]
  have : IsLocalization (q.comap (algebraMap R T)).primeCompl
      (Localization.AtPrime (g.base y).asIdeal) := by
    rw [hpc]
    infer_instance
  let eloc : Localization.AtPrime (q.comap (algebraMap R T)) ≃ₐ[R]
      Localization.AtPrime (g.base y).asIdeal :=
    IsLocalization.algEquiv (q.comap (algebraMap R T)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap R T)))
      (Localization.AtPrime (g.base y).asIdeal)
  refine smoothAt_of_formallySmoothNAdic_localRingHom g y rfl
    (eloc.toRingEquiv.trans (Spec.stalkIso R (g.base y)).commRingCatIsoToRingEquiv.symm)
    φ.symm (fun a => ?_) hsm
  have hgerm := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (germ_structureMap_eq g y)) a
  have hloc : eloc (algebraMap R (Localization.AtPrime (q.comap (algebraMap R T))) a) =
      algebraMap R (Localization.AtPrime (g.base y).asIdeal) a := eloc.commutes a
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, hloc]
  refine Eq.trans ?_ (congrArg φ.symm (hφ a))
  · rw [RingEquiv.symm_apply_apply]
    exact hgerm.symm

end AlgebraicGeometry

end
