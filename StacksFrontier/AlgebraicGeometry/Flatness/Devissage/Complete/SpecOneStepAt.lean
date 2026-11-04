module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecDevissageAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecResidueFieldTranscendental

/-!
# A one-step dévissage at a point out of algebraic data

`Module.DevissageStage.toOneStepDevissage` turns one stage of an algebraic complete dévissage of
`N/S/R` over a prime `r` of `R` into a one-step dévissage of `Ñ/Spec S/Spec R` over the point of
`r`. This file adds the distinguished points: for a stage carrying the pointed data of
Stacks 05HZ at a prime `q` of `S`, the prime `lp` of the smooth algebra is the point `y`, the
unique prime `up` of the finite algebra above it is the point `z`, and the conditions of
Stacks 05H5 are the conditions of Stacks 05HZ.

## Main definitions

* `Module.DevissageStage.toOneStepDevissageAt`: **one stage of an algebraic complete dévissage at
  `q`, with its pointed datum, is a one-step dévissage of `Ñ/Spec S/Spec R` at the point of
  `q`.**
* `Module.DevissageStage.toPointedStage`: **the same stage as a pointed stage of a complete
  dévissage.**

## Main results

* `AlgebraicGeometry.specMap_preimage_singleton_eq_of_unique`: the fibre of `Spec` of a ring map
  over a point is the single point given by the unique prime above it, which is the condition
  `AlgebraicGeometry.OneStepDevissageAt.fiber_eq_singleton`.
* `Module.DevissageStage.geometricFiberDim`: the fibre-dimension condition of Stacks 05H4 (5).
* `AlgebraicGeometry.asFiber_eq_specFiberPoint`: the point of the fibre of `Spec S → Spec R`
  attached to `q` by `AlgebraicGeometry.Scheme.Hom.asFiber` is the one attached to it by
  `AlgebraicGeometry.specFiberPoint`.

## Implementation notes

The base point of the one-step dévissage is the point of `q.under R`, which is literally the
image of the point of `q` under `Spec` of the structure map, so the stage is taken over
`q.under R` and no transport along an equality of base points is needed; that is what makes the
identification of the one-step dévissage with the stage's in
`Module.DevissageStage.toPointedStage` hold by `HEq.rfl`.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap

/-- **The fibre of `Spec` of a ring map over a point is a single point as soon as the prime there
has a unique prime above it.** -/
public theorem AlgebraicGeometry.specMap_preimage_singleton_eq_of_unique {A B : Type u}
    [CommRing A] [CommRing B] (φ : B →+* A) (lp : Ideal B) [hlp : lp.IsPrime] (up : Ideal A)
    [hup : up.IsPrime] (hunder : up.comap φ = lp)
    (huniq : ∀ p : Ideal A, p.IsPrime → p.comap φ = lp → p = up) :
    (Spec.map (CommRingCat.ofHom φ)) ⁻¹' {(⟨lp, hlp⟩ : Spec (CommRingCat.of B))}
      = {(⟨up, hup⟩ : Spec (CommRingCat.of A))} := by
  ext w
  simp only [Set.mem_preimage]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact PrimeSpectrum.ext (huniq w.asIdeal w.isPrime (congrArg PrimeSpectrum.asIdeal h))
  · subst h
    exact PrimeSpectrum.ext hunder

/-- **The point of the fibre of `Spec S → Spec R` attached to a prime `q` of `S` by
`AlgebraicGeometry.Scheme.Hom.asFiber` is the point `AlgebraicGeometry.specFiberPoint` names**:
both have image `q` in `Spec S`, and the fibre embeds in `Spec S`. -/
public theorem AlgebraicGeometry.asFiber_eq_specFiberPoint (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [hqp : q.IsPrime] :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber
        (⟨q, hqp⟩ : Spec (CommRingCat.of S)) =
      AlgebraicGeometry.specFiberPoint R S (q.under R) q rfl :=
  ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberHomeo
      (⟨q.under R, inferInstance⟩ : Spec (CommRingCat.of R))).injective
    (Subtype.ext
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι_asFiber
          (⟨q, hqp⟩ : Spec (CommRingCat.of S))).trans
        (AlgebraicGeometry.fiberι_specFiberPoint R S (q.under R) q rfl).symm))

namespace Module.DevissageStage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S} [hqp : q.IsPrime]
  (st : Module.DevissageStage R S N (q.under R)) (P : st.toData.Pointed)

/-- **The fibre-dimension condition of Stacks 05H4 (5) for the smooth algebra of a stage:** every
fibre of `Spec B → Spec R` has the dimension of the support of the fibre of `Ñ`. -/
public theorem geometricFiberDim (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q)
    (t : Spec (CommRingCat.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R st.B))).fiber t) =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨q.under R, inferInstance⟩ : Spec (CommRingCat.of R)))).obj
          (tilde (ModuleCat.of (CommRingCat.of S) N)))) := by
  refine (AlgebraicGeometry.topologicalKrullDim_fiber_specMap R st.B t).trans ?_
  rw [AlgebraicGeometry.topologicalKrullDim_supp_pullback_fiberι_tilde]
  exact (st.fiberDim P hst t).trans ((st.dimFacts P hst hinit).1).symm

/-- **One stage of an algebraic complete dévissage at a prime `q` of `S` is a one-step dévissage
of `Ñ/Spec S/Spec R` at the point of `q`.**

The prime `lp` of the smooth algebra is the point `y`, the unique prime `up` of the finite
algebra above it is the point `z`, the fibre of the finite morphism above `y` is `{z}` because
`up` is the unique prime above `lp`, and `q` is the contraction of `up`, which says that `z` lies
over the point of `q`. -/
public def toOneStepDevissageAt (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q) :
    AlgebraicGeometry.OneStepDevissageAt (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (tilde (ModuleCat.of (CommRingCat.of S) N))
      (⟨q, hqp⟩ : Spec (CommRingCat.of S)) where
  toOneStepDevissage := st.toOneStepDevissage (st.geometricFiberDim P hst hinit)
  mem_fiber_support := by
    rw [AlgebraicGeometry.asFiber_eq_specFiberPoint R S q]
    exact AlgebraicGeometry.specFiberPoint_mem_supp_pullback_fiberι_tilde (q.under R) q rfl
      (st.memFiberSupport P hinit)
  dimension :=
    (congrArg (topologicalKrullDimAt _)
        (Subtype.ext (AlgebraicGeometry.asFiber_eq_specFiberPoint R S q))).trans
      ((AlgebraicGeometry.topologicalKrullDimAt_supp_pullback_fiberι_tilde (q.under R) q rfl
          (st.memFiberSupport P hinit)
          (AlgebraicGeometry.specFiberPoint_mem_supp_pullback_fiberι_tilde (q.under R) q rfl
            (st.memFiberSupport P hinit))).trans
        ((st.dimFacts P hst hinit).2.trans
          (AlgebraicGeometry.topologicalKrullDim_supp_pullback_fiberι_tilde
            (N := N) (q.under R)).symm))
  z := ⟨P.upperPrime, P.upperPrime_isPrime⟩
  y := ⟨P.lowerPrime, P.lowerPrime_isPrime⟩
  i_z := PrimeSpectrum.ext hinit
  π_z := PrimeSpectrum.ext P.upperPrime_under
  g_y := PrimeSpectrum.ext P.lowerPrime_liesOver.over.symm
  fiber_eq_singleton :=
    letI := P.lowerPrime_isPrime
    letI := P.upperPrime_isPrime
    AlgebraicGeometry.specMap_preimage_singleton_eq_of_unique st.toLeft.toRingHom P.lowerPrime
      P.upperPrime P.upperPrime_under P.upperPrime_unique
  residueField_purelyTranscendental :=
    letI := P.lowerPrime_isPrime
    AlgebraicGeometry.purelyTranscendental_residueField_specMap (q.under R) P.lowerPrime
      P.lowerPrime_liesOver (PrimeSpectrum.ext P.lowerPrime_liesOver.over.symm)
      P.residueField_purelyTranscendental

/-- **One stage of an algebraic complete dévissage at a prime `q` of `S`, with its pointed datum,
is a pointed stage of a scheme-theoretic complete dévissage of `Ñ/Spec S/Spec R` at the point of
`q`.** -/
public def toPointedStage (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q) :
    AlgebraicGeometry.PointedDevissageStage (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (tilde (ModuleCat.of (CommRingCat.of S) N))
      ((Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
      (⟨q, hqp⟩ : Spec (CommRingCat.of S))
      (st.toGeometricStage (st.geometricFiberDim P hst hinit)) where
  atPoint := st.toOneStepDevissageAt P hst hinit
  sameOneStep := HEq.rfl
  y := ⟨P.lowerPrime, P.lowerPrime_isPrime⟩
  sameY := HEq.rfl

end Module.DevissageStage

end
