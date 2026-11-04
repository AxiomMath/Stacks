module

public import StacksFrontier.RingTheory.Flat.CompleteDevissagePointedChain
public import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport
public import StacksFrontier.RingTheory.RelativeDimension.Basic

/-!
# The relative dimension condition of a complete dévissage, fibre by fibre

Stacks 05HZ (4) asks that `R → Bᵢ` have relative dimension `dim_{qᵢ}(Supp(Mᵢ ⊗_R κ(r)))`.
`Module.NonemptyCompleteDevissageAt` records it as an equality for the single supremum
`Algebra.relativeDimension R Bᵢ` of Definition 00QD. Stacks 05I0 describes the condition as the
fibre-dimension condition of Stacks 05H4 (5), which constrains *every* fibre of
`Spec Bᵢ → Spec R`; the two are not the same, because the dimension of the fibres of a smooth
morphism is only locally constant
(`Algebra.not_forall_relativeDimension_eq_topologicalKrullDim_fiber`).
This file records the missing half: every fibre of `Spec Bᵢ → Spec R` has dimension
`Algebra.relativeDimension R Bᵢ`. Together with the supremum condition it says that every fibre
has dimension `dim_{qᵢ}(Supp(Mᵢ ⊗_R κ(r)))`.

## Main definitions

* `Module.DevissageStageData.FibresHaveRelativeDimension`: every fibre of `Spec B → Spec R` of a
  stage has the relative dimension of `R → B`.
* `Module.CompleteDevissage.FibresHaveRelativeDimension`: the same for every stage.
* `Module.CompleteDevissageAt.FibresHaveRelativeDimension`: the same for a complete dévissage at
  a prime; the empty dévissage satisfies it.

## Main results

* `Module.DevissageStageData.Pointed.topologicalKrullDim_fiber_eq_support`: for a pointed stage
  whose fibres have the relative dimension, every fibre of `Spec B → Spec R` has the local
  dimension of the support of the fibre module at the chosen prime.
* `Module.CompleteDevissageAt.fibresHaveRelativeDimension_ofRingEquiv`: the condition is carried
  along `Module.CompleteDevissageAt.ofRingEquiv`.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

universe u u' v w

namespace Module

namespace DevissageStageData

variable {R : Type u} [CommRing R] {r : Ideal R} [r.IsPrime]

/-- Every fibre of `Spec B → Spec R` of a stage has dimension the relative dimension of
`R → B`. -/
public def FibresHaveRelativeDimension (st : DevissageStageData.{u, w} R r) : Prop :=
  ∀ p : PrimeSpectrum R,
    topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R st.B) ⁻¹' {p}) =
      Algebra.relativeDimension R st.B

/-- **Stacks 05HZ (4), fibre by fibre.** For a pointed stage whose fibres have the relative
dimension, every fibre of `Spec B → Spec R` has the local dimension of the support of the fibre
module at the chosen lower prime: the fibre-dimension condition of Stacks 05H4 (5) read on
rings. -/
public theorem Pointed.topologicalKrullDim_fiber_eq_support {st : DevissageStageData.{u, w} R r}
    (P : st.Pointed) (hst : st.FibresHaveRelativeDimension) (p : PrimeSpectrum R) :
    letI : P.lowerPrime.IsPrime := P.lowerPrime_isPrime
    letI : Module st.B st.M := Module.compHom st.M st.toLeft.toRingHom
    letI : Algebra st.B (r.Fiber st.B) := Algebra.TensorProduct.rightAlgebra
    topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R st.B) ⁻¹' {p}) =
      topologicalKrullDimAt
        (↥(Module.support (r.Fiber st.B) (TensorProduct st.B (r.Fiber st.B) st.M)))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R st.B r
            ⟨P.lowerPrime, P.lowerPrime_isPrime, P.lowerPrime_liesOver⟩,
          P.lowerPrime_mem_fiberSupport⟩ :=
  (hst p).trans P.relativeDimension_eq_support

end DevissageStageData

/-- The condition that every fibre of `Spec B → Spec R` has the relative dimension of `R → B`
does not depend on which model of the base ring is used. -/
public theorem forall_topologicalKrullDim_fiber_eq_of_ringEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x)
    (h : ∀ p : PrimeSpectrum R,
      topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹' {p}) =
        Algebra.relativeDimension R B)
    (p' : PrimeSpectrum R') :
    topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R' B) ⁻¹' {p'}) =
      Algebra.relativeDimension R' B := by
  rw [topologicalKrullDim_congr_set
      (PrimeSpectrum.comap_preimage_singleton_eq_of_ringEquiv eR hmap p'), h,
    Algebra.relativeDimension_eq_of_ringEquiv eR hmap]

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- Every fibre of `Spec Bᵢ → Spec R` of every stage of a complete dévissage has the relative
dimension of `R → Bᵢ`. -/
public def FibresHaveRelativeDimension (D : CompleteDevissage R S N r) : Prop :=
  ∀ i, (D.stages i).FibresHaveRelativeDimension

/-- A one-stage dévissage satisfies the condition when its stage does. -/
public theorem fibresHaveRelativeDimension_ofStage (st : DevissageStageData.{u, w} R r)
    (toA : S →ₐ[R] st.A) (hsurj : Function.Surjective toA)
    (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha) (hst : st.FibresHaveRelativeDimension) :
    (ofStage st toA hsurj hfp equiv hfinal).FibresHaveRelativeDimension :=
  fun _ => hst

/-- A dévissage with a stage prepended satisfies the condition when the stage and the tail do. -/
public theorem fibresHaveRelativeDimension_consStageData (st : DevissageStageData.{u, w} R r)
    (toA : S →ₐ[R] st.A) (hsurj : Function.Surjective toA)
    (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' r)
    (hst : st.FibresHaveRelativeDimension) (hD : D.FibresHaveRelativeDimension) :
    (consStageData (N := N) st toA hsurj hfp equiv e D).FibresHaveRelativeDimension :=
  fun i => Fin.cases hst (fun j => hD j) i

end CompleteDevissage

namespace PointedCompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime] {q : Ideal S} [q.IsPrime]

/-- Identifying the base prime of a pointed complete dévissage with the contraction of `q` does
not change its stages, so the condition passes to the dévissage at `q`. -/
public theorem fibresHaveRelativeDimension_toNonemptyCompleteDevissageAt (hrq : q.under R = r)
    (E : PointedCompleteDevissage R S N r q)
    (hE : E.toCompleteDevissage.FibresHaveRelativeDimension) :
    (E.toNonemptyCompleteDevissageAt hrq).toCompleteDevissage.FibresHaveRelativeDimension := by
  subst hrq
  exact hE

end PointedCompleteDevissage

namespace CompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S}
  [q.IsPrime]

/-- Every fibre of `Spec Bᵢ → Spec R` of every stage of a complete dévissage at `q` has the
relative dimension of `R → Bᵢ`; the empty dévissage has no stages and satisfies it. Together
with `Module.NonemptyCompleteDevissageAt.relativeDimension_eq_support` this is the relative
dimension condition of Stacks 05HZ (4) for every fibre, which is how Stacks 05I0 reads it. -/
public def FibresHaveRelativeDimension : CompleteDevissageAt R S N q → Prop
  | .empty _ => True
  | .nonempty D => D.toCompleteDevissage.FibresHaveRelativeDimension

variable {R' : Type u} {S' : Type v} {N' : Type w} [CommRing R'] [CommRing S']
  [Algebra R' S'] [Algebra.FiniteType R' S'] [AddCommGroup N'] [Module S' N'] [Module.Finite S' N']

/-- **The condition is carried along a change of the data by isomorphisms.** The stage algebras
of `Module.CompleteDevissageAt.ofRingEquiv` are the old ones over the new base ring, and both the
fibres and the relative dimension are unchanged by the change of base ring. -/
public theorem fibresHaveRelativeDimension_ofRingEquiv
    (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {q' : Ideal S'} [q'.IsPrime] (hq : q = Ideal.comap eS.toRingHom q')
    (D : CompleteDevissageAt R S N q) (hD : D.FibresHaveRelativeDimension) :
    (D.ofRingEquiv eR eS eN halg hsmul hq).FibresHaveRelativeDimension := by
  match D, hD with
  | .empty _, _ => trivial
  | .nonempty data, hD =>
    intro i
    let : Algebra R' (data.toCompleteDevissage.stages i).B :=
      ((algebraMap R (data.toCompleteDevissage.stages i).B).comp eR.symm.toRingHom).toAlgebra
    exact forall_topologicalKrullDim_fiber_eq_of_ringEquiv
      (B := (data.toCompleteDevissage.stages i).B) eR
      (fun x => congrArg (algebraMap R (data.toCompleteDevissage.stages i).B)
        (eR.symm_apply_apply x)) (hD i)

end CompleteDevissageAt

end Module

end
