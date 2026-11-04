module

public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.BaseChangeAlgEquiv
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothBaseChange

/-!
# Rig-smoothness depends only on the isomorphism class

Let `A` be a Noetherian ring and `I ⊆ A` an ideal.  Rig-smoothness over `(A, I)` in the sense of
**Stacks 0GAI** is a property of an object of the category of **Stacks 0AL4**, and this file
shows it is a property of the isomorphism class: if the carriers of two objects are isomorphic
as `A`-algebras and one is rig-smooth, so is the other.  Together with part (1) of **Stacks
0GAK** that turns the algebraization datum of condition (8) of **Stacks 0AKG** — an
identification of the algebra with the `I`-adic completion of a finite type `A`-algebra smooth
over `Spec A ∖ V(I)` — into rig-smoothness, with nothing assumed about the completion.

This is the rig-smooth counterpart of `Rig.isRigEtale_of_algEquiv` and
`Rig.isRigEtale_of_isEtaleOutside_of_algEquiv`, and it is what
`AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap` needs in order to consume that
datum rather than assume its own conclusion.

## Main results

* `Rig.isRigSmooth_of_algEquiv`: invariance of `Rig.IsRigSmooth` under an equivalence of
  `A`-algebras.
* `Rig.isRigSmooth_of_smoothAwayFrom_of_algEquiv`: condition (8) of Stacks 0AKG, in the
  rig-smooth reading, implies rig-smoothness.
* `Rig.isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv`: the same for the
  target of a continuous homomorphism regarded as an object over an ideal of definition of its
  source, taking the identification as a ring equivalence compatible with the two structure
  maps out of the base — the form a geometric identification delivers, the formal spectrum of
  **Stacks 0AN0** seeing continuous ring maps and not algebra structures.

## Implementation notes

The transport is *not* a rewrite.  `Rig.IsRigSmooth` quantifies over the modules over the
carrier and over the `Ext¹` groups out of the completed naive cotangent complex, and the two
carriers need not even lie in the same universe, so what moves the condition across is the
base change of **Stacks 0GAM** along the identity of `(A, I)`: an isomorphism `B ≅ C` exhibits
`B` as `(C ⊗_A A)^∧_I`, by
`Rig.exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv`, and
`Rig.isRigSmooth_of_completedBaseChange` — the engine form of 0GAM, which takes that
identification as data — transports the annihilation.  That is step for step the proof of
`Rig.isRigEtale_of_algEquiv` over the engine form of Stacks 0GB2, which is why the shared
construction of the identification lives in its own file and is called by both.

The remaining hypothesis of the engine, that `I A` and `I` cut out the same closed subset of
`Spec A`, holds because base change along the identity carries `I` to itself.

No Stacks tag is registered here.  Both statements are steps in the proofs that consume them:
`Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom` carries Stacks 0GAK (1) and
`Rig.isRigSmooth_completedBaseChange` carries Stacks 0GAM, and restating either for an
isomorphic object is not a clause of either source.

## References

* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAK](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0GAM](https://stacks.math.columbia.edu/tag/0GAM)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
-/

@[expose] public noncomputable section

namespace Rig

universe u v w

section AlgEquiv

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Rig-smoothness depends only on the isomorphism class.**  If the carriers of two objects of
`Rig.AdicFiniteTypeAlgebra A I` are isomorphic as `A`-algebras and one of them is rig-smooth
over `(A, I)`, so is the other.

An isomorphism `B ≅ C` identifies `B` with the completed base change `(C ⊗_A A)^∧_I` of `C`
along the identity of `A`
(`Rig.exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv`); the engine form of **Stacks
0GAM**, `Rig.isRigSmooth_of_completedBaseChange`, then transports the annihilation of the
`Ext¹` groups out of the completed naive cotangent complex.  This is the rig-smooth counterpart
of `Rig.isRigEtale_of_algEquiv`, with the same proof over the other base-change engine. -/
public theorem isRigSmooth_of_algEquiv {B : AdicFiniteTypeAlgebra.{u, w} A I}
    {C : AdicFiniteTypeAlgebra.{u, v} A I} (e : B.carrier ≃ₐ[A] C.carrier)
    (hC : IsRigSmooth C) : IsRigSmooth B := by
  let _ : Algebra C.carrier B.carrier :=
    (e.symm : C.carrier →ₐ[A] B.carrier).toRingHom.toAlgebra
  have halg : ∀ c : C.carrier, algebraMap C.carrier B.carrier c = e.symm c := fun _ => rfl
  have : IsScalarTower A C.carrier B.carrier :=
    .of_algebraMap_eq fun a => (e.symm.commutes a).symm
  obtain ⟨e', heA, heB⟩ := exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv e halg
  refine isRigSmooth_of_completedBaseChange ?_ e' heA heB hC
  rw [Algebra.algebraMap_self, Ideal.map_id]

/-- **Condition (8) of Stacks 0AKG makes an object rig-smooth.**  If the carrier of an object of
`Rig.AdicFiniteTypeAlgebra A I` is isomorphic as an `A`-algebra to the `I`-adic completion `C^∧`
of a finite type `A`-algebra `C` with `Spec C → Spec A` smooth over `Spec A ∖ V(I)`, then it is
rig-smooth over `(A, I)`.

Nothing is assumed about the completion: part (1) of **Stacks 0GAK**,
`Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom`, is unconditional, so smoothness off
`V(I)` supplies the rig-smoothness that `Rig.isRigSmooth_of_algEquiv` transports.  This is the
rig-smooth counterpart of `Rig.isRigEtale_of_isEtaleOutside_of_algEquiv`. -/
public theorem isRigSmooth_of_smoothAwayFrom_of_algEquiv
    {B : AdicFiniteTypeAlgebra.{u, w} A I} {C : Type v} [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] (hC : SmoothAwayFrom A I C)
    (e : B.carrier ≃ₐ[A] (adicCompletionObj I (B := C)).carrier) :
    IsRigSmooth B :=
  isRigSmooth_of_algEquiv e (isRigSmooth_adicCompletionObj_of_smoothAwayFrom I hC)

end AlgEquiv

/-! ## The datum read on the target of a continuous homomorphism -/

section Arrow

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]
  {C : Type v} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]
  (φ : A →+* C) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
  (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
  {C₀ : Type v} [CommRing C₀] [Algebra A C₀] [Algebra.FiniteType A C₀]

include hft hI in
/-- **The algebraization datum on the target of an arrow makes that target rig-smooth over an
ideal of definition of the source.**  If the target of `φ : A → C` is, as an `A`-algebra through
`φ`, the `I`-adic completion of a finite type `A`-algebra `C₀` with `Spec C₀ → Spec A` smooth
over `Spec A ∖ V(I)`, then `C` regarded as an object over `(A, I)` by `Rig.adicFiniteTypeAlgebra`
is rig-smooth.

The identification is taken as a ring equivalence together with its compatibility with the two
structure maps out of `A`, which is what makes it an equivalence of `A`-algebras.  This is the
form in which a geometric identification arrives: by Stacks 0AN0 an isomorphism of formal
spectra is the formal spectrum of a continuous ring equivalence, and the square it sits in
records its compatibility with the arrows out of the base as an equation of ring maps.

The `A`-algebra structure on `C` is the one `φ` defines, which is also the one
`Rig.adicFiniteTypeAlgebra` uses; it is introduced by a `letI` in the proof rather than demanded
as an instance, so that no second `Algebra A C` can be in scope.  This is the rig-smooth
counterpart of `RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv`, except that the conclusion
is about the object and not about the arrow: the chart condition of
`AlgebraicGeometry.FormalSpace.IsRigSmooth` is `Rig.IsRigSmooth` of
`Rig.adicFiniteTypeAlgebra` of the presenting arrow, so no arrow-level predicate is involved. -/
public theorem isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv
    (e : C ≃+* (adicCompletionObj I (B := C₀)).carrier)
    (he : ∀ a : A, e (φ a) = algebraMap A (adicCompletionObj I (B := C₀)).carrier a)
    (hC₀ : SmoothAwayFrom A I C₀) :
    IsRigSmooth (adicFiniteTypeAlgebra φ hft I hI) := by
  let _ : Algebra A C := φ.toAlgebra
  exact isRigSmooth_of_smoothAwayFrom_of_algEquiv hC₀ { e with commutes' := he }

end Arrow

/-! ## The trivial algebraization is no algebraization -/

section Trivial

/-- The `J`-adic completion of a subsingleton module is a subsingleton: an element of it is a
compatible family of elements of the quotients, and all of those are trivial. -/
private theorem subsingleton_adicCompletion {A : Type u} [CommRing A] (J : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M] [Subsingleton M] :
    Subsingleton (AdicCompletion J M) :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

/-- **The trivial algebraization datum is not a datum.**  There is *no* ring equivalence of a
nontrivial ring with the `I`-adic completion of a subsingleton `A`-algebra, because that
completion is a subsingleton.

This is the non-vacuity certificate for the algebraization datum of condition (8) of **Stacks
0AKG** as `AlgebraicGeometry.FormalSpace.ChartSquareReducesToSmoothAwayFrom` and
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside` ask for it.  Both ask, at
each square of a covering, for an identification of that square's own `C` with the completion
of the finite type algebra `C₀` they produce; a formulation that asked only for *some* `C₀` with
`Spec C₀ → Spec A` smooth, respectively étale, off `V(I₀)` is satisfied by `C₀ = PUnit`, whose
spectrum has no primes at all, and is therefore vacuous.  With the identification present that
witness is refuted outright, and so is every other subsingleton one. -/
public theorem isEmpty_ringEquiv_adicCompletionObj_of_subsingleton
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {C₀ : Type v} [CommRing C₀] [Subsingleton C₀] [Algebra A C₀] [Algebra.FiniteType A C₀]
    (C : Type w) [CommRing C] [Nontrivial C] :
    IsEmpty (C ≃+* (adicCompletionObj I (B := C₀)).carrier) := by
  have : Subsingleton (adicCompletionObj I (B := C₀)).carrier :=
    subsingleton_adicCompletion (I.map (algebraMap A C₀))
  exact ⟨fun e => zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))⟩

end Trivial

end Rig

end
