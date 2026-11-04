module

public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# Rig-étaleness of an arrow whose target is the completion of an algebra étale off `V(I)`

Let `A` be a Noetherian adic topological ring, let `I ⊆ A` be an ideal of definition and let
`φ : A → C` be a homomorphism into a Noetherian adic topological ring which is adic of
topologically finite type — condition (6) of **Stacks 0GBW**, carried here by
`Rig.FiniteTypeAdicAlgebraForEveryIdeal`. Suppose `C` is identified, as an `A`-algebra through
`φ`, with the `I`-adic completion `C₀^` of a finite type `A`-algebra `C₀`. Then rig-étaleness
of `C₀^` over `(A, I)` in the sense of **Stacks 0GAY** is rig-étaleness of the *arrow* `φ` in
the sense of **Stacks 0GCV**, and if `Spec C₀ → Spec A` is étale over `Spec A ∖ V(I)` it holds
outright, by part (1) of **Stacks 0ALQ**.

This is the ring-theoretic bridge the chart conditions of
`StacksFrontier/AlgebraicGeometry/FormalSpace/RigEtale.lean` ask for. Those conditions are
`RingHom.IsRigEtale` of the homomorphism presenting a chart square, whereas the affine input of
the source's proofs of Stacks 0GDH and 0AR2 is rig-étaleness of a completion in the sense of
Stacks 0GAY — a property of an object of the category of **Stacks 0AL4**, which says nothing
about an arrow by itself. No declaration in this library crossed from one to the other: the
implication occurred only as a conjunct of
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside`.

## Main results

* `RingHom.isRigEtale_of_algEquiv_adicCompletionObj`: the bridge, taking the identification of
  `C` with `C₀^` as an equivalence of `A`-algebras.
* `RingHom.isRigEtale_of_ringEquiv_adicCompletionObj`: the same, taking a ring equivalence
  together with its compatibility with the two structure maps out of `A`. This is the form a
  geometric identification delivers, the formal spectrum of **Stacks 0AN0** seeing continuous
  ring maps and not algebra structures.
* `RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv`: with `Spec C₀ → Spec A` étale over the
  complement of `V(I)`, so that nothing at all is assumed about `C₀^`.

## Implementation notes

The identification is a hypothesis, and supplying it is the whole content of the step: the
target of an arrow does not determine an algebraization of itself, so a datum identifying `C`
with one has to be given. That datum is condition (8) of **Stacks 0AKG**, read for the target
of `φ`. What this file adds is the passage from that condition to the condition *on the arrow*:
`Rig.adicFiniteTypeAlgebra` regards `C` as an object of the category of Stacks 0AL4 over the
chosen ideal of definition, `Rig.isRigEtale_of_algEquiv` transports rig-étaleness along the
identification, `Rig.isRigEtaleOver_of_isRigEtale` repackages the completeness and finite-type
data existentially, and `RingHom.isRigEtale_of_isRigEtaleOver` checks Stacks 0GCV at that one
ideal of definition, which by **Stacks 0GCU** is as good as every one.

The `A`-algebra structure on `C` is the one `φ` defines, which is also the one
`Rig.IsRigEtaleOver` and `Rig.adicFiniteTypeAlgebra` use. It is introduced by a `letI` in the
statements rather than demanded as an instance, so that no second `Algebra A C` can be in
scope: that is the idiom of `Rig.IsRigEtaleOver` itself.

The base of the rig-étaleness hypothesis is `A`, the source of `φ`, and not an auxiliary ring
mapping to it. The affine data of the source's reduction of Stacks 0AR2 has for its base the
coordinate ring `A₀` of an étale chart, with `A = A₀^∧`; moving a rig-étaleness hypothesis from
`(A₀, I₀)` to `(A₀^∧, I₀ A₀^∧)` is **Stacks 0GB2**, `Rig.isRigEtale_of_completedBaseChange`,
applied to the completion map, and is not done here.

No Stacks tag is registered in this file. Condition (8) of Stacks 0AKG implying the equivalent
conditions of **Stacks 0AJU** is `Rig.isRigEtale_of_isEtaleOutside_of_algEquiv`, which carries
that tag, and part (1) of Stacks 0ALQ is
`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`, which carries that one. Restating either
for an arrow rather than for its target is a step in the proofs that consume them, not a clause
of either source.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0GB2](https://stacks.math.columbia.edu/tag/0GB2)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCU](https://stacks.math.columbia.edu/tag/0GCU)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

universe u v

namespace RingHom

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]
  {C : Type v} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C] [IsNoetherianRing C]
  (φ : A →+* C) (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ)
  (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
  {C₀ : Type v} [CommRing C₀] [Algebra A C₀] [Algebra.FiniteType A C₀]

include hft hI in
/-- **The bridge from rig-étaleness of an algebraization to rig-étaleness of the arrow.** If
the target of `φ : A → C` is, as an `A`-algebra through `φ`, the `I`-adic completion of a
finite type `A`-algebra `C₀`, and that completion is rig-étale over `(A, I)` in the sense of
Stacks 0GAY, then `φ` is rig-étale in the sense of Stacks 0GCV.

Rig-étaleness of the arrow is rig-étaleness of its target regarded as an object of the category
of Stacks 0AL4 over an ideal of definition of its source, so the equivalence transports the
hypothesis onto exactly that object, and Stacks 0GCU makes the one ideal `I` suffice. -/
theorem isRigEtale_of_algEquiv_adicCompletionObj
    (e : letI : Algebra A C := φ.toAlgebra
      C ≃ₐ[A] (Rig.adicCompletionObj I (B := C₀)).carrier)
    (h : Rig.IsRigEtale (Rig.adicCompletionObj I (B := C₀))) :
    IsRigEtale φ :=
  isRigEtale_of_isRigEtaleOver hft I hI
    (Rig.isRigEtaleOver_of_isRigEtale φ hft I hI (Rig.isRigEtale_of_algEquiv e h))

include hft hI in
/-- The bridge taking the identification of the target with the completion as a ring
equivalence together with its compatibility with the two structure maps out of `A`, which is
what makes it an equivalence of `A`-algebras.

This is the form in which a geometric identification arrives: by Stacks 0AN0 an isomorphism of
formal spectra is the formal spectrum of a continuous ring equivalence, and the square it sits
in records its compatibility with the arrows out of the base as an equation of ring maps. -/
theorem isRigEtale_of_ringEquiv_adicCompletionObj
    (e : C ≃+* (Rig.adicCompletionObj I (B := C₀)).carrier)
    (he : ∀ a : A, e (φ a) = algebraMap A (Rig.adicCompletionObj I (B := C₀)).carrier a)
    (h : Rig.IsRigEtale (Rig.adicCompletionObj I (B := C₀))) :
    IsRigEtale φ := by
  let : Algebra A C := φ.toAlgebra
  exact isRigEtale_of_algEquiv_adicCompletionObj φ hft I hI { e with commutes' := he } h

include hft hI in
/-- **Condition (8) of Stacks 0AKG makes the arrow rig-étale.** If the target of `φ : A → C`
is, as an `A`-algebra through `φ`, the `I`-adic completion of a finite type `A`-algebra `C₀`
with `Spec C₀ → Spec A` étale over `Spec A ∖ V(I)`, then `φ` is rig-étale in the sense of
Stacks 0GCV.

Nothing is assumed about the completion: part (1) of Stacks 0ALQ,
`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`, is unconditional, so étaleness off
`V(I)` supplies the rig-étaleness the bridge consumes. -/
theorem isRigEtale_of_isEtaleOutside_of_ringEquiv
    (e : C ≃+* (Rig.adicCompletionObj I (B := C₀)).carrier)
    (he : ∀ a : A, e (φ a) = algebraMap A (Rig.adicCompletionObj I (B := C₀)).carrier a)
    (hC₀ : Rig.IsEtaleOutside I C₀) :
    IsRigEtale φ :=
  isRigEtale_of_ringEquiv_adicCompletionObj φ hft I hI e he
    (Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside I hC₀)

end RingHom

end
