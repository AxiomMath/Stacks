module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PairFromQuadruple

/-!
# The universal invertible degree-one quotient of Tag 01O4

Let `𝒜` be a graded `𝒪_S`-algebra as in Situation 01NN, generated in degree one, and let `X` be a
relative homogeneous spectrum of `𝒜`. `StacksDraft.AlgebraicGeometry.ProjRepresentsF1.`
`PairFromQuadruple` proves that the classifying map is a bijection from the strict isomorphism
classes of invertible degree-one quotients of `f^*𝒜` to the morphisms `T ⟶ X` over `S`. This file
**builds the pair that the identity morphism of `X` corresponds to under that bijection** — the
universal invertible degree-one quotient of Tag 01O4, over `X` itself.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.universalQuadruple`: the quadruple of Section 01NS at
  `d = 1` over the structure morphism of `X` whose strict equivalence class the relative universal
  property attaches to the identity morphism of `X`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.universalPair`: **the universal invertible degree-one
  quotient**, over `X` itself.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom_universalPair`: **the morphism
  classified by the universal pair is the identity of `X`**.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingEquiv_symm_id`: **the class the
  bijection of Tag 01O4 attaches to the identity morphism of `X` is the class of the universal
  pair** — the normalisation clause of the tag.

## Implementation notes

**The universal pair is the pair of a universal quadruple, and the universal quadruple is a
representative of a class.** The relative universal property
`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv` is an equivalence onto the
morphisms over `S`, so the identity of `X` has a preimage: a strict equivalence class of
quadruples. `Quotient.out` picks a quadruple out of that class, and
`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadruplePair` turns it into a pair. The normalisation
clause is then `Quotient.out_eq` together with `strictlyEquivalent_quadruple_quadruplePair`, which
says the quadruple of the pair of a quadruple is strictly equivalent to that quadruple.

The pair is therefore pinned only up to strict isomorphism, which is all the tag's normalisation
clause determines: the class of the universal pair is unique, the pair itself is a choice of
representative.

**No relative homogeneous spectrum is chosen here.** `X` is an arbitrary `RelativeProjData 𝒜`, so
the statements apply in particular to
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj 𝒜`, which is the `X` that
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` names.

**No tensor-algebra pullback comparison appears**, and none is needed: the universal pair and its
normalisation are independent of the parameter `ι` of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraPullbackIsos`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)

## Not done here

The invertible sheaf of the universal pair is not identified with the degree-one twist of
Tag 01NR, so `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsCanonicalTwistPair` is not verified for
it and no `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` is assembled. The pullback
of a pair along a morphism of test schemes is in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalBundle`, not here.

The `Quotient.out` above is not an obstacle to that identification:
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_of_quot_eq` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.CanonicalClass` shows canonicality is a property
of the strict isomorphism class, and
`...ProjRepresentsF1.isCanonicalTwistPair_universalPair_iff` there restates what is missing as the
existence of *some* canonical pair whose classifying morphism is the identity. The normalisation
clause `pairClassifyingHom_universalPair` read on the affine charts of the base, where the
classifying morphism is the absolute one of Tag 01NA, is
`...ProjRepresentsF1.toProj_chartEquiv_universalQuadrupleClass` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalChart`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (X : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)
  (hgen : IsGeneratedInDegreeOne A)

/-! ### The universal quadruple -/

/-- The strict equivalence class of quadruples that the relative universal property at degree one
attaches to the identity morphism of `X`. -/
public def universalQuadrupleClass :
    Quotient (Quadruple.setoid X.toBase (situationAlgebra A) (1 : ℤ)) :=
  (quadrupleClassEquiv A X hgen X.toBase).symm ⟨𝟙 X.scheme, Category.id_comp _⟩

/-- A quadruple of Section 01NS at `d = 1` over the structure morphism of `X`, whose strict
equivalence class is the one attached to the identity morphism of `X`. -/
public def universalQuadruple : Quadruple X.toBase (situationAlgebra A) 1 :=
  (universalQuadrupleClass A X hgen).out

/-- The class of the universal quadruple is the class attached to the identity morphism of
`X`. -/
public theorem universalQuadruple_class :
    Quotient.mk _ (universalQuadruple A X hgen) = universalQuadrupleClass A X hgen :=
  Quotient.out_eq _

/-! ### The universal pair -/

/-- **The universal invertible degree-one quotient of Tag 01O4**: the pair over a relative
homogeneous spectrum `X` of `𝒜` itself determined by the universal quadruple. -/
public def universalPair : F1Pair A TA X.toBase :=
  quadruplePair A TA X.toBase (universalQuadruple A X hgen)

/-- The invertible sheaf of the universal pair is the invertible sheaf of the universal
quadruple. -/
public theorem universalPair_L :
    (universalPair A TA X hgen).L = (universalQuadruple A X hgen).L :=
  rfl

/-- The graded map of the universal pair is the one the universal quadruple determines. -/
public theorem universalPair_psi (n : ℤ) :
    (universalPair A TA X hgen).ψ n =
      quadruplePsi A TA X.toBase (universalQuadruple A X hgen) n :=
  rfl

/-- **Tag 01O4.** The morphism to `X` over `S` classified by the universal pair is the identity
morphism of `X`: the universal pair normalises the classifying map of the tag. -/
public theorem pairClassifyingHom_universalPair :
    pairClassifyingHom A TA X.toBase X hgen (Quot.mk _ (universalPair A TA X hgen)) =
      ⟨𝟙 X.scheme, Category.id_comp _⟩ :=
  Eq.trans
    (congrArg (quadrupleClassEquiv A X hgen X.toBase)
      (Eq.trans
        (Quotient.sound
          (strictlyEquivalent_quadruple_quadruplePair A TA X.toBase
            (universalQuadruple A X hgen)))
        (universalQuadruple_class A X hgen)))
    ((quadrupleClassEquiv A X hgen X.toBase).apply_symm_apply _)

/-- The class the bijection of Tag 01O4 attaches to the identity morphism of `X` is the strict
isomorphism class of the universal pair.

This is `pairClassifyingHom_universalPair` read through the equivalence, and so carries no project
tag of its own; it is the shape the normalisation field of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` asks for. -/
public theorem pairClassifyingEquiv_symm_id :
    (pairClassifyingEquiv A TA X.toBase X hgen).symm ⟨𝟙 X.scheme, Category.id_comp _⟩ =
      Quot.mk _ (universalPair A TA X hgen) :=
  (Equiv.symm_apply_eq _).2 (pairClassifyingHom_universalPair A TA X hgen).symm

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
