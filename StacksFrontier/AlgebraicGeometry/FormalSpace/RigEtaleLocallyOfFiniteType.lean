module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# A rig-étale morphism of locally Noetherian formal algebraic spaces is locally of finite type

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AQN** says that a rig-étale
morphism of locally Noetherian formal algebraic spaces over `S` is locally of finite type.

The source deduces this from **Stacks 0ANW**: rig-étaleness of an arrow of `WAdm^{Noeth}`
implies the equivalent conditions of Stacks 0ANU, so the chart-tested condition (1) of Stacks
0ANW holds for the property of being taut and topologically of finite type, and condition (4)
of that lemma is being locally of finite type. That is the route taken by
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_of_isRigEtale_of_isLocallyNoetherian`, which
proves Stacks 0AQN; this module names inputs of a conditional form of that route.

## Main definitions

* `TopologicalRing.IsTautTopologicallyOfFiniteTypeOfIsRigEtale`: the affine case, that is the
  implication at the level of arrows of `WAdm^{Noeth}`.
* `AlgebraicGeometry.FormalSpace.IsCountablyIndexedOfIsNoetherian` and
  `AlgebraicGeometry.FormalSpace.ChartPresentationIsNoetherianAdic`: the two further inputs
  this library does not carry, each named once with the Stacks tag it is.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyCountablyIndexed_of_isLocallyNoetherian`: granting
  `hci`, a locally Noetherian formal algebraic space is locally countably indexed. Stacks 0AQN
  itself is
  `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_of_isRigEtale_of_isLocallyNoetherian`.

## Implementation notes

The affine case is the hypothesis `h0GCV`: a rig-étale continuous homomorphism of Noetherian
adic topological rings is taut and topologically of finite type. This is the implication the
source gets from Stacks 0AQL — the property `P` of Stacks 0AQL implies the equivalent
conditions of Stacks 0ANU, of which condition (c) is tautness together with topological finite
type. Unwinding it in this library would mean deducing condition (6) of Stacks 0GBW, which is
the first half of Definition 0GCV, from conditions (2) or (3) of that lemma; only the
equivalence of "adic and topologically of finite type" with "taut and topologically of finite
type" (Stacks 0GBS) is carried, as
`TopologicalRing.adicTopologicallyFiniteType_isLocal` uses it. The affine case is a statement
about one arrow of `WAdm^{Noeth}`, not about the morphism of formal algebraic spaces, so
carrying it leaves the globalization to be proved.

Two further inputs are needed to make the two chart-tested conditions comparable, because
Stacks 0AQM tests charts over the class `WAdm^{Noeth}` while Stacks 0ANW tests them over the
class `WAdm^{count}`.

* `hci` is the affine implication from Noetherian to countably indexed, which is what makes a
  locally Noetherian formal algebraic space locally countably indexed; the source has it in
  the list of Stacks 0AKY, through the countable fundamental system of open ideals `Iⁿ` of a
  Noetherian adic ring.
* `hchart` says that a topological ring presenting an affine chart of a locally Noetherian
  formal algebraic space is Noetherian and adic. It is Stacks 0AKX in the Noetherian form of
  Stacks 0AKW together with the uniqueness up to isomorphism of the presenting ring of a
  McQuillan affine formal algebraic space (Stacks 0AIC); without it the rings `WAdm^{count}`
  supplies to the chart-tested condition of Stacks 0ANW are not known to be objects of
  `WAdm^{Noeth}`, and `IsRigEtale` says nothing about them.

## References

* [Stacks Project, Tag 0685](https://stacks.math.columbia.edu/tag/0685)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQN](https://stacks.math.columbia.edu/tag/0AQN)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- The affine case of **Stacks 0AQN**: a rig-étale continuous homomorphism of Noetherian adic
topological rings, in the sense of Definition 0GCV, is taut and topologically of finite type.

This is the implication of **Stacks 0685** that the source of Stacks 0AQN uses through Stacks
0AQL and Stacks 0ANU, and which this library does not carry: it carries the equivalence of
"adic and topologically of finite type" with "taut and topologically of finite type" (Stacks
0GBS) but not the passage from condition (6) of Stacks 0GBW, the first half of Definition
0GCV, to either of them. -/
abbrev IsTautTopologicallyOfFiniteTypeOfIsRigEtale : Prop :=
  ∀ {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C] [TopologicalSpace C]
      [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C] (φ : A →+* C),
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic C → RingHom.IsRigEtale φ →
      IsTautTopologicallyOfFiniteTypeHom φ

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs this library does not carry -/

/-- The affine implication of the list of **Stacks 0AKY**: a Noetherian affine formal algebraic
space over `S` is countably indexed. The source reads it off the fundamental system of open
ideals `Iⁿ` of a Noetherian adic topological ring, which is countable; this library carries
neither that fundamental system nor the resulting sequential presentation by thickenings. -/
abbrev IsCountablyIndexedOfIsNoetherian : Prop :=
  ∀ U : FppfSheaf B S hS, IsNoetherian B S hS U → IsCountablyIndexed B S hS U

/-- **Stacks 0AKX** in the Noetherian form of **Stacks 0AKW**, together with the uniqueness up
to isomorphism of the presenting ring of a McQuillan affine formal algebraic space (**Stacks
0AIC**): every weakly admissible topological ring presenting an affine formal algebraic space
representable étale over a locally Noetherian formal algebraic space over `S` is Noetherian and
adic. The library takes the atlas of Stacks 0AKY as the definition of "locally Noetherian", so
without this the charts appearing in a chart-tested condition are not known to be objects of
`WAdm^{Noeth}`. -/
abbrev ChartPresentationIsNoetherianAdic : Prop :=
  ∀ (Z : FppfSheaf B S hS), IsLocallyNoetherian B S hS Z →
    ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a →
      ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLinearTopology A A] (E : QuotientSystem B S hS A), (U ≅ formalSpectrum E) →
        IsNoetherianRing A ∧ TopologicalRing.IsAdic A

/-! ### Stacks 0AQN -/

variable {B S hS}

/-- A locally Noetherian formal algebraic space over `S` is locally countably indexed: the
atlas of Noetherian affine formal algebraic spaces of Stacks 0AKY is an atlas of countably
indexed ones. -/
theorem isLocallyCountablyIndexed_of_isLocallyNoetherian
    (hci : IsCountablyIndexedOfIsNoetherian B S hS) {X : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) :
    IsLocallyCountablyIndexed B S hS X := by
  obtain ⟨hform, I, Xi, a, haff, hetale, hsurj, hnoeth⟩ := hX
  exact ⟨hform, I, Xi, a, haff, hetale, hsurj, fun i ↦ hci (Xi i) (hnoeth i)⟩

end AlgebraicGeometry.FormalSpace

end
