module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism

/-!
# Isomorphism classes of solutions as a principal homogeneous space

Let `S` be a square-zero extension problem for a morphism of ringed topoi, as in
[Stacks Project, Tag 08UF]. Suppose its solutions carry obstruction data
`T : SolutionObstruction S.CompatibleFirstOrderThickening E`: a cocycle `o` of classes in an
abelian group `E`, and the construction `Q ↦ Q_ξ` with `o Q Q_ξ = ξ`. Suppose also that
`o P Q = 0` exactly when there is a morphism of solutions `P ⟶ Q`. Then the isomorphism classes
of solutions are a principal homogeneous space under `E`, and under any group `G ≃+ E`.

## Main definitions

* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.obstructionClassesEquiv`: the
  isomorphism classes of solutions are the classes of the setoid of `T`.
* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.addTorsorOfObstruction`: the
  principal homogeneous space structure.

## Main results

* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.addTorsorOfObstruction_vsub`: the
  element of `G` that separates two isomorphism classes is the obstruction class between any two
  representatives.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceThickening

universe v u w v' u' w' t

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [(forget CommRingCat.{w}).ReflectsIsomorphisms]

namespace CompatibleFirstOrderThickening

variable {E : Type t} [AddCommGroup E] (T : SolutionObstruction S.CompatibleFirstOrderThickening E)
  (hT : ∀ P Q : S.CompatibleFirstOrderThickening, T.o P Q = 0 ↔ Nonempty (Hom P Q))

/-- When the obstruction class of `T` vanishes exactly between solutions joined by a morphism,
the classes of the setoid of `T` are the isomorphism classes of solutions. -/
noncomputable def obstructionClassesEquiv : T.IsomorphismClasses ≃ IsomorphismClasses S :=
  Quotient.congr (Equiv.refl _) fun P Q => (hT P Q).trans (isomorphic_iff_nonempty_hom P Q).symm

/-- The equivalence `obstructionClassesEquiv` sends the class of a solution to its isomorphism
class. -/
theorem obstructionClassesEquiv_isoClass (P : S.CompatibleFirstOrderThickening) :
    obstructionClassesEquiv T hT (T.isoClass P) =
      (Quotient.mk (isomorphicSetoid S) P : IsomorphismClasses S) :=
  rfl

/-- **The isomorphism classes of solutions are a principal homogeneous space.** Given obstruction
data `T` whose class vanishes exactly between solutions joined by a morphism, and an additive
isomorphism `g : G ≃+ E`, the isomorphism classes of solutions are a principal homogeneous space
under `G`, provided a solution exists. -/
@[instance_reducible]
noncomputable def addTorsorOfObstruction {G : Type*} [AddCommGroup G] (g : G ≃+ E)
    [Nonempty S.CompatibleFirstOrderThickening] : AddTorsor G (IsomorphismClasses S) :=
  addTorsorCongr g (obstructionClassesEquiv T hT).symm

/-- The element of `G` separating the isomorphism classes of two solutions `P` and `Q` is the
obstruction class from `Q` to `P`, carried to `G`. -/
theorem addTorsorOfObstruction_vsub {G : Type*} [AddCommGroup G] (g : G ≃+ E)
    [Nonempty S.CompatibleFirstOrderThickening] (P Q : S.CompatibleFirstOrderThickening) :
    letI := addTorsorOfObstruction T hT g
    (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) P) -ᵥ
        (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) Q) =
      g.symm (T.o Q P) :=
  rfl

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
