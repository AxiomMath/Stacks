module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveExtComparison
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesTorsor
public import StacksFrontier.Deformation.ToposThickening.SolutionPairCocycle
public import StacksFrontier.Deformation.ToposThickening.SolutionPairSeparation
public import StacksFrontier.Deformation.ToposThickening.SolutionPushoutRealization

/-!
# Isomorphism classes of solutions are a torsor under `Ext¹`

Let `S` be the square-zero extension problem of [Stacks Project, Tag 08UF] for a morphism of
ringed topoi `f : (Sh(C), O) ⟶ (Sh(B), O_B)`, with prescribed module `G`. If a solution exists,
the set of isomorphism classes of solutions is a principal homogeneous space under
`Ext¹_O(NL_f, G)` ([Stacks Project, Tag 08UK]). It is also a principal homogeneous space under
`Ext¹_O(L_f, G)` ([Stacks Project, Tag 08V5], clause (2)).

The class separating two solutions `O'₁` and `O'₂` is the obstruction class `o(O'₁, O'₂)`. This
class is a cocycle, it vanishes exactly when the two solutions are isomorphic, and every class is
`o(O', O'_ξ)` for the pushout solution `O'_ξ`. The second statement follows from the first along
`Ext¹_O(NL_f, G) = Ext¹_O(L_f, G)`.

## Main definitions

All names below are in the namespace
`RingedToposExtensionProblem.CompatibleFirstOrderThickening`.

* `pairObstructionData`: the obstruction class and the pushout solutions, as obstruction data.
* `naiveIsomorphismClassesAddTorsor`: the torsor under `Ext¹_O(NL_f, G)`.
* `isomorphismClassesAddTorsor`: the torsor under `Ext¹_O(L_f, G)`.

## Main results

* `naiveIsomorphismClassesAddTorsor_vsub` and `isomorphismClassesAddTorsor_vsub`: the element
  separating the classes of two solutions is their obstruction class.

## Implementation notes

The ringed topos `X` has a site `C : Type u` with morphisms and structure sheaf in `Type u`. This
is the setting of the pushout construction of `O'_ξ`.

## References

* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceThickening

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

namespace CompatibleFirstOrderThickening

/-- The obstruction data of the solutions of `S`: the obstruction class `o(O'₁, O'₂)` in
`Ext¹_O(NL_f, G)`, which is a cocycle, and the pushout solution `O'_ξ` with `o(O', O'_ξ) = ξ`. -/
noncomputable def pairObstructionData :
    SolutionObstruction S.CompatibleFirstOrderThickening (S.f.naiveCotangentExt (targetG S) 1) where
  o := pairObstruction
  o_add Q₁ Q₂ Q₃ := pairDatumObstruction_add (S := S) Q₁ Q₂ Q₃
  twist Q ξ := Q.twist ξ
  o_twist Q ξ := pairObstruction_twist Q ξ

variable [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **Stacks 08UK**, the torsor half: if the square-zero extension problem has a solution, the
isomorphism classes of solutions are a principal homogeneous space under `Ext¹_O(NL_f, G)`. -/
@[stacks 08UK "the half asserting that, if a solution exists, the set of isomorphism classes of \
solutions is principal homogeneous under Ext¹(NL_f, G); the element separating two classes is \
their obstruction class", instance_reducible]
noncomputable def naiveIsomorphismClassesAddTorsor [Nonempty S.CompatibleFirstOrderThickening] :
    AddTorsor (S.f.naiveCotangentExt (targetG S) 1) (IsomorphismClasses S) :=
  addTorsorOfObstruction (pairObstructionData S)
    (fun P Q ↦ pairObstruction_eq_zero_iff (S := S) P Q) (AddEquiv.refl _)

/-- The element of `Ext¹_O(NL_f, G)` separating the isomorphism classes of two solutions `P` and
`Q` is the obstruction class `o(Q, P)`. -/
theorem naiveIsomorphismClassesAddTorsor_vsub [Nonempty S.CompatibleFirstOrderThickening]
    (P Q : S.CompatibleFirstOrderThickening) :
    letI := naiveIsomorphismClassesAddTorsor S
    (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) P) -ᵥ
        (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) Q) =
      pairObstruction Q P :=
  rfl

/-- **Stacks 08V5**, clause (2): if the square-zero extension problem has a solution, the
isomorphism classes of solutions are a principal homogeneous space under `Ext¹_O(L_f, G)`. -/
@[stacks 08V5 "clause (2): if a solution exists, the set of isomorphism classes of solutions is \
principal homogeneous under Ext¹(L_f, G); the element separating two classes is the image of \
their obstruction class under Ext¹(NL_f, G) = Ext¹(L_f, G)", instance_reducible]
noncomputable def isomorphismClassesAddTorsor [Nonempty S.CompatibleFirstOrderThickening] :
    AddTorsor (S.f.cotangentExt (targetG S) 1) (IsomorphismClasses S) :=
  addTorsorOfObstruction (pairObstructionData S)
    (fun P Q ↦ pairObstruction_eq_zero_iff (S := S) P Q)
    (S.f.naiveExtOneEquiv (targetG S)).symm

/-- The element of `Ext¹_O(L_f, G)` separating the isomorphism classes of two solutions `P` and
`Q` is the image of the obstruction class `o(Q, P)`, that is, its precomposition with the
canonical map `L_f ⟶ NL_f`. -/
theorem isomorphismClassesAddTorsor_vsub [Nonempty S.CompatibleFirstOrderThickening]
    (P Q : S.CompatibleFirstOrderThickening) :
    letI := isomorphismClassesAddTorsor S
    (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) P) -ᵥ
        (show IsomorphismClasses S from Quotient.mk (isomorphicSetoid S) Q) =
      S.f.naiveExtOneEquiv (targetG S) (pairObstruction Q P) :=
  rfl

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
