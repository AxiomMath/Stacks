module

public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroExtensionClasses
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroSolution
import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphism classes of square-zero extensions of `f⁻¹𝒪_B`-algebras (Stacks 0GQ5)

Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi and `𝒢` an `𝒪`-module. A
square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_ℬ`-algebras is a first order thickening
over the base with an `𝒪`-module isomorphism `𝒢 ≅ Ker(i^♯)`, that is, a solution of the
square-zero extension problem (91.13.0.1) of **Stacks 08UF** for the bottom row
`0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0`: the base reduction of the problem is invertible, and then its
ideal and its prescribed map `c` vanish automatically
(`Deformation.ToposThickening.RingedToposExtensionProblem.subsingleton_ideal`).

**Stacks 0GQ5** says those solutions have exactly `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` many isomorphism classes.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivExt`: the bijection of
  **Stacks 0GQ5** between the isomorphism classes of square-zero extensions and `Ext¹(NL(α), 𝒢)`.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.setoid_iff_isomorphic`: the relation
  that the torsor formalism quotients by — vanishing of the obstruction class of
  **Stacks 08UG** — is isomorphism of solutions.
* `Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivExt_trivialSolution`: the
  bijection is the canonical one, sending the class of `𝒪 ⋉ 𝒢` to `0`.

## Implementation notes

**Hypotheses carried, and why.** Five, and none of them is the bijection.

* `IsIso S.baseReduction`. Not a restriction but the identification of the problem: **Stacks
  0GQ5** is the instance of (91.13.0.1) whose bottom row is `0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0`, and
  a `RingedToposExtensionProblem` is that instance exactly when its base reduction is invertible.
* The difference cocycle `xi` of two solutions and its additivity `hxi`, the representation `rep`
  of every class of `Ext¹` by a homomorphism out of the conormal module (**Stacks 08UJ**, whose
  change of presentation is **Stacks 08TL**), and the pushout construction `pushout` realizing
  every class as a difference. These are the four fields of
  `AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction`, and together `xi` and `pushout`
  are the assertion of the torsor half of **Stacks 08UK**. The presentation the obstruction class
  is attached to is *pair-dependent*: the source enlarges the sheaf of generators `ℰ` to
  `ℰ ×_𝒪 𝒪'` for the chosen solution.
* The bijection `e` between morphisms of solutions and factorizations of the difference map
  through the degree `0` term of `NL(α)`. This is Steps 1 to 3 of the proof of **Stacks 08UG**;
  the vanishing criterion
  `Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff` of that tag does not
  assume it, being stated for those factorizations themselves.

**Why the acting group is the `Ext¹` of a fixed presentation.** `NL(α)` enters through
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm`, the two-term complex
`ℐ/ℐ² ⟶ Ω` of one presentation `α`, so the group here is `Ext¹(NL(α), 𝒢) = (NL(α) ⟶ 𝒢⟦1⟧)` and
not `Ext¹(NL_{𝒪/𝒪_ℬ}, 𝒢)`. Identifying the two is **Stacks 08TY** and **Stacks 08TL**.

**What is *not* restricted.** The left-hand side of the bijection is the honest quotient
`CompatibleFirstOrderThickening.IsomorphismClasses S` — solutions modulo isomorphism of
solutions — and not an auxiliary quotient by the vanishing of an obstruction; that is what
`setoid_iff_isomorphic` buys, using that a morphism of solutions of a ringed-topos extension
problem is automatically invertible. The base point is unconditional given the shape of the
problem, and the bijection is pinned, not merely asserted to exist: it is the obstruction class
against the class of `𝒪 ⋉ 𝒢`, by `classesEquivExt_trivialSolution`.

**Reuse.** The torsor formalism, the two-term complex `NL(α)` and the obstruction class are
stated in the `AlgebraicGeometry.RingedSpaceThickening` namespace over an abstract additive
functor `single : M ⥤ D` into an abstract pretriangulated category, with no ringed space
anywhere, so they are imported here rather than duplicated for topoi; only the solution type is
instantiated, at `CompatibleFirstOrderThickening`.

**Universes.** The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, inherited
from `StacksFrontier/Deformation/ToposThickening/TrivialSquareZeroSolution.lean`, where the trivial
square-zero extension needs a small site whose sheaves of rings have sections in the universe of
the site. The base ringed topos and the ambient triangulated category are unconstrained.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sheaves.Differentials (underlyingRingSheaf)

universe u v' u' w' v₃ u₃

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  (S : RingedToposExtensionProblem X B)
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {single : SheafOfModules.{u} (underlyingRingSheaf X.O) ⥤ D}
  [single.Full] [single.Faithful] [single.Additive]

/-! ### The quotient is by isomorphism of solutions -/

/-- **The relation the torsor formalism quotients by is isomorphism of solutions.** The
obstruction class of [Stacks 08UG] between two solutions of the square-zero extension problem of
[Stacks 08UF] vanishes exactly when they are isomorphic over the fixed diagram. -/
theorem setoid_iff_isomorphic (P : NaiveCotangentTwoTerm single)
    (xi : S.CompatibleFirstOrderThickening → S.CompatibleFirstOrderThickening →
      (P.conormal ⟶ S.G))
    (hxi : ∀ Q₁ Q₂ Q₃ : S.CompatibleFirstOrderThickening,
      xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ S.G // liftingObstruction P S.G δ = ξ })
    (pushout : ∀ (Q : S.CompatibleFirstOrderThickening) (δ : P.conormal ⟶ S.G),
      { Q' : S.CompatibleFirstOrderThickening // xi Q Q' = δ })
    (e : ∀ Q₁ Q₂ : S.CompatibleFirstOrderThickening,
      CompatibleFirstOrderThickening.Hom Q₁ Q₂ ≃
        { θ : P.base ⟶ S.G // P.d ≫ θ = xi Q₁ Q₂ })
    (Q₁ Q₂ : S.CompatibleFirstOrderThickening) :
    (liftingObstructionSolution P S.G xi hxi rep pushout).setoid.r Q₁ Q₂ ↔
      (CompatibleFirstOrderThickening.isomorphicSetoid S).r Q₁ Q₂ :=
  (setoid_iff_nonempty_lift P S.G xi hxi rep pushout e Q₁ Q₂).trans
    (isomorphic_iff_nonempty_hom Q₁ Q₂).symm

/-! ### The bijection -/

/-- The isomorphism classes of square-zero extensions `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_ℬ`-algebras —
equivalently, of first order thickenings over the base with an `𝒪`-module isomorphism
`𝒢 ≅ Ker(i^♯)`, i.e. of solutions of the problem of [Stacks 08UF] whose base reduction is
invertible — are in bijection with `Ext¹(NL(α), 𝒢)`.

The bijection is the torsor of [Stacks 08UK] evaluated at the base point supplied by the trivial
extension `𝒪 ⋉ 𝒢`: a class `q` goes to the obstruction class separating it from the class of
`𝒪 ⋉ 𝒢`, and a class `ξ` of `Ext¹` goes to the class of the solution obtained from `𝒪 ⋉ 𝒢` by
twisting with `ξ`. The five inputs — the four of
`AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction` and the lift bijection `e` of
[Stacks 08UG] — remain hypotheses; see the implementation notes of this file. -/
@[stacks 0GQ5 "the bijection between isomorphism classes of square-zero extensions of 𝒪 by 𝒢 \
as f⁻¹𝒪_ℬ-algebras and Ext¹ of a FIXED presentation α, carrying the four inputs of \
SolutionObstruction (xi, hxi, rep, pushout) and the lift bijection e of 08UG; identifying \
Ext¹(NL(α), 𝒢) with Ext¹(NL_{𝒪/𝒪_ℬ}, 𝒢) is 08TY and 08TL, absent on a general site"]
def classesEquivExt (h : IsIso S.baseReduction) (P : NaiveCotangentTwoTerm single)
    (xi : S.CompatibleFirstOrderThickening → S.CompatibleFirstOrderThickening →
      (P.conormal ⟶ S.G))
    (hxi : ∀ Q₁ Q₂ Q₃ : S.CompatibleFirstOrderThickening,
      xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ S.G // liftingObstruction P S.G δ = ξ })
    (pushout : ∀ (Q : S.CompatibleFirstOrderThickening) (δ : P.conormal ⟶ S.G),
      { Q' : S.CompatibleFirstOrderThickening // xi Q Q' = δ })
    (e : ∀ Q₁ Q₂ : S.CompatibleFirstOrderThickening,
      CompatibleFirstOrderThickening.Hom Q₁ Q₂ ≃
        { θ : P.base ⟶ S.G // P.d ≫ θ = xi Q₁ Q₂ }) :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      (P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧) :=
  (Quotient.congrRight (fun a b =>
      (S.setoid_iff_isomorphic P xi hxi rep pushout e a b).symm)).trans
    ((liftingObstructionSolution P S.G xi hxi rep pushout).isomorphismClassesEquiv
      (S.trivialSolution h))

/-- **The bijection `classesEquivExt` is the canonical one.** It carries the isomorphism class of
the trivial square-zero extension `𝒪 ⋉ 𝒢` to `0`. -/
@[stacks 0GQ5 "that the bijection is canonical: the class of the trivial extension 𝒪 ⋉ 𝒢 goes \
to 0; the hypotheses carried are those of the bijection itself"]
theorem classesEquivExt_trivialSolution (h : IsIso S.baseReduction)
    (P : NaiveCotangentTwoTerm single)
    (xi : S.CompatibleFirstOrderThickening → S.CompatibleFirstOrderThickening →
      (P.conormal ⟶ S.G))
    (hxi : ∀ Q₁ Q₂ Q₃ : S.CompatibleFirstOrderThickening,
      xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ S.G // liftingObstruction P S.G δ = ξ })
    (pushout : ∀ (Q : S.CompatibleFirstOrderThickening) (δ : P.conormal ⟶ S.G),
      { Q' : S.CompatibleFirstOrderThickening // xi Q Q' = δ })
    (e : ∀ Q₁ Q₂ : S.CompatibleFirstOrderThickening,
      CompatibleFirstOrderThickening.Hom Q₁ Q₂ ≃
        { θ : P.base ⟶ S.G // P.d ≫ θ = xi Q₁ Q₂ }) :
    S.classesEquivExt h P xi hxi rep pushout e
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S)
          (S.trivialSolution h)) = 0 :=
  (liftingObstructionSolution P S.G xi hxi rep pushout).o_self _

end Deformation.ToposThickening.RingedToposExtensionProblem

end
