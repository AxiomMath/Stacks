module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Rig.NaiveCotangent

/-!
# Rig-smoothness and rig-étaleness of adic algebras (Stacks 0GAI, 0GAY)

Let `A` be a Noetherian ring, `I` an ideal of `A` and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`.  Then `B` is *rig-smooth* over `(A, I)` when a power of `I`
annihilates `Ext¹` out of the completed naive cotangent complex of `B`, and *rig-étale* over
`(A, I)` when a power of `I` annihilates the completed naive cotangent complex itself in the
derived category of `B`-modules.

## Main definitions

* `Rig.IsRigSmooth`: **Stacks 0GAI**, rig-smoothness over `(A, I)`.
* `Rig.IsRigEtale`: **Stacks 0GAY**, rig-étaleness over `(A, I)`.

## Implementation notes

Both conditions are expressed through a completed polynomial presentation, which is what
represents the completed naive cotangent complex.  Rig-smoothness asks for *some* presentation
and a uniform exponent, rig-étaleness for *every* presentation with an exponent allowed to
depend on it; that these choices do not matter is the content of
`Rig.isRigSmooth_iff` and `Rig.isRigEtale_iff`, which transport the annihilation along the
homotopy equivalence of Stacks 0GAE.  The action of `I` is taken through its image under
`algebraMap A B.carrier`, and the derived-category `Ext` group places the module in degree zero.

The two notions are developed from here along two independent routes, each of which needs only
these definitions and not the other's lemmas: the presentation-independence route
(`StacksFrontier.RingTheory.Restricted.RigSmooth`, `…Restricted.RigEtale`) and the
ideal-of-definition-independence route (`StacksFrontier.RingTheory.Rig.RigSmooth`).  Keeping the
definitions here is what lets both be imported at once.

## References

* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Stacks Project, Tag 0GAI.** Rig-smoothness of an adically finite type `A`-algebra over
`(A, I)`: some uniform power of `I` annihilates `Ext¹` from its completed naive cotangent
complex to every `B`-module. -/
@[stacks 0GAI]
public def IsRigSmooth (B : AdicFiniteTypeAlgebra.{u, v} A I) : Prop :=
  ∃ P : CompletedPolynomialPresentation I B,
    ∃ c : ℕ, ∀ (N : ModuleCat.{max u v} B.carrier)
      (x : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      ∀ a : A, a ∈ I ^ c → (algebraMap A B.carrier a) • x = 0

/-- **Stacks Project, Tag 0GAY.** An adically complete algebra of finite type modulo `I` is
rig-étale over `(A, I)` if some power of `I` acts by zero on its completed naive cotangent
complex in `D(B)`.  The condition is imposed for each completed polynomial presentation
of `B`. -/
@[stacks 0GAY]
public abbrev IsRigEtale (B : AdicFiniteTypeAlgebra.{u, v} A I) : Prop :=
  ∀ P : CompletedPolynomialPresentation I B, ∃ c : ℕ,
    ∀ a : A, a ∈ I ^ c →
      (algebraMap A B.carrier a) •
        𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
          (completedNaiveCotangentComplex B P).cochainComplex) = 0

end Rig

end
