module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Completed constant sheaves and adic lisse sheaves on the pro-étale site

For a module `M` over a ring `Λ` and an ideal `I`, the completed constant sheaf on the small
pro-étale site of a scheme is the inverse limit of the constant sheaves attached to the
quotients `M / IⁿM`. A sheaf of modules is *adic lisse* if, pro-étale locally, it is the
completed constant sheaf of one adically complete module with finite quotient modulo `I`.

## Main definitions

* `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` is the inverse system of quotients of a
  module by the powers of an ideal.
* `AlgebraicGeometry.ProEtale.completedConstantSheaf` is the corresponding limit of constant
  sheaves.
* `AlgebraicGeometry.ProEtale.IsAdicLisse` is the adic lisse predicate for a sheaf of modules.

## Implementation notes

The construction of the completed constant sheaf does not require the Noetherian,
completeness, or finite-residue hypotheses of the source: these delimit the modules used for
adic lisse sheaves, but the inverse limit exists for every module. The quotient system is
indexed by `ℕᵒᵖ`, including the zero quotient at index zero. The result is a sheaf of
`Λ`-modules, so `IsAdicLisse` can use it directly as such.

The local isomorphisms in `IsAdicLisse` use coverings of each object of the pro-étale site and
Mathlib's restriction to the corresponding slice site. The same module is used over every member
of every cover. Noetherianity is not required to formulate this condition, so the definition
also applies to arbitrary commutative rings.

## References

* [Stacks Project, Tag 09BT](https://stacks.math.columbia.edu/tag/09BT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.ProEtale

/-- The tower of quotient modules `M / IⁿM`, with the canonical transition maps. -/
@[implicit_reducible]
def adicQuotientModuleSystem (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    (M : ModuleCat.{w} Λ) : ℕᵒᵖ ⥤ ModuleCat.{w} Λ :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ ModuleCat.of Λ (M ⧸ (I ^ n • ⊤ : Submodule Λ M)))
    (fun n ↦ ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ n)))

/-- The completed constant sheaf `limₙ (M / IⁿM)̲` on the small pro-étale site of `X`.

This is the object that part (3) of [Stacks, Tag 09BT] is stated in terms of, not one of that
definition's four numbered parts, so it carries no registration of its own: part (3) is
`IsAdicLisse` below, which states the whole of it. -/
abbrev completedConstantSheaf (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    (M : ModuleCat.{w} Λ)
    [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ) :=
  limit (adicQuotientModuleSystem Λ I M ⋙
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))

/-- A sheaf which is pro-étale locally the completed constant sheaf of a fixed
`I`-adically complete module with finite quotient modulo `I`. -/
@[stacks 09BT "adic_lisse_sheaf"]
abbrev IsAdicLisse (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  ∃ M : ModuleCat.{w} Λ, IsAdicComplete I M ∧
    Module.Finite Λ (M ⧸ (I • ⊤ : Submodule Λ M)) ∧
    ∀ U : Scheme.ProEt X, ∃ (K : Type (u + 1)) (V : K → Scheme.ProEt X)
      (f : ∀ k, V k ⟶ U), Sieve.ofArrows V f ∈ Scheme.ProEt.topology X U ∧
        ∀ k, Nonempty
          (((Scheme.ProEt.topology X).overPullback (ModuleCat.{w} Λ) (V k)).obj F ≅
            ((Scheme.ProEt.topology X).overPullback (ModuleCat.{w} Λ) (V k)).obj
              (completedConstantSheaf X Λ I M))

end AlgebraicGeometry.ProEtale

end
