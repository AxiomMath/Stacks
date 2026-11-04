module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
import StacksCore.Tactic.StacksAttribute

/-!
# Representing Ext classes of a naive cotangent complex by conormal homomorphisms

Let `𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on a topological space and let
`𝒢` be a `ℬ`-module. Every first Ext class of the naive cotangent complex `NL_{ℬ/𝒜}` becomes,
along the canonical comparison map of a suitable family of generators `α : ℰ ⟶ ℬ`, the class of
a homomorphism `ℐ/ℐ² ⟶ 𝒢` out of the conormal sheaf of the presentation of `ℬ` by `ℰ`.

## Main results

* `Stacks.SheafOfModules.ConormalRepresentative.exists_enlargement_conormalExtClass`: the
  statement above, on the site of open sets of a topological space.

## References

* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace Stacks.SheafOfModules.ConormalRepresentative

open Stacks.Sites.FreeAlgebra

variable (X : Type u) [TopologicalSpace X]

/-- **Stacks Project, Tag 08UB.** Let `𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative
rings on a topological space, let `𝒢` be a `ℬ`-module and let `ξ` be a first Ext class of
`NL_{ℬ/𝒜}` with values in `𝒢`. There is a family of generators `α : ℰ ⟶ ℬ` presenting `ℬ` over
`𝒜` for which `ξ`, restricted along the canonical comparison map `NL(α) ⟶ NL_{ℬ/𝒜}`, is the
class of a homomorphism `ℐ/ℐ² ⟶ 𝒢` out of the conormal sheaf. -/
@[stacks 08UB "on the site of open sets of a topological space, the setting of the statement; \
the family of generators and the homomorphism are produced by the proof"]
theorem exists_enlargement_conormalExtClass
    [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{max w u}]
    [(Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ CommRingCat.{max w u} RingCat.{max w u})]
    (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{max w u}) (a : A ⟶ B)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w u}]
    [HasDerivedCategory.{w} (SheafOfModules.{max w u} (Stacks.SheafOfModules.Tensor.ringSheaf B))]
    (G : SheafOfModules.{max w u} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, max w u, w}
          (Opens.grothendieckTopology X) A B a))
      ((DerivedCategory.singleFunctor _ 0).obj G) 1) :
    ∃ (E : Sheaf (Opens.grothendieckTopology X) (Type (max w u)))
      (α : E.obj ⟶ underlyingPresheaf (Opens.grothendieckTopology X) B)
      (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X) A B a E.obj α).hom),
      letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X) A B a E.obj α).hom :=
        hsurj
      ∃ f : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, max w u, w}
          (Opens.grothendieckTopology X) A B a E.obj α).X₁ ⟶ G,
        DerivedCategory.Q.map
            (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, max w u, w}
              (Opens.grothendieckTopology X) A B a E.obj α) ≫ ξ =
          Stacks.SheafOfModules.presentationConormalExtClass.{u, u, w, w}
            (Opens.grothendieckTopology X) A B a E.obj α G f :=
  Stacks.SheafOfModules.exists_presentation_conormalExtClass.{u, u, w, w}
    (Opens.grothendieckTopology X) A B a G ξ

end Stacks.SheafOfModules.ConormalRepresentative

end
