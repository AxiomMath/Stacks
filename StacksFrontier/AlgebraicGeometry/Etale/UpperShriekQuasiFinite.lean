module

public import Mathlib.Algebra.Category.Grp.Subobject
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition

import StacksCore.Tactic.StacksAttribute

/-!
# Upper shriek for locally quasi-finite morphisms

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site. The direct image with
compact support `f_! : Ab(X_étale) ⟶ Ab(Y_étale)` is exact and commutes with arbitrary direct
sums, which is Stacks 0F5F, and therefore preserves every colimit. The category of abelian
sheaves on the small étale site is cocomplete, locally small, well-copowered and has a
separator, so the special adjoint functor theorem produces a right adjoint
`f^! : Ab(Y_étale) ⟶ Ab(X_étale)`.

Warning: this `f^!` is the non-derived version.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fUpperShriekFunctor` — the functor `f^!`, and
  `AlgebraicGeometry.SmallEtale.fShriekAdjunction` the adjunction `f_! ⊣ f^!`.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekFunctor_preservesColimitsOfSize` — `f_!` preserves all
  colimits of abelian étale sheaves.
* `AlgebraicGeometry.SmallEtale.fShriekFunctor_isLeftAdjoint` — **`f_!` has a right adjoint.**

## Implementation notes

The route to the adjoint is the special adjoint functor theorem, Mathlib's
`CategoryTheory.isLeftAdjoint_of_preservesColimits_of_isSeparating`, rather than the source's
appeal to the dual of Stacks 0793 with the class of products of skyscraper sheaves. The two need
the same input: the source derives representability of `F ↦ Hom(f_!F, ȳ_*A)` from the stalk
decomposition of `f_!`, and the stalk decomposition is also what gives exactness and commutation
with direct sums, which is what the adjoint functor theorem consumes. Taking the latter route
avoids constructing the Godement embedding of Étale Cohomology, Theorem 03PU into the argument.

The functor `f^!` is the canonical chosen right adjoint `CategoryTheory.Functor.rightAdjoint`
of the `CategoryTheory.Functor.IsLeftAdjoint` instance, together with the adjunction
`CategoryTheory.Adjunction.ofIsLeftAdjoint`. It is therefore pinned down up to canonical
isomorphism by the adjunction, which is what statements about `f^!` are proved from.

## References

* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0793](https://stacks.math.columbia.edu/tag/0793)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The direct image with compact support of a locally quasi-finite morphism preserves all
colimits of abelian étale sheaves: it is exact and commutes with arbitrary direct sums, which is
Stacks 0F5F, and every colimit is a coequalizer of a map between coproducts. -/
public theorem fShriekFunctor_preservesColimitsOfSize :
    PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v} (fShriekFunctor.{u, v} B f) := by
  have hcoeqX : HasCoequalizers
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  have hcopX : HasCoproducts.{max (u + 1) v}
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :=
    fun _ => Sheaf.instHasColimitsOfShape
  have hExact := (exactFunctor_iff _).mp (fShriekFunctor_exact.{u, v} B f)
  have hfin : PreservesFiniteColimits (fShriekFunctor.{u, v} B f) := hExact.2
  have hcoeq : PreservesColimitsOfShape WalkingParallelPair (fShriekFunctor.{u, v} B f) :=
    inferInstance
  have hcop : ∀ I : Type (max (u + 1) v),
      PreservesColimitsOfShape (Discrete I) (fShriekFunctor.{u, v} B f) :=
    fun I => fShriekFunctor_preservesCoproductsOfShape.{u, v} B f I
  exact preservesColimits_of_preservesCoequalizers_and_coproducts _

/-- **Stacks 0F59, part (1).** The direct image with compact support
`f_! : Ab(X_étale) ⟶ Ab(Y_étale)` of a locally quasi-finite morphism of schemes has a right
adjoint `f^! : Ab(Y_étale) ⟶ Ab(X_étale)`. -/
@[stacks 0F59 "part (1), f_! on abelian étale sheaves has a right adjoint f^!"]
public instance fShriekFunctor_isLeftAdjoint :
    (fShriekFunctor.{u, v} B f).IsLeftAdjoint := by
  have hcolX : HasColimitsOfSize.{max (u + 1) v, max (u + 1) v}
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfSize
  have := fShriekFunctor_preservesColimitsOfSize.{u, v} B f
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{max (u + 1) v}
    (isSeparator_separator _) _

/-- The functor `f^! : Ab(Y_étale) ⟶ Ab(X_étale)` right adjoint to the direct image with
compact support of a locally quasi-finite morphism. -/
public def fUpperShriekFunctor :
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} :=
  (fShriekFunctor.{u, v} B f).rightAdjoint

/-- The adjunction `f_! ⊣ f^!` on abelian sheaves of the small étale sites. -/
public def fShriekAdjunction :
    fShriekFunctor.{u, v} B f ⊣ fUpperShriekFunctor.{u, v} B f :=
  Adjunction.ofIsLeftAdjoint (fShriekFunctor.{u, v} B f)

end AlgebraicGeometry.SmallEtale

end
