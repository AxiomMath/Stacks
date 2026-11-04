module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of modules and of abelian sheaves agree along an étale morphism of spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Extension by zero
of `𝒪`-modules along `f` is `AlgebraicGeometry.Space.etaleModuleLowerShriek`, the left adjoint
of étale restriction, and extension by zero of abelian sheaves is
`AlgebraicGeometry.Space.abelianEtaleExtensionByZero`.  Forgetting the module structure does
not commute with extension by zero for a general morphism of ringed sites, but Stacks 0798
gives a criterion, and it applies here: every slice functor of postcomposition along an étale
morphism is an equivalence, and the structure morphism of rings is the identity.  So the
abelian sheaf underlying `f_!M` *is* the extension by zero of the abelian sheaf underlying `M`,
and Equation 08GU on abelian sheaves computes the stalks of extension by zero of modules.
The comparison is registered as an instance, so `CategoryTheory.asIso` produces the
isomorphism of functors wherever it is wanted.

## Main results

* `AlgebraicGeometry.Space.isIso_etaleLowerShriekForgetComparison`: **Stacks 0798** for
  postcomposition along an étale morphism of algebraic spaces.

## Implementation notes

`AlgebraicGeometry.Space.etaleRingSheaf` is the structure sheaf of rings of the small étale
site read with its Grothendieck topology written as `AlgebraicGeometry.Space.SmallEtale.topology`
rather than as a projection of `AlgebraicGeometry.Space.smallEtaleRingedSite`.  The two are the
same sheaf, but instance search does not unfold the projection, so the sheaves-of-modules API
cannot find the continuity and adjointness instances it needs when the topology reaches it in
projected form.  The two sheafification hypotheses are restated locally for the same reason:
instance search commits to a sheafification instance at the wrong universe while the universe
of the module sections is still a metavariable.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The structure sheaf of rings of the small étale site of an algebraic space, with its
Grothendieck topology written as `AlgebraicGeometry.Space.SmallEtale.topology`. -/
abbrev etaleRingSheaf (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)

/-- **Stacks 0798** for postcomposition along an étale morphism of algebraic spaces: the
comparison from extension by zero of the underlying abelian sheaf to the underlying abelian
sheaf of extension by zero of modules is an isomorphism, because every slice functor of
postcomposition is an equivalence and the structure morphism of rings is the identity. -/
@[stacks 0798 "postcomposition along an étale morphism of algebraic spaces"]
instance isIso_etaleLowerShriekForgetComparison (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    IsIso (Stacks.SheafOfModules.lowerShriekForgetComparison.{u, u}
      (smallEtalePostcomp B S hS f hf)
      (Stacks.SheafOfModules.structureMap (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS f hf)
        (etaleRingSheaf B S hS Y))) := by
  have hsheafify : HasWeakSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u} :=
    inferInstance
  have hbij : (SmallEtale.topology B S hS Y.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  exact Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
    (smallEtalePostcomp B S hS f hf) (etaleRingSheaf B S hS Y)

end AlgebraicGeometry.Space

end
