module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalkFree

/-!
# Freeness of a fixed finite rank of a stalk is invariant under an isomorphism of modules

An isomorphism of `𝒪_X`-modules induces a linear equivalence of their stalks at every point: the
additive stalk functor carries an isomorphism of the underlying presheaves of abelian groups to
an isomorphism, and the induced map of stalks is linear over the stalk of the structure sheaf by
`SheafOfModules.FlatShortExact.stalkLinearMap`. Consequently
`AlgebraicGeometry.StalkFreeOfRank` is an isomorphism invariant.

This is what lets the fpqc descent of the generic-point condition of Situation 05MP move freeness
of a stalk across the comparison of the two base-changed modules: the module on `X ×_S T'` is
only *isomorphic* to the pullback of the module on `X ×_S T` along the transition morphism, not
equal to it, so the descent along the transition — which is stated for a pullback — has to be
fed through that isomorphism.

## Main definitions

* `AlgebraicGeometry.stalkLinearEquivOfModuleIso`: the linear equivalence of stalks induced by an
  isomorphism of modules.

## Main results

* `AlgebraicGeometry.StalkFreeOfRank.of_moduleIso`: freeness of a fixed finite rank of a stalk is
  carried along an isomorphism of modules.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The linear equivalence of stalks induced by an isomorphism of sheaves of modules.** The
stalk functor carries an isomorphism to an isomorphism, and the induced map of stalks is linear
over the stalk of the structure sheaf. -/
noncomputable def stalkLinearEquivOfModuleIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf x :=
  LinearEquiv.ofBijective (Stacks.SheafOfModules.FlatShortExact.stalkLinearMap e.hom x)
    ((ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).mapIso
          ((SheafOfModules.forget _).mapIso e))).hom).mp inferInstance)

/-- **Freeness of a fixed finite rank of a stalk is invariant under an isomorphism of modules.**
The stalks are linearly equivalent over the local ring at the point, so a trivialisation of one
transports to the other. -/
theorem StalkFreeOfRank.of_moduleIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (x : X)
    (p : ℕ) (h : StalkFreeOfRank M x p) : StalkFreeOfRank N x p :=
  h.elim fun g => ⟨(stalkLinearEquivOfModuleIso e x).symm.trans g⟩

end AlgebraicGeometry

end
