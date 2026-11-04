module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenObjects

/-!
# K-injective representatives of derived objects on an open subspace

The proof of [Stacks, Tag 0D6B] begins by choosing, for each member `W_α` of a well ordered
increasing cover, a K-injective complex `I_α` of `O_{W_α}`-modules *representing* the prescribed
object `K_α` of `D(O_{W_α})`.  This file carries that step: every object of the unbounded
derived category of a Grothendieck abelian category is the image under
`CategoryTheory.DerivedCategory.Q` of a K-injective complex, and in particular every object of
`D(O_U)` is.

It is a step of the proof of that tag rather than a clause of its statement, so nothing here
carries a `@[stacks]` attribute.

## Main results

* `Stacks.DerivedGlueing.exists_isKInjective_representative`: in a Grothendieck abelian
  category every object of the unbounded derived category is isomorphic to the image of a
  K-injective complex.
* `Stacks.DerivedGlueing.exists_isKInjective_representative_openDerivedCategory`: the same for
  the modules on an open subspace of a ringed space, which is the form the recursion of
  [Stacks, Tag 0D6B] uses.

## Implementation notes

This hosts in one place a statement the development previously had only as two *private*
clones, `exists_kInjectiveModel` in
`StacksFrontier.Homology.HomComplex.Evaluation.Iterated` and `exists_kInjective_model` in
`StacksFrontier.Homology.Perfect.SystemDuality`, both of them under the
`EnoughInjectives`-plus-countable-products hypotheses of Spaltenstein's construction.  The
Grothendieck abelian hypothesis used here is the one that is available on an open subspace, and
the resolution it feeds on is the development's [Stacks, Tag 079P],
`Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`.

The *other* complex-level step of that tag — realising a morphism of the derived category whose
target is K-injective as an honest map of complexes — is **not** restated here: it is already
`StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective`.

Neither step is a Mathlib result.  Mathlib defines `CochainComplex.IsKInjective` and proves
that maps into a K-injective complex are already correct on the homotopy category
(`CochainComplex.IsKInjective.Qh_map_bijective`), but it contains no existence theorem for
K-injective resolutions of an unbounded complex; that is what Tag 079P supplies.  Essential
surjectivity of `CategoryTheory.DerivedCategory.Q` *is* a Mathlib instance, `Q` being a
localization functor.

For the modules on an open subspace the Grothendieck abelian hypothesis is discharged by
instance search at the diagonal universe:
`IsGrothendieckAbelian.{u} (SheafOfModules.{u} (restrictedRingSheaf X U))`.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Stacks.DerivedGlueing

universe w v u

/-- **Every derived object has a K-injective representative.** In a Grothendieck abelian
category every object of the unbounded derived category is isomorphic to the image of a
K-injective complex.

This is the first step of the proof of [Stacks, Tag 0D6B].  Any complex representing the object
is resolved by `Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`, which is
[Stacks, Tag 079P]; the resolution is a quasi-isomorphism, hence inverted by
`CategoryTheory.DerivedCategory.Q`. -/
theorem exists_isKInjective_representative {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w, v, u} C] [HasDerivedCategory C] (K : DerivedCategory C) :
    ∃ I : CochainComplex C ℤ, I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ K) := by
  obtain ⟨I, q, hI, hq⟩ :=
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
      (DerivedCategory.Q.objPreimage K)
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map q)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

section OpenSubspace

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Every object of `D(O_U)` has a K-injective representative.**
`Stacks.DerivedGlueing.exists_isKInjective_representative` for the modules on an open subspace
`U` of a ringed space `X`, which is the form in which the recursion of [Stacks, Tag 0D6B] uses
it.  The Grothendieck abelian hypothesis is supplied by instance search. -/
theorem exists_isKInjective_representative_openDerivedCategory (X : RingedSpace.{u, u})
    (U : Opens X.carrier) (K : OpenDerivedCategory X U) :
    ∃ I : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ,
      I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ K) :=
  exists_isKInjective_representative.{u} K

end OpenSubspace

end Stacks.DerivedGlueing

end
