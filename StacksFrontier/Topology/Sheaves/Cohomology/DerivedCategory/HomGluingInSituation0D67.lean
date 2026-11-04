module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover

/-!
# Morphisms in Situation 0D67 are morphisms on the ringed site

Let `(X, 𝒪_X)` be a ringed space and let `S` be a system of locally given derived objects on it
(Situation 0D67, `Stacks.DerivedGlueing.LocallyGiven`).  The glueing of morphisms of
[Stacks, Tag 0D66] part (2) is available in this development on the *ringed site*, for objects of
the derived category of `𝒪_X`-modules on the whole of `X` restricted to the slices over the
opens — `Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered`.  Situation
0D67 instead carries objects of `Stacks.DerivedGlueing.OpenDerivedCategory X O`, modules on the
*open subspace* `O`, restricted by the system's own functors `S.restriction`.

The two readings are identified on objects at an arbitrary open by
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension`.  This file identifies them on
morphism groups, `Stacks.DerivedGlueing.homEquivSlice`, using that the passage between the two
models of modules on an open is fully faithful on unbounded derived categories.

## Main definitions

* `Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful` — the passage between the two
  models of modules on an open is fully faithful on unbounded derived categories.
* `Stacks.DerivedGlueing.homEquivSlice` — morphisms between the restrictions displayed by the
  system correspond bijectively to morphisms between the slice-model restrictions of the
  extensions by zero.

## Main results

* `Stacks.DerivedGlueing.subsingleton_shiftedHom_overFunctor_jShriek` — vanishing of the
  shifted morphisms between the restrictions displayed by the system implies vanishing between
  the slice-model restrictions of the extensions by zero.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The passage between the two models of modules on an open is fully faithful on unbounded
derived categories.** -/
def sliceToSubspaceDerivedFullyFaithful (W : Opens X.carrier) :
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory.FullyFaithful :=
  letI := full_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) W
  letI := faithful_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) W
  Functor.FullyFaithful.ofFullyFaithful _

/-- **A morphism between the restrictions displayed by the system is a morphism between the
slice-model restrictions of the extensions by zero.** For objects `K` and `L` given over `O` and
an open `W ≤ O`, the group of morphisms `K|_W ⟶ L|_W` of Situation 0D67 is carried bijectively
to the group of morphisms between the restrictions to the slice over `W` of the global objects
obtained by extending `K` and `L` by zero along `O`.

The objects are identified by `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension`,
and the passage between the two models is dropped by full faithfulness,
`Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful`. -/
def homEquivSlice (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) {W : Opens X.carrier} (hWO : W ≤ O) :
    ((S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) ≃
      ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) ⟶
        (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)) :=
  (Iso.homCongr (S.restrictionIsoOfExtension O W hWO K).symm
      (S.restrictionIsoOfExtension O W hWO L).symm).trans
    (sliceToSubspaceDerivedFullyFaithful W).homEquiv.symm

/-- **The negative-`Ext` hypothesis of Situation 0D67 is the negative-`Ext` hypothesis of the
ringed site.** If the restrictions to `W` displayed by the system admit no nonzero morphism in
degree `i`, then neither do the slice-model restrictions to `W` of the extensions by zero
(the vanishing clause of [Stacks, Tag 0D68], read across the two models). -/
theorem subsingleton_shiftedHom_overFunctor_jShriek (S : LocallyGiven X)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {W : Opens X.carrier} (hWO : W ≤ O)
    (i : ℤ)
    (h : Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
      ((S.restriction W O hWO).obj L) i)) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))
      ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)) i) := by
  have := faithful_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) W
  refine subsingleton_shiftedHom_of_faithful
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory _ _ i ?_
  exact subsingleton_shiftedHom_of_iso (S.restrictionIsoOfExtension O W hWO K)
    (S.restrictionIsoOfExtension O W hWO L) i h

end Stacks.DerivedGlueing

end
