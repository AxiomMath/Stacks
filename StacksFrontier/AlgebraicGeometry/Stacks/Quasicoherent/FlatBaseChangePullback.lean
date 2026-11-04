module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent

/-!
# Inverse image of a module in `LQCoh^fbc` (Stacks 0771, part (3))

Let `g : 𝒵 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S`. **Stacks 0771** part (3) says that
the inverse image `g^{-1}` carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒵)`, where `LQCoh^fbc` is
the category of **Stacks 07AQ**: the modules on the étale site which are locally quasi-coherent
(**Stacks 06WJ**) and have the flat base change property (**Stacks 0762**).

The source proves it by citing the two halves separately. The local quasi-coherence half is
**Stacks 06WL** and is available, as
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_stackModulePresheafPullback`. The flat base change
half is **Stacks 0764** part (1), which is not available; it is the hypothesis `hfbc`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_of_iso`: membership in
  `LQCoh^fbc(𝒪_𝒳)` transports along an isomorphism of presheaves of modules.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback`:
  **Stacks 0771** part (3), with the flat base change property of the inverse image assumed.

## Implementation notes

**Stacks 0764** part (1) is the statement that the comparison maps of **Stacks 0761** for
`g^{-1}F` are instances of those for `F`. Its ingredients at the level of sheaves of *sets* are
available: **Stacks 075D** part (3) identifies the restriction of `g^{-1}F` at an object `z` of
`𝒵` with the restriction of `F` at `g z`
(`AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso`), and **Stacks 075D** part (4)
says the comparison maps match under that identification
(`AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso`). What is
missing is the module-level form of part (4). Part (3) has been carried to modules, as
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageIso`, and part (4) has not; the
two sides of its square are maps of presheaves of modules over the two maps of structure sheaves
`AlgebraicGeometry.Stack.smallEtaleStructureComparison` for `𝒵` and for `𝒳`, which are built
from the localization equivalences of **Stacks 06W0** at `z` and at `g z` and are therefore not
the same map on the nose, so the square cannot even be formed before those two are identified.

The 1-morphism is presented strictly, through `CategoryTheory.CatFiberedInGroupoids.homFunctor`,
and the inverse image of a module along it is
`AlgebraicGeometry.Stack.stackModulePresheafPullback`, as for **Stacks 07AQ** part (1) in
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_of_isSmooth_jointlySurjective`.
The module sections are pinned to the universe `u` of the schemes, as the comparison map of
**Stacks 06WC** pins them.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Membership in `LQCoh^fbc(𝒪_𝒳)` transports along an isomorphism of presheaves of modules
over the structure sheaf of a category fibred in groupoids: local quasi-coherence does by
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_iso` and the flat base change property by
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_iso`. -/
theorem isLocallyQuasicoherentWithFlatBaseChange_of_iso {𝒳 : Type*} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj} (e : F ≅ G)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F) :
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp G :=
  ⟨isLocallyQuasicoherent_of_iso B E h S hS p hp e hF.1,
    hasFlatBaseChangeProperty_of_iso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) e hF.2⟩

/-- **Stacks 0771, part (3), the local quasi-coherence half.** Let `g : 𝒵 ⟶ 𝒳` be a 1-morphism
of algebraic stacks over `S` and let `F` lie in `LQCoh^fbc(𝒪_𝒳)`. Then the inverse image
`g^{-1}F` lies in `LQCoh^fbc(𝒪_𝒵)`.

Local quasi-coherence of `g^{-1}F` is **Stacks 06WL**, which holds for every 1-morphism of
categories fibred in groupoids. The flat base change property of `g^{-1}F` is the hypothesis
`hfbc`: the source deduces it from **Stacks 0764** part (1), whose module-level ingredient — the
form of **Stacks 075D** part (4) for presheaves of modules — is not available; see the
implementation notes of this file. -/
@[stacks 0771 "part (3), the local quasi-coherence half: the inverse image along a 1-morphism \
  of algebraic stacks of a module in LQCoh^fbc lies in LQCoh^fbc, with the flat base change \
  property of the inverse image assumed (Stacks 0764 part (1))"]
theorem isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F)
    (hfbc : HasFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) (etaleTopology B)
      (etaleTopology_le_topology B)
      ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F)) :
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F) :=
  ⟨isLocallyQuasicoherent_stackModulePresheafPullback B E h S hS g F hF.1, hfbc⟩

end AlgebraicGeometry.Stack

end
