module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLift
public import StacksFrontier.Deformation.RingedSpaceThickening.TrivialExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions with a prescribed canonical map form an `Ext¹`-torsor (Stacks 08L7)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces
(`AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening`, a condition on a morphism of
`RingedSpace`s: a homeomorphism with surjective structure-sheaf map whose kernel ideal `ℐ` has
square zero), let `ℱ`, `𝒦` be `𝒪_X`-modules and `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` an `𝒪_X`-linear map.
**Stacks 08L7** says that if there is an extension `0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0` of `𝒪_{X'}`-modules
as in **Stacks 08L4** with `c_{ℱ'} = c`, then the set of isomorphism classes of such extensions
is principal homogeneous under `Ext¹_{𝒪_X}(ℱ, 𝒦)`.

The isomorphism classes of these extensions are the elements of
`AlgebraicGeometry.RingedSpaceThickening.extensionClassesWithAction`: a class in
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` is the same thing as an isomorphism class of extensions of
`i_* ℱ` by `i_* 𝒦`, and the canonical map depends only on the class. The group
`Ext¹_{𝒪_X}(ℱ, 𝒦)` acts through `i_*`, i.e. by adding (Baer sum) the direct image of an
extension of `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extensionClassesWithAction_principalHomogeneous`:
  **Stacks 08L7**. The action `ξ • η = η + i_* ξ` of `Ext¹_{𝒪_X}(ℱ, 𝒦)` preserves the set of
  classes with canonical map `c`, it is an action, and it is simply transitive on that set.

## Implementation notes

The proof assembles the two halves proved in
`StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification` (adding an extension with
direct-image middle term keeps the canonical map; two extensions with the same canonical map
differ by such an extension) with the identification, from
`StacksFrontier.Deformation.RingedSpaceThickening.FlatLift`, of the classes of extensions with
direct-image middle term with the image of the injective map `i_* : Ext¹_{𝒪_X}(ℱ, 𝒦) ⟶
Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` (**Stacks 08KS**: `i_*` is exact and fully faithful with essential
image the modules annihilated by `ℐ`).

The exactness of `i_*` needed to form the map on `Ext` is a theorem
(`AlgebraicGeometry.RingedSpaceThickening.preservesFiniteColimits_modulePushforward` and
`preservesFiniteLimits_modulePushforward`), not a hypothesis; the statement installs it with
`haveI`.

## References

* [Stacks Project, Tag 08L7](https://stacks.math.columbia.edu/tag/08L7)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe e u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- **Stacks 08L7.** Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed
spaces, `ℱ`, `𝒦` two `𝒪_X`-modules and `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` an `𝒪_X`-linear map. The
isomorphism classes of extensions `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` of `𝒪_{X'}`-modules with
`c_{ℱ'} = c` (the set `extensionClassesWithAction i F K hi c ⊆ Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`)
form a principal homogeneous space under `Ext¹_{𝒪_X}(ℱ, 𝒦)`, acting by `ξ • η = η + i_* ξ`:

* the action preserves the set;
* it is an action of the group `Ext¹_{𝒪_X}(ℱ, 𝒦)`: `0` acts trivially and `ξ + ξ'` acts as
  `ξ` followed by `ξ'`;
* it is simply transitive: any two elements `η`, `η'` of the set satisfy `η' = η + i_* ξ` for
  exactly one `ξ ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)`.

So as soon as the set is nonempty (the source's hypothesis that some sequence (08L4) with
`c_{ℱ'} = c` exists, `hc`), every point `η₀` of it identifies it with `Ext¹_{𝒪_X}(ℱ, 𝒦)` via
`ξ ↦ η₀ + i_* ξ`. -/
@[stacks 08L7 "the whole lemma, for a first order thickening of ringed spaces: the isomorphism \
classes of extensions as in 08L4 with `c_{ℱ'} = c`, represented by their classes in \
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`, form a principal homogeneous space under `Ext¹_{𝒪_X}(ℱ, 𝒦)` \
acting through `i_*` by Baer sum"]
theorem extensionClassesWithAction_principalHomogeneous
    {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))]
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X'))]
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i))).obj (F)) ⟶ K)
    (hc : ∃ E : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (firstOrderExtensionAction i F K hi E).val = c) :
    haveI := preservesFiniteColimits_modulePushforward i hi.1
    haveI := preservesFiniteLimits_modulePushforward i
    (extensionClassesWithAction.{e} i F K hi c).Nonempty ∧
      (∀ η ∈ extensionClassesWithAction.{e} i F K hi c, ∀ ξ : Abelian.Ext.{e} F K 1,
        η + ξ.mapExactFunctor (modulePushforward i) ∈ extensionClassesWithAction.{e} i F K hi c) ∧
      (∀ η : Abelian.Ext.{e} ((modulePushforward i).obj F) ((modulePushforward i).obj K) 1,
        η + (0 : Abelian.Ext.{e} F K 1).mapExactFunctor (modulePushforward i) = η ∧
          ∀ ξ ξ' : Abelian.Ext.{e} F K 1,
            η + (ξ + ξ').mapExactFunctor (modulePushforward i) =
              (η + ξ.mapExactFunctor (modulePushforward i)) +
                ξ'.mapExactFunctor (modulePushforward i)) ∧
      ∀ η ∈ extensionClassesWithAction.{e} i F K hi c,
        ∀ η' ∈ extensionClassesWithAction.{e} i F K hi c,
          ∃! ξ : Abelian.Ext.{e} F K 1, η + ξ.mapExactFunctor (modulePushforward i) = η' := by
  have := preservesFiniteColimits_modulePushforward i hi.1
  have := preservesFiniteLimits_modulePushforward i
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨E, hE⟩ := hc
    exact ⟨_, E, rfl, hE⟩
  · rintro η ⟨E₀, rfl, hE₀⟩ ξ
    obtain ⟨D, hDcl, hDess⟩ :=
      exists_yonedaExtension_essImage_extClass_eq_mapExactFunctor i F K ξ
    obtain ⟨E, hEcl, hEact⟩ := exists_extClass_add_of_essImage i F K hi E₀ D hDess
    exact ⟨E, hEcl.trans (by rw [hDcl]), hEact.trans hE₀⟩
  · intro η
    refine ⟨by rw [Abelian.Ext.mapExactFunctor_zero, add_zero], fun ξ ξ' => ?_⟩
    rw [Abelian.Ext.mapExactFunctor_add, add_assoc]
  · rintro η ⟨E₀, rfl, hE₀⟩ η' ⟨E, rfl, hE⟩
    obtain ⟨ζ, ⟨hζ, D, hDcl, hDess⟩, -⟩ :=
      existsUnique_extClass_sub_of_firstOrderExtensionAction_eq i F K hi E₀ E
        (hE.trans hE₀.symm)
    obtain ⟨ξ, hξ, -⟩ := CategoryTheory.Abelian.existsUnique_mapExactFunctor_eq_of_essImage
      (modulePushforward i) ζ ⟨D, hDcl, hDess⟩
    have hsum : (Abelian.YonedaExtension.shortExact E₀).extClass +
        ξ.mapExactFunctor (modulePushforward i) = (Abelian.YonedaExtension.shortExact E).extClass :=
      (congrArg (fun z => (Abelian.YonedaExtension.shortExact E₀).extClass + z) hξ).trans hζ.symm
    refine ⟨ξ, hsum, fun ξ' hξ' => ?_⟩
    exact CategoryTheory.Abelian.mapExactFunctor_injective_one (modulePushforward i) K F
      (add_left_cancel (hξ'.trans hsum.symm))

end AlgebraicGeometry.RingedSpaceThickening

end
