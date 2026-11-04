module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictPullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The ideal sheaf and the conormal sheaf are local on the ambient space

Let `i : Z ⟶ X` be a morphism of ringed spaces, let `U` be an open subspace of `X` and write
`V = i⁻¹U`, so that `i` restricts to `i|_V : Z|_V ⟶ X|_U`
(`AlgebraicGeometry.RingedSpace.restrictHom`). This file proves two things:

* the ideal sheaf of `i|_V` is the restriction to `U` of the ideal sheaf of `i`, and
* the conormal sheaf of `i|_V` is the restriction to `V` of the conormal sheaf of `i`.

The second is the content of the first assertion of [Stacks Project, Tag 01R3] part (1), that
the conormal sheaf of an immersion does not depend on which open subscheme the immersion is
factored through as a closed immersion: two such opens are compared through their intersection,
and over the intersection both computations are the one carried out here. See the implementation
notes for what still separates this from the statement of that tag.

Both statements are *isomorphisms*, not equalities, and both come with the lemma that pins them
down: a bundled isomorphism whose type does not mention its characterisation asserts nothing by
itself.

## Main definitions

* `Stacks.ClosedImmersion.restrictPushforwardUnitIso` is the base-change square
  `(i_* 𝒪_Z)|_U ≅ (i|_V)_* 𝒪_{Z|V}` of
  `AlgebraicGeometry.RingedSpace.restrictPushforwardStructureModuleIso`, restated at the
  `structureSheafRing` types.
* `Stacks.ClosedImmersion.restrictIdealSheafMap` is the canonical map `ℐ_i|_U ⟶ ℐ_{i|_V}`, and
  `Stacks.ClosedImmersion.restrictIdealSheafIso` is the isomorphism it is.
* `Stacks.ClosedImmersion.restrictConormalSheafIso` is the identification
  `𝒞_i|_V ≅ 𝒞_{i|_V}`.

## Main results

* `Stacks.ClosedImmersion.moduleRestrict_map_structureSheafModuleHom`: restricting the
  structure-sheaf map `𝒪_X ⟶ i_* 𝒪_Z` to `U` and comparing along
  `restrictPushforwardUnitIso` gives the structure-sheaf map of `i|_V`. This holds by `rfl`, and
  it is the only input the file needs beyond left exactness of restriction.
* `Stacks.ClosedImmersion.restrictIdealSheafMap_comp_ι` and
  `Stacks.ClosedImmersion.restrictIdealSheafIso_hom_comp_ι`: the identification of ideal sheaves
  is compatible with the two inclusions into the structure sheaf. Since those inclusions are
  monomorphisms this determines it uniquely.
* `Stacks.ClosedImmersion.restrictConormalSheafIso_hom_comp_pullback_ι`: the identification of
  conormal sheaves, read inside `(i|_V)^* 𝒪_{X|U}`, is the restriction of the corresponding map
  for `i`. This is the pinning lemma for `restrictConormalSheafIso`.

## Implementation notes

The ideal sheaf is a kernel, so the first statement needs restriction to be left exact
(`AlgebraicGeometry.RingedSpace.moduleRestrict_preservesFiniteLimits`) and needs the restriction
of the structure-sheaf map of `i` to be the structure-sheaf map of `i|_V`. The latter is exactly
how `AlgebraicGeometry.RingedSpace.restrictHom` was built, so it holds by `rfl`; the rest is the
universal property of the kernel.

The two morphisms are written out with `CategoryTheory.Limits.kernel.lift` and the round trips
are checked by cancelling a monomorphism, rather than assembling
`CategoryTheory.Limits.PreservesKernel.iso`, `CategoryTheory.Limits.kernelIsoOfEq` and
`CategoryTheory.Limits.kernelCompMono` into a composite isomorphism. The composite exists and is
the same isomorphism, but its pinning lemma is then out of reach of `rw`: the object
`(moduleRestrict X U).obj (SheafOfModules.unit (structureSheafRing X))` and the structure sheaf
`SheafOfModules.unit (structureSheafRing (X|U))` of the open subspace are definitionally but not
syntactically equal, so a goal mentioning both is not type-correct at `implicit` transparency
and no rewrite motive can be built. Stating the two morphisms directly keeps every step either
`rfl`, a `CategoryTheory.Limits.kernel.lift_ι`, or an `Eq.trans` chain checked at default
transparency.

**Nothing here carries a `01R3` attribute.** What [Stacks Project, Tag 01R3] part (1) asserts is
that for an immersion `j : Z ⟶ X` of *schemes* and an open `U ⊆ X` through which `j` factors as
a closed immersion `j' : Z ⟶ U`, the conormal sheaf of `j` — defined through the factorization
over `X ∖ ∂Z` — is `(j')^* ℐ_{j'}`. That tag is proved in
`StacksFrontier.AlgebraicGeometry.Conormal.OpenFactorization`, but *not* by transporting
`restrictConormalSheafIso`: doing so would need the comparison of `↥U` with
`↥(j.coborderRange.ι ⁻¹ᵁ U)`, which are homeomorphic but not equal, together with
`Z|_⊤ ≅ Z` for the preimage of `U` in `Z`. Conjugating the structure-sheaf map of `j' ≫ ι_U`
along `ι_U` instead keeps every object in the vocabulary the tag is stated in and needs neither
comparison; see that module's docstring. The statements here are the ambient-locality form of
the same fact and are what a *second* open subspace would be compared through.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

namespace Stacks.ClosedImmersion

universe u

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-! ### The structure-sheaf map restricts to the structure-sheaf map -/

/-- **`(i_* 𝒪_Z)|_U ≅ (i|_V)_* 𝒪_{Z|V}`**, the base-change square at the structure sheaf.

This is `AlgebraicGeometry.RingedSpace.restrictPushforwardStructureModuleIso` with its type
written through `structureSheafRing` and
`CategoryTheory.SheafOfModules.unit` instead of through `StrictlyPerfect.structureSheafOfRings`
and `StrictlyPerfect.structureModule`. The two vocabularies describe the same objects, but
typeclass resolution unfolds only at reducible transparency and does not identify them, so an
isomorphism stated in one of them cannot be composed with the kernels below, which live in the
other. -/
def restrictPushforwardUnitIso :
    (moduleRestrict X U).obj
        ((modulePushforward i).obj (SheafOfModules.unit (structureSheafRing Z))) ≅
      (modulePushforward (restrictHom i U)).obj (SheafOfModules.unit
        (structureSheafRing (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding))) :=
  restrictPushforwardStructureModuleIso i U

/-- **The structure-sheaf map of `i` restricts to the structure-sheaf map of `i|_V`.**
Restricting `𝒪_X ⟶ i_* 𝒪_Z` to the open subspace `U` and comparing the target along
`Stacks.ClosedImmersion.restrictPushforwardUnitIso` gives `𝒪_{X|U} ⟶ (i|_V)_* 𝒪_{Z|V}`.

This holds by `rfl`: the structure-sheaf map of `i|_V` is by construction `i^♯` over `ι_U W`
followed by a restriction of sections, which is precisely what the left-hand side computes. It
is the only fact about `AlgebraicGeometry.RingedSpace.restrictHom` that this file uses. -/
theorem moduleRestrict_map_structureSheafModuleHom :
    (moduleRestrict X U).map (structureSheafModuleHom i) ≫
        (restrictPushforwardUnitIso i U).hom =
      structureSheafModuleHom (restrictHom i U) :=
  rfl

/-- `Stacks.ClosedImmersion.moduleRestrict_map_structureSheafModuleHom` solved for the
restriction of the structure-sheaf map. -/
theorem moduleRestrict_map_structureSheafModuleHom_eq :
    (moduleRestrict X U).map (structureSheafModuleHom i) =
      structureSheafModuleHom (restrictHom i U) ≫ (restrictPushforwardUnitIso i U).inv :=
  (Iso.eq_comp_inv _).mpr (moduleRestrict_map_structureSheafModuleHom i U)

/-! ### The ideal sheaf is local on the ambient space -/

/-- The inclusion of an ideal sheaf into the structure sheaf is killed by the structure-sheaf
map. -/
private theorem idealSheafι_comp_hom_eq_zero {W W' : RingedSpace.{u, u}} (j : W ⟶ W') :
    idealSheafι j ≫ structureSheafModuleHom j = 0 :=
  kernel.condition _

/-- The restriction to `U` of the inclusion `ℐ_i ⟶ 𝒪_X` is killed by the structure-sheaf map of
`i|_V`. This is what makes `Stacks.ClosedImmersion.restrictIdealSheafMap` exist. -/
theorem moduleRestrict_idealSheafι_comp_structureSheafModuleHom :
    (moduleRestrict X U).map (idealSheafι i) ≫
      structureSheafModuleHom (restrictHom i U) = 0 := by
  rw [← moduleRestrict_map_structureSheafModuleHom i U, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp,
    idealSheafι_comp_hom_eq_zero, CategoryTheory.Functor.map_zero, zero_comp]

/-- The inclusion `ℐ_{i|_V} ⟶ 𝒪_{X|U}` is killed by the restriction to `U` of the
structure-sheaf map of `i`. This is what makes `Stacks.ClosedImmersion.restrictIdealSheafInv`
exist. -/
theorem idealSheafι_comp_moduleRestrict_map_structureSheafModuleHom :
    idealSheafι (restrictHom i U) ≫
      (moduleRestrict X U).map (structureSheafModuleHom i) = 0 :=
  by rw [moduleRestrict_map_structureSheafModuleHom_eq, ← Category.assoc,
    idealSheafι_comp_hom_eq_zero, zero_comp]

/-- **The canonical map `ℐ_i|_U ⟶ ℐ_{i|_V}`.** The restriction of the ideal sheaf of `i` to the
open subspace `U` lands in the ideal sheaf of the restricted morphism, because its image in
`𝒪_{X|U}` is killed by the structure-sheaf map of `i|_V`. -/
def restrictIdealSheafMap :
    (moduleRestrict X U).obj (idealSheaf i) ⟶ idealSheaf (restrictHom i U) :=
  kernel.lift _ _ (moduleRestrict_idealSheafι_comp_structureSheafModuleHom i U)

/-- **The characterising property of `Stacks.ClosedImmersion.restrictIdealSheafMap`.** Followed
by the inclusion of `ℐ_{i|_V}` into `𝒪_{X|U}` it is the restriction to `U` of the inclusion of
`ℐ_i` into `𝒪_X`. Since those inclusions are monomorphisms, this determines the map. -/
@[simp]
theorem restrictIdealSheafMap_comp_ι :
    restrictIdealSheafMap i U ≫ idealSheafι (restrictHom i U) =
      (moduleRestrict X U).map (idealSheafι i) :=
  kernel.lift_ι _ _ _

/-- The inverse of `Stacks.ClosedImmersion.restrictIdealSheafMap`: the inclusion
`ℐ_{i|_V} ⟶ 𝒪_{X|U}` lifts through the restriction of the kernel defining `ℐ_i`, because
restriction to an open subspace is left exact. -/
def restrictIdealSheafInv :
    idealSheaf (restrictHom i U) ⟶ (moduleRestrict X U).obj (idealSheaf i) :=
  kernel.lift _ _ (idealSheafι_comp_moduleRestrict_map_structureSheafModuleHom i U) ≫
    (PreservesKernel.iso (moduleRestrict X U) (structureSheafModuleHom i)).inv

/-- `Stacks.ClosedImmersion.restrictIdealSheafInv` followed by the restriction of the inclusion
`ℐ_i ⟶ 𝒪_X` is the inclusion `ℐ_{i|_V} ⟶ 𝒪_{X|U}`. -/
theorem restrictIdealSheafInv_comp_map_ι :
    restrictIdealSheafInv i U ≫ (moduleRestrict X U).map (idealSheafι i) =
      idealSheafι (restrictHom i U) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z =>
        kernel.lift _ _ (idealSheafι_comp_moduleRestrict_map_structureSheafModuleHom i U) ≫ z)
      (PreservesKernel.iso_inv_ι (moduleRestrict X U)
        (structureSheafModuleHom i))).trans (kernel.lift_ι _ _ _))

/-- The inclusion of an ideal sheaf into the structure sheaf is a monomorphism: it is a
`CategoryTheory.Limits.kernel.ι`. -/
theorem mono_idealSheafι {W W' : RingedSpace.{u, u}} (j : W ⟶ W') : Mono (idealSheafι j) :=
  inferInstanceAs (Mono (kernel.ι (structureSheafModuleHom j)))

/-- **`ℐ_i|_U ≅ ℐ_{i|_V}`: the ideal sheaf is local on the ambient space.** The ideal sheaf of
the restricted morphism `i|_V : Z|_V ⟶ X|_U` is the restriction to `U` of the ideal sheaf of
`i`.

The isomorphism is `Stacks.ClosedImmersion.restrictIdealSheafMap`, so it is pinned by
`Stacks.ClosedImmersion.restrictIdealSheafIso_hom_comp_ι`. -/
def restrictIdealSheafIso :
    (moduleRestrict X U).obj (idealSheaf i) ≅ idealSheaf (restrictHom i U) where
  hom := restrictIdealSheafMap i U
  inv := restrictIdealSheafInv i U
  hom_inv_id :=
    haveI := mono_idealSheafι i
    haveI : Mono ((moduleRestrict X U).map (idealSheafι i)) :=
      (moduleRestrict X U).map_mono (idealSheafι i)
    (cancel_mono ((moduleRestrict X U).map (idealSheafι i))).1
      (((Category.assoc _ _ _).trans
        ((congrArg (fun z => restrictIdealSheafMap i U ≫ z)
          (restrictIdealSheafInv_comp_map_ι i U)).trans
            (restrictIdealSheafMap_comp_ι i U))).trans (Category.id_comp _).symm)
  inv_hom_id :=
    haveI := mono_idealSheafι (restrictHom i U)
    (cancel_mono (idealSheafι (restrictHom i U))).1
      (((Category.assoc _ _ _).trans
        ((congrArg (fun z => restrictIdealSheafInv i U ≫ z)
          (restrictIdealSheafMap_comp_ι i U)).trans
            (restrictIdealSheafInv_comp_map_ι i U))).trans (Category.id_comp _).symm)

/-- **The characterising property of `Stacks.ClosedImmersion.restrictIdealSheafIso`.** It is
compatible with the two inclusions into the structure sheaf, and because those are
monomorphisms, that determines it. -/
@[simp]
theorem restrictIdealSheafIso_hom_comp_ι :
    (restrictIdealSheafIso i U).hom ≫ idealSheafι (restrictHom i U) =
      (moduleRestrict X U).map (idealSheafι i) :=
  restrictIdealSheafMap_comp_ι i U

/-! ### The conormal sheaf is local on the ambient space -/

/-- **`𝒞_i|_V ≅ 𝒞_{i|_V}`: the conormal sheaf is local on the ambient space.** For a morphism of
ringed spaces `i : Z ⟶ X` and an open subspace `U` of `X` with `V = i⁻¹U`, the conormal sheaf of
the restricted morphism `i|_V : Z|_V ⟶ X|_U` is the restriction to `V` of the conormal sheaf of
`i`.

This is the first assertion of [Stacks Project, Tag 01R3] part (1) in the generality of ringed
spaces: it is what makes the conormal sheaf of an immersion independent of the open subscheme
through which the immersion is factored as a closed immersion, two such opens being compared
over their intersection. It is **not** that tag's statement — see the module docstring — and
carries no attribute.

The isomorphism is the pullback base-change square
`AlgebraicGeometry.RingedSpace.restrictPullbackIso` applied to the ideal sheaf, followed by the
pullback of `Stacks.ClosedImmersion.restrictIdealSheafIso`. It is pinned by
`Stacks.ClosedImmersion.restrictConormalSheafIso_hom_comp_pullback_ι`. -/
def restrictConormalSheafIso :
    (moduleRestrict Z ((Opens.map i.hom.base).obj U)).obj (conormalSheaf i) ≅
      conormalSheaf (restrictHom i U) :=
  (restrictPullbackIso i U).app (idealSheaf i) ≪≫
    (modulePullback (restrictHom i U)).mapIso (restrictIdealSheafIso i U)

/-- **The characterising property of `Stacks.ClosedImmersion.restrictConormalSheafIso`.** Read
inside `(i|_V)^* 𝒪_{X|U}` — that is, after mapping both conormal sheaves along the pullback of
the relevant ideal-sheaf inclusion — the identification is the restriction to `V` of the
corresponding map for `i`, compared along the pullback base-change square
`AlgebraicGeometry.RingedSpace.restrictPullbackIso`.

Since `AlgebraicGeometry.RingedSpace.restrictPullbackIso` is itself pinned by
`AlgebraicGeometry.RingedSpace.unit_modulePullbackRestrictIso_hom_app`, and the ideal-sheaf
inclusions are monomorphisms, this fixes the isomorphism rather than leaving it an arbitrary
witness of its type. -/
theorem restrictConormalSheafIso_hom_comp_pullback_ι :
    (restrictConormalSheafIso i U).hom ≫
        (modulePullback (restrictHom i U)).map (idealSheafι (restrictHom i U)) =
      (modulePullback i ⋙ moduleRestrict Z ((Opens.map i.hom.base).obj U)).map (idealSheafι i) ≫
        (restrictPullbackIso i U).hom.app (SheafOfModules.unit (structureSheafRing X)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (restrictPullbackIso i U).hom.app (idealSheaf i) ≫ z)
      (((modulePullback (restrictHom i U)).map_comp _ _).symm.trans
        (congrArg (modulePullback (restrictHom i U)).map
          (restrictIdealSheafIso_hom_comp_ι i U)))).trans
      ((restrictPullbackIso i U).hom.naturality (idealSheafι i)).symm)

end Stacks.ClosedImmersion

end
