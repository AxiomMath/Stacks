module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic

/-!
# The sectionwise kernel of a morphism of sheaves of modules is its categorical kernel

A morphism `f : M ⟶ N` of sheaves of modules on a site has two kernels in this development: the
*sectionwise* one `Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule`, an embedded
submodule of `M` whose sections over an object of the site are the kernel of the component of
`f` there, and the *categorical* one `CategoryTheory.Limits.kernel`.  This file identifies them,
and reads the identification at the ideal sheaf of a morphism of schemes, where the two kernels
are the two presentations of the ideal sheaf that the development uses side by side.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmoduleIso`: **the sectionwise kernel is
  the categorical kernel**, by the universal property in both directions.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`: **the defining ideal sheaf
  of a morphism of schemes is the ideal sheaf of `Stacks.ClosedImmersion`**, which is the
  comparison of the two presentations.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmoduleLift`: the factorisation of a
  morphism killed by `f` through the sectionwise kernel.

## Implementation notes

The two presentations of an ideal sheaf are used in different parts of the development and were
not connected.  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`, the sectionwise
one, is what `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf` pulls back, and it is the
one matched with Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom_obj_eq_ker`;
`Stacks.ClosedImmersion.idealSheaf`, the categorical one, is what
`Stacks.Thickenings.schemeConormalSheaf` and `Stacks.Thickenings.universalConormalSheaf` pull
back, and it is the one whose functoriality is built from
`CategoryTheory.Limits.kernel.lift`.  `definingIdealOfHomIso` is the bridge, and it is what lets
a statement proved about one of them be read on the other.

The factorisation is built on sections, by corestricting each component of the morphism to the
kernel of the corresponding component of `f` — which is where its image lies, by the hypothesis
read at that object.  Naturality is `CategoryTheory.PresheafOfModules.naturality_apply` of the
morphism being factored, since the inclusion of the sectionwise kernel is the inclusion of a
submodule on each object.  Both triangles of the isomorphism are checked after a monomorphism:
the inclusion of the sectionwise kernel for one, `CategoryTheory.Limits.kernel.ι` for the other.

The statements are at the module universe of the coefficient ring sheaf, which is where
`kernelSubmodule` is stated.

## References

* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### The sectionwise kernel is the categorical kernel -/

section Kernel

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A morphism killed by `f` factors through the sectionwise kernel of `f`.**  On sections over
an object of the site the factorisation is the corestriction of the component of the morphism to
the kernel of the component of `f`, which is where its image lies. -/
def kernelSubmoduleLift {M N L : SheafOfModules.{u} R} (f : M ⟶ N) (g : L ⟶ M)
    (hg : g ≫ f = 0) : L ⟶ (kernelSubmodule f).toSheafOfModules where
  val :=
    { app := fun U => ModuleCat.ofHom ((g.val.app U).hom.codRestrict _ fun x =>
        congrArg (fun k : L ⟶ N => k.val.app U x) hg)
      naturality := fun {U V} h => by
        ext x
        exact Subtype.ext (PresheafOfModules.naturality_apply g.val h x) }

/-- The factorisation through the sectionwise kernel is compatible with its inclusion: on
sections the corestriction followed by the inclusion of the submodule is the morphism itself. -/
theorem kernelSubmoduleLift_ι {M N L : SheafOfModules.{u} R} (f : M ⟶ N) (g : L ⟶ M)
    (hg : g ≫ f = 0) :
    kernelSubmoduleLift f g hg ≫ (kernelSubmodule f).ι = g := rfl

/-- **The sectionwise kernel of a morphism of sheaves of modules is its categorical kernel.**
The sectionwise kernel is killed by the morphism, by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule_ι_comp`, so its inclusion factors
through the categorical kernel; and the categorical kernel is killed by the morphism, so it
factors through the sectionwise one.  The two factorisations are mutually inverse because each
composite is compatible with a monomorphism out of the object it is an endomorphism of. -/
noncomputable def kernelSubmoduleIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmodule f).toSheafOfModules ≅ kernel f where
  hom := kernel.lift f (kernelSubmodule f).ι (kernelSubmodule_ι_comp f)
  inv := kernelSubmoduleLift f (kernel.ι f) (kernel.condition f)
  hom_inv_id := by
    apply (cancel_mono (kernelSubmodule f).ι).mp
    simp only [Category.assoc, kernelSubmoduleLift_ι, kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι f)).mp
    simp only [Category.assoc, kernel.lift_ι, kernelSubmoduleLift_ι, Category.id_comp]

/-- The comparison of the two kernels is compatible with their inclusions into the source: it is
the factorisation of the inclusion of the sectionwise kernel through the categorical one, so no
twist of its own is introduced and it is the canonical identification. -/
@[reassoc]
theorem kernelSubmoduleIso_hom_comp_ι {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmoduleIso f).hom ≫ kernel.ι f = (kernelSubmodule f).ι :=
  kernel.lift_ι _ _ _

/-- The inverse comparison is compatible with the inclusions as well. -/
@[reassoc]
theorem kernelSubmoduleIso_inv_comp_ι {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmoduleIso f).inv ≫ (kernelSubmodule f).ι = kernel.ι f :=
  kernelSubmoduleLift_ι f (kernel.ι f) (kernel.condition f)

end Kernel

/-! ### The two presentations of the ideal sheaf of a morphism of schemes -/

/-- **The defining ideal sheaf of a morphism of schemes is the ideal sheaf of
`Stacks.ClosedImmersion`.**  Both are the kernel of `𝒪_U ⟶ j_*𝒪_Z`: the first sectionwise, as an
ideal subsheaf of the structure sheaf module, the second categorically.  This is the bridge
between the two presentations the development uses side by side; the implementation notes of this
file say which results are stated on which side. -/
noncomputable def definingIdealOfHomIso {Z U : Scheme.{u}} (j : Z ⟶ U) :
    (definingIdealOfHom j).toSheafOfModules ≅
      Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom :=
  kernelSubmoduleIso _

/-- The comparison of the two presentations of the ideal sheaf is compatible with their
inclusions into the structure sheaf module of the target. -/
@[reassoc]
theorem definingIdealOfHomIso_hom_comp_idealSheafι {Z U : Scheme.{u}} (j : Z ⟶ U) :
    (definingIdealOfHomIso j).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom j.toLRSHom.toShHom)) =
      (definingIdealOfHom j).ι :=
  kernelSubmoduleIso_hom_comp_ι _

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
