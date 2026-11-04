module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# The subsheaf of sections supported in a closed subset

For a sheaf of modules on a scheme and a subset `Z` of the underlying space, the local sections
all of whose germs outside `Z` vanish form a sub-`𝒪`-module sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` is the subsheaf of sections
  supported in a given subset.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iff` characterizes its local
  sections by the vanishing of germs off the subset.
* `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iff_mem_supportedSections`
  identifies its underlying additive condition with the supported-sections subgroup of
  Tag 01AY.

## Implementation notes

The construction is made as a `SheafOfModules.Submodule`, so it carries its canonical inclusion
into the original sheaf of modules; on every open its underlying additive subgroup is
`AlgebraicGeometry.SheafOfModules.supportedSections`.

The construction works for an arbitrary subset and an arbitrary sheaf of modules. Closedness of
the subset, retrocompactness of its complement and quasi-coherence of the sheaf are what
Tag 07ZP needs in order to conclude that the resulting sheaf of modules is quasi-coherent; none
of them is needed here.

## References

* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 01AY](https://stacks.math.columbia.edu/tag/01AY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat
open AlgebraicGeometry.SheafOfModules (supportedSections)

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The presheaf of modules underlying a sheaf of modules on a scheme, retyped over the structure
presheaf of commutative rings. This is the spelling under which the scalar action on stalks, and
with it `PresheafOfModules.germ_smul`, is found by instance search: `X.ringCatSheaf.obj` and
`X.presheaf ⋙ forget₂ CommRingCat RingCat` are definitionally equal but not reducibly so. -/
public abbrev modulePresheaf (F : X.Modules) :
    _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val

/-- The sub-`𝒪`-module sheaf of `F` whose local sections have all their germs outside `Z`
equal to zero. -/
@[stacks 084L]
public noncomputable def supportedSectionsSubmodule (Z : Set X)
    (F : X.Modules) : F.Submodule where
  toSubmodule :=
    { obj := fun U ↦
        { carrier := {s | ∀ (x : X) (hx : x ∈ unop U), x ∉ Z →
              TopCat.Presheaf.germ (modulePresheaf F).presheaf (unop U) x hx s = 0}
          zero_mem' := by
            intro x hx _
            exact map_zero (TopCat.Presheaf.germ (modulePresheaf F).presheaf (unop U) x hx).hom
          add_mem' := by
            intro s t hs ht x hx hxZ
            refine (map_add
              (TopCat.Presheaf.germ (modulePresheaf F).presheaf (unop U) x hx).hom s t).trans ?_
            refine (congrArg
              (fun y ↦ y +
                (TopCat.Presheaf.germ (modulePresheaf F).presheaf (unop U) x hx).hom t)
              (hs x hx hxZ)).trans ?_
            exact (zero_add _).trans (ht x hx hxZ)
          smul_mem' := by
            intro r s hs x hx hxZ
            refine (PresheafOfModules.germ_smul (R := X.presheaf) (modulePresheaf F) x
              (unop U) hx r s).trans ?_
            rw [hs x hx hxZ, smul_zero] }
      map := by
        intro U V i s hs x hx hxZ
        exact (TopCat.Presheaf.germ_res_apply' (modulePresheaf F).presheaf i x hx s).trans
          (hs x (i.unop.le hx) hxZ) }
  isSheaf := by
    intro U s hs
    change ∀ (x : X) (hx : x ∈ unop U), x ∉ Z →
      TopCat.Presheaf.germ (modulePresheaf F).presheaf (unop U) x hx s = 0
    rw [Opens.mem_grothendieckTopology] at hs
    intro x hx hxZ
    obtain ⟨W, g, hg, hxW⟩ := hs x hx
    exact (TopCat.Presheaf.germ_res_apply (modulePresheaf F).presheaf g x hxW s).symm.trans
      (hg x hxW hxZ)

/-- Membership in the supported-sections submodule is precisely the vanishing of all germs
outside the support set. -/
@[simp]
public lemma mem_supportedSectionsSubmodule_iff (Z : Set X) (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ∀ (x : X) (hx : x ∈ U), x ∉ Z →
        TopCat.Presheaf.germ F.val.presheaf U x hx s = 0 := by
  with_unfolding_all rfl

/-- The module-valued construction has the supported-sections subgroup of Tag 01AY as its
underlying additive condition. -/
public lemma mem_supportedSectionsSubmodule_iff_mem_supportedSections (Z : Set X)
    (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      s ∈ supportedSections Z ⟨F.val.presheaf, F.isSheaf⟩ (op U) :=
  (mem_supportedSectionsSubmodule_iff Z F U s).trans
    (AlgebraicGeometry.SheafOfModules.mem_supportedSections_iff Z
      ⟨F.val.presheaf, F.isSheaf⟩ (op U) s).symm

end AlgebraicGeometry.Scheme.Modules
