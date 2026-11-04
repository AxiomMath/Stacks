module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.Support
import StacksCore.Tactic.StacksAttribute

/-!
# The submodule of sections supported on a subset

Let `R` be a sheaf of rings on a topological space `X` and let `F` be a sheaf of `R`-modules.
For a subset `Z` of `X`, the sections of `F` over an open `U` whose germs vanish at every point
of `U` outside `Z` form a submodule of `F`, and membership in it is a local condition. This file
builds that submodule.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule` is the submodule of `F` whose
  sections over `U` are those whose germs vanish outside `Z`.

## Main results

* `AlgebraicGeometry.SheafOfModules.mem_supportedSectionsSubmodule_iff` characterizes its local
  sections by vanishing of germs off `Z`.
* `AlgebraicGeometry.SheafOfModules.mem_supportedSectionsSubmodule_iff_mem_supportedSections`
  identifies the underlying additive condition with the supported-sections subgroup of Tag 01AY.

## Implementation notes

The construction is made as a `SheafOfModules.Submodule`, so it carries its canonical inclusion
into `F` and its own sheaf of modules. It needs nothing of `Z` and nothing of `F`: neither
closedness of `Z`, nor retrocompactness of its complement, nor quasi-coherence of `F`. Those
hypotheses belong to Stacks tag 07ZP, which is what makes the resulting submodule
quasi-coherent, and they are not needed to define it.

The base is bound as `CategoryTheory.Sheaf (Opens.grothendieckTopology ↥X) RingCat` rather than
as the definitionally equal `TopCat.Sheaf RingCat X`, and the proofs are terms rather than
rewrites. Both choices are load-bearing: the `TopCat.Sheaf` spelling is only reducibly the
sheaf category that `SheafOfModules` expects, and the membership condition elaborates its
sections at `F.val.obj U` while the germ maps expect `F.val.presheaf.obj (op U)` — also only
reducibly the same type. A `rw` of a germ lemma therefore cannot build its motive, whereas a
term proof, which is checked at default transparency, goes through directly.

## References

* [Stacks Project, Tag 01AY](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}} {R : CategoryTheory.Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u}}

/-- The submodule of sections of `F` supported on `Z`: its sections over an open `U` are the
sections of `F` over `U` all of whose germs at points of `U` outside `Z` vanish. -/
@[stacks 084L]
public noncomputable def supportedSectionsSubmodule (Z : Set X)
    (F : _root_.SheafOfModules.{u} R) : F.Submodule where
  toSubmodule :=
    { obj := fun U ↦
        { carrier := {s | ∀ (x : X) (hx : x ∈ unop U), x ∉ Z →
              TopCat.Presheaf.germ F.val.presheaf (unop U) x hx s = 0}
          zero_mem' := fun _ _ _ ↦ map_zero _
          add_mem' := fun {s t} hs ht x hx hxZ ↦
            (map_add _ s t).trans
              ((congrArg₂ (· + ·) (hs x hx hxZ) (ht x hx hxZ)).trans (add_zero 0))
          smul_mem' := fun r s hs x hx hxZ ↦
            (PresheafOfModules.germ_ringCat_smul F.val x (unop U) hx r s).trans (by
              rw [hs x hx hxZ, smul_zero]) }
      map := fun {_ _} i s hs x hx hxZ ↦
        (TopCat.Presheaf.germ_res_apply' F.val.presheaf i x hx s).trans
          (hs x (i.unop.le hx) hxZ) }
  isSheaf := by
    intro U s hs x hx hxZ
    rw [Opens.mem_grothendieckTopology] at hs
    obtain ⟨W, g, hg, hxW⟩ := hs x hx
    exact (TopCat.Presheaf.germ_res_apply F.val.presheaf g x hxW s).symm.trans (hg x hxW hxZ)

/-- Membership in the supported-sections submodule is precisely vanishing of all germs
outside `Z`. -/
@[simp]
public lemma mem_supportedSectionsSubmodule_iff (Z : Set X) (F : _root_.SheafOfModules.{u} R)
    (U : Opens X) (s : F.val.obj (op U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ∀ (x : X) (hx : x ∈ U), x ∉ Z →
        TopCat.Presheaf.germ F.val.presheaf U x hx s = 0 :=
  Iff.rfl

/-- A section over `U` is supported on `Z` exactly when it restricts to zero on any open `W`
whose points are the points of `U` outside `Z`. -/
public lemma mem_supportedSectionsSubmodule_iff_map_eq_zero (Z : Set X)
    (F : _root_.SheafOfModules.{u} R) {U W : Opens X} (i : op U ⟶ op W)
    (hW : (W : Set X) = (U : Set X) ∩ Zᶜ) (s : F.val.obj (op U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      F.val.presheaf.map i s = 0 := by
  constructor
  · intro hs
    refine TopCat.Presheaf.section_ext ⟨F.val.presheaf, F.isSheaf⟩ W _ 0 fun x hx ↦ ?_
    rw [map_zero, TopCat.Presheaf.germ_res_apply' F.val.presheaf i x hx s]
    have hx' : x ∈ (U : Set X) ∩ Zᶜ := hW ▸ hx
    exact hs x hx'.1 hx'.2
  · intro hs x hxU hxZ
    have hxW : x ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact ⟨hxU, hxZ⟩
    refine (TopCat.Presheaf.germ_res_apply' F.val.presheaf i x hxW s).symm.trans ?_
    rw [hs, map_zero]

/-- The module-valued construction has the supported-sections subgroup of Tag 01AY as its
underlying additive condition. -/
public lemma mem_supportedSectionsSubmodule_iff_mem_supportedSections (Z : Set X)
    (F : _root_.SheafOfModules.{u} R) (U : Opens X) (s : F.val.obj (op U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      s ∈ supportedSections Z ⟨F.val.presheaf, F.isSheaf⟩ (op U) :=
  Iff.rfl

end AlgebraicGeometry.SheafOfModules

end
