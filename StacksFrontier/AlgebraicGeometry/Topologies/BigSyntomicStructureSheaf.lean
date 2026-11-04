module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# The structure sheaf of a big syntomic site

The presheaf of rings `T/S ↦ Γ(T, 𝒪_T)` is a sheaf on the big syntomic site of a scheme `S`
inside a chosen big syntomic site.  This is syntomic descent of functions: a covering family of
the big syntomic site is a syntomic surjective family, hence flat and locally of finite
presentation, so the statement is the structure-sheaf case of faithfully flat descent and not a
gluing over a Zariski cover.

The proof restricts the fpqc sheaf of global functions.  Global functions on the schemes over
`S` are an fpqc sheaf of types (`Stacks.Sites.isSheaf_fpqcOver_globalSections`), the inclusion of
the big syntomic site over `S` into the schemes over `S` is continuous for the induced fpqc
topology (`AlgebraicGeometry.isSheaf_bigSyntomic_of_isSheaf_fpqc`), and a presheaf of rings is a
sheaf once its underlying presheaf of types is (`Stacks.Sites.isSheaf_structurePresheaf`).

## Main definitions

* `AlgebraicGeometry.BigSyntomicOver.structureSheaf`: the structure sheaf of the big syntomic
  site over `S`.  It is the structure sheaf `𝒪_S` of Stacks 04HS for the site
  `(Sch/S)_syntomic`.

## Main results

* `AlgebraicGeometry.BigSyntomicOver.structure_isSheaf`: the presheaf of global functions on the
  big syntomic site over `S` is a sheaf of rings.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigSyntomicOver

variable (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DU, big syntomic structure sheaf.**  The presheaf of global functions is a sheaf
of rings on the big syntomic site over `S`: a covering family of that site is syntomic and
surjective, hence an fpqc covering, and global functions satisfy fpqc descent. -/
@[stacks 03DU "big syntomic structure sheaf"]
public theorem structure_isSheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.structurePresheaf S (Over.post B.inclusion)) :=
  Stacks.Sites.isSheaf_structurePresheaf S _ _
    (isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- **Stacks 03DU, big syntomic structure sheaf construction.**  The structure sheaf of rings of
the big syntomic site over `S`, whose value at `T/S` is `Γ(T, 𝒪_T)`. -/
@[stacks 03DU "big syntomic structure sheaf construction"]
public noncomputable def structureSheaf : Sheaf (topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (Over.post B.inclusion), structure_isSheaf B S hS⟩

/-- The structure sheaf of the big syntomic site over `S` has the presheaf of global functions
as its underlying presheaf. -/
@[simp]
public theorem structureSheaf_obj :
    (structureSheaf B S hS).obj = Stacks.Sites.structurePresheaf S (Over.post B.inclusion) :=
  rfl

end AlgebraicGeometry.BigSyntomicOver

add_to_stacks 04HS "big syntomic structure sheaf"
  AlgebraicGeometry.BigSyntomicOver.structureSheaf

end
