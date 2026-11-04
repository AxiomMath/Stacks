module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# The structure sheaf of a big smooth site

The presheaf of rings `T/S ↦ Γ(T, 𝒪_T)` is a sheaf on the big smooth site of a scheme `S`
inside a chosen big smooth site.  This is smooth descent of functions: a covering family of the
big smooth site is a smooth surjective family, hence faithfully flat, so the statement is the
structure-sheaf case of faithfully flat descent and not a gluing over a Zariski cover.

The proof restricts the fpqc sheaf of global functions.  Global functions on the schemes over
`S` are an fpqc sheaf of types (`Stacks.Sites.isSheaf_fpqcOver_globalSections`), the inclusion of
the big smooth site over `S` into the schemes over `S` is continuous for the induced fpqc
topology (`AlgebraicGeometry.isSheaf_bigSmooth_of_isSheaf_fpqc`), and a presheaf of rings is a
sheaf once its underlying presheaf of types is (`Stacks.Sites.isSheaf_structurePresheaf`).

## Main definitions

* `AlgebraicGeometry.BigSmoothOver.structureSheaf`: the structure sheaf of the big smooth site
  over `S`.  It is the structure sheaf `𝒪_S` of Stacks 04HS for the site `(Sch/S)_smooth`.

## Main results

* `AlgebraicGeometry.BigSmoothOver.structure_isSheaf`: the presheaf of global functions on the
  big smooth site over `S` is a sheaf of rings.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigSmoothOver

variable (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)

/-- **Stacks 03DU, big smooth structure sheaf.**  The presheaf of global functions is a sheaf of
rings on the big smooth site over `S`: a covering family of that site is smooth and surjective,
hence an fpqc covering, and global functions satisfy fpqc descent. -/
@[stacks 03DU "big smooth structure sheaf"]
public theorem structure_isSheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.structurePresheaf S (Over.post (ObjectProperty.ι _))) :=
  Stacks.Sites.isSheaf_structurePresheaf S _ _
    (isSheaf_bigSmooth_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- **Stacks 03DU, big smooth structure sheaf construction.**  The structure sheaf of rings of
the big smooth site over `S`, whose value at `T/S` is `Γ(T, 𝒪_T)`. -/
@[stacks 03DU "big smooth structure sheaf construction"]
public noncomputable def structureSheaf : Sheaf (topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (Over.post (ObjectProperty.ι _)),
    structure_isSheaf B S hS⟩

/-- The structure sheaf of the big smooth site over `S` has the presheaf of global functions as
its underlying presheaf. -/
@[simp]
public theorem structureSheaf_obj :
    (structureSheaf B S hS).obj =
      Stacks.Sites.structurePresheaf S (Over.post (ObjectProperty.ι _)) :=
  rfl

end AlgebraicGeometry.BigSmoothOver

add_to_stacks 04HS "big smooth structure sheaf" AlgebraicGeometry.BigSmoothOver.structureSheaf

end
