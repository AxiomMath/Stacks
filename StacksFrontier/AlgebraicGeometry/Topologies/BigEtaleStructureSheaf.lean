module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# The structure sheaf of a big étale site

The presheaf of rings `T/S ↦ Γ(T, 𝒪_T)` is a sheaf on the big étale site of a scheme `S` inside
a chosen big étale site.  This is étale descent of functions: a covering family of the big étale
site is an étale surjective family, so the statement is the structure-sheaf case of faithfully
flat descent and not a gluing over a Zariski cover.

The proof restricts the fpqc sheaf of global functions.  Global functions on the schemes over
`S` are an fpqc sheaf of types (`Stacks.Sites.isSheaf_fpqcOver_globalSections`), the inclusion of
the big étale site over `S` into the schemes over `S` is continuous for the induced fpqc topology
(`AlgebraicGeometry.isSheaf_chosenBigEtale_of_isSheaf_fpqc`), and a presheaf of rings is a sheaf
once its underlying presheaf of types is (`Stacks.Sites.isSheaf_structurePresheaf`).

## Main definitions

* `AlgebraicGeometry.BigEtaleOver.structureSheaf`: the structure sheaf of the big étale site
  over `S`.  It is the structure sheaf `𝒪_S` of Stacks 04HS for the site `(Sch/S)_étale`.

## Main results

* `AlgebraicGeometry.BigEtaleOver.structure_isSheaf`: the presheaf of global functions on the
  big étale site over `S` is a sheaf of rings.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigEtaleOver

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DU, big étale structure sheaf.**  The presheaf of global functions is a sheaf of
rings on the big étale site over `S`: a covering family of that site is étale and surjective,
hence an fpqc covering, and global functions satisfy fpqc descent. -/
@[stacks 03DU "big étale structure sheaf"]
public theorem structure_isSheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.structurePresheaf S (Over.post B.inclusion)) :=
  Stacks.Sites.isSheaf_structurePresheaf S _ _
    (isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- **Stacks 03DU, big étale structure sheaf construction.**  The structure sheaf of rings of
the big étale site over `S`, whose value at `T/S` is `Γ(T, 𝒪_T)`. -/
@[stacks 03DU "big étale structure sheaf construction"]
public noncomputable def structureSheaf : Sheaf (topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (Over.post B.inclusion), structure_isSheaf B S hS⟩

/-- The structure sheaf of the big étale site over `S` has the presheaf of global functions as
its underlying presheaf. -/
@[simp]
public theorem structureSheaf_obj :
    (structureSheaf B S hS).obj = Stacks.Sites.structurePresheaf S (Over.post B.inclusion) :=
  rfl

end AlgebraicGeometry.BigEtaleOver

add_to_stacks 04HS "big étale structure sheaf" AlgebraicGeometry.BigEtaleOver.structureSheaf
add_to_sga "4½ Arcata 2.2" "structure sheaf O_S" AlgebraicGeometry.BigEtaleOver.structureSheaf

end
