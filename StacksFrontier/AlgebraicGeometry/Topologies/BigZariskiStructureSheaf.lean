module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# The structure sheaf of a big Zariski site

The presheaf of rings `T/S ↦ Γ(T, 𝒪_T)` is a sheaf on the big Zariski site of a scheme `S`
inside a chosen big Zariski site.  Its value at an object is the ring of global functions on
the whole of that object, so the sheaf condition for a covering family `{Tᵢ → T}` is the
assertion that functions on the pieces of a Zariski covering of `T` which agree on the
overlaps glue to a unique function on `T`; it is a statement about the schemes `T`, not a
reformulation of how the presheaf was built.

The proof restricts the fpqc sheaf of global functions.  Global functions on the schemes over
`S` are an fpqc sheaf of types (`Stacks.Sites.isSheaf_fpqcOver_globalSections`), the inclusion
of the big Zariski site over `S` into the schemes over `S` is continuous for the induced fpqc
topology (`AlgebraicGeometry.isSheaf_bigZariski_of_isSheaf_fpqc`), and a presheaf of rings is
a sheaf once its underlying presheaf of types is (`Stacks.Sites.isSheaf_structurePresheaf`).
Descent along a Zariski covering is thus obtained from the stronger faithfully flat descent.

## Main definitions

* `AlgebraicGeometry.BigZariskiOver.structureSheaf`: the structure sheaf of the big Zariski
  site over `S`.  It is the structure sheaf `𝒪_S` of Stacks 04HS for the site
  `(Sch/S)_Zariski`.

## Main results

* `AlgebraicGeometry.BigZariskiOver.structure_isSheaf`: the presheaf of global functions on
  the big Zariski site over `S` is a sheaf of rings.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigZariskiOver

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DU, big Zariski structure sheaf.**  The presheaf of global functions is a sheaf
of rings on the big Zariski site over `S`: a covering family of that site is a jointly
surjective family of open immersions, hence an fpqc covering, and global functions satisfy
fpqc descent. -/
@[stacks 03DU "big Zariski structure sheaf"]
public theorem structure_isSheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)) :=
  Stacks.Sites.isSheaf_structurePresheaf S _ _
    (isSheaf_bigZariski_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- **Stacks 03DU, big Zariski structure sheaf construction.**  The structure sheaf of rings of
the big Zariski site over `S`, whose value at `T/S` is `Γ(T, 𝒪_T)`. -/
@[stacks 03DU "big Zariski structure sheaf construction"]
public noncomputable def structureSheaf : Sheaf (topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion),
    structure_isSheaf B S hS⟩

/-- The structure sheaf of the big Zariski site over `S` has the presheaf of global functions
as its underlying presheaf. -/
@[simp]
public theorem structureSheaf_obj :
    (structureSheaf B S hS).obj =
      Stacks.Sites.structurePresheaf S
        (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) :=
  rfl

end AlgebraicGeometry.BigZariskiOver

add_to_stacks 04HS "big Zariski structure sheaf" AlgebraicGeometry.BigZariskiOver.structureSheaf

end
