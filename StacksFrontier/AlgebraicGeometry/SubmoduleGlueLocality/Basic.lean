module

public import StacksFrontier.AlgebraicGeometry.SubmoduleGlueOpens.Basic
public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Locality
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal

/-!
# The glued submodule restricted to a member of the family, and the properties that transfer

`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean` glues a family of submodules
`N i` of a fixed `𝒪_X`-module `F`, agreeing over the opens inside two members of a family `W` of
opens, into a single submodule `glue W N` of `F`, and proves the glueing identity
`(glue W N).obj (op U) = (N j).obj (op U)` for `U ≤ W j`.
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Basic.lean` carries a submodule of `F` across
an open immersion, producing `restrictTo f N : (F.restrict f).Submodule`.

This file composes the two, and that composition is what makes the glueing step of
[Stacks, Tag 01PF] usable: **the restriction of the glue to `W j` is the restriction of `N j`**,
as an equality of submodules of `F.restrict (W j).ι`. Every property of a sheaf of modules
therefore transfers from the pieces to the glue at once, via the locality theorems of
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Locality.lean`.

## Main results

* `restrictTo_glue_of_le`: **the restriction identity.**
  `restrictTo (W j).ι (glue W N) = restrictTo (W j).ι (N j)`.
* `isQuasicoherent_toSheafOfModules_of_restrict`: quasi-coherence of a concrete submodule is
  local over an arbitrary open cover, the companion over a cover of
  `Stacks.AlgebraicGeometry.SubmoduleRestrict.isQuasicoherent_toSheafOfModules_of_isAffineOpen`,
  which is stated over every affine open.
* `isQuasicoherent_glue`, `isFiniteType_glue`, `isCoherent_glue`: if the family `W` covers `X`
  and the restriction of each piece to its own member is quasi-coherent, of finite type, or
  coherent, then so is the glue.

## What this changes about the obligation recorded upstream

The module documentation of `SubmoduleGlueOpens/Basic.lean` records, as what is still owed, two
*sections-level* transfers — of finiteness of the `Γ(X, U)`-module of sections and of the
spanning identity of `Stacks.AlgebraicGeometry.GabberColimit.IsCompatible` — from the opens
inside a member of the family to every affine open of `X`, and its
`finite_sections_glue_of_le` / `span_sections_glue_of_le` are the restricted forms of those.
**Neither transfer is needed, and the sections spelling is not the right level for it.** What the
locality theorems consume is the *property* of the restricted module, and
`restrictTo_glue_of_le` supplies the restricted module itself: the glue and the piece have the
same restriction, so finiteness of sections, quasi-coherence, finite type, coherence and
anything else transfer by one rewrite each rather than one bridge each. The sections-level
lemmas remain correct and are not used here.

## Implementation notes

`restrictTo_glue_of_le` is an equality of `SheafOfModules.Submodule`s and is proved by
`SheafOfModules.Submodule.ext` through `PresheafOfModules.Submodule.ext`, i.e. open by open: the
sections of `restrictTo (W j).ι M` over an open `V` of `W j` are `M.obj (op ((W j).ι ''ᵁ V))` by
`Stacks.AlgebraicGeometry.SubmoduleRestrict.mem_restrictTo`, which is `Iff.rfl`, and
`(W j).ι ''ᵁ V ≤ W j` is `AlgebraicGeometry.Scheme.Opens.ι_image_le`, so the glueing identity
applies at that open. No scalar is moved: the two sides are submodules of the *same*
`Γ(W j, V)`-module, so the `(W j).ι.appIso` twist recorded in `SubmoduleRestrict/Basic.lean`
never enters.

The equality of submodules is applied by `rw`, never left to unification, for the reason
recorded in `SubmoduleRestrict/Locality.lean`: at `f = (W i).ι` the elaborator unfolds the
open-immersion structure and exhausts the heartbeat budget at `whnf`.

Quasi-coherence over a cover is `Stacks.Modules.isQuasicoherent_of_restrict`
(`StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentLocal.lean`), which **does** exist in the
`AlgebraicGeometry.Scheme.Modules.restrict` spelling and over an arbitrary open cover in an
arbitrary universe, so both locality statements the induction needs are available in this form. Finite type and
coherence go through the two theorems of `SubmoduleRestrict/Locality.lean`, whose
hypotheses are already in the `restrictTo` spelling; those two carry `{I : Type u}`, which is why
`isFiniteType_glue` and `isCoherent_glue` do and `isQuasicoherent_glue` does not.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** Nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag: this is the glueing step of that lemma's affine
induction, and the induction itself is not here. The induction still needs three
primitives, none of which is in the library:

* **the co-restriction**, sending `P : (F.restrict W.ι).Submodule` to a submodule of `F` whose
  restriction to `W` is `P` — without it the pieces of the induction, which are produced on the
  open subschemes, cannot be fed to `glue`, whose pieces are submodules of `F` itself;
* **the passage from `CategoryTheory.Subobject F` to `F.Submodule`**, the sectionwise image of a
  monomorphism into `F`. [Stacks, Tag 01PE] is formalized only in the `Subobject` spelling
  (`AlgebraicGeometry.exists_quasicoherentSubobject_restrict`), so the extension step of the
  affine case is not reachable from the concrete-submodule side;
* **the composition of a submodule of `N.toSheafOfModules` with `N : F.Submodule`** into a
  submodule of `F`, which the affine case needs because it truncates the 01PE extension `H` and
  must then read the truncation as a submodule of `F`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.SubmoduleGlueLocality

open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### The restriction identity -/

/-- **The restriction of the glue to a member of the family is the restriction of the
corresponding piece.** This is the glueing identity of
`Stacks.AlgebraicGeometry.SubmoduleGlueOpens.glue_obj_of_le` read as an equality of submodules of
the module on the open subscheme `W j`, which is the form every locality theorem consumes.

Open by open the two sides are the sections of the glue and of `N j` over the image open
`(W j).ι ''ᵁ V`, which is inside `W j`; so the glueing identity applies, and no scalar is
moved. -/
theorem restrictTo_glue_of_le {ι : Type*} (W : ι → X.Opens) (N : ι → F.Submodule)
    (hagree : Agree W N) (j : ι) :
    restrictTo (W j).ι (glue W N) = restrictTo (W j).ι (N j) := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  have key : (glue W N).obj (op ((W j).ι ''ᵁ V.unop)) = (N j).obj (op ((W j).ι ''ᵁ V.unop)) :=
    glue_obj_of_le W N hagree ((W j).ι_image_le V.unop)
  refine SetLike.ext fun x => ?_
  show x ∈ (glue W N).obj (op ((W j).ι ''ᵁ V.unop)) ↔
    x ∈ (N j).obj (op ((W j).ι ''ᵁ V.unop))
  rw [key]

/-! ### Quasi-coherence of a concrete submodule is local over a cover -/

/-- **Quasi-coherence of a concrete submodule is local over an arbitrary open cover.** This is
the companion over a cover of
`Stacks.AlgebraicGeometry.SubmoduleRestrict.isQuasicoherent_toSheafOfModules_of_isAffineOpen`,
which asks for every affine open of `X`; an affine open of `X` need not lie inside a member of a
given cover, so the two statements are not interchangeable and the glueing step needs this one.

The content is `Stacks.Modules.isQuasicoherent_of_restrict` applied to `N.toSheafOfModules`, the
hypothesis being read through
`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules`. -/
theorem isQuasicoherent_toSheafOfModules_of_restrict (N : F.Submodule) {I : Type w}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, (restrictTo (U i).ι N).toSheafOfModules.IsQuasicoherent) :
    (N.toSheafOfModules).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_of_restrict (N.toSheafOfModules : X.Modules) U hU
    fun i => restrictTo_toSheafOfModules (U i).ι N ▸ h i

/-! ### The properties that transfer from the pieces to the glue -/

variable {ι : Type*} (W : ι → X.Opens) (N : ι → F.Submodule)

/-- **The glue of quasi-coherent pieces over a covering family is quasi-coherent.** -/
theorem isQuasicoherent_glue (hagree : Agree W N) (hcov : iSup W = ⊤)
    (h : ∀ i, (restrictTo (W i).ι (N i)).toSheafOfModules.IsQuasicoherent) :
    ((glue W N).toSheafOfModules).IsQuasicoherent :=
  isQuasicoherent_toSheafOfModules_of_restrict (glue W N) W hcov fun i =>
    restrictTo_glue_of_le W N hagree i ▸ h i

/-- **The glue of pieces of finite type over a covering family is of finite type.** -/
theorem isFiniteType_glue {ι : Type u} (W : ι → X.Opens) (N : ι → F.Submodule)
    (hagree : Agree W N) (hcov : IsOpenCover W)
    (h : ∀ i, (restrictTo (W i).ι (N i)).toSheafOfModules.IsFiniteType) :
    ((glue W N).toSheafOfModules).IsFiniteType :=
  isFiniteType_toSheafOfModules_of_restrict (glue W N) W hcov fun i =>
    restrictTo_glue_of_le W N hagree i ▸ h i

/-- **The glue of coherent pieces over a covering family is coherent.** -/
theorem isCoherent_glue {ι : Type u} (W : ι → X.Opens) (N : ι → F.Submodule)
    (hagree : Agree W N) (hcov : iSup W = ⊤)
    (h : ∀ i, (restrictTo (W i).ι (N i)).toSheafOfModules.IsCoherent) :
    ((glue W N).toSheafOfModules).IsCoherent :=
  isCoherent_toSheafOfModules_of_restrict (glue W N) W hcov fun i =>
    restrictTo_glue_of_le W N hagree i ▸ h i

end Stacks.AlgebraicGeometry.SubmoduleGlueLocality

end
