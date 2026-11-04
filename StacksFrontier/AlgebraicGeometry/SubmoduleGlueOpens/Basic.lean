module

public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic

/-!
# Glueing submodules of a fixed module along a family of opens

Let `X` be a scheme and `F` an `𝒪_X`-module. A submodule of `F` in Mathlib's sense
(`SheafOfModules.Submodule`) is *concrete*: it is a family of `Γ(X, U)`-submodules of `Γ(F, U)`,
one for each open `U` of `X`, stable under the restriction maps and local. This file glues such
submodules along a family of opens of `X`.

Given opens `W i` of `X` and submodules `N i` of `F` which agree over every open contained in
two members of the family, `glue W N` is the submodule of `F` whose sections over an open `U`
are the sections of `F` over `U` whose restriction to `U ⊓ W i` lies in `N i` for every `i`, and
`glue_obj_of_le` says that over an open contained in `W j` it is `N j`. No hypothesis on `X`, on
the family of opens or on the pieces is used: the family need not cover `X`, need not be finite,
and `F` need not be quasi-coherent.

## Why the statement is about submodules of one fixed `F`

Glueing a subsheaf of `F|_{W₁}` to a subsheaf of `F|_{W₂}` is the step the induction of
[Stacks, Tag 01PF] performs, and the obvious formulation of it — subobjects of the restrictions
`F.restrict (W i).ι` in the category of sheaves of modules on the open subschemes — forces a
passage across the open immersions `(W i).ι`, which is a genuine obstacle: the sections of
`F.restrict W.ι` over an open of `W` *are* sections of `F`, by `rfl`, while the two scalar
actions differ by `(W.ι.appIso _).inv`, whose body is not exposed. This is explained
in the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Basic.lean`.

Nothing below crosses an open immersion. The pieces `N i` are submodules of `F` itself, and only
their values on the opens contained in `W i` are constrained by the hypotheses or used in the
conclusions, so a subsheaf defined only over `W i` enters as any submodule of `F` extending it.

## Main definitions

* `IsGlued`: the membership condition — the restriction to `U ⊓ W i` lies in `N i`, for all `i`.
* `localGlue`: that condition as a `Γ(X, U)`-submodule of `Γ(F, U)`.
* `glue`: the glued submodule of `F`.

## Main results

* `glue_obj_of_le`: **the glueing identity.** If the `N i` agree over every open contained in
  two members of the family, then over an open contained in `W j` the glued submodule is `N j`.
  This is what makes `glue` a glueing rather than an intersection: the glued object is not
  smaller than any piece on that piece's own open.
* `mem_glue_of_cover`: a section of `F` over `U` lies in the glued submodule as soon as `U` is
  covered by opens, each contained in some member of the family, over which the restriction of
  the section lies in the corresponding piece. This is the local-to-global half.
* `sections_glue_of_le`, `finite_sections_glue_of_le` and `span_sections_glue_of_le`: the
  glueing identity at the `Γ(X, U)`-module spelling of the sections, and the transfer from the
  pieces to the glue, over the opens inside a single member of the family, of finiteness of the
  sections and of the compatibility identity of
  `Stacks.AlgebraicGeometry.GabberColimit.IsCompatible`. Those are the two
  properties the extension step of [Stacks, Tag 01PF] carries along its induction, in the
  affine-open form they are stated in by
  `Stacks.AlgebraicGeometry.IdealPowerSmul.isFiniteType_of_finite_sections` and by
  `Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule`.

## What this does not do, and the one declaration still owed

**No stacks attribute is attached**, and none is earned: nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag. What is proved is the glueing step of that lemma's
induction, whose two ends are already proved — the affine case
(`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on`) and
the quasi-coherent extension across a quasi-compact open immersion
(`AlgebraicGeometry.exists_quasicoherentSubobject_restrict`, which carries the 01PE
attribute).

**The locality statements the induction needs on top of this are not proved here, and neither is
available in this form in either tree.** `finite_sections_glue_of_le` and
`span_sections_glue_of_le` transfer their properties only over opens *contained in a member* of
the family, while the
induction needs them at **every** affine open of `X` — and an affine open of `X` need not be
contained in any member of a covering of `X`. Spelled out, what is owed is: for `N : F.Submodule`
and `F` quasi-coherent, and an open covering `W` of `X`,

* if `N.obj (op V) = Submodule.span Γ(X, V) (F.presheaf.map _ '' N.obj (op U))` for all affine
  opens `V ≤ U ≤ W i`, then the same for all affine opens `V ≤ U` of `X`;
* if `N.obj (op U)` is a finite `Γ(X, U)`-module for all affine opens `U ≤ W i`, then the same
  for all affine opens `U` of `X`.

Both are instances of "quasi-coherence, and being of finite type, are local on the base", and
both of those *are* available: `SheafOfModules.IsQuasicoherent.of_coversTop` in pinned Mathlib,
`AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen` for the affine-local form,
`Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop` and
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections` for finite
type. Each of them is stated for `SheafOfModules.over` or for
`AlgebraicGeometry.Scheme.Modules.restrict`, so feeding a *concrete* submodule to any of them is
exactly the open-immersion crossing this file is arranged to avoid, and that crossing — a
construction sending `N : F.Submodule` to a submodule of `F.restrict W.ι` with the corresponding
sections — is the one declaration standing between the glueing proved here and
[Stacks, Tag 01PF]. `StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` records the
same gap for its own glued object and treats the bridge as a separate step.

## Implementation notes

Three elaboration facts shape the proofs below:

* `CategoryTheory.Limits.InfSet`-style lattice operations on `SheafOfModules.Submodule F` are
  **not synthesized** for `F : X.Modules`: `InfSet (SheafOfModules.Submodule F)` fails, because
  `AlgebraicGeometry.Scheme.Modules` is a `def` and instance search does not unfold it. So the
  glued family is written out rather than obtained as an infimum of the one-member glueings, and
  `glue_obj_of_le` is then an equation between the values of the families with no lattice lemma
  in between.
* `F.val.map f` and `F.presheaf.map f` are **different terms** that are definitionally equal on
  elements, and `PresheafOfModules.Submodule.map_mem` produces the first while
  `Stacks.AlgebraicGeometry.GabberColimit.res_res` is stated about the second. `rw` therefore
  fails across them while `exact` succeeds. Every proof below follows the idiom of
  `Stacks.AlgebraicGeometry.GabberColimit.preSubmodule`: build a hypothesis whose type is written
  out in the `F.presheaf.map` spelling, rewrite inside *that*, and close the goal with `exact`.
* `U ⊓ W j = U` for `U ≤ W j` is **not** used as a rewrite: it occurs inside the proof arguments
  of the `CategoryTheory.homOfLE`s of the statement, and rewriting an open there fails on the
  motive. The two inequalities `U ≤ U ⊓ W j` and `U ⊓ W j ≤ U` are used instead, composed by
  `res_res` and collapsed by `Stacks.AlgebraicGeometry.GabberColimit.res_self`.

The sheaf condition of `Opens.grothendieckTopology` is pointwise by `rfl`
(`TopologicalSpace.Opens.mem_grothendieckTopology`), so the sheaf-condition proof is a single
`fun x hx ↦ _` followed by intersecting the given member of the covering with `W i`; the needed
inequality `V ⊓ W i ≤ U ⊓ W i` is `inf_le_inf_right`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmoduleGlueOpens

open Stacks.AlgebraicGeometry.GabberColimit

variable {X : Scheme.{u}} {F : X.Modules} {ι : Type*}

/-! ### Two restriction identities in the spellings the submodule API produces -/

/-- `Stacks.AlgebraicGeometry.GabberColimit.res_res` with the outer restriction written in the
`F.val.map` spelling, which is the one `PresheafOfModules.Submodule.map_mem` produces. The two
sides are definitionally equal, which is why the proof is the same term. -/
theorem valRes_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(F, U)) :
    F.val.map (homOfLE h2).op (F.presheaf.map (homOfLE h1).op x) =
      F.presheaf.map (homOfLE (h2.trans h1)).op x :=
  res_res F h1 h2 x

/-- `Stacks.AlgebraicGeometry.GabberColimit.res_res` with the inner restriction written in the
`F.val.map` spelling. -/
theorem res_valRes {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h2).op (F.val.map (homOfLE h1).op x) =
      F.presheaf.map (homOfLE (h2.trans h1)).op x :=
  res_res F h1 h2 x

/-! ### The glued submodule -/

section

variable (W : ι → X.Opens) (N : ι → F.Submodule)

/-- A section of `F` over `U` is *glued from* `N` along `W` if its restriction to `U ⊓ W i` lies
in `N i`, for every `i`. This is the membership condition of `glue W N`. -/
def IsGlued {U : X.Opens} (s : Γ(F, U)) : Prop :=
  ∀ i, F.presheaf.map (homOfLE (inf_le_left : U ⊓ W i ≤ U)).op s ∈ (N i).obj (op (U ⊓ W i))

/-- The sections of `F` over `U` glued from `N` along `W`, as a `Γ(X, U)`-submodule. -/
def localGlue (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | IsGlued W N s}
  add_mem' := by
    intro a b ha hb i
    rw [map_add]
    exact Submodule.add_mem _ (ha i) (hb i)
  zero_mem' := by
    intro i
    rw [map_zero]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c s hs i
    rw [F.map_smul (homOfLE (inf_le_left : U ⊓ W i ≤ U)) c s]
    exact Submodule.smul_mem _ _ (hs i)

/-- A section lies in `localGlue W N U` if and only if it is glued from `N` along `W`. -/
theorem mem_localGlue_iff {U : X.Opens} (s : Γ(F, U)) :
    s ∈ localGlue W N U ↔ IsGlued W N s :=
  Iff.rfl

/-- The glued family, as a submodule of the underlying presheaf of modules of `F`. Being glued
from `N` is stable under restriction because `V ⊓ W i ≤ U ⊓ W i` whenever `V ≤ U`. -/
def preGlue : F.val.Submodule where
  obj U := localGlue W N U.unop
  map {U V} f := by
    rintro s hs i
    have key := (N i).map_mem
      (homOfLE (inf_le_inf_right (W i) f.unop.le : V.unop ⊓ W i ≤ U.unop ⊓ W i)).op (hs i)
    rwa [valRes_res (inf_le_left : U.unop ⊓ W i ≤ U.unop)
        (inf_le_inf_right (W i) f.unop.le : V.unop ⊓ W i ≤ U.unop ⊓ W i) s,
      ← res_res F f.unop.le (inf_le_left : V.unop ⊓ W i ≤ V.unop) s] at key

/-- **The glued submodule of `F`.** Over an open `U` its sections are the sections of `F` whose
restriction to `U ⊓ W i` lies in `N i`, for every `i`.

Being glued from `N` is a local condition: for `V` running through a covering of `U`, the opens
`V ⊓ W i` cover `U ⊓ W i`, and each `N i` is a sheaf. -/
def glue : F.Submodule where
  toSubmodule := preGlue W N
  isSheaf := by
    intro U s hs i
    refine (N i).isSheaf _ fun x hx ↦ ?_
    obtain ⟨V, f, hf, hxV⟩ := hs x hx.1
    refine ⟨V ⊓ W i, homOfLE (inf_le_inf_right (W i) f.le), ?_, hxV, hx.2⟩
    have key : F.presheaf.map (homOfLE (inf_le_left : V ⊓ W i ≤ V)).op
        (F.presheaf.map (homOfLE f.le).op s) ∈ (N i).obj (op (V ⊓ W i)) := hf i
    rwa [res_res F f.le (inf_le_left : V ⊓ W i ≤ V) s,
      ← res_res F (inf_le_left : U.unop ⊓ W i ≤ U.unop)
        (inf_le_inf_right (W i) f.le : V ⊓ W i ≤ U.unop ⊓ W i) s] at key

/-- The sections of `glue W N` over `U` form the submodule `localGlue W N U`. -/
theorem glue_obj (U : X.Opens) : (glue W N).obj (op U) = localGlue W N U :=
  rfl

/-- A section over `U` lies in `glue W N` if and only if it is glued from `N` along `W`. -/
theorem mem_glue_iff {U : X.Opens} (s : Γ(F, U)) :
    s ∈ (glue W N).obj (op U) ↔ IsGlued W N s :=
  Iff.rfl

end

/-! ### The glueing identity -/

section

variable (W : ι → X.Opens) (N : ι → F.Submodule)

/-- The agreement hypothesis: two pieces agree over every open contained in both of their
members of the family. -/
def Agree : Prop :=
  ∀ (i j : ι) (V : X.Opens), V ≤ W i → V ≤ W j → (N i).obj (op V) = (N j).obj (op V)

/-- **The glueing identity.** If the pieces agree over every open contained in two members of
the family, then over an open contained in `W j` the glued submodule is `N j`.

The inclusion `≤` uses only the `j`-th constraint, transported from `U ⊓ W j` back to `U` along
`U ≤ U ⊓ W j`; the inclusion `≥` is where the agreement hypothesis is used, to see that the
restriction to `U ⊓ W i` of a section of `N j` lies in `N i`. -/
theorem glue_obj_of_le (hagree : Agree W N) {U : X.Opens} {j : ι} (hUW : U ≤ W j) :
    (glue W N).obj (op U) = (N j).obj (op U) := by
  refine SetLike.ext fun s ↦ ?_
  obtain ⟨s, rfl⟩ : ∃ y : Γ(F, U), y = s := ⟨s, rfl⟩
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · have key := (N j).map_mem
      (homOfLE (le_inf le_rfl hUW : U ≤ U ⊓ W j)).op (h j)
    rwa [valRes_res (inf_le_left : U ⊓ W j ≤ U) (le_inf le_rfl hUW : U ≤ U ⊓ W j) s,
      res_self] at key
  · rw [hagree i j (U ⊓ W i) inf_le_right (inf_le_left.trans hUW)]
    exact (N j).map_mem (homOfLE (inf_le_left : U ⊓ W i ≤ U)).op h

/-- **The local-to-global half.** A section of `F` over `U` lies in the glued submodule as soon
as `U` is covered by opens, each contained in some member of the family, over which the
restriction of the section lies in the corresponding piece. -/
theorem mem_glue_of_cover (hagree : Agree W N) {U : X.Opens} (s : Γ(F, U))
    (hcov : ∀ x ∈ U, ∃ (V : X.Opens) (k : ι) (hVU : V ≤ U), V ≤ W k ∧ x ∈ V ∧
      F.presheaf.map (homOfLE hVU).op s ∈ (N k).obj (op V)) :
    s ∈ (glue W N).obj (op U) := by
  refine (glue W N).isSheaf s fun x hx ↦ ?_
  obtain ⟨V, k, hVU, hVW, hxV, hmem⟩ := hcov x hx
  refine ⟨V, homOfLE hVU, ?_, hxV⟩
  have key : F.val.map (homOfLE hVU).op s ∈ (N k).obj (op V) := hmem
  rwa [← glue_obj_of_le W N hagree hVW] at key

end

/-! ### Transfer of the two properties an extension argument carries -/

/-- The sections of a submodule of `F` over an open, at the `Γ(X, U)`-module spelling. The
projection `N.obj (op U)` is a submodule over `X.ringCatSheaf.obj.obj (op U)` of
`F.val.obj (op U)`; those are the same ring and the same module as `Γ(X, U)` and `Γ(F, U)`, but
not the same *terms*, and `Module.Finite` and `Submodule.span` both need the latter spelling to
find their instances. Giving the retyping a name is what lets `sections_glue_of_le` be used as a
rewrite: a `show … from …` ascription inlined into a statement becomes a `have`-expression, which
blocks `rw` under a coercion. -/
def sections (N : F.Submodule) (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) :=
  N.obj (op U)

section

variable (W : ι → X.Opens) (N : ι → F.Submodule) (hagree : Agree W N)

include hagree

/-- `glue_obj_of_le` at the `Γ(X, U)`-module spelling of the sections. -/
theorem sections_glue_of_le {U : X.Opens} {j : ι} (hUW : U ≤ W j) :
    sections (glue W N) U = sections (N j) U :=
  glue_obj_of_le W N hagree hUW

/-- Over an open contained in a member of the family the sections of the glue are the sections
of the corresponding piece, so finiteness of the sections transfers. -/
theorem finite_sections_glue_of_le {j : ι} {U : X.Opens} (hUW : U ≤ W j)
    (hfin : Module.Finite Γ(X, U) ↥(sections (N j) U)) :
    Module.Finite Γ(X, U) ↥(sections (glue W N) U) := by
  rwa [sections_glue_of_le W N hagree hUW]

/-- Over pairs of opens contained in one member of the family, the glue satisfies the
compatibility identity of `Stacks.AlgebraicGeometry.GabberColimit.IsCompatible` as soon as the
corresponding piece does. -/
theorem span_sections_glue_of_le {j : ι} {U V : X.Opens} (hUW : U ≤ W j) (hVW : V ≤ W j)
    (hVU : V ≤ U)
    (hcomp : sections (N j) V =
      Submodule.span Γ(X, V) (F.presheaf.map (homOfLE hVU).op '' (sections (N j) U))) :
    sections (glue W N) V =
      Submodule.span Γ(X, V) (F.presheaf.map (homOfLE hVU).op '' (sections (glue W N) U)) := by
  rwa [sections_glue_of_le W N hagree hVW, sections_glue_of_le W N hagree hUW]

end

end Stacks.AlgebraicGeometry.SubmoduleGlueOpens

end
