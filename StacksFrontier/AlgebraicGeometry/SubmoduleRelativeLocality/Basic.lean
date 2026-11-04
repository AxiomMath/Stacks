module

public import StacksFrontier.AlgebraicGeometry.SubmoduleAgree.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal

/-!
# Quasi-coherence and finite type over an open, from a covering of that open

Every locality theorem for `𝒪_X`-modules in this tree concludes about a module on `X` from
hypotheses on the members of a covering of `X`: `Stacks.Modules.isQuasicoherent_of_restrict` and
`AlgebraicGeometry.Modules.isFiniteType_of_restrict` both ask for `⨆ i, U i = ⊤`. The affine
induction of [Stacks, Tag 01PF] needs the same statements **relative to an open** `W` of `X`: at
the inductive step it glues a subsheaf given over a quasi-compact open `U` to one produced over an
affine open `V`, and what it must know about the result is that it is quasi-coherent and of finite
type over `U ⊔ V`, not over `X` — the family `{U, V}` covers `U ⊔ V` and nothing more.

This file supplies the relative statements, and then the glueing step of the induction in the
shape the recursion applies it: for two submodules of `F` agreeing over the opens inside `U ⊓ V`,
the glue is quasi-coherent and of finite type over `U ⊔ V`.

## Main results

* `iSup_preimage_eq_top`: a covering of `W` pulls back to a covering of the open subscheme `W`.
* `restrictPreimageIso`: **the comparison that makes the whole file work.** Restricting `M` to
  `W` and then to the preimage of `U` is restricting it to `U` and then along
  `AlgebraicGeometry.Modules.resOpen`.
* `isQuasicoherent_restrict_of_cover`, `isFiniteType_restrict_of_cover`: the relative locality
  statements for an `𝒪_X`-module.
* `isQuasicoherent_restrictTo_of_cover`, `isFiniteType_restrictTo_of_cover`: the same for a
  concrete submodule, which is the spelling the glueing step is written in.
* `isQuasicoherent_glue_pair`, `isFiniteType_glue_pair`: **the glueing step of the induction.**
  The glue of two pieces agreeing over the opens inside `U ⊓ V` is quasi-coherent, respectively
  of finite type, over `U ⊔ V`.
* `restrictTo_glue_pair_left`, `restrictTo_glue_pair_right`, `obj_glue_pair_of_le_left`: the glue
  restricts to the given piece on each of the two members, and has its sections over every open
  inside `U`. The first of these is what carries the inductive hypothesis forward and the last is
  what proves the conclusion `𝒢'|_U = 𝒢`.

## Implementation notes

The comparison `restrictPreimageIso` is `AlgebraicGeometry.Modules.restrictCompIso` — "two
iterated restrictions along equal composites agree" — instantiated at the equality
`AlgebraicGeometry.Modules.resOpen_comp_ι`, i.e. at
`(W.ι ⁻¹ᵁ U).ι ≫ W.ι = resOpen W.ι U ≫ U.ι`. Both of those are used in the proof of
`AlgebraicGeometry.Modules.isFiniteType_restrict` and are reused verbatim; no new comparison of
restriction functors is constructed here, and in particular no `eqToHom` on opens is written
anywhere in this file.

Two universe constraints are inherited and are not cosmetic. `isQuasicoherent_of_restrict` is
polymorphic in the universe of the index type, so the quasi-coherent statements are; whereas
`isFiniteType_of_restrict` indexes its covering by a `Type u` with `u` the universe of the
scheme, so the finite-type statements do too. That is why the two-member family of
`Stacks.AlgebraicGeometry.SubmoduleAgree.pairOpens` is indexed by `ULift Bool` and not by `Bool`.

The transports along `Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules` are
written out with `▸` and never left to unification, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Locality.lean`: at `f = W.ι` the elaborator
unfolds the open-immersion structure and exhausts the heartbeat budget at `whnf`, although the
equality is a `rfl` for a general open immersion.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** Nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag; this is the glueing step of that lemma's affine
induction, relativised to the open the induction is at.

Coherence is not relativised. `AlgebraicGeometry.Modules.isCoherent_restrict` is stated only for
the inclusion of an open subscheme, not for a general open immersion, so the argument below —
which restricts along `AlgebraicGeometry.Modules.resOpen` — does not apply to it unchanged.
[Stacks, Tag 01PF] does not need it.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.SubmoduleRelativeLocality

open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.SubmoduleGlueLocality Stacks.AlgebraicGeometry.SubmoduleAgree

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### A covering of an open, read on the open subscheme -/

/-- A family of opens of `X` with supremum `W` pulls back along `W.ι` to a covering of the open
subscheme `W`. -/
theorem iSup_preimage_eq_top {W : X.Opens} {I : Type*} (U : I → X.Opens)
    (hcov : ⨆ i, U i = W) : ⨆ i, W.ι ⁻¹ᵁ U i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hcov, W.ι_preimage_self]

/-! ### The comparison of the two ways of restricting twice -/

/-- **Restricting to `W` and then to the preimage of `U` is restricting to `U` and then along
`AlgebraicGeometry.Modules.resOpen`.** -/
def restrictPreimageIso (M : X.Modules) (W U : X.Opens) :
    Scheme.Modules.restrict (Scheme.Modules.restrict M W.ι) (W.ι ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrict (Scheme.Modules.restrict M U.ι)
        (AlgebraicGeometry.Modules.resOpen W.ι U) :=
  AlgebraicGeometry.Modules.restrictCompIso M W.ι (W.ι ⁻¹ᵁ U).ι U.ι
    (AlgebraicGeometry.Modules.resOpen W.ι U)
    (AlgebraicGeometry.Modules.resOpen_comp_ι W.ι U).symm

/-! ### The relative locality statements for a module -/

/-- Quasi-coherence is invariant under isomorphism, with the ring sheaf in an explicit binder.
This is the quasi-coherent twin of `AlgebraicGeometry.Modules.isFiniteType_of_iso`, and the
reason it is needed is elaboration and not mathematics: applying
`CategoryTheory.ObjectProperty.prop_of_iso` to `SheafOfModules.isQuasicoherent _` directly leaves
the ring sheaf as a metavariable that the hypothesis cannot determine. -/
theorem isQuasicoherent_of_iso {Z : Scheme.{u}} {M N : SheafOfModules.{u} Z.ringCatSheaf}
    (e : M ≅ N) (h : M.IsQuasicoherent) : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e h

/-- **Quasi-coherence over an open is local on that open.** -/
theorem isQuasicoherent_restrict_of_cover (M : X.Modules) (W : X.Opens) {I : Type w}
    (U : I → X.Opens) (hcov : ⨆ i, U i = W)
    (h : ∀ i, (Scheme.Modules.restrict M (U i).ι).IsQuasicoherent) :
    (Scheme.Modules.restrict M W.ι).IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict (Scheme.Modules.restrict M W.ι)
    (fun i => W.ι ⁻¹ᵁ U i) (iSup_preimage_eq_top U hcov) fun i => ?_
  have hi : (Scheme.Modules.restrict (Scheme.Modules.restrict M (U i).ι)
      (AlgebraicGeometry.Modules.resOpen W.ι (U i))).IsQuasicoherent :=
    have := h i
    inferInstance
  exact isQuasicoherent_of_iso (restrictPreimageIso M W (U i)).symm hi

/-- **Being of finite type over an open is local on that open.** -/
theorem isFiniteType_restrict_of_cover (M : X.Modules) (W : X.Opens) {I : Type u}
    (U : I → X.Opens) (hcov : ⨆ i, U i = W)
    (h : ∀ i, (Scheme.Modules.restrict M (U i).ι).IsFiniteType) :
    (Scheme.Modules.restrict M W.ι).IsFiniteType := by
  refine AlgebraicGeometry.Modules.isFiniteType_of_restrict (Scheme.Modules.restrict M W.ι)
    (fun i => W.ι ⁻¹ᵁ U i) (IsOpenCover.mk (iSup_preimage_eq_top U hcov)) fun i => ?_
  exact AlgebraicGeometry.Modules.isFiniteType_of_iso (restrictPreimageIso M W (U i)).symm
    (AlgebraicGeometry.Modules.isFiniteType_restrict
      (AlgebraicGeometry.Modules.resOpen W.ι (U i)) _ (h i))

/-! ### The relative locality statements for a concrete submodule -/

/-- **Quasi-coherence of a concrete submodule over an open is local on that open.** -/
theorem isQuasicoherent_restrictTo_of_cover (N : F.Submodule) (W : X.Opens) {I : Type w}
    (U : I → X.Opens) (hcov : ⨆ i, U i = W)
    (h : ∀ i, (restrictTo (U i).ι N).toSheafOfModules.IsQuasicoherent) :
    (restrictTo W.ι N).toSheafOfModules.IsQuasicoherent :=
  (restrictTo_toSheafOfModules W.ι N).symm ▸
    isQuasicoherent_restrict_of_cover (N.toSheafOfModules : X.Modules) W U hcov
      fun i => restrictTo_toSheafOfModules (U i).ι N ▸ h i

/-- **Being of finite type is local on an open, for a concrete submodule.** -/
theorem isFiniteType_restrictTo_of_cover (N : F.Submodule) (W : X.Opens) {I : Type u}
    (U : I → X.Opens) (hcov : ⨆ i, U i = W)
    (h : ∀ i, (restrictTo (U i).ι N).toSheafOfModules.IsFiniteType) :
    (restrictTo W.ι N).toSheafOfModules.IsFiniteType :=
  (restrictTo_toSheafOfModules W.ι N).symm ▸
    isFiniteType_restrict_of_cover (N.toSheafOfModules : X.Modules) W U hcov
      fun i => restrictTo_toSheafOfModules (U i).ι N ▸ h i

/-! ### The glueing step of the induction -/

section Pair

variable {U V : X.Opens} {N₀ N₁ : F.Submodule}
  (h : ∀ Z : X.Opens, Z ≤ U → Z ≤ V → N₀.obj (op Z) = N₁.obj (op Z))

include h

/-- **The glue of two pieces agreeing over the overlap restricts to the first piece on `U`.**
This is what carries the inductive hypothesis of [Stacks, Tag 01PF] forward. -/
theorem restrictTo_glue_pair_left :
    restrictTo U.ι (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁)) = restrictTo U.ι N₀ :=
  restrictTo_glue_of_le _ _ (agree_pair h) (ULift.up false)

/-- The glue restricts to the second piece on `V`. -/
theorem restrictTo_glue_pair_right :
    restrictTo V.ι (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁)) = restrictTo V.ι N₁ :=
  restrictTo_glue_of_le _ _ (agree_pair h) (ULift.up true)

/-- **The sections of the glue over an open inside `U` are the sections of the first piece.**
This is the statement that the extension produced by the induction restricts to the subsheaf it
started from. -/
theorem obj_glue_pair_of_le_left {Z : X.Opens} (hZ : Z ≤ U) :
    (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁)).obj (op Z) = N₀.obj (op Z) :=
  glue_obj_of_le _ _ (agree_pair h) (j := ULift.up false) hZ

/-- The sections of the glue over an open inside `V` are the sections of the second piece. -/
theorem obj_glue_pair_of_le_right {Z : X.Opens} (hZ : Z ≤ V) :
    (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁)).obj (op Z) = N₁.obj (op Z) :=
  glue_obj_of_le _ _ (agree_pair h) (j := ULift.up true) hZ

/-- A property of the restrictions to the two members of the pair covering transfers from the
pieces to the glue. -/
private theorem restrictTo_glue_pair_prop
    {P : ∀ W : X.Opens, (Scheme.Modules.restrict F W.ι).Submodule → Prop}
    (h₀ : P U (restrictTo U.ι N₀)) (h₁ : P V (restrictTo V.ι N₁)) (i : ULift Bool) :
    P (pairOpens.{u} U V i)
      (restrictTo (pairOpens.{u} U V i).ι (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁))) := by
  rcases i with ⟨_ | _⟩
  · rw [show pairOpens.{u} U V (ULift.up false) = U from rfl, restrictTo_glue_pair_left h]
    exact h₀
  · rw [show pairOpens.{u} U V (ULift.up true) = V from rfl, restrictTo_glue_pair_right h]
    exact h₁

/-- **The glue of two quasi-coherent pieces is quasi-coherent over `U ⊔ V`.** -/
theorem isQuasicoherent_glue_pair
    (h₀ : (restrictTo U.ι N₀).toSheafOfModules.IsQuasicoherent)
    (h₁ : (restrictTo V.ι N₁).toSheafOfModules.IsQuasicoherent) :
    (restrictTo (U ⊔ V).ι
      (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁))).toSheafOfModules.IsQuasicoherent := by
  refine isQuasicoherent_restrictTo_of_cover _ (U ⊔ V) (pairOpens.{u} U V)
    (iSup_pairOpens U V)
    (restrictTo_glue_pair_prop h (P := fun _ G => G.toSheafOfModules.IsQuasicoherent) h₀ h₁)

/-- **The glue of two pieces of finite type is of finite type over `U ⊔ V`.** -/
theorem isFiniteType_glue_pair
    (h₀ : (restrictTo U.ι N₀).toSheafOfModules.IsFiniteType)
    (h₁ : (restrictTo V.ι N₁).toSheafOfModules.IsFiniteType) :
    (restrictTo (U ⊔ V).ι
      (glue (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁))).toSheafOfModules.IsFiniteType := by
  refine isFiniteType_restrictTo_of_cover _ (U ⊔ V) (pairOpens.{u} U V)
    (iSup_pairOpens U V)
    (restrictTo_glue_pair_prop h (P := fun _ G => G.toSheafOfModules.IsFiniteType) h₀ h₁)

end Pair

end Stacks.AlgebraicGeometry.SubmoduleRelativeLocality

end
