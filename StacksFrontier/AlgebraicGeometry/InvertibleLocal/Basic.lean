module

public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# Invertibility of a module on a scheme is local on the base

Let `X` be a scheme, let `L` be a sheaf of `𝒪_X`-modules and let `U i` be a family of opens
covering `X`.  This file proves that `L` is invertible as soon as each restriction
`L|_{U i}` is invertible on the open subscheme `U i`, and conversely that every restriction of
an invertible module is invertible.  Invertibility is therefore a local property, which is not
visible from its definition: following [Stacks, Tag 01CS] it says that the sheafified tensor
functor `- ⊗ L` is an equivalence, a property of the whole category of modules on `X`.

Both halves needed for this were already in the repository and had not been joined:

* `Stacks.Modules.exists_restrict_iso_unit_of_isInvertible` of
  `StacksFrontier/AlgebraicGeometry/PullbackInvertible/Basic.lean` trivializes an invertible module
  on an open cover — this is clause 2 of [Stacks, Tag 0B8M] in the only form the repository has
  it, and it is available because a scheme is locally ringed;
* `Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyTrivialInvertible/Basic.lean` concludes
  invertibility from trivializations on a covering — clause 1 of the same tag.

What has to be supplied between them is the transport of a trivialization produced on an open
`V` of the open subscheme `U` to the corresponding open `U.ι ''ᵁ V` of `X`, which is
`Stacks.Modules.restrictIsoUnitOfImage` below.  Then the trivializing opens of all the `U i`,
pushed into `X`, cover `X`, and clause 1 applies on `X` itself.

## Main definitions

* `Stacks.Modules.restrictIsoUnitOfImage`: a trivialization of `L|_U` on an open `V` of `U`,
  read as a trivialization of `L` on the open `U.ι ''ᵁ V` of `X`.

## Main results

* `Stacks.Modules.exists_mem_restrict_iso_unit_of_isInvertible_restrict`: if `L|_U` is
  invertible then every point of `U` has an open neighbourhood inside `U` on which `L` is
  isomorphic to the structure sheaf.
* `Stacks.Modules.isInvertible_of_isInvertible_restrict_of_iSup_eq_top` and
  `Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover`: **invertibility is local
  on the base.**  A module whose restriction to each member of an open cover is invertible is
  invertible.
* `Stacks.Modules.isInvertible_restrict_of_isInvertible`: the converse, so that no hypothesis
  of the two preceding statements is stronger than their conclusion.
* `Stacks.Modules.isInvertible_iff_forall_isInvertible_restrict`: the two together, as an
  equivalence.

## Implementation notes

**This is not the descent statement on a general site.**
`Stacks.InvertibleLocallyFree.InvertibleIsLocal` of
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean` is the same assertion for an
arbitrary site and remains open; the route taken here does not prove it, because clause 2 of
Tag 0B8M is used, and the only proof of clause 2 in the repository
(`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`) needs the stalks of the
structure sheaf to be local rings.  A scheme has that; a site does not.  So the locality proved
here is locality over a *locally ringed* base, and the general descent problem is untouched.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class both halves of
Tag 0B8M are stated in and the one the statements of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalForm.lean` use.  The
hypothesis and conclusion are spelled with `X.ringCatSheaf.2` for the sheaf condition, as those
statements do; `Stacks.Modules.exists_restrict_iso_unit_of_isInvertible` spells the same
condition `(structureSheafRing X.toRingedSpace).property`, and the two are identified by proof
irrelevance alone, so a `have` naming the one spelling for the other is all that is needed.

**The cover indexing.** The trivializing family is indexed by the *points* of `X`: for each
point one member of the given cover containing it is chosen, and then one trivializing
neighbourhood inside that member.  This is the shape
`Stacks.Modules.exists_restrict_iso_unit_of_isInvertible` itself produces, and it avoids forming
the sigma type `Σ i, U i`, whose elaboration would carry the index family into the covering
hypothesis.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Modules

variable {X : Scheme.{u}}

/-! ### Pushing a trivialization out of an open subscheme -/

/-- **A trivialization on an open of an open subscheme, read on the image open.**  Let `U` be an
open of the scheme `X` and `V` an open of the open subscheme `U`.  A trivialization of
`(L|_U)|_V` is a trivialization of `L` on the open `U.ι ''ᵁ V` of `X`, because
`Scheme.Hom.isoImage` identifies `V` with `U.ι ''ᵁ V` over `X`.

This is the step that lets local data produced inside an open subscheme be collected on the
ambient scheme, where clause 1 of [Stacks, Tag 0B8M] can be applied. -/
noncomputable def restrictIsoUnitOfImage (U : X.Opens) (V : U.toScheme.Opens) (L : X.Modules)
    (e : Scheme.Modules.restrict (Scheme.Modules.restrict L U.ι) V.ι ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) :
    Scheme.Modules.restrict L (U.ι ''ᵁ V).ι ≅
      SheafOfModules.unit (U.ι ''ᵁ V).toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr
        (Scheme.Hom.isoImage_inv_ι U.ι V)).app L).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (U.ι.isoImage V).inv (V.ι ≫ U.ι)).app L ≪≫
    (Scheme.Modules.restrictFunctor (U.ι.isoImage V).inv).mapIso
      ((Scheme.Modules.restrictFunctorComp V.ι U.ι).app L ≪≫ e) ≪≫
    Scheme.Modules.restrictUnitIso (U.ι.isoImage V).inv

/-! ### From local invertibility to local triviality -/

/-- A point of a space lies in some member of a family of opens whose supremum is `⊤`. -/
private theorem mem_iSup_of_eq_top {Y : Type*} [TopologicalSpace Y] {ι : Type*}
    {V : ι → Opens Y} (h : (⨆ i, V i) = ⊤) (y : Y) : ∃ i, y ∈ V i :=
  Opens.mem_iSup.mp (h ▸ Opens.mem_top y)

/-- **An invertible restriction trivializes in a neighbourhood of every point of the open.**  If
`L|_U` is invertible on the open subscheme `U`, every point of `U` has an open neighbourhood
`W ≤ U` in `X` with `L|_W` isomorphic to `𝒪_W`.

This is clause 2 of [Stacks, Tag 0B8M], applied on `U.toScheme` and transported back to `X` by
`restrictIsoUnitOfImage`. -/
theorem exists_mem_restrict_iso_unit_of_isInvertible_restrict (L : X.Modules) (U : X.Opens)
    (hL : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      (Scheme.Modules.restrict L U.ι))
    (x : X) (hx : x ∈ U) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ U ∧
      Nonempty (Scheme.Modules.restrict L W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  have : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf
      (structureSheafRing U.toScheme.toRingedSpace).property
      (Scheme.Modules.restrict L U.ι) := hL
  obtain ⟨V, hV, hiso⟩ :=
    exists_restrict_iso_unit_of_isInvertible (Scheme.Modules.restrict L U.ι)
  obtain ⟨y, hy⟩ := mem_iSup_of_eq_top hV (⟨x, hx⟩ : U.toScheme)
  exact ⟨U.ι ''ᵁ V y, ⟨⟨x, hx⟩, hy, rfl⟩, U.ι_image_le (V y),
    ⟨restrictIsoUnitOfImage U (V y) L (hiso y).some⟩⟩

/-! ### Invertibility is local on the base -/

/-- **Invertibility of a module on a scheme is local on the base.**  If the restriction of `L`
to each member of a family of opens with supremum `⊤` is invertible, then `L` is invertible.

The converse is `isInvertible_restrict_of_isInvertible`, so the hypothesis is no stronger than
the conclusion. -/
theorem isInvertible_of_isInvertible_restrict_of_iSup_eq_top (L : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (hL : ∀ i, Stacks.SheafOfModules.IsInvertible (U i).toScheme.presheaf
      (U i).toScheme.ringCatSheaf.2 (Scheme.Modules.restrict L (U i).ι)) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := by
  have key : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty (Scheme.Modules.restrict L W.ι ≅
        SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨i, hi⟩ := mem_iSup_of_eq_top hU x
    obtain ⟨W, hxW, -, hW⟩ :=
      exists_mem_restrict_iso_unit_of_isInvertible_restrict L (U i) (hL i) x hi
    exact ⟨W, hxW, hW⟩
  choose W hxW hiso using key
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit
    X.presheaf X.ringCatSheaf.2 L (X := W) ?_
    fun x => ⟨overIsoUnitOfRestrictIsoUnit L (W x) (hiso x).some⟩
  exact (Opens.coversTop_iff _ _).2
    (IsOpenCover.mk (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hxW x⟩))

/-- **Invertibility of a module on a scheme may be checked on an open cover.**  The
`TopologicalSpace.IsOpenCover` form of `isInvertible_of_isInvertible_restrict_of_iSup_eq_top`,
which is the spelling the reconstruction statements of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalForm.lean` produce. -/
theorem isInvertible_of_isInvertible_restrict_isOpenCover (L : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hL : ∀ i, Stacks.SheafOfModules.IsInvertible (U i).toScheme.presheaf
      (U i).toScheme.ringCatSheaf.2 (Scheme.Modules.restrict L (U i).ι)) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
  isInvertible_of_isInvertible_restrict_of_iSup_eq_top L U hU.iSup_eq_top hL

/-- **The restriction of an invertible module to an open subscheme is invertible.**  This is the
converse of `isInvertible_of_isInvertible_restrict_of_iSup_eq_top`: it shows that the
hypothesis there is implied by the conclusion, so nothing stronger than invertibility has been
assumed on the members of the cover.

The restriction along an open immersion is the pullback along it
(`Scheme.Modules.restrictFunctorIsoPullback`), and the pullback of an invertible module is
invertible by `Stacks.Modules.isInvertible_pullback`. -/
theorem isInvertible_restrict_of_isInvertible (L : X.Modules) (U : X.Opens)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      (Scheme.Modules.restrict L U.ι) := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L := hL
  have : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf
      U.toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback U.ι).obj L) :=
    isInvertible_pullback U.ι L
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

/-- **Invertibility of a module on a scheme is exactly invertibility of its restrictions to the
members of an open cover.**  The two directions are
`isInvertible_of_isInvertible_restrict_isOpenCover` and
`isInvertible_restrict_of_isInvertible`. -/
theorem isInvertible_iff_forall_isInvertible_restrict (L : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : IsOpenCover U) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ↔
      ∀ i, Stacks.SheafOfModules.IsInvertible (U i).toScheme.presheaf
        (U i).toScheme.ringCatSheaf.2 (Scheme.Modules.restrict L (U i).ι) :=
  ⟨fun hL i => isInvertible_restrict_of_isInvertible L (U i) hL,
    isInvertible_of_isInvertible_restrict_isOpenCover L U hU⟩

end Stacks.Modules

end
