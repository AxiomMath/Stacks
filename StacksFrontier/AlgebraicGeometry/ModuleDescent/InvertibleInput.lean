module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# The invertible-module inputs for descent through a limit of schemes

Stacks Tag 0B8W descends an invertible module on a cofiltered limit of quasi-compact and
quasi-separated schemes with affine transition morphisms to an invertible module at a finite
stage.  Its proof in the source runs through Tag 01ZR, which descends *finitely presented*
modules, and the passage between the two hypotheses is the rank-one characterization of
invertibility.  This file supplies that passage **on a scheme, in the spelling the statement
of Tag 0B8W uses for its hypothesis**, and reduces the shape of its conclusion to
the rank-one statement.

Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean` (Tag 01CS): tensoring by the module is an
equivalence.  Fixed-rank local freeness is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean` (Tag 01C6, part 3).  Finite presentation
is Mathlib's `SheafOfModules.IsFinitePresentation`, which is what the statement of Tag 01ZR assumes.

## Route

Everything here is assembled from results already in the repository; no mathematics is new.

* Invertible implies rank one: `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible`
  on a ringed space, specialized to a scheme (where the stalks are local rings automatically) by
  `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme`.
* Rank one implies invertible: `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`,
  whose dual is built explicitly and which needs no hypothesis on the stalks.
* Rank one implies finitely presented: the class bridge
  `Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank`
  followed by `Stacks.FiniteLocallyFree.isFinitePresentation`.

The only friction is spelling, and it is the one recorded at
`AlgebraicGeometry.Scheme.structureSheaf_sheaf_obj_property`: a scheme's `ringCatSheaf` and the
site-level structure sheaf of Tag 05NA built from `X.sheaf.obj` and `X.ringCatSheaf.property` are
equal by `rfl` at default transparency, but instance search is keyed syntactically and does not
see it.  Each statement below therefore re-types its hypothesis at the spelling the consumed
result quantifies over, which is enough.

## Main results

* `Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: on a scheme, with no
  hypothesis on the stalks, a sheaf of modules is invertible exactly when it is finite locally
  free of rank one.  This is the translation between the hypothesis of Tag 0B8W and a
  condition that descends.
* `Stacks.ModuleDescent.isFinitePresentation_of_isInvertible`: an invertible module on a scheme
  is of finite presentation.  This is exactly the implication that lets the hypothesis of
  Tag 0B8W be fed to the hypothesis of Tag 01ZR.
* `Stacks.ModuleDescent.exists_isInvertible_of_exists_isFiniteLocallyFreeOfRank_one`: the shape
  of the Tag 0B8W conclusion follows from the corresponding rank-one statement.  It assumes
  nothing about the index category, the diagram, or the cone, so it applies to the situation
  of Tag 0B8W in particular.

## What is not done

* **Neither Tag 01ZR nor Tag 0B8W is proved here, and nothing here is tagged.** No descent
  statement for sheaves of modules through a limit of schemes is proved in this file or anywhere
  in the repository.  What is missing, concretely, is a declaration of the shape asserted by
  `exists_isInvertible_of_exists_isFiniteLocallyFreeOfRank_one`'s hypothesis: for a cofiltered
  `D : I ⥤ Scheme` with affine transitions and quasi-compact quasi-separated stages, and a limit
  cone `c`, a rank-one locally free module on `c.pt` is the pullback of one at a stage.  That
  statement is the single remaining input for Tag 0B8W.
* The two implications of `isInvertible_iff_isFiniteLocallyFreeOfRank_one` are *not* reproved;
  they are the two results named in the route above, restated for a scheme.  The ringed-space
  form of the same biconditional is `Stacks.InvertibleRankOneIff`, which is stated over
  `structureSheaf X.sheaf` of Tag 01CO rather than over `X.ringCatSheaf`, and so is not
  applicable to a module on a scheme without the re-typing done here.
* No converse of `isFinitePresentation_of_isInvertible` is stated, and none is true: a finitely
  presented module need not be invertible.
* Nothing is proved about pullback: in particular it is *not* shown here that the pullback of an
  invertible module along a morphism of schemes is invertible, nor that the pullback of a module
  of finite presentation is of finite presentation.  Both are needed by a full proof of Tag 0B8W
  and neither is available in the repository at the `Scheme.Modules` spelling.
* The index-universe question of Tag 0B8W is untouched.  Its statement leaves the universe
  of the index type free of the scheme universe, while the statements of Tag 01ZR tie the two
  together;
  the statements here are indifferent to this, since they quantify over a single scheme.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.ModuleDescent

/-- Rank-one local freeness over `X.ringCatSheaf` re-typed at the structure sheaf of Tag 05NA. -/
private theorem isFiniteLocallyFreeOfRank_structureSheaf (X : Scheme.{u}) (L : X.Modules)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1) :
    SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        X.ringCatSheaf.property) L 1 := hL

/-- A finite locally free module of rank one on a scheme is invertible.

This is `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`, whose rank-one
hypothesis is re-typed at the structure sheaf of Tag 05NA built from the scheme's own sheaf and
sheaf condition. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one (X : Scheme.{u}) (L : X.Modules)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  have := isFiniteLocallyFreeOfRank_structureSheaf X L hL
  Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one
    X.sheaf.obj X.ringCatSheaf.property L

/-- An invertible module on a scheme is finite locally free of rank one.

This is `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme`; the stalks of
a scheme are local rings, so the hypothesis on the stalks that the ringed-space form of this
implication carries is automatic. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (X : Scheme.{u}) (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1 :=
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L

/-- On a scheme, a sheaf of modules is invertible exactly when it is finite locally free of
rank one.  No hypothesis on the stalks is needed: a scheme has local stalks. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one (X : Scheme.{u}) (L : X.Modules) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1 :=
  ⟨isFiniteLocallyFreeOfRank_one_of_isInvertible X L,
    isInvertible_of_isFiniteLocallyFreeOfRank_one X L⟩

/-- A finite locally free module of rank one on a scheme is of finite presentation.

The rank-one class gives `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, from which finite
presentation follows by `Stacks.FiniteLocallyFree.isFinitePresentation`. -/
theorem isFinitePresentation_of_isFiniteLocallyFreeOfRank_one (X : Scheme.{u}) (L : X.Modules)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) L :=
  have := isFiniteLocallyFreeOfRank_structureSheaf X L hL
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
    Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      X.sheaf.obj X.ringCatSheaf.property L 1
  Stacks.FiniteLocallyFree.isFinitePresentation L

/-- An invertible module on a scheme is of finite presentation.

This is the implication that connects the hypothesis of the statement of Tag 0B8W to the
hypothesis of the statement of Tag 01ZR: the latter assumes Mathlib's
`SheafOfModules.IsFinitePresentation`, the former assumes invertibility in the sense of
Tag 01CS, and a proof of Tag 0B8W along the lines of the source needs to pass from the second
to the first. -/
theorem isFinitePresentation_of_isInvertible (X : Scheme.{u}) (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) L :=
  isFinitePresentation_of_isFiniteLocallyFreeOfRank_one X L
    (isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL)

/-- The conclusion of the statement of Tag 0B8W follows from the same statement with
invertibility replaced by rank-one local freeness.

Nothing is assumed about the index category, the diagram, the cone, or the module: the statement
is a pointwise application of `isInvertible_of_isFiniteLocallyFreeOfRank_one` at the stage
produced by the hypothesis.  In the situation of Tag 0B8W -- `I` cofiltered, the transition
morphisms affine, every stage quasi-compact and quasi-separated, and `c` a limit cone -- the
hypothesis is the rank-one case of part (1) of Tag 0B8W, which is the single remaining input for
that tag. -/
theorem exists_isInvertible_of_exists_isFiniteLocallyFreeOfRank_one {I : Type w} [Category.{v} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (L : c.pt.Modules)
    (h : ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := (D.obj i).ringCatSheaf) Lᵢ 1 ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ)) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      SheafOfModules.IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) := by
  obtain ⟨i, Lᵢ, hLᵢ, e⟩ := h
  exact ⟨i, Lᵢ, isInvertible_of_isFiniteLocallyFreeOfRank_one (D.obj i) Lᵢ hLᵢ, e⟩

end Stacks.ModuleDescent

end
