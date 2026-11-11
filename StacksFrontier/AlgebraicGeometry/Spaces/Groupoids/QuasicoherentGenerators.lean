module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# A generating family for the quasi-coherent modules on a groupoid in algebraic spaces

Stacks 0780 asserts that for a groupoid in algebraic spaces with flat source and target there
is a *set* of quasi-coherent modules on the groupoid such that every quasi-coherent module on
it is the directed colimit of those of its submodules that are isomorphic to a member of the
set.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.isomorphicGeneratorSubobjectProperty` selects the
  subobjects isomorphic to a member of a fixed family.
* `AlgebraicGeometry.Space.QuasicoherentModule.IsomorphicGeneratorSubobject` is the full
  subcategory of `CategoryTheory.Subobject` that this property cuts out, and
  `AlgebraicGeometry.Space.QuasicoherentModule.isomorphicGeneratorSubobjectFunctor` is its
  diagram in the quasi-coherent modules.
* `AlgebraicGeometry.Space.QuasicoherentModule.isomorphicGeneratorSubobjectCocone` is the
  canonical cocone from that diagram to the ambient module.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.exists_generating_family`: the same conclusion
  with a class-sized family, indexed by a type of the universe `u + 1` of the objects of the
  category.  It is not Stacks 0780, whose content is that the family is a set; that is
  `AlgebraicGeometry.Space.QuasicoherentModule.exists_small_generating_family` in
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentGeneratingSet.lean`.

## Implementation notes

Submodules are categorical subobjects of the quasi-coherent module, directedness is
filteredness of the full subcategory they form, and "is the colimit" is the universal property
of the canonical cocone.

## References

* [Stacks Project, Tag 0780](https://stacks.math.columbia.edu/tag/0780)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasicoherentModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- The subobjects of a quasi-coherent module on a groupoid in algebraic spaces that are
isomorphic to a member of a fixed family. -/
def isomorphicGeneratorSubobjectProperty (T : Type v)
    (F : T → QuasicoherentModule B S hS G) (M : QuasicoherentModule B S hS G) :
    ObjectProperty (Subobject M) :=
  fun N => ∃ t : T, Nonempty ((N : QuasicoherentModule B S hS G) ≅ F t)

/-- The full subcategory of the subobjects of `M` that are isomorphic to a member of the
family `F`. -/
abbrev IsomorphicGeneratorSubobject (T : Type v) (F : T → QuasicoherentModule B S hS G)
    (M : QuasicoherentModule B S hS G) :=
  (isomorphicGeneratorSubobjectProperty T F M).FullSubcategory

/-- The diagram of those subobjects of `M` that are isomorphic to a member of the family `F`,
valued in the quasi-coherent modules on the groupoid. -/
def isomorphicGeneratorSubobjectFunctor (T : Type v) (F : T → QuasicoherentModule B S hS G)
    (M : QuasicoherentModule B S hS G) :
    IsomorphicGeneratorSubobject T F M ⥤ QuasicoherentModule B S hS G :=
  (isomorphicGeneratorSubobjectProperty T F M).ι ⋙ Subobject.underlying

/-- The canonical cocone from the subobjects of `M` isomorphic to a member of the family `F`,
with vertex `M` and the subobject inclusions as its legs. -/
def isomorphicGeneratorSubobjectCocone (T : Type v) (F : T → QuasicoherentModule B S hS G)
    (M : QuasicoherentModule B S hS G) :
    Cocone (isomorphicGeneratorSubobjectFunctor T F M) :=
  Cocone.mk M
    { app := fun N => N.obj.arrow
      naturality := fun {_ _} f => Subobject.underlying_arrow f.hom }

/-- **A class-sized generating family.**  There is a family of quasi-coherent modules on the
groupoid, independent of the module, such that every quasi-coherent module on the groupoid is the
directed colimit of those of its submodules that are isomorphic to a member of the family.

The index type lives in `Type (u + 1)`, the universe of the objects of the category, so the
family may be taken to be every module, and the proof does that: each module is a member of the
family and is the terminal subobject of itself.  The flatness hypotheses are not used.  This is
not Stacks 0780, which asks for a *set*: the set-indexed statement is
`AlgebraicGeometry.Space.QuasicoherentModule.exists_small_generating_family`. -/
theorem exists_generating_family (G : GroupoidInAlgebraicSpaces B S hS A)
    (_hs : IsFlat B S hS G.source.hom) (_ht : IsFlat B S hS G.target.hom) :
    ∃ (T : Type (u + 1)) (F : T → QuasicoherentModule B S hS G),
      ∀ M : QuasicoherentModule B S hS G,
        IsFiltered (IsomorphicGeneratorSubobject T F M) ∧
          Nonempty (IsColimit (isomorphicGeneratorSubobjectCocone T F M)) := by
  refine ⟨QuasicoherentModule B S hS G, fun M => M, ?_⟩
  intro M
  let I := IsomorphicGeneratorSubobject (QuasicoherentModule B S hS G) (fun M => M) M
  let topObj : I := ⟨⊤, ⟨M, ⟨Subobject.underlyingIso (𝟙 M)⟩⟩⟩
  have hterminal : IsTerminal topObj :=
    IsTerminal.ofUniqueHom (fun _ => ⟨homOfLE le_top⟩) (by intros; ext; apply Subsingleton.elim)
  refine ⟨IsFiltered.of_isTerminal I hterminal, ⟨IsColimit.ofIsoColimit
    (colimitOfDiagramTerminal hterminal _)
    (Cocone.ext (Subobject.underlyingIso (𝟙 M)) ?_)⟩⟩
  intro j
  convert (isomorphicGeneratorSubobjectCocone _ _ M).w (hterminal.from j) using 1
  simp [topObj, coconeOfDiagramTerminal, isomorphicGeneratorSubobjectCocone,
    Subobject.underlyingIso_top_hom]

end AlgebraicGeometry.Space.QuasicoherentModule

end
