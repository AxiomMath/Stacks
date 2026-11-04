module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Localization.SimultaneousTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.OverPullbackLimits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Elementary closure properties of finite locally constant sheaves of sets

Let `J` be a Grothendieck topology on `C`. The property
`Stacks.ConstantSheaf.IsFiniteLocallyConstant` of sheaves in `Sheaf J (Type w)` is stable under
isomorphism, and a terminal sheaf is finite locally constant, with constant value `PUnit`; that
is, the property is closed under limits of the empty shape.

## Main results

* `Stacks.ConstantSheaf.isTerminal_constantSheaf_punit`: the constant sheaf on `PUnit` is a
  terminal sheaf.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isTerminal`: a terminal sheaf of sets is
  finite locally constant.
* `Stacks.ConstantSheaf.isClosedUnderIsomorphisms_isFiniteLocallyConstant`: finite local
  constancy is stable under isomorphism.
* `Stacks.ConstantSheaf.isClosedUnderLimitsOfShape_pempty_isFiniteLocallyConstant`: finite
  locally constant sheaves are closed under limits of the empty shape.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantSheaf

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Terminal

variable [HasWeakSheafify J (Type w)]

/-- The constant sheaf on `PUnit` is a terminal sheaf of sets. -/
def isTerminal_constantSheaf_punit :
    IsTerminal ((constantSheaf J (Type w)).obj PUnit) :=
  IsTerminal.ofIso (Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{w})
    ((fullyFaithfulSheafToPresheaf J (Type w)).preimageIso
      (isoSheafify J (Sheaf.terminal J Types.isTerminalPUnit.{w}).property))

end Terminal

variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- A terminal sheaf of sets is finite locally constant, with constant value `PUnit`. -/
lemma isFiniteLocallyConstant_of_isTerminal (F : Sheaf J (Type w)) (hF : IsTerminal F) :
    IsFiniteLocallyConstant J F where
  exists_finite_cover U :=
    ⟨PUnit.{max u v + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, sieve_ofArrows_id_mem J U,
      fun _ ↦ ⟨PUnit.{w + 1}, inferInstance,
        ⟨IsTerminal.uniqueUpToIso (isTerminal_constantSheaf_punit (J.over U))
          (hF.isTerminalObj (J.overPullback (Type w) U) F)⟩⟩⟩

/-- Finite local constancy of a sheaf of sets is stable under isomorphism. -/
instance isClosedUnderIsomorphisms_isFiniteLocallyConstant :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : Sheaf J (Type w) => IsFiniteLocallyConstant J F) where
  of_iso e hF := isFiniteLocallyConstant_congr J e (hF := hF)

/-- Finite locally constant sheaves of sets are closed under limits of the empty shape, i.e.
contain the terminal sheaf. -/
instance isClosedUnderLimitsOfShape_pempty_isFiniteLocallyConstant :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun F : Sheaf J (Type w) => IsFiniteLocallyConstant J F) (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact isFiniteLocallyConstant_of_isTerminal J X
      ((IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit : IsTerminal X)

end Stacks.ConstantSheaf

end
