module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentedPresheaf

/-!
# An algebraic space over `S` read over the integers

Let `S` be a scheme of a big fppf site `B` which also contains `Spec ℤ`, and let `g : S ⟶ Spec ℤ`
be the unique morphism. The forward functor of Stacks 04SG,
`AlgebraicGeometry.spacesOverSmallerBaseFunctor`, reads an algebraic space `X` over `S` as an
algebraic space over `Spec ℤ` together with a morphism to `S`. This file records what is needed
to turn `X` into a family of curves over `S` in the sense of Stacks 0D4Z, whose base is a scheme
over `Spec ℤ`:

* properness, flatness and finite presentation of `X ⟶ S` are those of the morphism to `S`
  read over `Spec ℤ` (Stacks 03ZM, 03MJ, 03XP);
* if `X` read over `Spec ℤ` is a scheme, then `X` is a scheme over `S`, i.e. it is representable
  on the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.integerBaseMap`: the morphism `S ⟶ Spec ℤ` of the site.
* `AlgebraicGeometry.spaceOverIntegers`: `X` read over `Spec ℤ`, with its morphism to `S`.

## Main results

* `AlgebraicGeometry.Space.toYonedaId_eq_terminal_from_comp`: the structural morphism to the
  representable presheaf of `S ⟶ S` is the structural morphism to the terminal presheaf, followed
  by the identification of the two.
* `AlgebraicGeometry.isProper_spaceOverIntegers_hom` and its companions for flatness and finite
  presentation.
* `AlgebraicGeometry.nonempty_iso_yoneda_of_spaceOverIntegers_iso`: if `X` read over `Spec ℤ` is
  isomorphic to a scheme then `X` is isomorphic to a scheme over `S`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains integerBase)

/-- The structural morphism `toYonedaId` of a presheaf on the big fppf site of `S` to the
representable presheaf of `𝟙 S` is its morphism to the terminal presheaf followed by the
identification of the terminal presheaf with that representable presheaf. -/
theorem Space.toYonedaId_eq_terminal_from_comp (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Space.toYonedaId B S hS F = terminal.from F ≫
      (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
        terminalIsTerminal).inv :=
  ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).hom_ext _ _

variable (B) in
/-- The unique morphism `S ⟶ Spec ℤ` of the big fppf site. -/
def integerBaseMap : B.obj hS ⟶ B.obj hZ :=
  B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)

/-- An algebraic space over `S` read over `Spec ℤ` by the forward functor of Stacks 04SG: an
algebraic space over `Spec ℤ` together with a morphism to the representable algebraic space of
`S`. -/
abbrev spaceOverIntegers (F : AlgebraicSpaces B S hS) :
    SpacesOverSmallerBase B S integerBase hS hZ (integerBaseMap B hS hZ) :=
  (spacesOverSmallerBaseFunctor B S integerBase hS hZ (integerBaseMap B hS hZ)).obj F

/-- Properness of an algebraic space over `S` is properness of its morphism to `S` read over
`Spec ℤ`. -/
theorem isProper_spaceOverIntegers_hom_iff (F : AlgebraicSpaces B S hS) :
    Space.IsProper B integerBase hZ (spaceOverIntegers hS hZ F).1.hom ↔
      Space.IsProper B S hS (terminal.from F.1) := by
  rw [Space.isProper_spacesOverSmallerBaseFunctor_obj_hom_iff,
    Space.toYonedaId_eq_terminal_from_comp, Space.isProper_comp_isIso_iff]

/-- An every-étale-chart condition on an algebraic space over `S` is the same condition on its
morphism to `S` read over `Spec ℤ`; in particular flatness. -/
theorem holdsOnEveryEtaleChart_spaceOverIntegers_hom_iff (P : MorphismProperty Scheme.{u})
    (F : AlgebraicSpaces B S hS) :
    Space.HoldsOnEveryEtaleChart B integerBase hZ P (spaceOverIntegers hS hZ F).1.hom ↔
      Space.HoldsOnEveryEtaleChart B S hS P (terminal.from F.1) := by
  rw [Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff,
    Space.toYonedaId_eq_terminal_from_comp, Space.holdsOnEveryEtaleChart_comp_iso_iff]

/-- Finite presentation of an algebraic space over `S` is finite presentation of its morphism to
`S` read over `Spec ℤ`. -/
theorem isFinitePresentation_spaceOverIntegers_hom_iff (F : AlgebraicSpaces B S hS) :
    Space.IsFinitePresentation B integerBase hZ (spaceOverIntegers hS hZ F).1.hom ↔
      Space.IsFinitePresentation B S hS (terminal.from F.1) := by
  rw [Space.isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff,
    Space.toYonedaId_eq_terminal_from_comp]
  refine and_congr (Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS _ _ _)
    (and_congr (Space.isQuasiCompact_comp_isIso_iff B S hS _ _)
      (Space.isQuasiSeparated_comp_isIso_iff B S hS _ _))

/-- **Non-representability passes down from `Spec ℤ` to `S`.** If an algebraic space `F` over `S`,
read over `Spec ℤ`, is isomorphic to the representable presheaf of a scheme `V` over `Spec ℤ`, then
`F` is isomorphic to the representable presheaf of a scheme over `S`. -/
theorem nonempty_iso_yoneda_of_spaceOverIntegers_iso (F : AlgebraicSpaces B S hS)
    {V : BigFppfOver B integerBase hZ}
    (e : (spaceOverIntegers hS hZ F).1.left ≅ yoneda.obj V) :
    ∃ U : BigFppfOver B S hS, Nonempty (F.1 ≅ yoneda.obj U) :=
  ⟨_, OverShriek.nonempty_iso_yoneda_of_relocalize (integerBaseMap B hS hZ) F.1
    (((spacesOverSmallerBaseFunctorForgetIso B S integerBase hS hZ
      (integerBaseMap B hS hZ)).app F).symm ≪≫ e)⟩

end AlgebraicGeometry

end
