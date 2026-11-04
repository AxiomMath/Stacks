module

public import StacksFrontier.Deformation.RingThickening.CotangentObstructionSquare
public import StacksFrontier.Deformation.SquareZero.SolutionsFibre
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to a square-zero extension problem lies in `Ext²_B(L_{B/A}, N)`

Let `A' → A` be a surjection of rings with square-zero kernel `I`, let `A → B` be a ring map,
let `N` be a `B`-module and `c : I → N` an `A`-linear map. This file constructs a class
`ξ ∈ Ext²_B(L_{B/A}, N)` which vanishes if and only if the extension problem has a solution:
part (1) of Tag 08SP.

The class is the image of the class of the extension `A'` of `A` by `I`, pushed along `c` and
read in `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N)`, under the connecting map of the fundamental triangle
`L_{A/A'} ⊗^𝐋_A B → L_{B/A'} → L_{B/A} → (L_{A/A'} ⊗^𝐋_A B)[1]` of Tag 08QX. By the long exact
sequence of `Ext_B(-, N)` it vanishes exactly when that class comes from `Ext¹_B(L_{B/A'}, N)`;
after `NL = τ_{≥ -1} L` (Tag 08RB) and the compatibility `baseClass_towerMap`, this says that
the class lies in the image of `Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)`, which by
Lemma 0GPX is the existence of a solution.

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentObstructionClass`: the class `ξ`.

## Main results

* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentObstructionClass_eq_zero_iff`:
  **Tag 08SP**, part (1).

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 0GPX](https://stacks.math.columbia.edu/tag/0GPX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Deformation.SquareZeroExtensionProblem

attribute [local instance high] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u, u, u, u})

/-- The first vertex `L_{A/A'} ⊗^𝐋_A B` of the lifted fundamental triangle is the lifted
termwise base change of `L_{A/A'}`, the cotangent complex being a complex of projectives. -/
noncomputable def liftedFundamentalTriangleObj₁Iso :
    S.liftedFundamentalTriangle.obj₁ ≅
      DerivedCategory.Q.obj ((S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A))) :=
  S.liftDerived.mapIso (CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso S.A'
      (CommAlgCat.of S.A' S.A) S.B) ≪≫
    S.liftB.mapDerivedCategoryFactors.app _

/-- The second vertex `L_{B/A'}` of the lifted fundamental triangle is the lifted cotangent
complex. -/
noncomputable def liftedFundamentalTriangleObj₂Iso :
    S.liftedFundamentalTriangle.obj₂ ≅
      DerivedCategory.Q.obj ((S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.B))) :=
  S.liftB.mapDerivedCategoryFactors.app _

/-- The first morphism of the lifted fundamental triangle is the lifted map of Tag 08PN. -/
theorem liftedFundamentalTriangle_mor₁_comp_obj₂Iso :
    S.liftedFundamentalTriangle.mor₁ ≫ S.liftedFundamentalTriangleObj₂Iso.hom =
      S.liftedFundamentalTriangleObj₁Iso.hom ≫ DerivedCategory.Q.map S.towerComplexMap := by
  change S.liftDerived.map ((CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso S.A'
      (CommAlgCat.of S.A' S.A) S.B).hom ≫ DerivedCategory.Q.map
        (CommAlgCat.cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A')
          (B := CommAlgCat.of S.A' S.A) (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom)) ≫
      S.liftB.mapDerivedCategoryFactors.hom.app _ =
    (S.liftDerived.map (CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso S.A'
      (CommAlgCat.of S.A' S.A) S.B).hom ≫ S.liftB.mapDerivedCategoryFactors.hom.app _) ≫
      DerivedCategory.Q.map S.towerComplexMap
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  exact _ ≫= S.liftB.mapDerivedCategoryFactors_hom_naturality
    (CommAlgCat.cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A')
      (B := CommAlgCat.of S.A' S.A) (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom)

/-- The class in `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N)` of the extension `A'` of `A` by `I`, pushed along
`c : I → N`. -/
noncomputable def pushedBaseClass :
    S.liftedFundamentalTriangle.obj₁ ⟶ (liftedKernelSingle.{u, u, u, u} S)⟦(1 : ℤ)⟧ :=
  S.liftedFundamentalTriangleObj₁Iso.hom ≫
    S.baseClass (naiveCotangentExtOneMap S.A' S.A S.c (baseExtClass S))

/-- **The obstruction class `ξ ∈ Ext²_B(L_{B/A}, N)`** of the square-zero extension problem: the
image of `pushedBaseClass` under the connecting map of the fundamental triangle of
`A' → A → B`. -/
noncomputable def cotangentObstructionClass : cotangentExt.{u, u, u, u} S 2 :=
  S.obstructionOf S.pushedBaseClass

/-- A solution exists exactly when the pushed class of `A'` lies in the image of
`Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` (Lemma 0GPX). -/
theorem nonempty_compatibleExtension_iff :
    Nonempty (S.CompatibleExtension.{u}) ↔
      ∃ ζ : naiveCotangentExtOne S.A' S.B S.N, naiveCotangentExtOneTowerMap S.A' S.A S.B ζ =
        naiveCotangentExtOneMap S.A' S.A S.c (baseExtClass S) :=
  (nonempty_quotient_iff (CompatibleExtension.isomorphicSetoid S)).symm.trans
    ((solutionsEquivFibre S).nonempty_congr.trans nonempty_subtype)

/-- **Stacks 08SP**, part (1). The class `ξ ∈ Ext²_B(L_{B/A}, N)` vanishes if and only if the
square-zero extension problem has a solution. -/
@[stacks 08SP "(1): there is a class in Ext²_B(L_{B/A}, N) whose vanishing is necessary and \
  sufficient for the existence of a solution"]
theorem cotangentObstructionClass_eq_zero_iff :
    S.cotangentObstructionClass = 0 ↔ Nonempty (S.CompatibleExtension.{u}) := by
  rw [nonempty_compatibleExtension_iff, cotangentObstructionClass, obstructionOf_eq_zero_iff]
  constructor
  · rintro ⟨ζ, hζ⟩
    obtain ⟨y, hy⟩ := S.towerClass.surjective (S.liftedFundamentalTriangleObj₂Iso.inv ≫ ζ)
    refine ⟨y, S.baseClass.injective ?_⟩
    rw [S.baseClass_towerMap, hy, ← cancel_epi S.liftedFundamentalTriangleObj₁Iso.hom,
      ← Category.assoc, ← S.liftedFundamentalTriangle_mor₁_comp_obj₂Iso, Category.assoc,
      Iso.hom_inv_id_assoc, ← hζ]
    rfl
  · rintro ⟨ζ, hζ⟩
    refine ⟨S.liftedFundamentalTriangleObj₂Iso.hom ≫ S.towerClass ζ, ?_⟩
    rw [← Category.assoc, S.liftedFundamentalTriangle_mor₁_comp_obj₂Iso, Category.assoc,
      ← S.baseClass_towerMap, hζ]
    rfl

end Stacks.Deformation.SquareZeroExtensionProblem

end
