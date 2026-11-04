module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExteriorAlgebra

/-!
# The exterior algebra of a sheaf of modules commutes with restriction to an open subspace

Let `X` be a ringed space, `U ⊆ X` an open, `M` a sheaf of `𝒪_X`-modules and `A` an exterior
algebra of `M` with degree-one generator `gen`. This file proves that the restriction of `A` to
the open subspace `U` is an exterior algebra of the restriction of `M`, **with its algebra
structure**: the comparison with any exterior algebra of `M|_U` on `U` carries the generators,
the multiplications and the units. Here the restriction of a sheaf of modules to `U` is the
restriction to the slice site `(Opens X).over U` followed by the pushforward along the site
functor `Stacks.SheafOfModules.openSubspaceSiteFunctor`.

## Main results

* `SheafOfModules.isExteriorAlgebra_openSubspaceAlg`: **the restriction of an exterior algebra
  of `M` to an open subspace is an exterior algebra of the restriction of `M`**, on the
  restricted generator.
* `SheafOfModules.exteriorRestrictOpenSubspaceIso`: the resulting degreewise comparison
  `(⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)` with an arbitrary exterior algebra of `M|_U` on `U`, and
  `exteriorRestrictOpenSubspaceIso_generator`, `_mul`, `_one`: it carries the generator, the
  multiplication and the unit.
* `SheafOfModules.exteriorPowerRestrictOpenSubspaceIso`: the same comparison at the canonical
  bundles `SheafOfModules.ringedSpaceAlgebras` of `X` and of the open subspace.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
  AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
  Stacks.SheafOfModules.PushforwardSheafification

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe u

namespace SheafOfModules

open _root_.SheafOfModules.GradedAlgebra Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing X))
  (A : GradedAlgebra.{u, u} (structureSheafRing X)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen) (U : Opens X.carrier)

/-- The graded algebra `A` restricted to the open subspace `U`: the restriction to the slice
site over `U`, pushed forward along the site functor of
`TopologicalSpace.Opens.overEquivalence`. -/
abbrev openSubspaceAlg :=
  GradedAlgebra.pushforwardAlg.{u, u} (Jt := (Opens.grothendieckTopology X.carrier).over U)
    (R := (structureSheafRing X).over U) (Opens.grothendieckTopology ↥U)
    (openSubspaceSiteFunctor U) (A.over U)

/-- The degree-one generator of `A` restricted to the open subspace `U`. -/
abbrev openSubspaceGen :=
  pushforwardGen.{u} (Jt := (Opens.grothendieckTopology X.carrier).over U)
    (Osharp := X.sheaf.over U) (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
    (M.over U) (A.over U) (overGen M A gen U)

/-- The homogeneous pieces of the restriction of `A` to the open subspace are the restrictions
of those of `A`, in the pushforward spelling. -/
theorem openSubspaceAlg_piece (n : ℤ) :
    (openSubspaceAlg A U).piece n =
      (sheafPushforwardFunctor.{u} (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        ((structureSheafRing X).over U)).obj ((A.piece n).over U) :=
  rfl

/-- The homogeneous pieces of the restriction of `A` to the open subspace, in the spelling of
Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver`. -/
theorem openSubspaceAlg_piece_eq_openSubspaceEquiv (n : ℤ) :
    (openSubspaceAlg A U).piece n =
      (openSubspaceEquiv U).functor.obj ((A.piece n).over U) :=
  (openSubspaceAlg_piece A U n).trans
    (congrArg (fun F => Functor.obj F ((A.piece n).over U)) (openSubspaceEquiv_functor U).symm)

include hA in
/-- **The restriction of an exterior algebra of `M` to an open subspace is an exterior algebra
of the restriction of `M`**, on the restricted generator. -/
theorem isExteriorAlgebra_openSubspaceAlg :
    GradedAlgebra.IsExteriorAlgebra (openSubspaceAlg A U) (openSubspaceGen M A gen U) :=
  isExteriorAlgebra_pushforward.{u} (Jt := (Opens.grothendieckTopology X.carrier).over U)
    (Osharp := X.sheaf.over U) (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
    (M.over U) (A.over U) (overGen M A gen U) (isExteriorAlgebra_over M A gen hA U)

variable (B : GradedAlgebra.{u, u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
    (openSubspaceSiteFunctor U) ((structureSheafRing X).over U)))
  (gen' : (sheafPushforwardFunctor.{u} (Opens.grothendieckTopology ↥U)
    (openSubspaceSiteFunctor U) ((structureSheafRing X).over U)).obj (M.over U) ⟶ B.piece 1)
  (hB : GradedAlgebra.IsExteriorAlgebra B gen')

include hA hB

/-- **`(⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)` on an open subspace of a ringed space**, for an arbitrary exterior
algebra `A` of `M` on `X` and an arbitrary exterior algebra `B` of `M|_U` on `U`. -/
def exteriorRestrictOpenSubspaceIso (n : ℤ) :
    (openSubspaceAlg A U).piece n ≅ B.piece n :=
  GradedAlgebra.IsUniversal.pieceIso
    (isExteriorAlgebra_openSubspaceAlg M A gen hA U).isUniversal hB.isUniversal n

/-- The comparison carries the restricted generator to the generator of `B`. -/
theorem exteriorRestrictOpenSubspaceIso_generator :
    openSubspaceGen M A gen U ≫
        (exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB 1).hom = gen' :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison is multiplicative on homogeneous local sections: the multiplication of `A`
read over the image open of `V` is carried to the multiplication of `B` over `V`. -/
theorem exteriorRestrictOpenSubspaceIso_mul (i j : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (x : ((openSubspaceAlg A U).piece i).val.obj V)
    (y : ((openSubspaceAlg A U).piece j).val.obj V) :
    (exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB (i + j)).hom.val.app V
        (((openSubspaceAlg A U).mul i j).app V x y) =
      (B.mul i j).app V
        ((exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB i).hom.val.app V x)
        ((exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB j).hom.val.app V y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j V x y

/-- The comparison carries the unit to the unit. -/
theorem exteriorRestrictOpenSubspaceIso_one (V : (Opens ↥U)ᵒᵖ) :
    (exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB 0).hom.val.app V
        ((openSubspaceAlg A U).one.eval V) = B.one.eval V :=
  GradedAlgebra.IsUniversal.pieceIso_one _ _ V

/-! ### The comparison at the canonical bundles of algebras -/

section Canonical

variable (F : SheafOfModules.{u} (structureSheafRing X))

/-- **`(⋀ⁿF)|_U ≅ ⋀ⁿ(F|_U)` at the canonical bundles of algebras**: on the left the exterior
power of `SheafOfModules.ringedSpaceAlgebras` of `X`, restricted to the open subspace `U`; on
the right the exterior power of `SheafOfModules.ringedSpaceAlgebras` of `U` itself. -/
def exteriorPowerRestrictOpenSubspaceIso (n : ℤ) :
    (openSubspaceAlg (ringedSpaceAlgebras X F).exterior U).piece n ≅
      (openSubspaceAlgebras U F).exterior.piece n :=
  exteriorRestrictOpenSubspaceIso F (ringedSpaceAlgebras X F).exterior
    (ringedSpaceAlgebras X F).exteriorGenerator
    (ringedSpaceAlgebras X F).exterior_isExteriorAlgebra U
    (openSubspaceAlgebras U F).exterior (openSubspaceAlgebras U F).exteriorGenerator
    (openSubspaceAlgebras U F).exterior_isExteriorAlgebra n

end Canonical

end SheafOfModules

end
