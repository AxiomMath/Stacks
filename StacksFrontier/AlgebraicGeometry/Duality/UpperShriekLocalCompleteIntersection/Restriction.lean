module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.FundamentalClassConstantRank
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleNaturalIso
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothAtPoint

/-!
# The cohomology sheaves of `f^!𝒪_Y` restricted to an open

For `j : U ⟶ X` a morphism of `FTS S` whose underlying morphism is an open immersion and `c` a
compactification of `f : X ⟶ Y`, the cohomology sheaves of `(j ≫ f)^!𝒪_Y`, computed at the
restricted compactification, are the restrictions of those of `f^!𝒪_Y`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality.ClosedOpenProperFactorization

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S} (j : U ⟶ X) [IsOpenImmersion j.left]
  (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))

/-- **`H^k((j ≫ f)^!𝒪_Y) ≅ H^k(f^!𝒪_Y)|_U`** for an open immersion `j`, with `(j ≫ f)^!` computed
at the compactification restricted from one of `f`. -/
def upperShriekHomologyRestrictIso (k : ℤ) :
    upperShriekHomology (j ≫ f) (c.precompOpen j.left) k ≅
      (Scheme.Modules.restrictFunctor j.left).obj (upperShriekHomology f c k) :=
  (DerivedCategory.homologyFunctor U.left.Modules k).mapIso
      ((ObjectProperty.ι _).mapIso ((upperShriekPrecompOpenIso j f c).app
        (DerivedPushforward.derivedStructureSheaf Y.left)) ≪≫
        ((derivedRestrictIsoDerivedPullback j.left).app _).symm) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor j.left) k).app _

/-- The stalk at `x` of `H^k((j ≫ f)^!𝒪_Y)` is the stalk at `j x` of `H^k(f^!𝒪_Y)`. -/
theorem nontrivial_stalk_upperShriekHomology_comp_iff (k : ℤ) (x : U.left) :
    Nontrivial ↑((upperShriekHomology (j ≫ f) (c.precompOpen j.left) k).presheaf.stalk x) ↔
      Nontrivial ↑((upperShriekHomology f c k).presheaf.stalk (j.left x)) :=
  ((stalkAddEquivOfIso (upperShriekHomologyRestrictIso j f c k) x).trans
    ((Scheme.Modules.restrictStalkNatIso j.left x).app
      (upperShriekHomology f c k)).addCommGroupIsoToAddEquiv).toEquiv.nontrivial_congr

/-- **`(∧^n Ω_{X/Y})|_U ≅ ∧^n Ω_{U/Y}`** for an open immersion `j : U ⟶ X`. -/
def exteriorPowerRestrictIso (n : ℤ) :
    (Scheme.Modules.restrictFunctor j.left).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) n) ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (j ≫ f).left) n :=
  (Scheme.Modules.restrictFunctorIsoPullback j.left).app _ ≪≫
    Scheme.Modules.exteriorPowerPullbackIso j.left _ n ≪≫
    (Scheme.Modules.exteriorPowerFunctor U.left n).mapIso
      (Scheme.Hom.etaleRelativeDifferentialsIso j.left f.left (j ≫ f).left rfl)

/-- **Transport of the map of [Stacks, Tag 0E9Z] to an open.** A map
`∧^n Ω_{U/Y} ⟶ H^{-n}((j ≫ f)^!𝒪_Y)` whose stalks are isomorphisms exactly at the points where
`j ≫ f` is smooth gives a map between the restrictions to `U` of `∧^n Ω_{X/Y}` and
`H^{-n}(f^!𝒪_Y)` whose stalk at `x` is an isomorphism exactly when `f` is smooth at `j x`. -/
theorem exists_restrict_map_isIso_stalkMap_iff (n : ℤ)
    (φ : Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (j ≫ f).left) n ⟶
      upperShriekHomology (j ≫ f) (c.precompOpen j.left) (-n))
    (hφ : ∀ x : U.left, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology
          ↥U.left.toLocallyRingedSpace.toRingedSpace.carrier)
          U.left.toLocallyRingedSpace.toRingedSpace.sheaf) x φ) ↔
      InfinitesimalLifting.SmoothAt (j ≫ f).left x) :
    ∃ ψ : (Scheme.Modules.restrictFunctor j.left).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) n) ⟶
      (Scheme.Modules.restrictFunctor j.left).obj (upperShriekHomology f c (-n)),
      ∀ x : U.left, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
          (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology
            ↥U.left.toLocallyRingedSpace.toRingedSpace.carrier)
            U.left.toLocallyRingedSpace.toRingedSpace.sheaf) x ψ) ↔
        InfinitesimalLifting.SmoothAt f.left (j.left x) := by
  refine ⟨(exteriorPowerRestrictIso j f n).hom ≫ φ ≫
    (upperShriekHomologyRestrictIso j f c (-n)).hom, fun x => ?_⟩
  let F := Stacks.ConormalSequenceRight.stalkAb U.left x
  refine (isIso_stalkMap_iff_isIso_stalkAb x _).trans (Iff.trans ?_
    (((isIso_stalkMap_iff_isIso_stalkAb x φ).symm.trans (hφ x)).trans
      (InfinitesimalLifting.smoothAt_comp_iff_of_etale j.left f.left x)))
  show IsIso (F.map _) ↔ IsIso (F.map φ)
  rw [F.map_comp, F.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

end Stacks.Duality.ClosedOpenProperFactorization
