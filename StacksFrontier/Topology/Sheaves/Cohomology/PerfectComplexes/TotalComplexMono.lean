module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexLocalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# The total tensor complex preserves degreewise monomorphisms against flat terms

Let `j : 𝒦 ⟶ ℳ` be a map of cochain complexes of `O`-modules which is a monomorphism in every
degree, and let `𝒩` be a complex all of whose terms are flat. Then `Tot(j ⊗ 𝒩)` is a
monomorphism in every degree.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.mono_whiskerRight_of_isFlat`: tensoring a monomorphism of
  `O`-modules with a flat `O`-module gives a monomorphism.
* `Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f`: the statement above, over the site
  of opens of a space.
* `Stacks.Cohomology.LeftDualPerfect.mono_whiskerRight_of_isFlat_general` and
  `Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general`: the same two over an
  arbitrary small site.

## Implementation notes

The total tensor complex is spelled `HomologicalComplex.mapBifunctorMap`. The other spelling,
`AlgebraicGeometry.RingedSite.tensorTotal`, totalises the presheaf-level tensor products and
sheafifies afterwards; the two are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.LeftDualPerfect

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

/-- Over an arbitrary small site, tensoring a monomorphism with a flat module is a monomorphism. -/
private theorem mono_whiskerRight_of_isFlat_aux {C : Type u} [SmallCategory.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M M' : Mod R} (φ : M ⟶ M') [Mono φ] (F : Mod R)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    Mono (((curriedTensor (Mod R)).map φ).app F) := by
  have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj F) :=
    ((Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R F).1 hF).1
  exact (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj F |>.map_mono φ

/-- Tensoring a monomorphism of `O`-modules with a flat `O`-module gives a monomorphism. -/
theorem mono_whiskerRight_of_isFlat {M M' : Mod R} (φ : M ⟶ M') [Mono φ] (F : Mod R)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    Mono (((curriedTensor (Mod R)).map φ).app F) := by
  exact mono_whiskerRight_of_isFlat_aux φ F hF

/-- The category of `O`-modules has finite biproducts. -/
instance hasFiniteBiproducts_mod : HasFiniteBiproducts (Mod R) := Abelian.hasFiniteBiproducts

/-- The category of `O`-modules satisfies AB4 for coproducts indexed by `Type u`. -/
instance ab4Mod : AB4OfSize.{u} (Mod R) := AB4.of_AB5 (Mod R)

/-- The category of `O`-modules satisfies AB4 for coproducts indexed by `Type`. -/
instance ab4Mod₀ : AB4OfSize.{0} (Mod R) := AB4OfSize_shrink.{0, u} (Mod R)

/-- In the category of `O`-modules, a coproduct of monomorphisms is a monomorphism. -/
instance isStableUnderCoproductsOfShape_monomorphisms (J : Type) :
    (MorphismProperty.monomorphisms (Mod R)).IsStableUnderColimitsOfShape (Discrete J) := by
  have : HasExactColimitsOfShape (Discrete J) (Mod R) := AB4OfSize.ofShape J
  have : PreservesFiniteLimits (colim : (Discrete J ⥤ Mod R) ⥤ Mod R) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  infer_instance

/-- Over an arbitrary small site, the total tensor complex of a degreewise monomorphism with a
complex of flat modules is a degreewise monomorphism. -/
private theorem mono_mapBifunctorMap_f_aux {C : Type u} [SmallCategory.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasFiniteBiproducts (Mod R)]
    [∀ K : Type, (MorphismProperty.monomorphisms (Mod R)).IsStableUnderColimitsOfShape
      (Discrete K)]
    {K A B : CochainComplex (Mod R) ℤ} (j : K ⟶ A) [∀ p, Mono (j.f p)]
    (hB : ∀ q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (B.X q)) (n : ℤ) :
    Mono ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R))
      (ComplexShape.up ℤ)).f n) := by
  have hc₁ := HomologicalComplex.isColimitCofanιMapBifunctor K B (curriedTensor (Mod R)) n
  have hc₂ := HomologicalComplex.isColimitCofanιMapBifunctor A B (curriedTensor (Mod R)) n
  refine MorphismProperty.colimitsOfShape_le (W := MorphismProperty.monomorphisms (Mod R))
    (J := Discrete {ij : ℤ × ℤ // ij.1 + ij.2 = n}) _
    (MorphismProperty.colimitsOfShape.mk' _ _ _ _ hc₁ hc₂
      (Discrete.natTrans fun ij => ((curriedTensor (Mod R)).map (j.f ij.as.1.1)).app
        (B.X ij.as.1.2)) (fun ij => mono_whiskerRight_of_isFlat_aux _ _ (hB _)) _ fun ij => ?_)
  have e := HomologicalComplex.ι_mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R))
    (ComplexShape.up ℤ) ij.as.1.1 ij.as.1.2 n (by simpa using ij.as.2)
  rwa [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp] at e

/-- **The total tensor complex preserves monomorphisms against flat terms.** If `j : K ⟶ A` is
injective in every degree and every term of `B` is flat, then `Tot(j ⊗ B)` is injective in every
degree. -/
theorem mono_mapBifunctorMap_f {K A B : CochainComplex (Mod R) ℤ} (j : K ⟶ A)
    [∀ p, Mono (j.f p)]
    (hB : ∀ q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (B.X q)) (n : ℤ) :
    Mono ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R))
      (ComplexShape.up ℤ)).f n) := by
  exact mono_mapBifunctorMap_f_aux j hB n

section AnySite

/-! ### The same two statements over an arbitrary small site -/

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Over an arbitrary small site, tensoring a monomorphism of `O`-modules with a flat `O`-module
gives a monomorphism. -/
theorem mono_whiskerRight_of_isFlat_general {M M' : Mod R} (φ : M ⟶ M') [Mono φ] (F : Mod R)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    Mono (((curriedTensor (Mod R)).map φ).app F) := by
  exact mono_whiskerRight_of_isFlat_aux φ F hF

/-- The category of `O`-modules on a small site has finite biproducts. -/
local instance hasFiniteBiproducts_mod_general : HasFiniteBiproducts (Mod R) :=
  Abelian.hasFiniteBiproducts

/-- The category of `O`-modules on a small site satisfies AB4 for coproducts indexed by
`Type u`. -/
local instance ab4Mod_general : AB4OfSize.{u} (Mod R) := AB4.of_AB5 (Mod R)

/-- The category of `O`-modules on a small site satisfies AB4 for coproducts indexed by `Type`. -/
local instance ab4Mod₀_general : AB4OfSize.{0} (Mod R) := AB4OfSize_shrink.{0, u} (Mod R)

/-- In the category of `O`-modules on a small site, a coproduct of monomorphisms is a
monomorphism. -/
local instance isStableUnderCoproductsOfShape_monomorphisms_general (K : Type) :
    (MorphismProperty.monomorphisms (Mod R)).IsStableUnderColimitsOfShape (Discrete K) := by
  have : HasExactColimitsOfShape (Discrete K) (Mod R) := AB4OfSize.ofShape K
  have : PreservesFiniteLimits (colim : (Discrete K ⥤ Mod R) ⥤ Mod R) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  infer_instance

/-- **The total tensor complex preserves monomorphisms against flat terms**, over an arbitrary
small site. If `j : K ⟶ A` is injective in every degree and every term of `B` is flat, then
`Tot(j ⊗ B)` is injective in every degree. -/
theorem mono_mapBifunctorMap_f_general {K A B : CochainComplex (Mod R) ℤ} (j : K ⟶ A)
    [∀ p, Mono (j.f p)]
    (hB : ∀ q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (B.X q)) (n : ℤ) :
    Mono ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R))
      (ComplexShape.up ℤ)).f n) := by
  exact mono_mapBifunctorMap_f_aux j hB n

end AnySite

end Stacks.Cohomology.LeftDualPerfect
