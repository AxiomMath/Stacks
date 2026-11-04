module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionAnnihilatedModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence

/-!
# Proper pushforward of the cycle of a coherent module and of a closed subspace

In Situation 0EDT let `f : X ⟶ Y` be a proper morphism of good algebraic spaces over the base.
**Stacks 0EP3** says:

1. for a closed subspace `Z ⊂ X` with `dim_δ(Z) ≤ k`, `f_*[Z]_k = [f_*𝒪_Z]_k`;
2. for a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`, `f_*[F]_k = [f_*F]_k`.

Both are proved here with exactly these hypotheses.

The cycle `[G]_k` of an `𝒪_Y`-module `G` (Stacks 0EEB) is the formal sum, over the integral
closed subspaces `W ⊂ Y` of δ-dimension `k`, of the length of `G` at the generic point of `W`;
its coefficient family is `AlgebraicGeometry.Space.cycleCoeffOfModule`. The source notes that
`[f_*F]_k` makes sense because `f_*F` is coherent (Stacks 08AR); here the statement is proved
without that input, by computing the coefficients directly, and the equality itself shows that
the coefficient family of `f_*F` is a `k`-cycle. So the right hand sides are the elements of
`Z_k(Y)` with the coefficient families of `f_*F` and of `f_*𝒪_Z`.

## Main results

* `AlgebraicGeometry.Space.properCyclePushforwardCoeff_cycleCoeffOfModule_eq`: the coefficient
  family of `f_*[F]_k` is that of `[f_*F]_k`.
* `AlgebraicGeometry.Space.properCyclePushforward_associatedCycle_eq`: **Stacks 0EP3, part (2).**
* `AlgebraicGeometry.Space.properCyclePushforward_closedSubspaceCycle_eq`: **Stacks 0EP3,
  part (1).**

## Implementation notes

At an integral closed subspace `W ⊂ Y` of δ-dimension `k` with generic point `η`, both sides are
`∑_{x ∈ Supp(F), f(x) = η} length_x(F) · [κ(x) : κ(η)]`: the left one by the definition of the
pushforward of Stacks 0EP1
(`AlgebraicGeometry.Space.finsum_cycleCoeffOfModule_mul_properCycleMult_eq_finsum_fibre`), the
right one by the computation of the length of the direct image
(`AlgebraicGeometry.Space.geometricLength_directImageModule_toNat_eq_finsum`), which follows the
source's proof: reduction to the scheme-theoretic support, where the morphism has finite fibre
over `η`, and then to a finite morphism of affine schemes over an elementary étale
neighbourhood of `η`. At an integral closed subspace of δ-dimension other than `k` both sides
vanish.

For part (1), `f_*𝒪_Z` is the direct image of the structure sheaf of `Z` along the composite
`Z → X → Y`, as in the source. The proof is the source's: `[Z]_k = [i_*𝒪_Z]_k` by Stacks 0EED,
and `f_*(i_*𝒪_Z) = (f ∘ i)_*𝒪_Z`.

The cycle of a module is read at chosen geometric representatives `γ` of the points; by
Stacks 0EE1 the lengths do not depend on that choice.

## References

* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **The coefficients of `f_*[F]_k` are those of `[f_*F]_k`.** For a proper morphism `f` of good
algebraic spaces over the base and a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`, the
pushforward of Stacks 0EP1 of the coefficient family of `[F]_k` is the coefficient family of
`[f_*F]_k`. -/
theorem properCyclePushforwardCoeff_cycleCoeffOfModule_eq {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    properCyclePushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) =
      cycleCoeffOfModule D sY hY (directImageModule D hX.1 hY.1 f F) k γY := by
  funext W
  by_cases hW : deltaDimension D sY W = k
  · rw [properCyclePushforwardCoeff,
      finsum_cycleCoeffOfModule_mul_properCycleMult_eq_finsum_fibre D sX hX sY hY hfB F k hdimF
        γX hγX W hW,
      cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hW, moduleMultiplicity,
      geometricLength_directImageModule_toNat_eq_finsum D sX hX sY hY hfB hproper F k hdimF γX
        hγX W hW _ (hγY _),
      Nat.cast_finsum_mem (finite_moduleSupport_fibre D sX hX sY hY hfB hproper.2.1.2 F k hdimF
        γX hγX W hW)]
    push_cast
    rfl
  · rw [properPushforwardCoeff_cycleCoeffOfModule_eq_zero D sX hX sY hY f F k γX hW,
      cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right hW]

/-- The coefficient family of the direct image `f_*F` along a proper morphism, of a coherent
module with `dim_δ(Supp(F)) ≤ k`, is a `k`-cycle: it is the pushforward of the `k`-cycle
`[F]_k`. -/
theorem cycleCoeffOfModule_directImageModule_mem_cyclesOfDimension {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    cycleCoeffOfModule D sY hY (directImageModule D hX.1 hY.1 f F) k γY ∈
      cyclesOfDimension D sY k := by
  rw [← properCyclePushforwardCoeff_cycleCoeffOfModule_eq D sX hX sY hY hfB hproper F k hdimF γX
    hγX γY hγY]
  exact properCyclePushforwardCoeff_mem_cyclesOfDimension D sX hX sY hY hfB hproper.2.1.2 k
    (associatedCycle D sX hX F k γX hγX hdimF)

/-- **Stacks 0EP3, part (2).** In Situation 0EDT let `f : X ⟶ Y` be a proper morphism of good
algebraic spaces over the base and let `F` be a coherent `𝒪_X`-module with
`dim_δ(Supp(F)) ≤ k`. Then

`f_*[F]_k = [f_*F]_k`

in `Z_k(Y)`: the proper pushforward of the `k`-cycle `[F]_k` of Stacks 0EEB is the `k`-cycle
whose coefficient at an integral closed subspace `W ⊂ Y` of δ-dimension `k` is the length of
`f_*F` at the generic point of `W`. The cycles of modules are read at chosen geometric
representatives `γX`, `γY` of the points (by Stacks 0EE1 the lengths do not depend on them). That
the coefficient family of `f_*F` is a `k`-cycle is part of the statement
(`AlgebraicGeometry.Space.cycleCoeffOfModule_directImageModule_mem_cyclesOfDimension`); the
coherence of `f_*F` (Stacks 08AR) is not needed. -/
@[stacks 0EP3 "part (2)"]
theorem properCyclePushforward_associatedCycle_eq {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    properCyclePushforward D sX hX sY hY hfB hproper.2.1.2 k
        (associatedCycle D sX hX F k γX hγX hdimF) =
      ⟨cycleCoeffOfModule D sY hY (directImageModule D hX.1 hY.1 f F) k γY,
        cycleCoeffOfModule_directImageModule_mem_cyclesOfDimension D sX hX sY hY hfB hproper F k
          hdimF γX hγX γY hγY⟩ :=
  Subtype.ext (properCyclePushforwardCoeff_cycleCoeffOfModule_eq D sX hX sY hY hfB hproper F k
    hdimF γX hγX γY hγY)

/-! ### The cycle of a closed subspace -/

/-- The direct image `f_*𝒪_Z` of the structure sheaf of a closed subspace `Z ⊂ X` along the
composite `Z → X → Y`. -/
noncomputable abbrev closedSubspaceDirectImageStructureSheaf (f : X ⟶ Y) (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) :
    Modules.{u, u} D.site D.base D.base_mem Y hY.1 :=
  (modulePushforward D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ ≫
      (ObjectProperty.homMk f :
        (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩))).obj
    (SheafOfModules.unit _)

include sY in
/-- The direct image `i_*𝒪_Z` of the structure sheaf of a closed subspace is coherent, on a good
algebraic space: it is the direct image of the structure sheaf along a closed immersion, Stacks
07UH for the structure sheaf (`AlgebraicGeometry.Space.isCoherent_structureSheafPushforward`),
read through the comparison of the two direct images. -/
theorem isCoherent_closedSubspacePushforwardStructureSheaf (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) :
    IsCoherent D.site D.base D.base_mem X hX.1
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ) := by
  have hcoh := isCoherent_structureSheafPushforward D.site D.base D.base_mem
    (X := ⟨X, hX.1⟩) (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
    (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
  have : SheafOfModules.IsCoherentOnSite
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ) :=
    Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (modulePushforwardIsoChartDirectImage D.site D.base D.base_mem
        (closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
        (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
        (SheafOfModules.unit _)) hcoh.toIsCoherentOnSite
  exact isCoherent_of_isCoherentOnSite D.site D.base D.base_mem X hX.1 _

/-- The support of `i_*𝒪_Z` of a closed subspace `Z ⊂ X` with `dim_δ(Z) ≤ k` has δ-dimension at
most `k`: it is contained in `|Z|`, the module being annihilated by the ideal of `Z`. -/
theorem deltaDimensionClosed_closedSubspacePushforwardStructureSheaf_le (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    [IsCoherent D.site D.base D.base_mem X hX.1
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)] :
    deltaDimensionClosed D sX hX
      (moduleSupport D.site D.base D.base_mem hX.1
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 _) ≤ (k : EInt) :=
  deltaDimensionClosed_le_of_subset_subspacePointSet D sX hX Z hZ _ _ k hdim
    (supportOfSheaf_subset_of_annihilatedByKerIdeal D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
      (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ) _
      (annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem
        hX.1 Z hZ))

/-- **The coefficients of `f_*[Z]_k` are those of `[f_*𝒪_Z]_k`.** -/
theorem properCyclePushforwardCoeff_closedSubspaceCycle_eq {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f) (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    properCyclePushforwardCoeff D sX hX sY hY f (closedSubspaceCycle D sX hX Z hZ k hdim).1 =
      cycleCoeffOfModule D sY hY (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z hZ) k
        γY := by
  have := isCoherent_closedSubspacePushforwardStructureSheaf D sX hX sY Z hZ
  have hdimF := deltaDimensionClosed_closedSubspacePushforwardStructureSheaf_le D sX hX Z hZ k
    hdim
  change properCyclePushforwardCoeff D sX hX sY hY f
    (cycleCoeffOfClosedSubspace D sX hX Z hZ k
      (canonicalGeometricPoint D.site D.base D.base_mem Z.toFunctor)) = _
  rw [cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero D sX hX Z hZ k hdim
      (canonicalGeometricPoint D.site D.base D.base_mem Z.toFunctor)
      (canonicalGeometricPoint D.site D.base D.base_mem X)
      (canonicalGeometricPoint_image D.site D.base D.base_mem Z.toFunctor)
      (canonicalGeometricPoint_image D.site D.base D.base_mem X),
    properCyclePushforwardCoeff_cycleCoeffOfModule_eq D sX hX sY hY hfB hproper _ k hdimF
      (canonicalGeometricPoint D.site D.base D.base_mem X)
      (canonicalGeometricPoint_image D.site D.base D.base_mem X) γY hγY]
  let i := closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ
  let fA : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩ :=
    ObjectProperty.homMk f
  let e : directImageModule D hX.1 hY.1 f
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ) ≅
      closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z hZ :=
    (modulePushforward D.site D.base D.base_mem fA).mapIso
        (modulePushforwardIsoChartDirectImage D.site D.base D.base_mem i
          (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Z hZ)
          (SheafOfModules.unit _)).symm ≪≫
      ((modulePushforwardCompIso D.site D.base D.base_mem i fA).app (SheafOfModules.unit _) :
        (modulePushforward D.site D.base D.base_mem fA).obj
          ((modulePushforward D.site D.base D.base_mem i).obj (SheafOfModules.unit _)) ≅ _)
  funext W
  rw [cycleCoeffOfModule_eq_moduleMultiplicity, cycleCoeffOfModule_eq_moduleMultiplicity,
    moduleMultiplicity, moduleMultiplicity,
    geometricLength_eq_of_iso D.site D.base D.base_mem ⟨Y, hY.1⟩ _ e]

/-- The coefficient family of `f_*𝒪_Z`, for a closed subspace `Z ⊂ X` with `dim_δ(Z) ≤ k` and a
proper `f`, is a `k`-cycle: it is the pushforward of the `k`-cycle `[Z]_k`. -/
theorem cycleCoeffOfModule_closedSubspaceDirectImageStructureSheaf_mem_cyclesOfDimension
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem f)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    cycleCoeffOfModule D sY hY (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z hZ) k
      γY ∈ cyclesOfDimension D sY k := by
  rw [← properCyclePushforwardCoeff_closedSubspaceCycle_eq D sX hX sY hY hfB hproper Z hZ k hdim
    γY hγY]
  exact properCyclePushforwardCoeff_mem_cyclesOfDimension D sX hX sY hY hfB hproper.2.1.2 k
    (closedSubspaceCycle D sX hX Z hZ k hdim)

/-- In Situation 0EDT let `f : X ⟶ Y` be a proper morphism of good algebraic spaces over the base
and let `Z ⊂ X` be a closed subspace with `dim_δ(Z) ≤ k`. Then

`f_*[Z]_k = [f_*𝒪_Z]_k`

in `Z_k(Y)`, where `[Z]_k` is the `k`-cycle of Stacks 0EE9 and `f_*𝒪_Z` is the direct image of
the structure sheaf of `Z` along `Z → X → Y`: the proper pushforward of `[Z]_k` is the
`k`-cycle whose coefficient at an integral closed subspace `W ⊂ Y` of δ-dimension `k` is the
length of `f_*𝒪_Z` at the generic point of `W` (read at the chosen geometric representative
`γY`; by Stacks 0EE1 it does not depend on it). That this coefficient family is a `k`-cycle is
part of the statement
(`cycleCoeffOfModule_closedSubspaceDirectImageStructureSheaf_mem_cyclesOfDimension`). -/
@[stacks 0EP3 "part (1)"]
theorem properCyclePushforward_closedSubspaceCycle_eq {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f) (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y) :
    properCyclePushforward D sX hX sY hY hfB hproper.2.1.2 k
        (closedSubspaceCycle D sX hX Z hZ k hdim) =
      ⟨cycleCoeffOfModule D sY hY (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f Z hZ)
          k γY,
        cycleCoeffOfModule_closedSubspaceDirectImageStructureSheaf_mem_cyclesOfDimension D sX hX
          sY hY hfB hproper Z hZ k hdim γY hγY⟩ :=
  Subtype.ext (properCyclePushforwardCoeff_closedSubspaceCycle_eq D sX hX sY hY hfB hproper Z hZ
    k hdim γY hγY)

end AlgebraicGeometry.Space

end
