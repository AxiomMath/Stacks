module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded

/-!
# The relative dualizing complex is bounded coherent, from its affine charts, for `f` perfect

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a perfect morphism of `AlgebraicGeometry.FTS S`.
If around every point the restriction of `f^!𝒪_Y` to an affine chart is the associated sheaf of
the algebraic upper shriek of the model of `𝒪_Y`, then `f^!𝒪_Y` lies in `D^b_Coh(𝒪_X)`. This is
`Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf` with flatness and
finite presentation replaced by perfectness.

## Main results

* `Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_charts` —
  `f^!𝒪_Y ∈ D^b_Coh(𝒪_X)` from a chart description around every point.

## References

* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
-/
-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.CoherentOfFiniteType
open StacksDraft.TorAmplitude

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **`f^!𝒪_Y ∈ D^b_Coh(𝒪_X)` from an affine-chart description, for `f` perfect.** If around every
point the restriction of `f^!𝒪_Y` to an affine chart `U ⊆ f⁻¹(V)` is the associated sheaf of the
algebraic upper shriek of `Γ(Y, V)` along a polynomial presentation of `f.appLE V U`, then
`f^!𝒪_Y` is bounded with coherent cohomology: the algebraic upper shriek along a perfect ring map
carries `D^b_Coh` into `D^b_Coh` ([Stacks, Tag 0BZK] (2)), and the globalisation of this file
applies. The chart description is [Stacks, Tag 0BV2] for `𝒪_Y`,
`Stacks.Duality.upperShriekStructureSheafCharts`, whose file imports this one; the unconditional
statement, part (a) of [Stacks, Tag 0B6U], is
`Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf`. -/
theorem derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_charts [Perfect f.left]
    (hcharts : ∀ x : X.left, ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) := by
  have hln : ∀ Z : AlgebraicGeometry.FTS S, IsLocallyNoetherian Z.left := fun Z ↦ by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hYn := hln Y
  have hXn := hln X
  have hXc : CompactSpace X.left := by
    have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (CompactSpace S)
    exact QuasiCompact.compactSpace_of_compactSpace X.hom
  have hmodels : ∀ x : X.left,
      HasTildeModelAt.{u, u}
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) x := by
    intro x
    obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := hcharts x
    have hVn : IsNoetherianRing Γ(Y.left, V) :=
      IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have hUn : IsNoetherianRing Γ(X.left, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let D : CertifiedDerivedTensoring.{u, u} Γ(Y.left, V) :=
      canonicalCertifiedDerivedTensoring Γ(Y.left, V)
    exact ⟨U, hU, hxU, _,
      Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap.{u, u} p
        D.tensor D.comparison D.isLeftDerived
        (AlgebraicGeometry.Perfect.perfect_appLE f.left U hU V hV hUV D)
        (derivedCategoryBBounded_structureModel (Y := Y) V),
      he⟩
  exact ⟨isBounded_of_tildeModels hmodels, isCoherent_homology_of_tildeModels hmodels⟩

end Shriek

end Stacks.Duality

end
