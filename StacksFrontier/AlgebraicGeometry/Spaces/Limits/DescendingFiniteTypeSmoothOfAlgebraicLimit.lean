module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitBridgeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystemOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.TailSystemOfAlgebraicLimit

/-!
# Stacks 0CPD with no bound on the index type

In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated over `B`,
described by a morphism `(f_i)_{i ≥ i₀}` of the inverse systems of scheme-theoretic images
`X = lim X_i` and `Y = lim Y_i`, as in Stacks 0CPA. Stacks 0CPD asserts that if `f` is smooth,
then so is `f_i` for every sufficiently large `i`. Here no bound is put on the size of the index
type.

The proof is that of the source: Stacks 0CPC makes the squares formed by `f_i` and `f` cartesian
from some stage `i₃` on, so that `f` and the `f_i` are base changes of `f_{i₃}`, and Stacks 0CN2
makes some `f_j` smooth. Stacks 0CN2 is applied here in a form for inverse systems whose chart
systems have limit bridges, which the image system of `Y` has because its limit projections are
scheme-theoretically dominant.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isSmooth_of_algebraicLimit`:
  **Stacks 0CPD**.

## Implementation notes

The library's Stacks 0CN2, `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt`,
bounds the size of the index type, which is how it obtains the limits of the affine charts of the
stages. The form used here,
`AlgebraicGeometry.Space.exists_isSmooth_of_isPullback_of_hasChartLimitBridges`, takes those
limits as the hypothesis `AlgebraicGeometry.Space.HasChartLimitBridges` instead, which the image
system of `Y` on a later tail satisfies by
`AlgebraicGeometry.Space.GoodDiagram.tailSystem_hasChartLimitBridges`.

The stage `i₃` is produced with `i₀ ≤ i₃`, which is what the source's `i₃ > i₀` means for a
directed set. The form carrying the bound `#I < B.cutoff.ord.cof` is
`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isSmooth`.

## References

* [Stacks Project, Tag 0CPD](https://stacks.math.columbia.edu/tag/0CPD)
* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 0CPD -/

namespace GoodDiagram.SystemMorphism

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt} {pY : Y ⟶ D.limitCone.pt}

/-- **Stacks 0CPD.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces
quasi-separated over `B`, let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and `Y`, and
let `(f_i)_{i ≥ i₀}` be a morphism of the inverse systems of scheme-theoretic images
`X = lim X_i` and `Y = lim Y_i` whose limit is `f`, as in Stacks 0CPA. If `f` is smooth, then
there is a stage `i₃ ≥ i₀` such that `f_i` is smooth for every `i ≥ i₃`. No bound is put on the
size of the index type. -/
theorem exists_isSmooth_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}
    (F : SystemMorphism GX GY f i₀ leX leY) (smooth : IsSmooth B S hS f) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ k : Over (op i₀), i₃ ≤ k.left.unop →
      IsSmooth B S hS (F.maps.app k) := by
  classical
  -- `f` is flat and of finite presentation.
  have qsXa : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone_of_algebraicLimit algX qsX
  have qsYa : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone_of_algebraicLimit algY qsY
  have qcX : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS
      (tailSystem_isAlgebraicSpace GX leX (Over.mk (𝟙 (op i₀))))
      (tailSystem_isQuasiCompactSpace GX leX _)
      (isQuasiCompact_tailCone_π_of_algebraicLimit GX leX (Over.mk (𝟙 (op i₀))))
  have fp : IsFinitePresentation B S hS f :=
    ⟨isLocallyOfFinitePresentation_of_isSmooth B S hS smooth,
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ algY qsYa qcX f,
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ algX qsXa f⟩
  -- Stacks 0CPC: from some stage on, the system morphism is cartesian.
  obtain ⟨i₃, h₀₃, H⟩ := exists_isFlat_isPullback_of_algebraicLimit algX algY qsX qsY F
    (isFlat_of_isSmooth B S hS f smooth) fp
  let k₃ : Over (op i₀) := Over.mk (homOfLE h₀₃).op
  obtain ⟨-, sqX, -⟩ := H k₃ le_rfl
  -- The component `f_{i₃}` is locally of finite presentation.
  have ftk : IsLocallyOfFiniteType B S hS (F.maps.app k₃) :=
    isLocallyOfFiniteType_of_comp B S hS (tailSystem_isAlgebraicSpace GX leX k₃)
      (tailSystem_isAlgebraicSpace GY leY k₃) (D.system_isAlgebraicSpace _) _
      (tailBase GY leY k₃) (by
        rw [show F.maps.app k₃ ≫ tailBase GY leY k₃ = tailBase GX leX k₃ from F.over_base k₃]
        exact isLocallyOfFiniteType_tailBase GX leX k₃)
  have fpk : IsLocallyOfFinitePresentation B S hS (F.maps.app k₃) :=
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS
      (tailSystem_isAlgebraicSpace GX leX k₃) (tailSystem_isAlgebraicSpace GY leY k₃) _
      (tailSystem_isLocallyNoetherian GY leY k₃) ftk
  -- Stacks 0CN2, along the image system of `Y` above `i₃`, which has limit bridges.
  obtain ⟨j, a, Hj⟩ := exists_isSmooth_of_isPullback_of_hasChartLimitBridges (tailSystem GY leY)
    (tailSystem_hasChartLimitBridges GY leY algY) (isLimit_tailCone_of_algebraicLimit GY leY algY)
    (tailSystem_isAlgebraicSpace GY leY) (fun a => tailSystem_map_isAffineHom GY leY a)
    (tailSystem_isQuasiCompactSpace GY leY k₃)
    (tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GY leY algY qsY k₃)
    (tailSystem_isAlgebraicSpace GX leX k₃) (tailSystem_isQuasiCompactSpace GX leX k₃)
    (F.maps.app k₃) fpk sqX smooth
  have hj : i₃ ≤ j.left.unop := leOfHom a.left.unop
  have smoothj : IsSmooth B S hS (F.maps.app j) := Hj _ _ ((H k₃ le_rfl).2.2 j a)
  -- Every later component is a base change of `f_j`.
  refine ⟨j.left.unop, leOfHom j.hom.unop, fun k hk => ?_⟩
  let b : k ⟶ j := Over.homMk (homOfLE hk).op (Subsingleton.elim _ _)
  exact isSmooth_of_isPullback ((H j hj).2.2 k b).flip (tailSystem_isAlgebraicSpace GX leX k)
    (tailSystem_isAlgebraicSpace GX leX j) (tailSystem_isAlgebraicSpace GY leY k)
    (tailSystem_isAlgebraicSpace GY leY j) smoothj

end GoodDiagram.SystemMorphism

end AlgebraicGeometry.Space

end
