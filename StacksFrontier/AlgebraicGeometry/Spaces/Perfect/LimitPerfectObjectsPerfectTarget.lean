module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Perfect objects along a limit of algebraic spaces

In Situation 09RH, Stacks 09RJ asserts that

`colim_{i ≥ 0} D_perf(𝒪_{X_i}) ⟶ D_perf(𝒪_X)`

is an equivalence; its full faithfulness is Stacks 09RI. This file states full faithfulness for
a pair of perfect objects `E₀`, `K₀` of `D(𝒪_{X₀})`, with no quasi-coherence hypothesis on `K₀`:
a perfect object is `m`-pseudo-coherent for every `m`, so by Stacks 08JL its cohomology sheaves
are quasi-coherent (`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPerfect`). The
categories of perfect objects are full subcategories of the derived categories, so the hom-sets
involved are those of `D(𝒪_X)` and of the `D(𝒪_{X_i})`. Essential surjectivity, the other half
of Stacks 09RJ, is not part of this file. The statements take the affine ring dictionary
`model : AlgebraicGeometry.Space.DescentSituation.RingModel` of Stacks 09RI as a hypothesis.

All names are in the namespace `AlgebraicGeometry.Space.DescentSituation`.

## Main results

* `exists_descendedHom_of_isPerfect`: **fullness** of the comparison out of the colimit: every
  morphism `Lf_0^*E₀ ⟶ Lf_0^*K₀` in `D(𝒪_X)` between the derived pullbacks of perfect objects
  `E₀`, `K₀` of `D(𝒪_{X₀})` is the image of a morphism `Lf_{i0}^*E₀ ⟶ Lf_{i0}^*K₀` at some
  stage `i ≥ 0`.
* `eventually_map_eq_of_isPerfect`: **faithfulness**: two morphisms
  `Lf_{i0}^*E₀ ⟶ Lf_{i0}^*K₀` at a stage `i` with the same image in `D(𝒪_X)` already agree at
  some later stage.
* `isHomColimit_of_isPerfect`: the two of them together, in the packaged form `IsHomColimit`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 36.29.3 (Tag 09RF)](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 75.4.2 (Tag 071Q)](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Lemma 75.13.5 (Tag 08HG)](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Definition 36.11.1 (Tag 0F8I)](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Lemma 36.10.3 (Tag 08JL)](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), (modulePullback B S hS f).Additive]
  {D : DescentSituation B S hS hZ I} (sys : D.DerivedPullbackSystem)

section

variable
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    HasSheafify ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U) AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).O).obj M).Additive]
  [∀ (M N : CochainComplex
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) ℤ),
    HomologicalComplex.HasMapBifunctor M N
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O)
      (ComplexShape.up ℤ)]
  (E₀ K₀ : PerfectDerivedCategory B S hS (D.stage D.base))

/-- **Stacks 09RI for a pair of perfect objects of `D(𝒪_{X₀})`.** For perfect objects `E₀` and
`K₀` of `D(𝒪_{X₀})`, the homomorphisms between their derived pullbacks to `X` are the filtered
colimit of the homomorphisms between their derived pullbacks to the stages `X_i`. -/
theorem isHomColimit_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R) :
    IsHomColimit sys E₀.obj K₀.obj :=
  isHomColimit_of_perfect sys E₀ K₀ T
    (fun n => isQuasicoherentOnSite_homology_of_isPerfect B S hS (D.stage D.base).obj
      (D.stage D.base).property K₀.obj n K₀.property) R model

/-- **Fullness of the comparison out of the colimit, Stacks 09RJ.**  In Situation 09RH, let `E₀`
and `K₀` be perfect objects of `D(𝒪_{X₀})` and put `E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for
`i ≥ 0` and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  Then every morphism `E ⟶ K` of `D(𝒪_X)` is the
image, under the map of Stacks 09RI, of a morphism `E_i ⟶ K_i` at some stage `i ≥ 0`.

This is fullness of the comparison functor out of the colimit of the `D_perf(𝒪_{X_i})`. -/
@[stacks 09RJ "fullness of the comparison out of the colimit of the categories of perfect \
objects, which the source's proof takes from Stacks 09RI; essential surjectivity, the other \
half of that proof, is not included"]
theorem exists_descendedHom_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R)
    (φ : limitObj sys E₀.obj ⟶ limitObj sys K₀.obj) :
    ∃ (i : D.Stages) (g : stageObj sys E₀.obj i ⟶ stageObj sys K₀.obj i),
      homProjection sys E₀.obj K₀.obj i g = φ :=
  Stacks.IsStagesColimit.exists_stage (isHomColimit_of_isPerfect sys E₀ K₀ T R model) φ

/-- **Faithfulness of the comparison out of the colimit, Stacks 09RJ.**  In Situation 09RH, with
`E₀` and `K₀` perfect objects of `D(𝒪_{X₀})` as above, two morphisms `E_i ⟶ K_i` at a stage
`i ≥ 0` whose images `E ⟶ K` in `D(𝒪_X)` agree already have equal images at some later stage.

This is faithfulness of the comparison functor out of the colimit of the `D_perf(𝒪_{X_i})`. -/
@[stacks 09RJ "faithfulness of the comparison out of the colimit of the categories of perfect \
objects, which the source's proof takes from Stacks 09RI; essential surjectivity, the other \
half of that proof, is not included"]
theorem eventually_map_eq_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀.obj K₀.obj R) (i : D.Stages)
    (g g' : stageObj sys E₀.obj i ⟶ stageObj sys K₀.obj i)
    (hgg : homProjection sys E₀.obj K₀.obj i g = homProjection sys E₀.obj K₀.obj i g') :
    ∃ (j : D.Stages) (h : i ≤ j), homTransition sys E₀.obj K₀.obj i j h g =
      homTransition sys E₀.obj K₀.obj i j h g' :=
  Stacks.IsStagesColimit.exists_trans_eq
    (isHomColimit_of_isPerfect sys E₀ K₀ T R model) i g g' hgg

end

end DescentSituation

end AlgebraicGeometry.Space

end
