module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishing

/-!
# Finite affine covering families of an affine étale chart, at a free index universe

`AlgebraicGeometry.Space.SmallEtale.sliceHypercover`,
`AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceHypercover_map` and
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ` present the
finite affine covering families of an affine étale chart of an algebraic space at the index
universe `u` of the schemes, which is where the Čech vanishing of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartCechVanishing.lean` consumes them, its coefficients
being at `u`.

A Čech statement with coefficients at an enlarged universe needs its families presented there:
the Čech complex of a family indexed by `I` is built from products indexed by `I`, which exist in
an abelian-group category of the coefficient universe only for `I` in that universe.  The
coefficient universe of the closure clauses of [Stacks, Tag 03M1], which is where the tensor
products of [Stacks, Tag 09LX] are formed on the small étale site of an algebraic space, is
`max (u + 1) m`.  So this file states the three results at a free index universe; their content
is unchanged, the index type of a family being lifted along `ULift` with the same arrows.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.sliceHypercoverFreeIndex`: a family of morphisms of étale
  charts with target `W`, read as a family in the slice `Over W` with target `Over.mk (𝟙 W)`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceHypercoverFreeIndex_map`: a finite
  covering family of an affine chart by affine charts has standard étale form downstairs.
* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_freeIndex`: a
  covering sieve of an affine étale chart is refined by a finite affine covering family presented
  at any index universe.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : SmallEtale B S hS F)

/-- A family of morphisms of étale charts with target `W`, indexed in any universe, read as a
family in the slice `Over W` with target the terminal object `Over.mk (𝟙 W)`: the member
`V_i → W` becomes the object `Over.mk (V_i → W)` with its own structure morphism.

This is `AlgebraicGeometry.Space.SmallEtale.sliceHypercover` at a free index universe; see that
declaration for why the slice reading is needed. -/
def sliceHypercoverFreeIndex (E : PreZeroHypercover.{v} W) :
    PreZeroHypercover.{v} (Over.mk (𝟙 W)) where
  I₀ := E.I₀
  X i := Over.mk (E.f i)
  f i := Over.homMk (E.f i) (by simp)

/-- Pushing the slice reading of a family back down along the slice projection returns the
family itself, on the nose. -/
theorem sliceHypercoverFreeIndex_map_forget (E : PreZeroHypercover.{v} W) :
    (sliceHypercoverFreeIndex B S hS F W E).map (Over.forget W) = E := rfl

/-- **A finite covering family of an affine chart by affine charts, indexed in any universe, has
standard étale form downstairs**, in the sense of [Stacks, Tag 03X9].

This is `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceHypercover_map` at a free
index universe, with the same proof: joint surjectivity is
`AlgebraicGeometry.Space.SmallEtale.iUnion_range_eq_univ_of_sieve₀_mem_topology`, which is
already stated at a free index universe, and étaleness of a morphism of charts over `W` is
`AlgebraicGeometry.Space.SmallEtale.etale_sliceToOver_obj_hom`. -/
theorem isStandardCovering_sliceHypercoverFreeIndex_map (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{v} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W) :
    letI : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
    IsStandardCovering .etale
      (fun i ↦ (((sliceHypercoverFreeIndex B S hS F W E).map (sliceToOver B S hS F W)).X i).left)
      (fun i ↦ (((sliceHypercoverFreeIndex B S hS F W E).map (sliceToOver B S hS F W)).f i).left) :=
  let : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
  { finite_index := hfin
    affine_source := haff
    jointly_surjective := iUnion_range_eq_univ_of_sieve₀_mem_topology B S hS F E hcov
    standard := fun i ↦ etale_sliceToOver_obj_hom B S hS F W (Over.mk (E.f i)) }

variable {B S hS F}

/-- **A covering sieve of an affine étale chart is refined by a finite affine covering family
presented at any index universe `w`.**

This is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ` at a
free index universe: the refinement of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` with its index type lifted
to `Type w`.  The lifted family has the same arrows, hence the same generated sieve. -/
theorem exists_finite_affine_preZeroHypercover_freeIndex (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (R : Sieve W) (hR : R ∈ SmallEtale.topology B S hS F W) :
    ∃ E : PreZeroHypercover.{w} W,
      (Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W) ∧
        E.sieve₀ ≤ R := by
  obtain ⟨ι, hι, V, f, haff, hle, hmem⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F W hW R hR
  have _ : Finite ι := hι
  have hsieve : (PreZeroHypercover.mk (ULift.{w} ι) (fun i => V i.down)
        (fun i => f i.down) : PreZeroHypercover.{w} W).sieve₀ = Sieve.ofArrows V f := by
    change Sieve.generate _ = Sieve.generate _
    congr 1
    funext Z
    ext g
    constructor <;> rintro ⟨i⟩
    exacts [⟨i.down⟩, ⟨ULift.up i⟩]
  exact ⟨⟨ULift.{w} ι, fun i => V i.down, fun i => f i.down⟩,
    ⟨inferInstance, fun i => haff i.down, hsieve ▸ hmem⟩, hsieve ▸ hle⟩

end AlgebraicGeometry.Space.SmallEtale

end
