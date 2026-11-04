module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureModuleChartEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFiniteLocallyFree

/-!
# Stacks 03ZU: a representable morphism is finite locally free exactly when `f_*𝒪_X` is

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a *representable*
morphism of algebraic spaces over `S`. Stacks 03ZU asserts that `f` is finite locally free in the
sense of Section 03HA — every represented base change of `f` is a finite locally free morphism of
schemes — if and only if `f` is affine and the direct image `f_*𝒪_X` is a finite locally free
`𝒪_Y`-module, which is the definition of Stacks 03ZV.

The biconditional is read at one surjective étale chart `V` of `Y`: the scheme-level finite local
freeness of the base change `ψ : V ×_Y X ⟶ V` agrees with affineness of `f` together with finite
local freeness of the restriction of `f_*𝒪_X` to the slice of the small étale site of `Y` at `V`.

## Main results

* `isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_iff_of_affine`: for an *affine* base
  change `ψ`, finite local freeness of `(f_*𝒪_X)|_V` on the slice at `V` is the scheme-level finite
  local freeness of `ψ`.
* `isAffineHom_baseChange_of_isAffineHom`: affineness of `f` gives affineness of the represented
  base change `ψ`.
* `isFiniteLocallyFree_baseChange_iff_chart`: the chart comparison, at one chart which is étale and
  surjective on points.
* `presheaf_iff_isFiniteLocallyFree`: **Stacks 03ZU**, with no hypothesis beyond representability.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The module conjunct of the chart comparison -/

/-- **The module conjunct of the chart comparison of Stacks 03ZU.**  For a representable
`f : X ⟶ Y` and an étale scheme chart `V` of `Y` whose cartesian projection `ψ : V ×_Y X ⟶ V` is
affine, finite local freeness of the restriction of `f_*𝒪_X` to the slice of the small étale site
of `Y` at `V` is exactly the scheme-level finite local freeness of `ψ`. -/
theorem isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_iff_of_affine (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    [haff : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))] :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
        ((pushforwardStructureModule B S hS f).over V) ↔
      Stacks.Morphisms.IsFiniteLocallyFree
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) := by
  have e := overPushforwardStructureModuleIsoSliceAssociatedModule B S hS f hf V
  have key := isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff B S hS Y V
    (Stacks.Morphisms.pushforwardStructureSheaf
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine .mk (toIsAffineHom := haff) (toIsFiniteLocallyFree := key.1 ?_)
    exact @SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
        _ _ e h
  · exact @SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
        _ _ e.symm
      (key.2 h.toIsFiniteLocallyFree)

/-! ### Affineness of the base change -/

/-- **An affine morphism of algebraic spaces has affine represented base changes.**  For a
representable `f : X ⟶ Y` which is affine in the sense of Stacks 03WF and any chart
`V.1.hom : yoneda.obj V.1.left ⟶ Y`, the base change `ψ : V ×_Y X ⟶ V` is an affine morphism of
schemes. -/
theorem isAffineHom_baseChange_of_isAffineHom (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (haff : IsAffineHom B S hS f.hom) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) :=
  (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.2 Y.2 haff).2.property
    V.1.hom (hf.fst V.1.hom) (hf.snd V.1.hom) (hf.isPullback V.1.hom)

/-! ### The chart comparison -/

/-- **The chart comparison of Stacks 03ZU.**  For a representable morphism `f : X ⟶ Y` of
algebraic spaces over `S` and an étale chart `V` of `Y` whose structure morphism is surjective on
points, the scheme-level finite local freeness of the base change `ψ : V ×_Y X ⟶ V` holds exactly
when `f` is affine and the restriction of `f_*𝒪_X` to the slice of the small étale site of `Y` at
`V` is finite locally free. -/
theorem isFiniteLocallyFree_baseChange_iff_chart (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (hV : IsSurjective B S hS V.1.hom) :
    Stacks.Morphisms.IsFiniteLocallyFree
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) ↔
      (IsAffineHom B S hS f.hom ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
          ((pushforwardStructureModule B S hS f).over V)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)) := h.toIsAffineHom
    refine ⟨isAffineHom_of_presheaf_isFiniteLocallyFree B S hS
        ((isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints
          B S hS X.2 Y.2 hf V.2 hV).2 h),
      (isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_iff_of_affine
        B S hS f hf V).2 h⟩
  · have := isAffineHom_baseChange_of_isAffineHom B S hS f hf V h.1
    exact (isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_iff_of_affine
      B S hS f hf V).1 h.2

/-! ### Stacks 03ZU -/

/-- Let `S` be a scheme and let `f : X ⟶ Y` be a representable morphism of algebraic spaces over
`S`.  Then `f` is finite locally free in the sense of Section 03HA — every represented base change
of `f` is a finite locally free morphism of schemes — if and only if `f` is affine and the sheaf
`f_*𝒪_X` is a finite locally free `𝒪_Y`-module, which is the definition of Stacks 03ZV,
`AlgebraicGeometry.Space.IsFiniteLocallyFree`. -/
@[stacks 03ZU]
theorem presheaf_iff_isFiniteLocallyFree (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
      IsFiniteLocallyFree B S hS f := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  exact (presheaf_iff_isFiniteLocallyFree_iff_chartComparison B S hS f hf V hV).2
    (isFiniteLocallyFree_baseChange_iff_chart B S hS f hf V hV)

end AlgebraicGeometry.Space

end
