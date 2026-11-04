module

public import StacksFrontier.AlgebraicGeometry.Limits.IntegralAffineLimit09YZ
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfIntegralDomination

/-!
# Domination of an fppf covering over an affine base, and the ph topology

An fppf covering of schemes is a ph covering. Over an affine base, an fppf covering is dominated
by a finite surjective morphism of finite presentation which, on a Zariski covering of its source,
factors through members of the covering; since a ph covering is tested on the affine opens of the
target, this suffices.

## Main results

* `AlgebraicGeometry.exists_finite_surjective_refinement_of_isAffine`: an fppf covering of an
  affine scheme is dominated by a finite surjective morphism of finite presentation, factoring
  Zariski locally through members of the covering.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine`:
  an fppf covering of an affine scheme is refined by a standard ph covering of it.
* `AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage`: an fppf covering of schemes is a ph
  covering.

## References

* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The members of an fppf covering are flat and locally of finite presentation, and cover. -/
private theorem surjective_and_flat_lfp_of_mem_fppfPrecoverage {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    (∀ x, ∃ i, x ∈ Set.range (f i).base) ∧
      ∀ i, (@Flat ⊓ @LocallyOfFinitePresentation) (f i) :=
  (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf

/-- An fppf covering of an affine scheme is dominated by a finite surjective morphism of finite
presentation which, on a Zariski covering of its source, factors through members of the given
covering. -/
theorem exists_finite_surjective_refinement_of_isAffine
    {I : Type v} {S : Scheme.{u}} [IsAffine S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
        ∃ (J : Type u) (U : J → Scheme.{u}) (ι : ∀ c, U c ⟶ S'),
          Presieve.ofArrows U ι ∈ Scheme.zariskiPrecoverage S' ∧
            ∀ c, ∃ i, ∃ t : U c ⟶ X i, ι c ≫ g = t ≫ f i := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i =>
    ((surjective_and_flat_lfp_of_mem_fppfPrecoverage hf).2 i).2
  obtain ⟨Y, g, hgint, hgsurj, J, U, ι, hιcover, hιfac⟩ :=
    exists_integral_surjective_refinement_of_mem_fppfPrecoverage hasQuasiFiniteSlices X f hf
  obtain ⟨p⟩ := @nonempty_integralLimitPresentation_of_isAffine _ _ g hgint ‹_›
  exact @exists_finite_surjective_refinement_of_isLimit I S inferInstance inferInstance X f hfp
    Y g hgint hgsurj J U ι hιcover hιfac p.indexType p.indexPreorder p.indexNonempty
    p.indexDirected p.diagram p.structureMap p.limitCone p.compatible p.isLimit p.stageFinite
    p.stageFinitePresentation

/-- An fppf covering of an affine scheme is refined by a standard ph covering of it. -/
theorem exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine
    {I : Type v} {T : Scheme.{u}} [IsAffine T] (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T) :
    ∃ A : PreZeroHypercover.{u} T, StandardPHCovering A.f ∧
      Nonempty (A.Hom ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T)) := by
  classical
  have hdata := surjective_and_flat_lfp_of_mem_fppfPrecoverage hf
  have hopen : ∀ i, IsOpen (Set.range (f i).base) := fun i ↦
    have := (hdata.2 i).1; have := (hdata.2 i).2; (f i).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set T)).elim_finite_subcover
      (fun i ↦ Set.range (f i).base) hopen fun x _ ↦ Set.mem_iUnion.mpr (hdata.1 x)
  have hmemfin : Presieve.ofArrows (fun i : {i : I // i ∈ s} ↦ X i.1)
      (fun i : {i : I // i ∈ s} ↦ f i.1) ∈ Scheme.fppfPrecoverage T := by
    refine (Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨fun x ↦ ?_, fun i ↦ hdata.2 i.1⟩
    obtain ⟨i, his, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨i, his⟩, hx⟩
  obtain ⟨S', g, hgfin, hgsurj, -, J, V, j, hV, hfactor⟩ :=
    exists_finite_surjective_refinement_of_isAffine _ _ hmemfin
  have : IsFinite g := hgfin
  have : IsAffine S' := isAffine_of_isAffineHom g
  let Z : Scheme.OpenCover S' :=
    { toPreZeroHypercover := ⟨J, V, j⟩
      mem₀ := hV }
  let A := Z.affineRefinement.openCover
  let W := A.finiteSubcover
  let toZ : W ⟶ Z :=
    (⟨fun a ↦ A.idx a.val, fun _ ↦ 𝟙 _, fun _ ↦ rfl⟩ : W ⟶ A).comp Z.fromAffineRefinement
  refine ⟨⟨W.I₀, W.X, fun a ↦ W.f a ≫ g⟩, ?_, ?_⟩
  · exact StandardPHCovering.of_presentation _
      (hX := fun a ↦ by
        change IsAffine (Spec (Z.affineRefinement.X (A.idx a.val)))
        infer_instance)
      g W.f inferInstance hgsurj (fun _ ↦ inferInstance) W.iUnion_range fun _ ↦ rfl
  · refine ⟨⟨fun a ↦ ((hfactor (toZ.s₀ a)).choose).val,
      fun a ↦ toZ.h₀ a ≫ (hfactor (toZ.s₀ a)).choose_spec.choose, fun a ↦ ?_⟩⟩
    change (toZ.h₀ a ≫ (hfactor (toZ.s₀ a)).choose_spec.choose) ≫
      f ((hfactor (toZ.s₀ a)).choose).val = W.f a ≫ g
    rw [Category.assoc, ← (hfactor (toZ.s₀ a)).choose_spec.choose_spec, ← Category.assoc,
      toZ.w₀]

/-- An fppf covering of schemes is a ph covering. -/
@[stacks 0DBT]
theorem IsPHCovering.of_mem_fppfPrecoverage
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T) :
    IsPHCovering X f := by
  have hdata := surjective_and_flat_lfp_of_mem_fppfPrecoverage hf
  refine ⟨fun i ↦ have := (hdata.2 i).2; inferInstance, fun U hU ↦ ?_⟩
  have : IsAffine U.toScheme := hU
  exact exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine _ _
    (Precoverage.mem_coverings_of_isPullback f hf U.ι (fun i ↦ pullback.snd (f i) U.ι)
      (fun i ↦ pullback.fst (f i) U.ι) fun i ↦ (IsPullback.of_hasPullback (f i) U.ι).flip)

end AlgebraicGeometry

end
