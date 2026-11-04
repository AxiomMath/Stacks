module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.BaseChange

/-!
# Dominance is fpqc local on the base in the presence of quasi-compactness, and fppf local alone

Dominance is not stable under arbitrary base change, so it is not fpqc local on the base on its
own: the conjunction with quasi-compactness is. For the fppf topology no such extra hypothesis is
needed, because a flat morphism locally of finite presentation is an open map.

## Main results

* `AlgebraicGeometry.isDominant_descendsAlong_surjective`: dominance descends along a surjection.
* `AlgebraicGeometry.quasiCompact_isDominant_isLocalAtTarget_fpqc`: being quasi-compact and
  dominant is fpqc local on the base.
* `AlgebraicGeometry.isDominant_isLocalAtTarget_fppf`: being dominant is fppf local on the base.

## Implementation notes

Descent of dominance needs nothing but surjectivity of the covering morphism `g`: if the base
change of `f` along `g` is dominant then so is its composite with `g`, which is the composite of
the other projection with `f`, and dominance of a composite passes to the second factor.

For the fpqc statement the remaining hypothesis of the criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` is stability under flat base change, and this is
where quasi-compactness is used: a flat morphism lifts generalizations, and a generizing base
change of a *quasi-compact* dominant morphism is dominant
(`AlgebraicGeometry.isDominant_pullback_snd_of_liftsGeneralizations`).

The fppf statement does not go through that criterion at all. Both directions are visible
directly on underlying spaces once the range of a base change is identified with a preimage
(`AlgebraicGeometry.Scheme.Pullback.range_snd`): a member `g` of an fppf covering family is flat
and locally of finite presentation, hence an open map, so `g ⁻¹' closure s = closure (g ⁻¹' s)`;
density of the range of `f` therefore transfers to each base change, and conversely density of
every preimage puts the range of every `g` inside the closure of the range of `f`, which is all
of the target because an fppf covering family is jointly surjective.

## References

* [Stacks Project, Tag 0H8H](https://stacks.math.columbia.edu/tag/0H8H)
* [Stacks Project, Tag 0H8J](https://stacks.math.columbia.edu/tag/0H8J)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty TopologicalSpace

namespace AlgebraicGeometry

universe w u

/-- Dominance of morphisms of schemes descends along a surjection: if the base change of `g`
along a surjective morphism is dominant, then so is `g`. -/
@[ega "IV 1.1.4"]
instance isDominant_descendsAlong_surjective :
    MorphismProperty.DescendsAlong (@IsDominant : MorphismProperty Scheme.{u}) @Surjective where
  of_isPullback {_ _ _ _ fst snd f g} h hf hfst := by
    have _ : Surjective f := hf
    have _ : IsDominant fst := hfst
    have : IsDominant (snd ≫ g) := by rw [← h.w]; infer_instance
    exact IsDominant.of_comp snd g

/-- Being quasi-compact and dominant is stable under flat base change. -/
@[sga "4 IV 8.5.5" "partial"]
instance quasiCompact_isDominant_isStableUnderFlatBaseChange :
    Stacks.Descent.IsStableUnderFlatBaseChange
      (@QuasiCompact ⊓ @IsDominant : MorphismProperty Scheme.{u}) where
  isStableUnderBaseChangeAlong q := by
    refine ⟨fun {_ _ _ _ g} pb hg ↦ ⟨?_, ?_⟩⟩
    · exact quasiCompact_isStableUnderBaseChange.of_isPullback pb hg.1
    · have _ : QuasiCompact g := hg.1
      have _ : IsDominant g := hg.2
      rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsDominant) pb.isoPullback.inv,
        pb.isoPullback_inv_snd]
      exact isDominant_pullback_snd_of_liftsGeneralizations g q
        ((liftsGeneralizations_iff_generalizingMap q).2 (Flat.generalizingMap q))

/-- **Stacks Project, Tag 0H8H.** Being quasi-compact and dominant is fpqc local on the base. -/
@[stacks 0H8H, sga "3 VIB 2.1.2" "qc+dominant example", sga "4 IV 8.5.5"]
instance quasiCompact_isDominant_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@QuasiCompact ⊓ @IsDominant : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc.of_le
      Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have : IsZariskiLocalAtTarget (@QuasiCompact ⊓ @IsDominant : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  have : MorphismProperty.DescendsAlong
      (@QuasiCompact ⊓ @IsDominant : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    have : MorphismProperty.DescendsAlong (@IsDominant : MorphismProperty Scheme.{u})
        (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
      MorphismProperty.DescendsAlong.of_le fun _ _ _ h ↦ h.1.1
    MorphismProperty.DescendsAlong.inf
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- Every member of an fppf covering family is an open map. -/
private lemma isOpenMap_of_mem_fppfPrecoverage {Y : Scheme.{u}}
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fppfPrecoverage.{u} Y) (i : 𝒰.I₀) :
    IsOpenMap (𝒰.f i).base := by
  obtain ⟨hflat, hfp⟩ :
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (𝒰.f i) :=
    𝒰.mem₀.2 ⟨i⟩
  have _ : Flat (𝒰.f i) := hflat
  have _ : LocallyOfFinitePresentation (𝒰.f i) := hfp
  exact (𝒰.f i).isOpenMap

/-- **Stacks Project, Tag 0H8J.** Being dominant is fppf local on the base. -/
@[stacks 0H8J, ega "I 2.2.8" "more general"]
instance isDominant_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsDominant : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage := by
  have hjs : Scheme.JointlySurjective Scheme.fppfPrecoverage.{u} := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    infer_instance
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦
    ⟨fun hf i ↦ ?_, fun h ↦ ?_⟩
  · have _ : IsDominant f := hf
    exact isDominant_pullback_snd_of_isOpenMap f (𝒰.f i) (isOpenMap_of_mem_fppfPrecoverage 𝒰 i)
  · rw [isDominant_iff, DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    obtain ⟨i, z, rfl⟩ := Scheme.Cover.exists_eq 𝒰 y
    have hi : closure ((𝒰.f i).base ⁻¹' Set.range f.base) = Set.univ := by
      have := (h i).denseRange
      rwa [DenseRange, Scheme.Pullback.range_snd, dense_iff_closure_eq] at this
    rw [← (isOpenMap_of_mem_fppfPrecoverage 𝒰 i).preimage_closure_eq_closure_preimage
      (𝒰.f i).continuous] at hi
    exact hi.ge (Set.mem_univ z)

end AlgebraicGeometry

end
