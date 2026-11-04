module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.UniversallySubmersive
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination

/-!
# The flat cases of Stacks 0ETR and 0ETT, with no carried hypothesis

The last paragraph of the Stacks proof of 0ETR, and the endgame of the Stacks proof of 0ETT,
recognize a *flat* family which is jointly surjective as an fppf covering and appeal to Stacks
0DBT to turn it into a ph covering. In
`StacksFrontier.AlgebraicGeometry.Topologies.V.FppfVComparison` and
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.UniversallySubmersive` that appeal is made
through `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage`, which carries the weak form of
Stacks 0CP0 isolated as `AlgebraicGeometry.FppfHasFiniteDomination` as an explicit hypothesis.

Stacks 0DBT is now available with no hypothesis at all, as
`AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage` in
`StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination`: the domination input is only
ever needed over an affine base, and there it is unconditional. This file restates the four
consequences of the flat case through that form, so that none of them carries
`AlgebraicGeometry.FppfHasFiniteDomination` any more.

What is left of Stacks 0ETR (2) ⟹ (1) and of Stacks 0ETT (1) ⟹ (2) after this is therefore
*exactly* the reduction of the general case to the flat one — the generic flatness stratification
of the base together with the Raynaud–Gruson flattening blowup — and nothing about fppf coverings
or finite domination. See `AlgebraicGeometry.StandardVCoveringHasPHRefinement` and
`AlgebraicGeometry.UniversallySubmersiveHasPHRefinement` for the two shapes that reduction is
asked for in.

## Main results

* `AlgebraicGeometry.IsVCovering.isPHCovering_of_flat` and
  `AlgebraicGeometry.flat_isPHCovering_iff_isVCovering`: the flat case of Stacks 0ETR, the
  hypothesis-free forms of `AlgebraicGeometry.isPHCovering_of_isVCovering_of_flat` and
  `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_flat`.
* `AlgebraicGeometry.IsStandardVCovering.exists_standardPHCovering_refinement_of_flat`: the flat
  case of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, in the shape that hypothesis has;
  the hypothesis-free form of `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat`.
* `AlgebraicGeometry.IsHCovering.of_universallySubmersive_of_flat`: the flat case of Stacks 0ETT
  (1) ⟹ (2), the hypothesis-free form of
  `AlgebraicGeometry.isHCovering_of_universallySubmersive_of_flat`.

## Implementation notes

No tag is attached to anything here. The flat case of Stacks 0ETR is not Stacks 0ETR and the flat
case of Stacks 0ETT is not Stacks 0ETT: in both tags the family is assumed only locally of finite
presentation, respectively of finite type, and the whole content of the direction being proved is
the reduction of that case to the flat one. The existing conditional forms keep their names and
are not touched, so nothing downstream of them changes.

The refinement in
`AlgebraicGeometry.IsStandardVCovering.exists_standardPHCovering_refinement_of_flat` is read
straight off
`AlgebraicGeometry.exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine`,
whose conclusion already is the conclusion of
`AlgebraicGeometry.StandardVCoveringHasPHRefinement`; the conditional form had to go through
`AlgebraicGeometry.Scheme.topIso` instead, because the general ph covering condition it used
supplies its refinement over an affine *open* of the base rather than over the base itself.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- **The flat case of Stacks 0ETR (2) ⟹ (1).** A V covering whose members are flat and locally
of finite presentation is a ph covering.

This is `AlgebraicGeometry.isPHCovering_of_isVCovering_of_flat` with its hypothesis
`AlgebraicGeometry.FppfHasFiniteDomination` discharged by Stacks 0DBT,
`AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage`. The family is jointly surjective by
`AlgebraicGeometry.IsVCovering.exists_mem_range`, hence an fppf covering. -/
theorem IsVCovering.isPHCovering_of_flat {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hflat : ∀ i, Flat (f i))
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) (hV : IsVCovering X f) :
    IsPHCovering X f :=
  IsPHCovering.of_mem_fppfPrecoverage X f (mem_fppfPrecoverage_of_isVCovering X f hflat hfp hV)

/-- **The flat case of Stacks 0ETR.** For a family of flat morphisms locally of finite
presentation, the ph and the V covering conditions agree.

This is `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_flat` with its hypothesis
`AlgebraicGeometry.FppfHasFiniteDomination` discharged. -/
theorem flat_isPHCovering_iff_isVCovering {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hflat : ∀ i, Flat (f i))
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  ⟨isVCovering_of_isPHCovering X f, IsVCovering.isPHCovering_of_flat X f hflat hfp⟩

/-- **The flat case of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`.** A standard V
covering of an affine scheme whose members are flat and locally of finite presentation is refined
by a standard ph covering.

This is `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat` with its hypothesis
`AlgebraicGeometry.FppfHasFiniteDomination` discharged. Stated in exactly the shape of the
hypothesis that `AlgebraicGeometry.isPHCovering_iff_isVCovering` carries, it measures what is left
of that hypothesis: only the reduction of a standard V covering by finitely presented affines to a
flat one, that is the flattening. -/
theorem IsStandardVCovering.exists_standardPHCovering_refinement_of_flat {U : Scheme.{u}}
    (hU : IsAffine U) (K : Type u) (hK : Finite K) (A : K → Scheme.{u}) (hA : ∀ κ, IsAffine (A κ))
    (a : ∀ κ, A κ ⟶ U) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hstd : @IsStandardVCovering U hU K hK A hA a) :
    ∃ 𝒱 : PreZeroHypercover.{u} U, @StandardPHCovering 𝒱.I₀ U hU 𝒱.X 𝒱.f ∧
      Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} U)) := by
  have : IsAffine U := hU
  have : Finite K := hK
  have : ∀ κ, IsAffine (A κ) := hA
  exact exists_standardPHCovering_refinement_of_mem_fppfPrecoverage_of_isAffine A a
    (mem_fppfPrecoverage_of_isStandardVCovering A a hflat hfp hstd)

/-- **The flat case of Stacks 0ETT (1) ⟹ (2).** A finite family of flat morphisms of finite type
to a Noetherian scheme whose disjoint-union morphism is universally submersive is an h covering.

This is `AlgebraicGeometry.isHCovering_of_universallySubmersive_of_flat` with its hypothesis
`AlgebraicGeometry.FppfHasFiniteDomination` discharged by Stacks 0DBT.
Universal submersiveness enters only through surjectivity of the disjoint-union morphism, so the
family is jointly surjective, flat and locally of finite presentation, that is an fppf
covering. -/
theorem IsHCovering.of_universallySubmersive_of_flat {X : Scheme.{u}} [IsNoetherian X]
    {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)] [∀ i, Flat (f i)]
    (hsub : UniversallySubmersive (Sigma.desc f)) : IsHCovering Y f := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i ↦
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  refine ⟨hfp, IsPHCovering.of_mem_fppfPrecoverage Y f ?_⟩
  refine (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨?_, fun i ↦ ⟨inferInstance, hfp i⟩⟩
  exact exists_mem_range_of_surjective_sigmaDesc
    ((submersive_iff _).1 (submersive_of_universallySubmersive hsub)).surjective

end AlgebraicGeometry

end
