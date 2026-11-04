module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleObjectStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleShriekConstructible
public import StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseLift

/-!
# Stacks 03S8 part (1) for sheaves of sets in a larger universe

Let `j : U ⟶ X` be an étale morphism of quasi-compact and quasi-separated schemes of a big étale
site, presented as an object `U` of the small étale site of `X`. Part (1) of Stacks 03S8 says
that the sheaf `h_U` of sets it represents is constructible, and
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` proves it for the sheaf of
sets `CategoryTheory.Sheaf.sheafifiedYoneda` produces, which lives in `Type (u + 1)`.

Comparing `h_U^#` with a sheaf of modules over a ring `Λ : Type r` forces a sheaf of sets in
`Type (max (u + 1) r)` instead, that being the module universe extension by zero works in. This
file proves part (1) there, for the sheafified representable
`CategoryTheory.Sheaf.sheafifiedUliftYoneda` of that universe.

## Main results

* `AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs` — **Stacks 03S8
  part (1) for a sheaf of sets in `Type (max (u + 1) r)`**.

## Implementation notes

The proof is that of `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, with its last
step replaced. The stratification of Stacks 03S0 and the reduction of constructibility to it are
already universe polymorphic:
`AlgebraicGeometry.isConstructibleFiniteSheaf_of_constructible_immersion_cover` and
`AlgebraicGeometry.isConstructibleFiniteSheaf_of_isFiniteLocallyConstant` are stated for a sheaf
with values in any concrete category. What is not polymorphic is finite local constancy of the
sheaf represented by a finite étale object,
`Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable`, whose sheaf of sets
is `Type (u + 1)`-valued. Rather than repeat its proof — the splitting of a finite étale morphism
into sheets and the local bijectivity of the comparison with the constant sheaf on the set of
sheets — it is transported: the representable at the larger universe is the pointwise universe
lift of the representable at `u + 1`
(`CategoryTheory.Sheaf.sheafifiedUliftYonedaIsoSheafCompose`) and that lift preserves finite
local constancy (`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor`).

The inverse image to a stratum is computed by
`Stacks.Sites.sheafPullbackSheafifiedUliftYonedaIso`, the larger-universe form of Stacks 04D3 for
sheafified representables.

The instance that the direct image of sheaves of sets in `Type (max (u + 1) r)` along a small
étale base change is a right adjoint is available for each morphism separately but is not found
by instance search in the `∀`-quantified form the constructibility predicate asks for; it is
therefore named and made a local instance.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03S0](https://stacks.math.columbia.edu/tag/03S0)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe s u

namespace AlgebraicGeometry

/-- The direct image of sheaves of sets in `Type (max (u + 1) s)` along a small étale base change
has a left adjoint.

The statement is `inferInstance`, but instance search does not find it when the goal is the
`∀`-quantified form that `AlgebraicGeometry.IsConstructibleFiniteSheaf` asks for, so it is named
here and used as a local instance. -/
public theorem isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type max (u + 1) s)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale

/-- **Stacks 03S8, part (1), for a sheaf of sets in a larger universe.** For an étale morphism
`j : U ⟶ X` of quasi-compact and quasi-separated schemes, presented as an object `U` of the small
étale site of `X`, the sheaf of sets in `Type (max (u + 1) s)` represented by `U` is
constructible.

This is `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` at the larger
universe; no `@[stacks 03S8]` attribute is added, the tag being carried there. -/
public theorem isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleFiniteSheaf B X
      ((Sheaf.sheafifiedUliftYoneda.{s} (SmallEtale.topology B X.obj X.property)).obj U) := by
  classical
  obtain ⟨P, hP, hc, hstrata⟩ :=
    hasFiniteEtaleStratification B X U ‹_› ‹_› ⟨‹_›, ‹_›⟩
  choose T i himm hrange hfin het using fun p : {S : Set X.obj // S ∈ P} => hstrata p.1 p.2
  refine isConstructibleFiniteSheaf_of_constructible_immersion_cover B X _ T i himm
    (fun p => (hrange p).symm ▸ hc p.1 p.2) ?_ ?_
  · ext x
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
    obtain ⟨S, ⟨hS, hx⟩, -⟩ := hP.1.2 x
    exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, (hrange ⟨S, hS⟩).symm ▸ hx⟩
  · intro p
    have hlc : Stacks.ConstantSheaf.IsFiniteLocallyConstant
        (SmallEtale.topology B (T p).obj (T p).property)
        ((Sheaf.sheafifiedUliftYoneda.{s}
          (SmallEtale.topology B (T p).obj (T p).property)).obj
            ((smallEtaleBaseChange B (i p)).obj U)) := by
      refine Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
        (Sheaf.sheafifiedUliftYonedaIsoSheafCompose.{s}
          (SmallEtale.topology B (T p).obj (T p).property)
          ((smallEtaleBaseChange B (i p)).obj U)).symm
        (hF := ?_)
      refine Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor.{s}
        (SmallEtale.topology B (T p).obj (T p).property) _ ?_
      exact Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable B (T p) _
        ⟨(smallEtaleBaseChange B (i p)).obj U, hfin p, ⟨Iso.refl _⟩⟩
    have := hlc
    exact isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B (T p) _
      (hF := Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
        (Stacks.Sites.sheafPullbackSheafifiedUliftYonedaIso.{s}
          (smallEtaleBaseChange B (i p))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (T p).obj (T p).property) U).symm)

end AlgebraicGeometry

end
