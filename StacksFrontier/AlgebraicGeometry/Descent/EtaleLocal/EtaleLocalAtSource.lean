module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# Étaleness is étale local on the source and target

Étaleness of a morphism of schemes is étale local on the source and target in the sense of
Tag 04QZ, which is the étale entry of the list of Tag 04R3; that statement is what the Tag 0AML
and Tag 0AMM statements for algebraic spaces take as input for étaleness.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, the étale case —
  étaleness of a morphism of schemes is étale local on the source and target.

## Implementation notes

Locality on the base — Tag 02VN and the étale entry of Tag 02WH — is
`AlgebraicGeometry.etale_isLocalAtTarget_fpqc` and
`AlgebraicGeometry.etale_isLocalAtTarget_fppf` of
`StacksFrontier/AlgebraicGeometry/Descent/EtaleFpqcLocalAtTarget.lean`, which this file imports.

Étale locality on the source and target is Mathlib's splitting
`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified` of étaleness into flatness, formal
unramifiedness and local finite presentation. The flat and locally-of-finite-presentation cases
of Tag 04R3 are already available, and formal unramifiedness is read off the unramified case
through Tag 02HE: in a commuting square of étale neighbourhoods the top morphism is étale, hence
unramified (Tag 03II), so the unramified case applies and its conclusion splits into local
finite type and formal unramifiedness. No new descent argument is needed, and in particular the
fibre-degree induction of Tag 04R2 is not used. The two remaining conditions of Tag 04QZ are
instances: étale morphisms compose, and étaleness is stable under base change.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 04R3, the étale case.** Being an étale morphism of schemes is étale local on the
source and target.

The local criterion is reduced, through
`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`, to the flat and
locally-of-finite-presentation cases of [Stacks Project, Tag 04R3] together with its unramified
case, from which formal unramifiedness is extracted by [Stacks Project, Tag 02HE]. -/
@[stacks 04R3 "etale", ega "IV 17.3.2" "partial"]
theorem etale_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Etale.{u} : MorphismProperty Scheme.{u}) where
  precomp :=
    { precomp := fun i hi f hf => by
        have : Etale i := hi
        have : Etale f := hf
        exact inferInstance }
  pullbackSnd_of_etale f hf g _ := by
    have : MorphismProperty.IsStableUnderBaseChange (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      Etale.etale_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) hf
  iff_forall_exists_etale_neighborhood {X Y} f := by
    refine ⟨fun hf x => ⟨X, Y, 𝟙 X, 𝟙 Y, f, x, inferInstance, inferInstance, by simp, by simp,
      hf⟩, fun hloc => ?_⟩
    choose U V a b h u ha hb hu hsq hP using hloc
    have key : ∀ {P : MorphismProperty Scheme.{u}}, IsEtaleLocalOnSourceAndTarget P →
        (∀ x, P (h x)) → P f := fun hP' hPh =>
      (hP'.iff_forall_exists_etale_neighborhood f).mpr fun x =>
        ⟨U x, V x, a x, b x, h x, u x, ha x, hb x, hu x, hsq x, hPh x⟩
    have hflat : Flat f :=
      key Flat.isEtaleLocalOnSourceAndTarget fun x => by have := hP x; infer_instance
    have hpres : LocallyOfFinitePresentation f :=
      key LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget fun x => by
        have := hP x; infer_instance
    have hunr : Unramified f :=
      key unramified_isEtaleLocalOnSourceAndTarget fun x => unramified_of_etale (h x)
    have := hflat
    have := hpres
    have := ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp hunr).2
    exact Etale.of_formallyUnramified_of_flat f

end AlgebraicGeometry

end
