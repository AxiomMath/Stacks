module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentablePresentation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
import StacksCore.Tactic.StacksAttribute

/-!
# A finite presentation by representables makes a sheaf of sets constructible

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site. Stacks 09Y9 says that
the constructible sheaves of sets on `X_étale` are exactly the sheaves occurring as coequalizers
`F₁ ⇉ F₀ → F` of two maps between finite coproducts of sheaves `h_U` represented by quasi-compact
and quasi-separated objects `U` of `X_étale`. This file proves the implication from such a
presentation to constructibility, assuming nothing beyond quasi-compactness and
quasi-separatedness of `X`.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_of_hasFiniteQCSRepresentableCoequalizerPresentation`
  — the direction of Stacks 09Y9 that reads a presentation as a proof of constructibility.

## Implementation notes

The argument is the one the source points back to in its proof of Stacks 03SA. Each `h_U` at a
quasi-compact quasi-separated étale object is a constructible sheaf of sets, which is
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs`, the library's
Stacks 03S8 (1); and
constructible sheaves of sets are closed under finite colimits, which is
`AlgebraicGeometry.isConstructibleSetSheaf_colimit`, the library's Stacks 03RZ (1). A finite
coproduct is a colimit over a finite discrete category and a coequalizer is a colimit over
`CategoryTheory.Limits.WalkingParallelPair`, which is finite as well, so the second statement
applies twice: once to each of the two coproducts and once to the coequalizer of the pair of maps
between them.

The reverse implication of Stacks 09Y9, from constructibility to the existence of a presentation,
is a different matter and is not proved here: it passes through Stacks 03RV on the strata of a
constructible stratification, hence through effective descent of representability by a finite
étale scheme along an étale covering, which the library does not have in that shape.

## References

* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 2000] Sheaf.instHasFiniteColimits

/-- A finite coproduct of sheaves represented by quasi-compact quasi-separated étale objects of
the small étale site of a quasi-compact quasi-separated scheme is a constructible sheaf of
sets. -/
private theorem isConstructibleSetSheaf_sigma_representable (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {k : ℕ}
    (W : Fin k → SmallEtale B X.obj X.property)
    (hW : ∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (W i)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (W i))) :
    IsConstructibleSetSheaf B X
      (∐ fun i =>
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (W i)) := by
  refine isConstructibleSetSheaf_colimit B X (Discrete.functor fun i =>
    (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (W i)) ?_
  rintro ⟨i⟩
  have hc : CompactSpace (W i).obj.left.obj := (hW i).1
  have hq : QuasiSeparatedSpace (W i).obj.left.obj := (hW i).2
  exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X (W i)

/-- **Stacks 09Y9, the implication from a presentation to constructibility.** Let `X` be a
quasi-compact and quasi-separated scheme of a big étale site and let `F` be a sheaf of sets on
`X_étale` which is a coequalizer of two maps between finite coproducts of sheaves represented by
quasi-compact and quasi-separated objects of `X_étale`. Then `F` is a constructible sheaf of
sets. -/
@[stacks 09Y9 "the implication from a finite coequalizer presentation by representables of \
quasi-compact quasi-separated etale objects to constructibility, for sheaves of sets; the \
reverse implication, from constructibility to the existence of such a presentation, is not part \
of this statement", sga "4 IX 2.7" "Sheaves of sets", sga "4 IX 2.7.1" "Sufficiency"]
public theorem isConstructibleSetSheaf_of_hasFiniteQCSRepresentableCoequalizerPresentation
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : HasFiniteQCSRepresentableCoequalizerPresentation B X F) :
    IsConstructibleSetSheaf B X F := by
  obtain ⟨n, m, U, V, hU, hV, f, g, ⟨e⟩⟩ := hF
  refine isConstructibleSetSheaf_congr B X e ?_
  refine isConstructibleSetSheaf_colimit B X (parallelPair f g) ?_
  rintro (_ | _)
  · exact isConstructibleSetSheaf_sigma_representable B X V hV
  · exact isConstructibleSetSheaf_sigma_representable B X U hU

end AlgebraicGeometry

end
