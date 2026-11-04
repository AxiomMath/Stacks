module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperIsomorphismOverOpenBlowup
import all StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence

/-!
# A proper morphism which is an isomorphism over a quasi-compact open, after a blowup

Let `f : X ⟶ A` be a proper morphism of algebraic spaces over a scheme `S` and let `U ⊆ A` be a
quasi-compact open subspace, with `A` quasi-compact and quasi-separated, such that
`f⁻¹(U) ⟶ U` is an isomorphism. Stacks 0GUW says that there is a `U`-admissible blowup
`A' ⟶ A` such that the strict transform of `X` maps isomorphically to `A'`.

This is `exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper`, whose two inputs are
the statements of Stacks 07VR and 0873. Both are discharged here: Stacks 07VR is
`exists_integralFiniteSystem_of_isFinite`, and Stacks 0873 is the factorization of a separated
morphism of finite type proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence`.

## Main results

* `exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper_unconditional`:
  after a `U`-admissible blowup `A' ⟶ A`, the strict transform of `X` maps isomorphically to `A'`.

## References

* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is proper
and that `f⁻¹(U) ⟶ U` (the restriction `X ×_A U ⟶ U`) is an isomorphism. Then there is a
`U`-admissible blowup `b : A' ⟶ A` -- the blowup of `A` in a closed subspace `Z` of finite
presentation whose points avoid those of `U` -- such that the strict transform of `X` with
respect to `b` maps isomorphically to `A'`. -/
@[stacks 0GUW]
theorem exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper_unconditional
    {A X : AlgebraicSpaces B S hS} (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hf : IsProper B S hS f.hom) (hiso : IsIso (pullback.snd f.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsIso (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom :=
  exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper B.contains_terminal f U
    hAqc hAqs hUqc hf hiso
    (fun g hX' hY' hg hY'qc hY'qs ↦
      exists_integralFiniteSystem_of_isFinite B S hS g hX' hY' hg hY'qc hY'qs)
    (fun g hX' hY' hgft hgsep hY'qc hY'qs ↦
      exists_closedImmersion_separated_finitePresentation_of_finiteType B S hS g hX' hY' hgft
        hgsep hY'qc hY'qs)

end AlgebraicGeometry.Space

end
