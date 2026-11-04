module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence

/-!
# Coherence of the structure sheaf of a finite preimage

Let `f : Y ⟶ X` be a finite morphism of algebraic spaces over a scheme `S` with `X` locally
Noetherian, let `i : Z ⟶ X` be a closed immersion and let `f' : Z' ⟶ Z` be the base change of
`f` along `i`.  The coherence assertion of Stacks 0GF7 is that `𝒢 = f'_*𝒪_{Z'}` is a coherent
`𝒪_Z`-module; its support assertion is
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ`.

## Main results

* `Space.isCoherent_modulePushforward_structureSheaf_preimage_of_isLocallyNoetherian`: the
  coherence assertion of Stacks 0GF7. The version
  `AlgebraicGeometry.Space.isCoherent_modulePushforward_structureSheaf_preimage` takes the case
  of a chart as a hypothesis.

## References

* [Stacks Project, Tag 0GF7](https://stacks.math.columbia.edu/tag/0GF7)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z Z' : AlgebraicSpaces B S hS}

/-- **The coherence assertion of Stacks 0GF7.**  Let `f : Y ⟶ X` be a finite morphism of
algebraic spaces over `S` with `X` locally Noetherian, let `i : Z ⟶ X` be a closed immersion,
and let `f' : Z' ⟶ Z` be the base change of `f` along `i`.  Then `𝒢 = f'_*𝒪_{Z'}` is a
coherent `𝒪_Z`-module.

`Z` is locally Noetherian by Stacks 06ED and 04ZK, `f'` is finite by Stacks 03ZS, `Z'` is
locally Noetherian for the same reason as `Z`, and `𝒪_{Z'}` is then coherent by Stacks 07UB; so
this is Stacks 07UH,
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`.
Surjectivity of `f` is not used. -/
@[stacks 0GF7 "coherence of the direct image"]
theorem isCoherent_modulePushforward_structureSheaf_preimage_of_isLocallyNoetherian (f : Y ⟶ X)
    (i : Z ⟶ X) {i' : Z' ⟶ Y} {f' : Z' ⟶ Z} (sq : IsPullback i' f' f i)
    (hf : IsFinite B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hi : IsClosedImmersion B S hS i.hom) :
    IsCoherent B S hS Z.1 Z.2 ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS Z'))) := by
  have hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.2 X.2 i.hom
      (isLocallyOfFiniteType_of_isImmersion B S hS i.hom
        (isImmersion_of_isClosedImmersion B S hS hi)) hX
  have hf' : IsFinite B S hS f'.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hZ' : HasEtaleLocalProperty B S hS Z'.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z'.2 Z.2 f'.hom
      (isLocallyOfFiniteType_of_isFinite B S hS Z'.2 Z.2 hf') hZ
  have : Fact (HasEtaleLocalProperty B S hS Z'.1
    (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hZ'⟩
  exact isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hZ _
    (isCoherent_structureSheaf B S hS Z'.1 Z'.2)

end AlgebraicGeometry.Space

end
