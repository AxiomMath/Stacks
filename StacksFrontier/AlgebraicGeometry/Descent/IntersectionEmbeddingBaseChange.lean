module

public import StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImage
public import StacksFrontier.AlgebraicGeometry.Descent.StageEmbeddingBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SectionsRingOnSubsetFunctorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffineBaseChange

/-!
# The canonical embedding of an intersection of quasi-compact opens, under flat base change

Let
```
  Z ---k---→ T
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
be a Cartesian square of schemes with `S` and `T` affine, `g` flat and `Y` ind-quasi-affine, let
`E ⊆ Y` be an intersection of a nonempty family of quasi-compact opens and let `W ⊆ E` be open in
`Y`. Writing `j` for the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) at `E` and `j'` for the one at
`p⁻¹E`, this file proves that the inverse image of `j(W)` under the spectrum of the restriction
map on functions is `j'(p⁻¹W)`.

This is the intersection-level form of
`AlgebraicGeometry.preimage_specMap_appLE_image_toSpecΓ`, which is the same statement for a single
quasi-compact open.

## Main results

* `AlgebraicGeometry.Scheme.openToSubset_comp_sectionsRingOnSubsetMap` : restricting the functions
  on an open to a subset and pushing forward along `p` is pulling back along `p` and restricting.
* `AlgebraicGeometry.preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage` : **images are
  preimages at an intersection of quasi-compact opens.**

## Implementation notes

*Why the base change is again ind-quasi-affine.* A morphism of affine schemes is affine, so `p`
is affine as a base change of `g`, and the source of an affine morphism into an ind-quasi-affine
scheme is ind-quasi-affine by `AlgebraicGeometry.IsIndQuasiAffine.of_isAffineHom`. So Tag 0API
applies to `Z` with the family of inverse images of the given quasi-compact opens, and no
hypothesis on `Z` is needed.

*How the two embeddings are compared.* Tag 0API identifies `j(W)` with the inverse image of the
image of `W` at any one stage of the family, along a comparison map which is the spectrum of
`AlgebraicGeometry.Scheme.openToSubset` at that stage. Transporting that identification across
the square therefore only needs the stage-level statement, which is
`AlgebraicGeometry.preimage_specMap_appLE_image_toSpecΓ`, together with the commuting triangle
relating the two restriction maps to the pullback of functions along `p`.

*Why the inverse image of `E` is a hypothesis.* `p⁻¹(⋂ᵢ Uᵢ)` and `⋂ᵢ p⁻¹Uᵢ` are equal but not
definitionally so, and the ring of sections on a subset — hence the type of the conclusion —
depends on the subset. Both readings are therefore named, with their equality a hypothesis, so
that a consumer may supply the one it has.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

/-- **The characterizing property of the restriction from an open to a subset.** Restricting the
functions on an open `V` of `Y` to a subset `E` of `V` and pushing the result forward along
`f : X ⟶ Y` is pulling back along `f` and then restricting the functions on `f⁻¹V` to `E'`. -/
lemma Scheme.openToSubset_comp_sectionsRingOnSubsetMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (E : Set Y) (hE : E ⊆ (V : Set Y)) (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) :
    Y.openToSubset V E hE ≫ Scheme.sectionsRingOnSubsetMap f E E' h =
      f.appLE V (f ⁻¹ᵁ V) le_rfl ≫ X.openToSubset (f ⁻¹ᵁ V) E' (fun _ hx ↦ hE (h hx)) :=
  Scheme.stageToSubset_comp_sectionsRingOnSubsetMap f (fun _ : PUnit.{u + 1} ↦ V) E
    (fun _ ↦ hE) E' h ⟨PUnit.unit⟩

/-- The inverse image of a subset under the spectrum of a composite of ring maps, resolved into
the two inverse images. -/
private lemma preimage_specMap_comp {A B C : CommRingCat.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (O : Set (Spec A)) :
    (Spec.map (a ≫ b)).base ⁻¹' O = (Spec.map b).base ⁻¹' ((Spec.map a).base ⁻¹' O) := by
  rw [Spec.map_comp]
  exact Set.preimage_comp

/-- The inverse image of the image of `W` at one stage of a family of quasi-compact opens, under
the spectrum of the restriction map to the intersection, is the image of `W` at the intersection. -/
private lemma preimage_specMap_openToSubset_image_toSpecΓ {X : Scheme.{u}} [IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) (i : I)
    (W : Set X) (hW : IsOpen W) (hWE : W ⊆ ⋂ j, (U j : Set X)) :
    (Spec.map (X.openToSubset (U i) (⋂ j, (U j : Set X))
        (Set.iInter_subset (fun j ↦ (U j : Set X)) i))).base ⁻¹'
          ((U i).toSpecΓ.base '' {x : U i | (x : X) ∈ W}) =
      subsetΓSpecImage X (⋂ j, (U j : Set X)) W := by
  classical
  obtain ⟨pX, -, -, -, -, hpre, hstage, -⟩ := exists_iInter_iso_iInter_in_specΓ U hU
  refine Eq.trans ?_ (hpre i W hW hWE)
  rw [hstage i]
  rfl

variable {S T Y Z : Scheme.{u}} [IsAffine S] [IsAffine T]
    {πY : Y ⟶ S} {g : T ⟶ S} {p : Z ⟶ Y} {k : Z ⟶ T}

/-- **Images are preimages at an intersection of quasi-compact opens.**  In a Cartesian square
```
  Z ---k---→ T
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
with `S` and `T` affine, `g` flat and `Y` ind-quasi-affine, let `E` be the intersection of a
nonempty family of quasi-compact opens of `Y`, let `E'` be the intersection of their inverse
images, and let `W ⊆ E` be open in `Y`.  Then the inverse image under the spectrum of the
restriction map on functions of the image of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) at `E` is the image of `p⁻¹W` under
the canonical embedding at `E'`.

This is the statement that step 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) reads off its commutative diagram.
-/
theorem preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage
    (H : IsPullback p k πY g) [Flat g] [IsIndQuasiAffine Y]
    {I : Type v} [Nonempty I] (U : I → Y.Opens) (hU : ∀ i, IsCompact (U i : Set Y))
    (E : Set Y) (E' : Set Z) (W : Set Y) (hE : E = ⋂ i, (U i : Set Y))
    (hE' : E' = ⋂ i, ((p ⁻¹ᵁ U i : Z.Opens) : Set Z)) (h : E' ⊆ p.base ⁻¹' E)
    (hWE : W ⊆ E) (hW : IsOpen W) :
    (Spec.map (Scheme.sectionsRingOnSubsetMap p E E' h)).base ⁻¹' subsetΓSpecImage Y E W =
      subsetΓSpecImage Z E' (p.base ⁻¹' W) := by
  classical
  subst hE'
  subst hE
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_isIndQuasiAffine Y
  have hpaff : IsAffineHom p := MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip
    inferInstance
  have : IsIndQuasiAffine Z := IsIndQuasiAffine.of_isAffineHom p
  have hUZ : ∀ i, IsCompact ((p ⁻¹ᵁ U i : Z.Opens) : Set Z) := fun i ↦
    (inferInstance : QuasiCompact p).isCompact_preimage _ (U i).2 (hU i)
  let i : I := Classical.arbitrary I
  have hWZ : p.base ⁻¹' W ⊆ ⋂ j, ((p ⁻¹ᵁ U j : Z.Opens) : Set Z) := fun z hz ↦
    Set.mem_iInter.mpr fun j ↦ Set.mem_iInter.mp (hWE hz) j
  have hcomp : Y.openToSubset (U i) (⋂ j, (U j : Set Y))
        (Set.iInter_subset (fun j ↦ (U j : Set Y)) i) ≫
      Scheme.sectionsRingOnSubsetMap p (⋂ j, (U j : Set Y))
        (⋂ j, ((p ⁻¹ᵁ U j : Z.Opens) : Set Z)) h =
      p.appLE (U i) (p ⁻¹ᵁ U i) le_rfl ≫
        Z.openToSubset (p ⁻¹ᵁ U i) (⋂ j, ((p ⁻¹ᵁ U j : Z.Opens) : Set Z))
          (Set.iInter_subset (fun j ↦ ((p ⁻¹ᵁ U j : Z.Opens) : Set Z)) i) :=
    Scheme.openToSubset_comp_sectionsRingOnSubsetMap p (U i) _ _ _ h
  rw [← preimage_specMap_openToSubset_image_toSpecΓ U hU i W hW hWE,
    ← preimage_specMap_openToSubset_image_toSpecΓ (fun j ↦ p ⁻¹ᵁ U j) hUZ i _
      (hW.preimage p.base.hom.continuous) hWZ,
    ← preimage_specMap_comp, hcomp, preimage_specMap_comp,
    preimage_specMap_appLE_image_toSpecΓ H (U i) (hU i) W hW]

end AlgebraicGeometry

end

end
