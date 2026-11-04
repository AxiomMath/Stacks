module

public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumInvariantSet
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.IntersectionEmbedding

/-!
# The image of an open under the canonical embedding of an intersection, as an open subscheme

Let `X` be an ind-quasi-affine scheme, let `E ⊆ X` be an intersection of a nonempty family of
quasi-compact opens, and write `C = Γ(E, 𝒪_X|_E)`. Stacks 0API provides the canonical embedding
`j : (E, 𝒪_X|_E) ⟶ Spec C` of locally ringed spaces and says that `j` carries a subset of `E`
which is open in `X` to an open subset of `Spec C`; that last assertion is proved as
`AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen`.

Step 5 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) needs `j(W)`
not as an open *subset* of the topological space of `Spec C` but as an `AlgebraicGeometry.Opens`
of the scheme `Spec C`, because that is what the descent of opens along a faithfully flat ring
map — `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout`, and through it
`AlgebraicGeometry.ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` —
consumes. This file performs that repackaging, and records it for the `W ⊆ E` produced by step 3
of the proof of Tag 0APK.

## Main definitions

* `AlgebraicGeometry.subsetΓSpecImage` : the image `j(W)` of a subset `W ⊆ E` under the canonical
  map, as a subset of `Spec Γ(E, 𝒪_X|_E)`.
* `AlgebraicGeometry.subsetΓSpecOpens` : the same image as an open subscheme of
  `Spec Γ(E, 𝒪_X|_E)`, for `W` open in `X`.

## Main results

* `AlgebraicGeometry.coe_subsetΓSpecOpens` : the underlying set of that open subscheme is the
  image.
* `AlgebraicGeometry.DescentDatum.exists_opens_coe_eq_subsetΓSpecImage` : for a descent datum
  over an affine base whose underlying scheme is ind-quasi-affine over it, the image of an open
  `W` contained in an intersection `E` of a nonempty family of quasi-compact opens is an open
  subscheme of `Spec Γ(E, 𝒪_V|_E)`. This is the shape in which step 5 of the proof of Tag 0APK
  receives `j(W)`.

## Implementation notes

*Why no comparison isomorphism is needed.* The target of
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec` for the locally ringed space
`AlgebraicGeometry.subsetLocallyRingedSpace X.toLocallyRingedSpace E` is
`Spec.toLocallyRingedSpace.obj (op (LocallyRingedSpace.Γ.obj (op _)))`, and both
`LocallyRingedSpace.Γ.obj (op (subsetLocallyRingedSpace X.toLocallyRingedSpace E)) =
Scheme.sectionsRingOnSubset X E` and the comparison of the underlying topological spaces with
that of the scheme `Spec (Scheme.sectionsRingOnSubset X E)` are definitional — the first is
recorded as `rfl` inside the proof of
`AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ`. So the image set may be *stated* as a
subset of the scheme `Spec Γ(E, 𝒪_X|_E)` with no transport.

*What is still owed for step 5.* The hypothesis `hcompat` of
`AlgebraicGeometry.ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` asks
in addition that the two preimages of `j(W)` under the projections of
`Spec C ×_{Spec C₀} Spec C` agree. In the source that is read off the commutative diagram
relating `j` to the maps `j'` and `j''` of `E ×_S X ⊆ V ×_S X` and `X ×_S E ⊆ X ×_S V`, and it is
*not* proved here: the library has functoriality of the ring of sections on a subset
(`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`) but no functoriality of
`AlgebraicGeometry.subsetLocallyRingedSpace` itself, hence no naturality statement for `j`. See
the report accompanying this file for the exact signature that is wanted.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- The image of a subset `W` of `E` under the canonical map
`j : (E, 𝒪_X|_E) ⟶ Spec Γ(E, 𝒪_X|_E)` of Stacks 0API, as a subset of the scheme
`Spec Γ(E, 𝒪_X|_E)`. -/
def subsetΓSpecImage (X : Scheme.{u}) (E W : Set X) : Set (Spec (X.sectionsRingOnSubset E)) :=
  (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base '' { x : E | (x : X) ∈ W }

/-- **The image of an open under the canonical embedding of an intersection, as an open
subscheme.**  For `X` ind-quasi-affine, `E` an intersection of a nonempty family of quasi-compact
opens of `X`, and `W ⊆ E` open in `X`, the image `j(W)` is an open subscheme of
`Spec Γ(E, 𝒪_X|_E)`.

Openness is `AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen`, which is Stacks 0API's last
assertion; this is that assertion packaged as an `AlgebraicGeometry.Scheme.Opens`, which is what
the descent of opens along a faithfully flat ring map consumes. -/
def subsetΓSpecOpens (X : Scheme.{u}) [IsIndQuasiAffine X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) (E W : Set X)
    (hE : E = ⋂ i, (U i : Set X)) (hWE : W ⊆ E) (hW : IsOpen W) :
    (Spec (X.sectionsRingOnSubset E)).Opens :=
  ⟨subsetΓSpecImage X E W, isOpen_image_toΓSpec_of_isOpen X U hU E W hE hWE hW⟩

/-- The underlying set of `AlgebraicGeometry.subsetΓSpecOpens` is the image `j(W)`. -/
lemma coe_subsetΓSpecOpens (X : Scheme.{u}) [IsIndQuasiAffine X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) (E W : Set X)
    (hE : E = ⋂ i, (U i : Set X)) (hWE : W ⊆ E) (hW : IsOpen W) :
    (subsetΓSpecOpens X U hU E W hE hWE hW : Set (Spec (X.sectionsRingOnSubset E))) =
      subsetΓSpecImage X E W := rfl

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **Step 5 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
receives `j(W)` as an open subscheme of `Spec Γ(E, 𝒪_V|_E)`.**  Let `D` be a descent datum
relative to `f : X ⟶ S` with `X` affine and `V ⟶ X` ind-quasi-affine, let `E ⊆ V` be an
intersection of a nonempty family of quasi-compact opens, and let `W ⊆ E` be open.  Then the
image of `W` under the canonical map `j` of Stacks 0API is an open subscheme of
`Spec Γ(E, 𝒪_V|_E)`.

Ind-quasi-affineness of `V` itself — which is what Stacks 0API asks for — is read off the
morphism `V ⟶ X` by `AlgebraicGeometry.isIndQuasiAffine_of_isIndQuasiAffineHom_hom`, exactly as
in the step-3 statements. -/
theorem exists_opens_coe_eq_subsetΓSpecImage [IsAffine X] [IsIndQuasiAffineHom D.over.hom]
    {I : Type v} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (E W : Set D.over.left)
    (hE : E = ⋂ i, (U i : Set D.over.left)) (hWE : W ⊆ E) (hW : IsOpen W) :
    ∃ W₀ : (Spec (D.over.left.sectionsRingOnSubset E)).Opens,
      (W₀ : Set (Spec (D.over.left.sectionsRingOnSubset E))) =
        subsetΓSpecImage D.over.left E W := by
  have : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  exact ⟨subsetΓSpecOpens D.over.left U hU E W hE hWE hW,
    coe_subsetΓSpecOpens D.over.left U hU E W hE hWE hW⟩

end DescentDatum

end AlgebraicGeometry

end

end
