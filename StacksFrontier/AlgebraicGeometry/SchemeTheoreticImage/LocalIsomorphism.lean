module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.RegularStalkAt
public import StacksFrontier.AlgebraicGeometry.RestrictIso
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Where a morphism is a closed immersion it is an isomorphism onto its scheme-theoretic image

Let `f : X ⟶ Y` be quasi-compact with `X` reduced, and let `R` be an open of `Y` over which the
restriction `f ∣_ R` is a closed immersion. Then the morphism `f.toImage` onto the
scheme-theoretic image is an *isomorphism* over the part of the image lying in `R`, and
consequently `f.toImage` is étale at every point of `X` that `f` carries into `R`.

Both halves come from the factorization `f = f.toImage ≫ f.imageι` restricted over `R`: the
second factor is a closed immersion, so the first is one too by cancellation, and it is dominant
because `f.toImage` is and dominance is local at the target. A dominant closed immersion into a
reduced scheme is an isomorphism.

This is the step of the proof of Stacks 0B0E which turns the conclusion of Tag 0B1Q part (1) —
that `r_p|_X` is a closed immersion over a neighbourhood of `r_p(x)` — into the statement that
`X ⟶ r_p(X)` is a *local isomorphism* at `x`, which is what carries the chosen points of the
source's induction from one stage of the chain of projections to the next.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_toImage`: `f.toImage` is an isomorphism
  over `f.imageι ⁻¹ᵁ R`.
* `AlgebraicGeometry.Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict`:
  `f.toImage` is étale at every point of `X` whose image lies in `R`.
* `AlgebraicGeometry.Scheme.Hom.mem_regularLocus_toImage_of_isClosedImmersion_morphismRestrict`:
  such a point stays in the regular locus when carried onto the image.
* `AlgebraicGeometry.Scheme.Hom.injOn_of_isIso_morphismRestrict` and
  `AlgebraicGeometry.Scheme.Hom.exists_isOpen_forall_inter_preimage_image_subset_toImage`: on the
  inverse image of `R` the morphism onto the image is injective, so that near such a point every
  subset of `X` is the whole inverse image of its own image.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- **A morphism which is a closed immersion over an open of the target is an isomorphism onto
its scheme-theoretic image there.** For `f` quasi-compact with reduced source and `R` an open of
the target over which `f ∣_ R` is a closed immersion, the morphism `f.toImage` onto the
scheme-theoretic image restricts to an isomorphism over `f.imageι ⁻¹ᵁ R`.

The restriction of `f.toImage` is a closed immersion by cancelling the closed immersion
`f.imageι ∣_ R` out of `f ∣_ R`, and it is dominant because `f.toImage` is and dominance is local
at the target; a dominant closed immersion has dense closed image, hence is surjective, and a
surjective closed immersion into a reduced scheme is an isomorphism. -/
@[ega "I 9.5.10" "special case"]
public theorem isIso_morphismRestrict_toImage (f : X ⟶ Y) [QuasiCompact f] [IsReduced X]
    (R : Y.Opens) (h : IsClosedImmersion (f ∣_ R)) :
    IsIso (f.toImage ∣_ f.imageι ⁻¹ᵁ R) := by
  have h1 : IsClosedImmersion (f.imageι ∣_ R) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance R
  -- the factorization is an equality of morphisms, so it is transported by generalizing the
  -- morphism rather than by rewriting under `∣_`, whose source scheme depends on it
  have hgen : ∀ g : X ⟶ Y, g = f → IsClosedImmersion (g ∣_ R) := fun _ hg => hg ▸ h
  have h2 := hgen (f.toImage ≫ f.imageι) f.toImage_imageι
  rw [morphismRestrict_comp] at h2
  have hci : IsClosedImmersion (f.toImage ∣_ f.imageι ⁻¹ᵁ R) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _
      (f.toImage ∣_ f.imageι ⁻¹ᵁ R) (f.imageι ∣_ R) h1 h2
  have hdom : IsDominant (f.toImage ∣_ f.imageι ⁻¹ᵁ R) :=
    IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance _
  have : Surjective (f.toImage ∣_ f.imageι ⁻¹ᵁ R) :=
    surjective_of_isDominant_of_isClosed_range _
      (f.toImage ∣_ f.imageι ⁻¹ᵁ R).isClosedEmbedding.isClosed_range
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The inverse image of `R` under `f.imageι`, pulled back along `f.toImage`, is `f ⁻¹ᵁ R`. -/
private theorem preimage_toImage_imageι (f : X ⟶ Y) [QuasiCompact f] [IsReduced X]
    (R : Y.Opens) : f.toImage ⁻¹ᵁ (f.imageι ⁻¹ᵁ R) = f ⁻¹ᵁ R := by
  rw [← Scheme.Hom.comp_preimage, f.toImage_imageι]

/-- **Étaleness of the morphism onto the scheme-theoretic image at a point carried into the
open.** In the situation of
`AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_toImage`, the morphism `f.toImage` is étale
at every point `x` of `X` with `f x ∈ R`: on the open `f ⁻¹ᵁ R` it is an isomorphism followed by
the inclusion of an open, both of which are étale. -/
public theorem etaleAt_toImage_of_isClosedImmersion_morphismRestrict (f : X ⟶ Y) [QuasiCompact f]
    [IsReduced X] (R : Y.Opens) (h : IsClosedImmersion (f ∣_ R)) {x : X} (hx : f.base x ∈ R) :
    EtaleAt f.toImage x := by
  have := isIso_morphismRestrict_toImage f R h
  rw [etaleAt_iff_exists_open]
  refine ⟨f.toImage ⁻¹ᵁ (f.imageι ⁻¹ᵁ R), by rw [preimage_toImage_imageι]; exact hx, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- **A nonsingular point carried into the open stays nonsingular on the scheme-theoretic
image.** In the situation of
`AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_toImage`, a point `y` of the regular locus
of `X` with `f y ∈ R` has `f.toImage y` in the regular locus of `f.image`.

`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt` is an *iff*, so this runs in the
forward direction from étaleness of `f.toImage` at `y`, which
`AlgebraicGeometry.Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict` already
establishes from the data at hand. In the chain of projections of Stacks 0B0E that is what makes
the chosen points nonsingular on the image at each stage: the regularity needed to apply a
generic-projection lemma at a stage comes from the local isomorphism established at that same
stage, not from étaleness at the next one. -/
public theorem mem_regularLocus_toImage_of_isClosedImmersion_morphismRestrict (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] (R : Y.Opens) (h : IsClosedImmersion (f ∣_ R)) {y : X}
    (hy : f.base y ∈ R) (hreg : y ∈ regularLocus X) :
    f.toImage.base y ∈ regularLocus f.image :=
  (isRegularLocalRing_stalk_iff_of_etaleAt f.toImage
    (etaleAt_toImage_of_isClosedImmersion_morphismRestrict f R h hy)).mp hreg

/-! ### Separating a subset from its image -/

/-- **A morphism which restricts to an isomorphism over an open of the target is injective on the
inverse image of that open.** -/
public theorem injOn_of_isIso_morphismRestrict (f : X ⟶ Y) (R : Y.Opens) [IsIso (f ∣_ R)] :
    Set.InjOn f.base (f ⁻¹ᵁ R : Set X) := by
  have key : ∀ (z : X) (hz : z ∈ (f ⁻¹ᵁ R : Set X)),
      R.ι.base ((f ∣_ R).base ⟨z, hz⟩) = f.base z := by
    intro z hz
    have h : (f ∣_ R ≫ R.ι).base ⟨z, hz⟩ = ((f ⁻¹ᵁ R).ι ≫ f).base ⟨z, hz⟩ := by
      rw [morphismRestrict_ι]
    exact h
  intro x hx y hy hxy
  have h3 : (f ∣_ R).base ⟨x, hx⟩ = (f ∣_ R).base ⟨y, hy⟩ :=
    R.ι.isOpenEmbedding.injective (by rw [key x hx, key y hy, hxy])
  exact congrArg Subtype.val ((f ∣_ R).homeomorph.injective h3)

/-- A function is separated from its images by the inverse image of a set on which it is
injective: a point of `u ⁻¹' O` whose value is a value taken on `S` lies in `S`, because the
point of `S` taking that value also lies in `u ⁻¹' O`. -/
public theorem inter_preimage_image_subset_of_injOn_preimage {A B : Type*} (u : A → B)
    (O : Set B) (hinj : Set.InjOn u (u ⁻¹' O)) (S : Set A) :
    (u ⁻¹' O) ∩ u ⁻¹' (u '' S) ⊆ S := by
  rintro y ⟨hyO, s, hsS, hs⟩
  have hsO : s ∈ u ⁻¹' O := by rw [Set.mem_preimage, hs]; exact hyO
  exact hinj hsO hyO hs ▸ hsS

/-- **One stage of the chain of projections of Stacks 0B0E separates every subset from its
image.** For `f` quasi-compact with reduced source, a closed immersion over an open `R` of the
target, and a point `x` with `f x ∈ R`, there is an open neighbourhood `V` of `x` such that
every subset `S` of `X` contains all the points of `V` that `f.toImage` carries into
`f.toImage (S)`.

`V` is the inverse image of `R`, on which `f.toImage` is an isomorphism onto an open of its
image by `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_toImage`. The conclusion is in the
form which composes along the chain, and it is what makes the chosen point of `Z` miss every
component of `π^{-1}(π(Z))` other than `Z` at the stages where the projection is injective near
the point — all of them but the last. -/
public theorem exists_isOpen_forall_inter_preimage_image_subset_toImage (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] (R : Y.Opens) (h : IsClosedImmersion (f ∣_ R)) {x : X}
    (hx : f.base x ∈ R) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ S : Set X, V ∩ f.toImage.base ⁻¹' (f.toImage.base '' S) ⊆ S := by
  have := isIso_morphismRestrict_toImage f R h
  have hVeq : (f ⁻¹ᵁ R : Set X) =
      f.toImage.base ⁻¹' ((f.imageι ⁻¹ᵁ R : f.image.Opens) : Set f.image) := by
    rw [← preimage_toImage_imageι f R]; rfl
  refine ⟨(f ⁻¹ᵁ R : Set X), (f ⁻¹ᵁ R).isOpen, hx, fun S => ?_⟩
  rw [hVeq]
  exact inter_preimage_image_subset_of_injOn_preimage _ _
    (hVeq ▸ injOn_of_isIso_morphismRestrict f.toImage (f.imageι ⁻¹ᵁ R)) S

end AlgebraicGeometry.Scheme.Hom

end
