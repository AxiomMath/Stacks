module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Gluing morphisms over the preimages of the affine opens of the target

Let `f : T ⟶ S` be a morphism of schemes. The preimages `f⁻¹(U)`, for `U` an affine open of
`S`, cover `T`, and they are directed: if `U ≤ V` then `f⁻¹(U) ≤ f⁻¹(V)`. Consequently a
morphism out of `T` may be assembled from morphisms on the `f⁻¹(U)` which are compatible with
these inclusions, with no condition on overlaps, and two morphisms out of `T` agreeing on every
`f⁻¹(U)` are equal.

## Main definitions

* `AlgebraicGeometry.Scheme.preimageIsoPullback` identifies `f⁻¹(U)` with the fibre product
  `T ×_S U`.
* `AlgebraicGeometry.Scheme.glueOverAffinePullbacks` and
  `AlgebraicGeometry.Scheme.glueOverAffinePreimages` assemble a morphism out of `T` from
  compatible morphisms on the fibre products `T ×_S U`, respectively on the preimages
  `f⁻¹(U)`.

## Main results

* `AlgebraicGeometry.Scheme.fst_comp_glueOverAffinePullbacks` and
  `AlgebraicGeometry.Scheme.ι_glueOverAffinePreimages` compute the restriction of the glued
  morphism to each piece.
* `AlgebraicGeometry.Scheme.hom_ext_of_affinePullbacks` and
  `AlgebraicGeometry.Scheme.hom_ext_of_affinePreimages` are the corresponding extensionality
  statements.

## Implementation notes

The directedness is Mathlib's `AlgebraicGeometry.Scheme.Cover.locallyDirectedPullbackCover` for
the cover of `S` by all its affine opens, whose pieces are the fibre products `T ×_S U`. The
fibre-product form of the statements is therefore the primitive one, and the form phrased in
terms of the open subschemes `f⁻¹(U)` is deduced from it through
`AlgebraicGeometry.isPullback_morphismRestrict`.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {S T Y : Scheme.{u}}

/-! ### The preimage of an open as a fibre product -/

/-- The preimage of an open `U` of `S` along `f : T ⟶ S`, as the fibre product `T ×_S U`. -/
noncomputable def preimageIsoPullback (f : T ⟶ S) (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme ≅ pullback f U.ι :=
  (isPullback_morphismRestrict f U).flip.isoPullback

/-- Composed with the first projection `T ×_S U ⟶ T`, the identification `f⁻¹(U) ≅ T ×_S U` is
the inclusion of `f⁻¹(U)` in `T`. -/
@[reassoc]
lemma preimageIsoPullback_hom_fst (f : T ⟶ S) (U : S.Opens) :
    (preimageIsoPullback f U).hom ≫ pullback.fst f U.ι = (f ⁻¹ᵁ U).ι :=
  (isPullback_morphismRestrict f U).flip.isoPullback_hom_fst

/-- Composed with the inclusion of `f⁻¹(U)` in `T`, the inverse of the identification
`f⁻¹(U) ≅ T ×_S U` is the first projection `T ×_S U ⟶ T`. -/
@[reassoc]
lemma preimageIsoPullback_inv_comp_ι (f : T ⟶ S) (U : S.Opens) :
    (preimageIsoPullback f U).inv ≫ (f ⁻¹ᵁ U).ι = pullback.fst f U.ι := by
  rw [← preimageIsoPullback_hom_fst, Iso.inv_hom_id_assoc]

/-- The identification of the preimages with the fibre products carries the inclusion
`f⁻¹(U) ⟶ f⁻¹(V)` attached to `U ≤ V` to the canonical map of fibre products. -/
@[reassoc]
lemma map_comp_preimageIsoPullback_inv (f : T ⟶ S) {U V : S.Opens} (h : U ≤ V) :
    pullback.map f U.ι f V.ι (𝟙 T) (S.homOfLE h) (𝟙 S) (by simp) (by simp) ≫
        (preimageIsoPullback f V).inv =
      (preimageIsoPullback f U).inv ≫ T.homOfLE (f.preimage_mono h) := by
  apply (cancel_mono (f ⁻¹ᵁ V).ι).mp
  simp only [Category.assoc, preimageIsoPullback_inv_comp_ι, Scheme.homOfLE_ι]
  rw [pullback.lift_fst, Category.comp_id]

/-! ### Gluing over the fibre products -/

section

variable (f : T ⟶ S) (g : ∀ U : S.affineOpens, pullback f U.1.ι ⟶ Y)
  (hg : ∀ (U V : S.affineOpens) (h : U.1 ≤ V.1),
    pullback.map f U.1.ι f V.1.ι (𝟙 T) (S.homOfLE h) (𝟙 S) (by simp) (by simp) ≫ g V = g U)

include hg

/-- A morphism out of `T` assembled from morphisms on the fibre products `T ×_S U`, for `U` an
affine open of `S`, that are compatible with the canonical maps between them. -/
noncomputable def glueOverAffinePullbacks : T ⟶ Y :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    (S.directedAffineCover.pullback₁ f : T.OpenCover) g
    fun {i j} hij => hg i j (leOfHom hij)

/-- The restriction of `glueOverAffinePullbacks f g hg` to the fibre product `T ×_S U` is
`g U`. -/
@[reassoc]
lemma fst_comp_glueOverAffinePullbacks (U : S.affineOpens) :
    pullback.fst f U.1.ι ≫ glueOverAffinePullbacks f g hg = g U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
    (S.directedAffineCover.pullback₁ f : T.OpenCover) g
    (fun {i j} hij => hg i j (leOfHom hij)) U

end

/-- Two morphisms out of `T` which agree on the fibre product `T ×_S U` for every affine open
`U` of `S` are equal. -/
lemma hom_ext_of_affinePullbacks (f : T ⟶ S) {a b : T ⟶ Y}
    (h : ∀ U : S.affineOpens, pullback.fst f U.1.ι ≫ a = pullback.fst f U.1.ι ≫ b) : a = b :=
  Scheme.Cover.hom_ext (S.directedAffineCover.pullback₁ f : T.OpenCover) a b h

/-! ### Gluing over the preimages -/

section

variable (f : T ⟶ S) (g : ∀ U : S.affineOpens, (f ⁻¹ᵁ U.1).toScheme ⟶ Y)
  (hg : ∀ (U V : S.affineOpens) (h : U.1 ≤ V.1), T.homOfLE (f.preimage_mono h) ≫ g V = g U)

include hg

/-- A morphism out of `T` assembled from morphisms on the preimages of the affine opens of `S`
that are compatible with the inclusions between those preimages. -/
noncomputable def glueOverAffinePreimages : T ⟶ Y :=
  glueOverAffinePullbacks f (fun U => (preimageIsoPullback f U.1).inv ≫ g U) <| by
    intro U V h
    rw [← Category.assoc, map_comp_preimageIsoPullback_inv, Category.assoc, hg U V h]

/-- The restriction of `glueOverAffinePreimages f g hg` to the preimage `f⁻¹(U)` is `g U`. -/
@[reassoc]
lemma ι_glueOverAffinePreimages (U : S.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ glueOverAffinePreimages f g hg = g U := by
  rw [← preimageIsoPullback_hom_fst, Category.assoc, glueOverAffinePreimages,
    fst_comp_glueOverAffinePullbacks, Iso.hom_inv_id_assoc]

end

/-- Two morphisms out of `T` which agree on the preimage of every affine open of `S` are
equal. -/
lemma hom_ext_of_affinePreimages (f : T ⟶ S) {a b : T ⟶ Y}
    (h : ∀ U : S.affineOpens, (f ⁻¹ᵁ U.1).ι ≫ a = (f ⁻¹ᵁ U.1).ι ≫ b) : a = b := by
  refine hom_ext_of_affinePullbacks f fun U => ?_
  rw [← preimageIsoPullback_inv_comp_ι, Category.assoc, Category.assoc, h]

end AlgebraicGeometry.Scheme

end
