module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChangeMorphism
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePullbackGlobalSections

/-!
# The coordinate rings of a base-changed affine groupoid

A base change `bc : AffineInvariantBaseChange G C₁` of an affine groupoid scheme comes with a
cartesian square exhibiting its object scheme as `U ×_{Spec C} Spec C₁`. The square of global
functions is then cocartesian, which identifies the coordinate ring of the object scheme of the
base change with `A ⊗[C] C₁`: on the left tensor factor the identification is pullback of global
functions along the projection to `U`, and on the right tensor factor it is pullback along the
structure morphism to `Spec C₁`. The same holds for the arrow scheme, and for the base change of
a source groupoid along a morphism of groupoid schemes.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.objectsBaseChangeIso`: **the coordinate ring of the object
  scheme of a base change is `A ⊗[C] C₁`**, compatibly with the projection to `U`.
* `AlgebraicGeometry.GroupoidScheme.arrowsBaseChangeIso`: the same for the arrow scheme, where
  the invariant ring acts on the arrow ring through the source map.

## Main results

* `AlgebraicGeometry.GroupoidScheme.objectsBaseChangeIso_includeLeft` and
  `AlgebraicGeometry.GroupoidScheme.objectsBaseChangeIso_includeRight`: the identification on the
  two tensor factors.
* `AlgebraicGeometry.GroupoidScheme.isPushout_objectsProjection_appTop` and
  `AlgebraicGeometry.GroupoidScheme.isPushout_arrowsProjection_appTop`: the squares of global
  functions attached to the cartesian squares of a base change are cocartesian.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

groupoid scheme, base change, invariant ring, tensor product, pushout
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G : GroupoidScheme S} {C₁ : Type u} [CommRing C₁]
  [Algebra (invariantRing G) C₁]

/-- The structure morphism of the object scheme to the invariant spectrum is `Spec` of the
inclusion of the invariant ring, read through the canonical isomorphism of the object scheme with
the spectrum of its global functions. -/
theorem objectsToInvariantSpectrum_eq_isoSpec_comp (G : GroupoidScheme S)
    [IsAffine G.objects.left] :
    objectsToInvariantSpectrum G = G.objects.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) Γ(G.objects.left, ⊤))) := by
  rw [Scheme.isoSpec_hom]
  rfl

/-- The structure morphism of the arrow scheme to the invariant spectrum is `Spec` of the
composite of the source map with the inclusion of the invariant ring, read through the canonical
isomorphism of the arrow scheme with the spectrum of its global functions. -/
theorem arrowsToInvariantSpectrum_eq_isoSpec_comp (G : GroupoidScheme S)
    [IsAffine G.arrows.left] :
    letI := invariantRingAlgebraArrow G
    arrowsToInvariantSpectrum G = G.arrows.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) Γ(G.arrows.left, ⊤))) := by
  let := invariantRingAlgebraArrow G
  rw [Scheme.isoSpec_hom]
  show G.source.left ≫ G.objects.left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariantRing G).subtype) = _
  rw [Scheme.toSpecΓ_naturality_assoc G.source.left, ← Spec.map_comp]
  rfl

section Objects

variable [IsAffine G.objects.left]

/-- **The square of global functions attached to the cartesian object square of a base change is
cocartesian.** -/
theorem isPushout_objectsProjection_appTop (bc : AffineInvariantBaseChange G C₁) :
    IsPushout (CommRingCat.ofHom (algebraMap (invariantRing G) Γ(G.objects.left, ⊤)))
      (CommRingCat.ofHom (algebraMap (invariantRing G) C₁)) bc.objectsProjection.appTop
      ((Scheme.ΓSpecIso (.of C₁)).inv ≫ bc.groupoid.objects.hom.appTop) :=
  isPushout_appTop_of_isPullback_specMap _ _
    (objectsToInvariantSpectrum_eq_isoSpec_comp G ▸ bc.objects_isPullback)

/-- **The coordinate ring of the object scheme of a base change is `A ⊗[C] C₁`.** -/
def objectsBaseChangeIso (bc : AffineInvariantBaseChange G C₁) :
    CommRingCat.of (objectRingBaseChange G C₁) ≅ Γ(bc.groupoid.objects.left, ⊤) :=
  (CommRingCat.isPushout_tensorProduct (invariantRing G) Γ(G.objects.left, ⊤) C₁).isoIsPushout
    _ _ (isPushout_objectsProjection_appTop bc)

/-- On the left tensor factor the identification is pullback of global functions along the
projection to the object scheme of `G`. -/
theorem objectsBaseChangeIso_includeLeft (bc : AffineInvariantBaseChange G C₁) :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G.objects.left, ⊤) →+* objectRingBaseChange G C₁) ≫
      (objectsBaseChangeIso bc).hom = bc.objectsProjection.appTop :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- On the right tensor factor the identification is pullback of global functions along the
structure morphism to `Spec C₁`. -/
theorem objectsBaseChangeIso_includeRight (bc : AffineInvariantBaseChange G C₁) :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* objectRingBaseChange G C₁) ≫ (objectsBaseChangeIso bc).hom =
      (Scheme.ΓSpecIso (.of C₁)).inv ≫ bc.groupoid.objects.hom.appTop :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

end Objects

section Arrows

variable [IsAffine G.arrows.left]

/-- **The square of global functions attached to the cartesian arrow square of a base change is
cocartesian.** -/
theorem isPushout_arrowsProjection_appTop (bc : AffineInvariantBaseChange G C₁) :
    letI := invariantRingAlgebraArrow G
    IsPushout (CommRingCat.ofHom (algebraMap (invariantRing G) Γ(G.arrows.left, ⊤)))
      (CommRingCat.ofHom (algebraMap (invariantRing G) C₁)) bc.arrowsProjection.appTop
      ((Scheme.ΓSpecIso (.of C₁)).inv ≫ bc.groupoid.arrows.hom.appTop) :=
  let := invariantRingAlgebraArrow G
  isPushout_appTop_of_isPullback_specMap _ _
    (arrowsToInvariantSpectrum_eq_isoSpec_comp G ▸ bc.arrows_isPullback)

/-- **The coordinate ring of the arrow scheme of a base change is `B ⊗[C] C₁`.** -/
def arrowsBaseChangeIso (bc : AffineInvariantBaseChange G C₁) :
    CommRingCat.of (arrowRingBaseChange G C₁) ≅ Γ(bc.groupoid.arrows.left, ⊤) :=
  letI := invariantRingAlgebraArrow G
  (CommRingCat.isPushout_tensorProduct (invariantRing G) Γ(G.arrows.left, ⊤) C₁).isoIsPushout
    _ _ (isPushout_arrowsProjection_appTop bc)

/-- On the left tensor factor the identification is pullback of global functions along the
projection to the arrow scheme of `G`. -/
theorem arrowsBaseChangeIso_includeLeft (bc : AffineInvariantBaseChange G C₁) :
    letI := invariantRingAlgebraArrow G
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G.arrows.left, ⊤) →+* arrowRingBaseChange G C₁) ≫
      (arrowsBaseChangeIso bc).hom = bc.arrowsProjection.appTop :=
  let := invariantRingAlgebraArrow G
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- On the right tensor factor the identification is pullback of global functions along the
structure morphism to `Spec C₁`. -/
theorem arrowsBaseChangeIso_includeRight (bc : AffineInvariantBaseChange G C₁) :
    letI := invariantRingAlgebraArrow G
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* arrowRingBaseChange G C₁) ≫ (arrowsBaseChangeIso bc).hom =
      (Scheme.ΓSpecIso (.of C₁)).inv ≫ bc.groupoid.arrows.hom.appTop :=
  let := invariantRingAlgebraArrow G
  IsPushout.inr_isoIsPushout_hom _ _ _ _

end Arrows

/-! ### The base change of the source groupoid, read over the invariant ring of the target -/

section Morphism

variable {G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G) (C₁ : Type u) [CommRing C₁]
  [Algebra (invariantRing G) C₁]

/-- `Γ(U', ⊤)` as an algebra over the invariant ring of `G`, through the map on invariant rings
induced by `F` followed by the inclusion of the invariant ring of `G'`. -/
@[instance_reducible]
def objectRingAlgebraOfHom : Algebra (invariantRing G) Γ(G'.objects.left, ⊤) :=
  ((algebraMap (invariantRing G') Γ(G'.objects.left, ⊤)).comp (invariantRingMap F)).toAlgebra

/-- `Γ(R', ⊤)` as an algebra over the invariant ring of `G`, through the map on invariant rings
induced by `F` followed by the source map of `G'`. -/
@[instance_reducible]
def arrowRingAlgebraOfHom : Algebra (invariantRing G) Γ(G'.arrows.left, ⊤) :=
  letI := invariantRingAlgebraArrow G'
  ((algebraMap (invariantRing G') Γ(G'.arrows.left, ⊤)).comp (invariantRingMap F)).toAlgebra

variable (bc' : AffineInvariantBaseChange G' (tensorBaseRing F C₁))

/-- Rewriting the map from an affine scheme to `Spec` of the invariant ring of `G'` along `Spec` of
the map on invariant rings induced by `F`. -/
private theorem isoSpec_comp_map_eq {G : GroupoidScheme S} {G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of (invariantRing G'))) (f : invariantRing G' →+* Γ(X, ⊤))
    (h : p = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (f.comp (invariantRingMap F))) =
      p ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F)) := by
  rw [h, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **The object scheme of the base change of `G'` along `C' ⟶ C' ⊗[C] C₁` is the fibre product
of `U'` with `Spec C₁` over `Spec C`.** -/
theorem isPullback_objectsProjection_tensorBaseRing [IsAffine G'.objects.left] :
    letI := objectRingAlgebraOfHom F
    IsPullback bc'.objectsProjection
      (bc'.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁)))
      (G'.objects.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (invariantRing G) Γ(G'.objects.left, ⊤))))
      (invariantSpectrumMap G C₁) := by
  let := objectRingAlgebraOfHom F
  rw [isoSpec_comp_map_eq F _ (algebraMap (invariantRing G') Γ(G'.objects.left, ⊤))
    (objectsToInvariantSpectrum_eq_isoSpec_comp G')]
  exact bc'.objects_isPullback.paste_vert
    (isPullback_invariantSpectrumMap_tensorBaseRing F C₁)

/-- **The arrow scheme of the base change of `G'` is the fibre product of `R'` with `Spec C₁`
over `Spec C`.** -/
theorem isPullback_arrowsProjection_tensorBaseRing [IsAffine G'.arrows.left] :
    letI := arrowRingAlgebraOfHom F
    IsPullback bc'.arrowsProjection
      (bc'.groupoid.arrows.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁)))
      (G'.arrows.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (invariantRing G) Γ(G'.arrows.left, ⊤))))
      (invariantSpectrumMap G C₁) := by
  let := arrowRingAlgebraOfHom F
  let := invariantRingAlgebraArrow G'
  rw [isoSpec_comp_map_eq F _ (algebraMap (invariantRing G') Γ(G'.arrows.left, ⊤))
    (arrowsToInvariantSpectrum_eq_isoSpec_comp G')]
  exact bc'.arrows_isPullback.paste_vert
    (isPullback_invariantSpectrumMap_tensorBaseRing F C₁)

/-- **The coordinate ring of the object scheme of the base change of `G'` is `A' ⊗[C] C₁`**, the
invariant ring of `G` acting on `A'` through the map on invariant rings. -/
def objectsTensorBaseRingIso [IsAffine G'.objects.left] :
    letI := objectRingAlgebraOfHom F
    CommRingCat.of (Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≅
      Γ(bc'.groupoid.objects.left, ⊤) :=
  letI := objectRingAlgebraOfHom F
  tensorAppTopIso (isPullback_objectsProjection_tensorBaseRing F C₁ bc')

/-- **The coordinate ring of the arrow scheme of the base change of `G'` is `B' ⊗[C] C₁`.** -/
def arrowsTensorBaseRingIso [IsAffine G'.arrows.left] :
    letI := arrowRingAlgebraOfHom F
    CommRingCat.of (Γ(G'.arrows.left, ⊤) ⊗[invariantRing G] C₁) ≅
      Γ(bc'.groupoid.arrows.left, ⊤) :=
  letI := arrowRingAlgebraOfHom F
  tensorAppTopIso (isPullback_arrowsProjection_tensorBaseRing F C₁ bc')

/-- On the left tensor factor the identification of the object ring is pullback of global
functions along the projection to `U'`. -/
theorem objectsTensorBaseRingIso_includeLeft [IsAffine G'.objects.left] :
    letI := objectRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G'.objects.left, ⊤) →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      (objectsTensorBaseRingIso F C₁ bc').hom = bc'.objectsProjection.appTop :=
  let := objectRingAlgebraOfHom F
  tensorAppTopIso_includeLeft (isPullback_objectsProjection_tensorBaseRing F C₁ bc')

/-- On the right tensor factor the identification of the object ring is pullback of global
functions along the structure morphism to `Spec C₁`. -/
theorem objectsTensorBaseRingIso_includeRight [IsAffine G'.objects.left] :
    letI := objectRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      (objectsTensorBaseRingIso F C₁ bc').hom =
      (Scheme.ΓSpecIso (.of C₁)).inv ≫
        (bc'.groupoid.objects.hom ≫
          Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).appTop :=
  let := objectRingAlgebraOfHom F
  tensorAppTopIso_includeRight (isPullback_objectsProjection_tensorBaseRing F C₁ bc')

/-- On the left tensor factor the identification of the arrow ring is pullback of global
functions along the projection to `R'`. -/
theorem arrowsTensorBaseRingIso_includeLeft [IsAffine G'.arrows.left] :
    letI := arrowRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G'.arrows.left, ⊤) →+* Γ(G'.arrows.left, ⊤) ⊗[invariantRing G] C₁) ≫
      (arrowsTensorBaseRingIso F C₁ bc').hom = bc'.arrowsProjection.appTop :=
  let := arrowRingAlgebraOfHom F
  tensorAppTopIso_includeLeft (isPullback_arrowsProjection_tensorBaseRing F C₁ bc')

/-- On the right tensor factor the identification of the arrow ring is pullback of global
functions along the structure morphism to `Spec C₁`. -/
theorem arrowsTensorBaseRingIso_includeRight [IsAffine G'.arrows.left] :
    letI := arrowRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* Γ(G'.arrows.left, ⊤) ⊗[invariantRing G] C₁) ≫
      (arrowsTensorBaseRingIso F C₁ bc').hom =
      (Scheme.ΓSpecIso (.of C₁)).inv ≫
        (bc'.groupoid.arrows.hom ≫
          Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).appTop :=
  let := arrowRingAlgebraOfHom F
  tensorAppTopIso_includeRight (isPullback_arrowsProjection_tensorBaseRing F C₁ bc')

end Morphism

end AlgebraicGeometry.GroupoidScheme

end

end
