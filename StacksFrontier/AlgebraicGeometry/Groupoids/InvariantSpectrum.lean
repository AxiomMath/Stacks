module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# The invariant spectrum of an affine groupoid scheme and its base changes

Let `G` be a groupoid scheme with affine object and arrow schemes and with finite locally free
source and target. Its object and arrow schemes are schemes over the spectrum of the ring `C`
of invariant functions, through the canonical morphisms `objectsToInvariantSpectrum` and
`arrowsToInvariantSpectrum`. Extending the invariant ring along `C ⟶ C'` makes the object and
arrow rings `A ⊗[C] C'` and `B ⊗[C] C'`, and this file records the coordinate rings, the
structure maps as homomorphisms of algebras over `C`, and the data of a base-changed groupoid.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum` and
  `AlgebraicGeometry.GroupoidScheme.arrowsToInvariantSpectrum`: the structure morphisms over the
  spectrum of the invariant ring.
* `AlgebraicGeometry.GroupoidScheme.objectRingBaseChange` and
  `AlgebraicGeometry.GroupoidScheme.arrowRingBaseChange`: the object and arrow rings after
  extension of the invariant ring.
* `AlgebraicGeometry.GroupoidScheme.sourceAlgHom` and
  `AlgebraicGeometry.GroupoidScheme.targetAlgHom`: the source and target maps as homomorphisms
  of algebras over the invariant ring.
* `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange`: the base-changed groupoid with
  its specified tensor-product presentations and its ring of invariant functions.

## Implementation notes

The rings of global functions are used as the affine presentations `A` and `B`. The two
displayed compatibility equations `source_eq` and `target_eq` say that the source and target of
the new groupoid are the scalar extensions of the original maps; stating them, rather than only
asserting that some groupoid with isomorphic coordinate rings exists, is what makes the
presentation canonical. The projection fields and their cartesian squares specify the canonical
base change, and compatibility with every groupoid operation — in particular with composition —
says that the operations are induced from `G`.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Coordinate rings after extension of the invariant ring -/

/-- The coordinate ring of the object scheme after extension of the invariant ring. -/
abbrev objectRingBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u) [CommRing C']
    [Algebra (invariantRing G) C'] :=
  Γ(G.objects.left, ⊤) ⊗[invariantRing G] C'

/-- The invariant ring acts on the arrow ring through the source map. -/
@[instance_reducible]
def invariantRingAlgebraArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    Algebra (invariantRing G) Γ(G.arrows.left, ⊤) :=
  (RingHom.comp (sourceMap G) (invariantRing G).subtype).toAlgebra

/-- The coordinate ring of the arrow scheme after extension of the invariant ring. -/
abbrev arrowRingBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u) [CommRing C']
    [Algebra (invariantRing G) C'] :=
  letI := invariantRingAlgebraArrow G
  Γ(G.arrows.left, ⊤) ⊗[invariantRing G] C'

/-- The specified `C'`-scheme `Spec (A ⊗[C] C')`. -/
abbrev objectSchemeBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u) [CommRing C']
    [Algebra (invariantRing G) C'] : Over (Spec (.of C')) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom))

/-- The specified `C'`-scheme `Spec (B ⊗[C] C')`. -/
abbrev arrowSchemeBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u) [CommRing C']
    [Algebra (invariantRing G) C'] : Over (Spec (.of C')) :=
  letI := invariantRingAlgebraArrow G
  Over.mk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      C' →ₐ[invariantRing G] arrowRingBaseChange G C').toRingHom))

/-- The source map, as a homomorphism of algebras over the invariant ring. -/
def sourceAlgHom {S : Scheme.{u}} (G : GroupoidScheme S) :=
  letI := invariantRingAlgebraArrow G
  ({ toRingHom := sourceMap G
     commutes' := fun _ ↦ rfl } :
    Γ(G.objects.left, ⊤) →ₐ[invariantRing G] Γ(G.arrows.left, ⊤))

/-- The target map, as a homomorphism of algebras over the invariant ring. -/
def targetAlgHom {S : Scheme.{u}} (G : GroupoidScheme S) :=
  letI := invariantRingAlgebraArrow G
  ({ toRingHom := targetMap G
     commutes' := fun c ↦ c.property.symm } :
    Γ(G.objects.left, ⊤) →ₐ[invariantRing G] Γ(G.arrows.left, ⊤))

/-! ### The structure morphisms to the invariant spectrum -/

/-- The canonical morphism from the object scheme to the spectrum of the invariant ring. -/
def objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.objects.left ⟶ Spec (.of (invariantRing G)) :=
  G.objects.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (invariantRing G).subtype)

/-- The canonical morphism from the arrow scheme to the spectrum of the invariant ring. -/
def arrowsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.arrows.left ⟶ Spec (.of (invariantRing G)) :=
  G.source.left ≫ objectsToInvariantSpectrum G

/-- The morphism of affine schemes associated to an extension of the invariant ring. -/
def invariantSpectrumMap {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u) [CommRing C']
    [Algebra (invariantRing G) C'] :
    Spec (.of C') ⟶ Spec (.of (invariantRing G)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) C'))

/-! ### The base-changed groupoid -/

/-- The affine groupoid obtained by extending the object and arrow rings from the invariant
ring. The compatibility fields make the displayed affine presentations canonical, rather than
merely asserting that isomorphic schemes exist. -/
structure AffineInvariantBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) (C' : Type u)
    [CommRing C'] [Algebra (invariantRing G) C'] where
  /-- The base-changed groupoid scheme over `Spec C'`. -/
  groupoid : GroupoidScheme (Spec (.of C'))
  /-- The identification of its object scheme with `Spec (A ⊗[C] C')`. -/
  objectsIso : groupoid.objects.left ≅ Spec (.of (objectRingBaseChange G C'))
  /-- The identification of its arrow scheme with `Spec (B ⊗[C] C')`. -/
  arrowsIso : groupoid.arrows.left ≅ Spec (.of (arrowRingBaseChange G C'))
  objectsIso_over : objectsIso.hom ≫ (objectSchemeBaseChange G C').hom = groupoid.objects.hom
  arrowsIso_over : arrowsIso.hom ≫ (arrowSchemeBaseChange G C').hom = groupoid.arrows.hom
  /-- The projection to the object scheme of `G`. -/
  objectsProjection : groupoid.objects.left ⟶ G.objects.left
  /-- The projection to the arrow scheme of `G`. -/
  arrowsProjection : groupoid.arrows.left ⟶ G.arrows.left
  objects_isPullback : IsPullback objectsProjection groupoid.objects.hom
    (objectsToInvariantSpectrum G) (invariantSpectrumMap G C')
  arrows_isPullback : IsPullback arrowsProjection groupoid.arrows.hom
    (arrowsToInvariantSpectrum G) (invariantSpectrumMap G C')
  projection_source : arrowsProjection ≫ G.source.left =
    groupoid.source.left ≫ objectsProjection
  projection_target : arrowsProjection ≫ G.target.left =
    groupoid.target.left ≫ objectsProjection
  projection_identity : objectsProjection ≫ G.identity.left =
    groupoid.identity.left ≫ arrowsProjection
  projection_inverse : arrowsProjection ≫ G.inverse.left =
    groupoid.inverse.left ≫ arrowsProjection
  /-- The projection on the schemes of composable arrows. -/
  composableProjection : (pullback groupoid.source groupoid.target).left ⟶
    (pullback G.source G.target).left
  composableProjection_fst : composableProjection ≫ (pullback.fst G.source G.target).left =
    (pullback.fst groupoid.source groupoid.target).left ≫ arrowsProjection
  composableProjection_snd : composableProjection ≫ (pullback.snd G.source G.target).left =
    (pullback.snd groupoid.source groupoid.target).left ≫ arrowsProjection
  projection_comp : groupoid.comp.left ≫ arrowsProjection =
    composableProjection ≫ G.comp.left
  baseRingMap_invariant : ∀ x : C',
    sourceMap groupoid (((Scheme.ΓSpecIso (.of C')).inv ≫ groupoid.objects.hom.appTop).hom x) =
      targetMap groupoid
        (((Scheme.ΓSpecIso (.of C')).inv ≫ groupoid.objects.hom.appTop).hom x)
  source_eq : groupoid.source.left = arrowsIso.hom ≫
    Spec.map (CommRingCat.ofHom
      (letI := invariantRingAlgebraArrow G
      (Algebra.TensorProduct.map (sourceAlgHom G) (AlgHom.id _ C')).toRingHom)) ≫
    objectsIso.inv
  target_eq : groupoid.target.left = arrowsIso.hom ≫
    Spec.map (CommRingCat.ofHom
      (letI := invariantRingAlgebraArrow G
      (Algebra.TensorProduct.map (targetAlgHom G) (AlgHom.id _ C')).toRingHom)) ≫
    objectsIso.inv
  source_isFiniteLocallyFree : IsFiniteLocallyFree groupoid.source.left
  target_isFiniteLocallyFree : IsFiniteLocallyFree groupoid.target.left

namespace AffineInvariantBaseChange

/-- The ring of invariant functions of the base-changed groupoid. -/
abbrev invariantFunctions {S : Scheme.{u}} {G : GroupoidScheme S} {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') :=
  invariantRing G'.groupoid

/-- The canonical map from the new base ring to the invariant functions of the base-changed
groupoid, obtained from the structure morphism of its object scheme. -/
def canonicalMapToInvariantFunctions {S : Scheme.{u}} {G : GroupoidScheme S} {C' : Type u}
    [CommRing C'] [Algebra (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') :
    C' →+* G'.invariantFunctions :=
  RingHom.codRestrict ((Scheme.ΓSpecIso (.of C')).inv ≫ G'.groupoid.objects.hom.appTop).hom
    (invariantRing G'.groupoid) G'.baseRingMap_invariant

end AffineInvariantBaseChange

end AlgebraicGeometry.GroupoidScheme

end

end
