module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.BaseChangeGlobalSections

/-!
# The source and target maps of a base change, read on the tensor product

Let `F : G' ⟶ G` be a morphism of affine groupoid schemes and let `C₁` be an extension of the
invariant ring `C` of `G`. The coordinate rings of the object and arrow schemes of the base change
of `G'` along `C' ⟶ C' ⊗[C] C₁` are `A' ⊗[C] C₁` and `B' ⊗[C] C₁`, by
`AlgebraicGeometry.GroupoidScheme.objectsTensorBaseRingIso` and
`AlgebraicGeometry.GroupoidScheme.arrowsTensorBaseRingIso`. This file identifies the **source and
target maps of the base change** through those two identifications: they are `s'^♯ ⊗ id` and
`t'^♯ ⊗ id`.

That identification is what turns invariance of a subset of the object scheme of the base change —
a statement about points — into a single equation between two elements of `B' ⊗[C] C₁`, which is
the form in which invariance is *descended* along a filtered colimit in the proof of
[Stacks Project, Tag 0DT9].

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.comp_assoc_left` and
  `AlgebraicGeometry.GroupoidScheme.comp_assoc_left₂`: the two reassociation identities on plain
  objects of `CommRingCat` that all the edge computations over base changes are written with.
* `AlgebraicGeometry.GroupoidScheme.sourceAlgHomOfHom` and
  `AlgebraicGeometry.GroupoidScheme.targetAlgHomOfHom`: the source and target maps of `G'`, read as
  homomorphisms of algebras over the invariant ring of `G`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.objectsTensorBaseRingIso_hom_comp_source_appTop` and
  `AlgebraicGeometry.GroupoidScheme.objectsTensorBaseRingIso_hom_comp_target_appTop`: **the source
  and target maps of the base change are `s'^♯ ⊗ id` and `t'^♯ ⊗ id`.**
* `AlgebraicGeometry.GroupoidScheme.sourceMap_objectsTensorBaseRingIso` and
  `AlgebraicGeometry.GroupoidScheme.targetMap_objectsTensorBaseRingIso`: the same read on
  elements.

## Implementation notes

Both identifications come from one private lemma, applied to the source and to the target map in
turn. It is proved from the cocartesian square presenting `A' ⊗[C] C₁`, whose two edges are the
inclusions of the two tensor factors: on the `A'` edge the computation is that the projection to
`U'` commutes with the two source, respectively target, maps, and on the `C₁` edge it is that the
source, respectively target, map is a morphism over `Spec (C' ⊗[C] C₁)`.

All the reassociation is done by `AlgebraicGeometry.GroupoidScheme.comp_assoc_left` and
`AlgebraicGeometry.GroupoidScheme.comp_assoc_left₂`, which are about plain objects of
`CommRingCat`, and the two edge computations in term mode, so that no rewrite happens inside
the coordinate ring of a base change; a monolithic `rw` chain over those terms exhausts the
heartbeat budget.

The algebra structures are the ones the two identifications are formed with:
`AlgebraicGeometry.GroupoidScheme.objectRingAlgebraOfHom` on `A'` and
`AlgebraicGeometry.GroupoidScheme.arrowRingAlgebraOfHom` on `B'`, both through the map on invariant
rings. The source map is a homomorphism for them by construction, and the target map is one
because an invariant function has equal source and target pullbacks.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

groupoid scheme, base change, source map, target map, tensor product, invariance
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Reassociation on plain rings: a map into a pushout which factors through an identification,
composed with a further map, is the factorisation followed by that map.

Stated for plain objects of `CommRingCat` so that it can be applied to the coordinate ring of a
base change without any rewrite inside that term. -/
theorem comp_assoc_left {X P P' Q : CommRingCat.{u}} {i : X ⟶ P} {e : P ⟶ P'}
    {j : X ⟶ P'} (he : i ≫ e = j) (m : P' ⟶ Q) : i ≫ e ≫ m = j ≫ m :=
  (Category.assoc i e m).symm.trans (congrArg (· ≫ m) he)

/-- Reassociation on plain rings, with the factorisation itself a composite whose second half is
then simplified. -/
theorem comp_assoc_left₂ {X A P' P Q : CommRingCat.{u}} {i : X ⟶ P} {e : P ⟶ P'}
    {a : X ⟶ A} {b : A ⟶ P'} (he : i ≫ e = a ≫ b) {m : P' ⟶ Q} {c : A ⟶ Q} (hb : b ≫ m = c) :
    i ≫ e ≫ m = a ≫ c :=
  ((Category.assoc i e m).symm.trans (congrArg (· ≫ m) he)).trans
    ((Category.assoc a b m).trans (congrArg (a ≫ ·) hb))

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- The source map of `G'`, read as a homomorphism of algebras over the invariant ring of `G`:
the invariant ring of `G` acts on `A'` through the map on invariant rings and on `B'` through the
map on invariant rings followed by the source map, so the source map is a homomorphism of
algebras by construction. -/
def sourceAlgHomOfHom :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    Γ(G'.objects.left, ⊤) →ₐ[invariantRing G] Γ(G'.arrows.left, ⊤) :=
  let := objectRingAlgebraOfHom F
  let := arrowRingAlgebraOfHom F
  { toRingHom := sourceMap G'
    commutes' := fun _ => rfl }

/-- The target map of `G'`, read as a homomorphism of algebras over the invariant ring of `G`:
an invariant function of `G'` has equal source and target pullbacks, so the target map agrees with
the source map on the image of the invariant ring. -/
def targetAlgHomOfHom :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    Γ(G'.objects.left, ⊤) →ₐ[invariantRing G] Γ(G'.arrows.left, ⊤) :=
  let := objectRingAlgebraOfHom F
  let := arrowRingAlgebraOfHom F
  { toRingHom := targetMap G'
    commutes' := fun c => (invariantRingMap F c).property.symm }

section Bridge

variable (C₁ : Type u) [CommRing C₁] [Algebra (invariantRing G) C₁]
  (bc' : AffineInvariantBaseChange G' (tensorBaseRing F C₁))
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]

/-- **The bridge, for either of the two maps of the groupoid.** A morphism `sg` from the arrows to
the objects of the base change which commutes with the projections and a corresponding morphism
`sG` of `G'`, together with an algebra homomorphism `φ` on coordinate rings realising `sG`, are
identified by the two tensor product presentations: pullback along `sg` is `φ ⊗ id`.

The source and target maps of a groupoid scheme are both of this shape, which is why the
computation is done once. -/
private theorem objectsTensorBaseRingIso_hom_comp_appTop
    (sg : bc'.groupoid.arrows ⟶ bc'.groupoid.objects) (sG : G'.arrows ⟶ G'.objects)
    (hproj : bc'.arrowsProjection ≫ sG.left = sg.left ≫ bc'.objectsProjection) :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    ∀ φ : Γ(G'.objects.left, ⊤) →ₐ[invariantRing G] Γ(G'.arrows.left, ⊤),
      CommRingCat.ofHom (φ : Γ(G'.objects.left, ⊤) →+* Γ(G'.arrows.left, ⊤)) = sG.left.appTop →
        (objectsTensorBaseRingIso F C₁ bc').hom ≫ sg.left.appTop =
          CommRingCat.ofHom (Algebra.TensorProduct.map φ
              (AlgHom.id (invariantRing G) C₁)).toRingHom ≫
            (arrowsTensorBaseRingIso F C₁ bc').hom := by
  let := objectRingAlgebraOfHom F
  let := arrowRingAlgebraOfHom F
  intro φ hφ
  -- the two maps out of the `A'` factor
  have hleftφ : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G'.objects.left, ⊤) →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map φ
        (AlgHom.id (invariantRing G) C₁)).toRingHom =
      CommRingCat.ofHom (φ : Γ(G'.objects.left, ⊤) →+* Γ(G'.arrows.left, ⊤)) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Γ(G'.arrows.left, ⊤) →+* Γ(G'.arrows.left, ⊤) ⊗[invariantRing G] C₁) := by
    ext a
    exact Algebra.TensorProduct.map_tmul φ (AlgHom.id (invariantRing G) C₁) a 1
  have hrightφ : CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map φ
        (AlgHom.id (invariantRing G) C₁)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* Γ(G'.arrows.left, ⊤) ⊗[invariantRing G] C₁) := by
    ext c
    refine (Algebra.TensorProduct.map_tmul φ (AlgHom.id (invariantRing G) C₁) 1 c).trans ?_
    rw [map_one]
    rfl
  -- the `A'` edge: the projection commutes with the two maps
  have hedgeL : bc'.objectsProjection.appTop ≫ sg.left.appTop =
      sG.left.appTop ≫ bc'.arrowsProjection.appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans
      ((congrArg Scheme.Hom.appTop hproj.symm).trans (Scheme.Hom.comp_appTop _ _))
  -- the `C₁` edge: both maps lie over `Spec (C' ⊗[C] C₁)`
  have hw : sg.left ≫ bc'.groupoid.objects.hom ≫
      Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁)) =
      bc'.groupoid.arrows.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁)) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) (Over.w sg))
  have hedgeR : (bc'.groupoid.objects.hom ≫
        Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).appTop ≫ sg.left.appTop =
      (bc'.groupoid.arrows.hom ≫
        Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop hw)
  refine (CommRingCat.isPushout_tensorProduct (invariantRing G) Γ(G'.objects.left, ⊤)
    C₁).hom_ext ?_ ?_
  · refine ((comp_assoc_left (objectsTensorBaseRingIso_includeLeft F C₁ bc') _).trans
      hedgeL).trans ?_
    refine Eq.trans ?_
      (comp_assoc_left₂ hleftφ (arrowsTensorBaseRingIso_includeLeft F C₁ bc')).symm
    exact congrArg (· ≫ bc'.arrowsProjection.appTop) hφ.symm
  · refine (comp_assoc_left (objectsTensorBaseRingIso_includeRight F C₁ bc') _).trans ?_
    refine ((Category.assoc _ _ _).trans
      (congrArg ((Scheme.ΓSpecIso (.of C₁)).inv ≫ ·) hedgeR)).trans ?_
    refine Eq.trans ?_ (comp_assoc_left hrightφ _).symm
    exact (arrowsTensorBaseRingIso_includeRight F C₁ bc').symm

/-- **The source map of the base change is `s'^♯ ⊗ id`**, read through the two identifications of
the coordinate rings of the base change with tensor products. -/
theorem objectsTensorBaseRingIso_hom_comp_source_appTop :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    (objectsTensorBaseRingIso F C₁ bc').hom ≫ bc'.groupoid.source.left.appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.map (sourceAlgHomOfHom F)
        (AlgHom.id (invariantRing G) C₁)).toRingHom ≫
        (arrowsTensorBaseRingIso F C₁ bc').hom :=
  objectsTensorBaseRingIso_hom_comp_appTop F C₁ bc' bc'.groupoid.source G'.source
    bc'.projection_source (sourceAlgHomOfHom F) rfl

/-- **The target map of the base change is `t'^♯ ⊗ id`**, read through the two identifications of
the coordinate rings of the base change with tensor products. -/
theorem objectsTensorBaseRingIso_hom_comp_target_appTop :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    (objectsTensorBaseRingIso F C₁ bc').hom ≫ bc'.groupoid.target.left.appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.map (targetAlgHomOfHom F)
        (AlgHom.id (invariantRing G) C₁)).toRingHom ≫
        (arrowsTensorBaseRingIso F C₁ bc').hom :=
  objectsTensorBaseRingIso_hom_comp_appTop F C₁ bc' bc'.groupoid.target G'.target
    bc'.projection_target (targetAlgHomOfHom F) rfl

/-- The source map of the base change read on elements of the tensor product. -/
theorem sourceMap_objectsTensorBaseRingIso
    (e : letI := objectRingAlgebraOfHom F; Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    sourceMap bc'.groupoid ((objectsTensorBaseRingIso F C₁ bc').hom e) =
      (arrowsTensorBaseRingIso F C₁ bc').hom
        (Algebra.TensorProduct.map (sourceAlgHomOfHom F) (AlgHom.id (invariantRing G) C₁) e) :=
  congr($(objectsTensorBaseRingIso_hom_comp_source_appTop F C₁ bc').hom e)

/-- The target map of the base change read on elements of the tensor product. -/
theorem targetMap_objectsTensorBaseRingIso
    (e : letI := objectRingAlgebraOfHom F; Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) :
    letI := objectRingAlgebraOfHom F
    letI := arrowRingAlgebraOfHom F
    targetMap bc'.groupoid ((objectsTensorBaseRingIso F C₁ bc').hom e) =
      (arrowsTensorBaseRingIso F C₁ bc').hom
        (Algebra.TensorProduct.map (targetAlgHomOfHom F) (AlgHom.id (invariantRing G) C₁) e) :=
  congr($(objectsTensorBaseRingIso_hom_comp_target_appTop F C₁ bc').hom e)

end Bridge

end AlgebraicGeometry.GroupoidScheme

end

end
