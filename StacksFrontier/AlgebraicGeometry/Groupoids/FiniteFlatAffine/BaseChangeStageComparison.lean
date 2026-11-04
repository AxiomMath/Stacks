module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.BaseChangeArrowBridge

/-!
# Comparing two base changes along a map of the extension ring

Let `F : G' ⟶ G` be a morphism of affine groupoid schemes and let `h : C₁ ⟶ C₂` be a map of
extensions of the invariant ring `C` of `G`. The object scheme of the base change of `G'` along
`C' ⟶ C' ⊗[C] C₁` is the fibre product `U' ×_{Spec C} Spec C₁`
(`AlgebraicGeometry.GroupoidScheme.isPullback_objectsProjection_tensorBaseRing`), so `h` induces a
**comparison morphism** `U'_{C₂} ⟶ U'_{C₁}` over `U'` and over `Spec h`, and on coordinate rings
that morphism is `id ⊗ h` under the two tensor product presentations.

That is what carries a point of `U'_{C₂}` to a point of `U'_{C₁}` and, through the identification
of the kernels, a point of the sheet of a section over `C₁` to a point of the sheet over `C₂`. In
the descent of [Stacks Project, Tag 0DT9] it is used in the direction `C₁` an étale stage and
`C₂` the strict henselization: the sheet is produced over the strict henselization and the
comparison identifies it with the pullback of the sheet at the stage.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.tensorBaseRingComparison`: the comparison morphism
  `U'_{C₂} ⟶ U'_{C₁}` induced by a map `C₁ ⟶ C₂` of extensions of the invariant ring.

## Main results

* `AlgebraicGeometry.GroupoidScheme.tensorBaseRingComparison_comp_objectsProjection`: the
  comparison lies over the identity of `U'`.
* `GroupoidScheme.objectsTensorBaseRingIso_hom_comp_tensorBaseRingComparison_appTop`:
  **the comparison is `id ⊗ h` on coordinate rings**, read through the two tensor product
  presentations.

## Implementation notes

The comparison is the universal map out of the fibre product presentation of `U'_{C₁}`, so its two
defining identities are `CategoryTheory.IsPullback.lift_fst` and
`CategoryTheory.IsPullback.lift_snd`; nothing is assumed of `h` beyond being a map of algebras over
the invariant ring.

The identification on coordinate rings is checked on the two edges of the cocartesian square
presenting `A' ⊗[C] C₁`, as in
`StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.BaseChangeArrowBridge`, and with the same
reassociation lemmas `AlgebraicGeometry.GroupoidScheme.comp_assoc_left` and
`AlgebraicGeometry.GroupoidScheme.comp_assoc_left₂`: on the `A'` edge the computation is that the
comparison lies over `U'`, and on the `C₁` edge that it lies over `Spec h`.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

groupoid scheme, base change, extension ring, tensor product, comparison morphism
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂] [Algebra (invariantRing G) C₁]
  [Algebra (invariantRing G) C₂] (h : C₁ →ₐ[invariantRing G] C₂)
  (bc₁ : AffineInvariantBaseChange G' (tensorBaseRing F C₁))
  (bc₂ : AffineInvariantBaseChange G' (tensorBaseRing F C₂))
  [IsAffine G'.objects.left]

/-- `Spec` of a map of extensions of the invariant ring is a morphism over the invariant
spectrum. -/
theorem specMap_comp_invariantSpectrumMap :
    Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂)) ≫ invariantSpectrumMap G C₁ =
      invariantSpectrumMap G C₂ := by
  rw [invariantSpectrumMap, invariantSpectrumMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom k))
    (RingHom.ext fun c => h.commutes c)

/-- The square that the comparison morphism is the universal map out of: the object scheme of the
base change over `C₂` lies over `U'` and over `Spec C₁`, compatibly over the invariant
spectrum. -/
theorem objectsProjection_comp_eq_of_algHom :
    letI := objectRingAlgebraOfHom F
    bc₂.objectsProjection ≫ (G'.objects.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (invariantRing G) Γ(G'.objects.left, ⊤)))) =
      ((bc₂.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₂))) ≫
        Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂))) ≫ invariantSpectrumMap G C₁ := by
  let := objectRingAlgebraOfHom F
  rw [Category.assoc, specMap_comp_invariantSpectrumMap h]
  exact (isPullback_objectsProjection_tensorBaseRing F C₂ bc₂).w

/-- **The comparison morphism `U'_{C₂} ⟶ U'_{C₁}` induced by a map `C₁ ⟶ C₂` of extensions of the
invariant ring.** -/
def tensorBaseRingComparison : bc₂.groupoid.objects.left ⟶ bc₁.groupoid.objects.left :=
  letI := objectRingAlgebraOfHom F
  (isPullback_objectsProjection_tensorBaseRing F C₁ bc₁).lift bc₂.objectsProjection
    ((bc₂.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₂))) ≫
      Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂)))
    (objectsProjection_comp_eq_of_algHom F h bc₂)

/-- The comparison morphism lies over the identity of `U'`. -/
@[reassoc]
theorem tensorBaseRingComparison_comp_objectsProjection :
    tensorBaseRingComparison F h bc₁ bc₂ ≫ bc₁.objectsProjection = bc₂.objectsProjection :=
  let := objectRingAlgebraOfHom F
  (isPullback_objectsProjection_tensorBaseRing F C₁ bc₁).lift_fst _ _ _

/-- The comparison morphism lies over `Spec h`. -/
@[reassoc]
theorem tensorBaseRingComparison_comp_hom :
    tensorBaseRingComparison F h bc₁ bc₂ ≫
        (bc₁.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) =
      (bc₂.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₂))) ≫
        Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂)) :=
  let := objectRingAlgebraOfHom F
  (isPullback_objectsProjection_tensorBaseRing F C₁ bc₁).lift_snd _ _ _

omit [IsAffine G'.objects.left] in
/-- On the `A'` factor the base change of a map of extensions is the inclusion of the `A'`
factor. -/
private theorem includeLeft_comp_map_id_algHom :
    letI := objectRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G'.objects.left, ⊤) →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map
        (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(G'.objects.left, ⊤) →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₂) := by
  let := objectRingAlgebraOfHom F
  ext a
  refine (Algebra.TensorProduct.map_tmul
    (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h a 1).trans ?_
  rw [map_one]
  rfl

omit [IsAffine G'.objects.left] in
/-- On the `C₁` factor the base change of a map of extensions is `h` followed by the inclusion of
the `C₂` factor. -/
private theorem includeRight_comp_map_id_algHom :
    letI := objectRingAlgebraOfHom F
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        C₁ →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map
        (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h).toRingHom =
      CommRingCat.ofHom (h : C₁ →+* C₂) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
          C₂ →+* Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₂) := by
  let := objectRingAlgebraOfHom F
  ext c
  exact Algebra.TensorProduct.map_tmul
    (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h 1 c

/-- **The comparison morphism is `id ⊗ h` on coordinate rings**, read through the two tensor
product presentations of the coordinate rings of the two base changes.

Both edges of the cocartesian square presenting `A' ⊗[C] C₁` are checked: on the `A'` edge the
computation is that the comparison lies over `U'`, and on the `C₁` edge that it lies over
`Spec h`. -/
theorem objectsTensorBaseRingIso_hom_comp_tensorBaseRingComparison_appTop :
    letI := objectRingAlgebraOfHom F
    (objectsTensorBaseRingIso F C₁ bc₁).hom ≫ (tensorBaseRingComparison F h bc₁ bc₂).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h).toRingHom ≫
        (objectsTensorBaseRingIso F C₂ bc₂).hom := by
  let := objectRingAlgebraOfHom F
  have hedgeL : bc₁.objectsProjection.appTop ≫ (tensorBaseRingComparison F h bc₁ bc₂).appTop =
      bc₂.objectsProjection.appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop
      (tensorBaseRingComparison_comp_objectsProjection F h bc₁ bc₂))
  have hedgeR : (bc₁.groupoid.objects.hom ≫
          Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).appTop ≫
        (tensorBaseRingComparison F h bc₁ bc₂).appTop =
      (Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂))).appTop ≫
        (bc₂.groupoid.objects.hom ≫
          Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₂))).appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans ((congrArg Scheme.Hom.appTop
      (tensorBaseRingComparison_comp_hom F h bc₁ bc₂)).trans (Scheme.Hom.comp_appTop _ _))
  have hnat : (Scheme.ΓSpecIso (.of C₁)).inv ≫
      (Spec.map (CommRingCat.ofHom (h : C₁ →+* C₂))).appTop =
      CommRingCat.ofHom (h : C₁ →+* C₂) ≫ (Scheme.ΓSpecIso (.of C₂)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (h : C₁ →+* C₂))).symm
  refine (CommRingCat.isPushout_tensorProduct (invariantRing G) Γ(G'.objects.left, ⊤)
    C₁).hom_ext ?_ ?_
  · refine ((comp_assoc_left (objectsTensorBaseRingIso_includeLeft F C₁ bc₁) _).trans
      hedgeL).trans ?_
    exact Eq.symm ((comp_assoc_left (includeLeft_comp_map_id_algHom F h) _).trans
      (objectsTensorBaseRingIso_includeLeft F C₂ bc₂))
  · refine (comp_assoc_left (objectsTensorBaseRingIso_includeRight F C₁ bc₁) _).trans ?_
    refine Eq.trans ?_ (comp_assoc_left₂ (includeRight_comp_map_id_algHom F h)
      (objectsTensorBaseRingIso_includeRight F C₂ bc₂)).symm
    refine ((Category.assoc _ _ _).trans
      (congrArg ((Scheme.ΓSpecIso (.of C₁)).inv ≫ ·) hedgeR)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (bc₂.groupoid.objects.hom ≫
      Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₂))).appTop) hnat)

/-- The comparison morphism read on elements: pullback of global functions along it is `id ⊗ h`
through the two tensor product presentations. -/
theorem appTop_tensorBaseRingComparison
    (e : letI := objectRingAlgebraOfHom F; Γ(G'.objects.left, ⊤) ⊗[invariantRing G] C₁) :
    letI := objectRingAlgebraOfHom F
    (tensorBaseRingComparison F h bc₁ bc₂).appTop.hom
        ((objectsTensorBaseRingIso F C₁ bc₁).hom.hom e) =
      (objectsTensorBaseRingIso F C₂ bc₂).hom.hom
        (Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G'.objects.left, ⊤)) h e) :=
  congr($(objectsTensorBaseRingIso_hom_comp_tensorBaseRingComparison_appTop F h bc₁ bc₂).hom e)

end AlgebraicGeometry.GroupoidScheme

end

end
