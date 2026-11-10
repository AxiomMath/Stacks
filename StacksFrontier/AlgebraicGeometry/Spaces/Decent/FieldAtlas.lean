module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Decent algebraic spaces with an étale atlas by the spectrum of a field

Let `k` be a field and let `X` be an algebraic space over a scheme `S` admitting a surjective
étale morphism `Spec k ⟶ X`. If `X` is decent then `X` is the spectrum of a field `k'`, and `k`
is a finite separable extension of `k'`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_isDecentSpace_of_etale_fieldSpec`:
  **Stacks 03IK**.

## Implementation notes

The atlas makes `|X|` a singleton: the spectrum of a field has exactly one point in the sense of
Stacks 03BU, and the atlas is surjective on points. Decency produces at that point a field-valued
representative `Spec k' ⟶ X` which is a monomorphism of presheaves, so the atlas factors through
it, uniquely, by Stacks 0H2X. That factorization is the identification
`Spec k' ×_X Spec k = Spec k` which the source reads off from Stacks 03DP, and the factoring
morphism `χ : Spec k ⟶ Spec k'` is the projection the source is left with. A monomorphism
cancels, so the square with `χ` along one edge and an identity along the other is cartesian;
hence `χ` is étale, and it is surjective because both spectra have a single point. Therefore `k`
is a finite separable extension of `k'`.

Étaleness of the representative `Spec k' ⟶ X` itself then descends along `χ` by Stacks 03EC, and
an étale surjective monomorphism of algebraic spaces is an isomorphism by Stacks 05W5. That is
the form in which the last step of the source argument is carried out here, in place of the
quasi-compact flat surjective monomorphism of Stacks 0B8C; quasi-compactness of the
representative, which decency also supplies, is consequently not used.

The quasi-separated analogue, with the same conclusion, is
`AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_surjective_etale_fieldSpec`, which is
Stacks 03DZ. That a decent algebraic space whose point set is a singleton is a scheme is
Stacks 047Z, `AlgebraicGeometry.Space.isRepresentable_of_subsingleton_points`.

The spectrum of `k` is taken as the object of the big fppf site over `S` determined by a
structure morphism `b : Spec k ⟶ S`, and the spectrum of `k'` is produced in the same form. The
last clause of the conclusion records that the identification of `X` with `Spec k'` carries the
given atlas to the morphism of site objects induced by the field extension.

## References

* [Stacks Project, Tag 03IK](https://stacks.math.columbia.edu/tag/03IK)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks Project, Tag 03IK.** Let `S` be a scheme, let `k` be a field and let `F` be an
algebraic space over `S` admitting a surjective étale morphism from the spectrum of `k`. If `F`
is decent then `F` is represented by the spectrum of a field `k'` over `S`, with `k` a finite
separable extension of `k'`, and under that identification the given morphism is the one induced
by the extension `k/k'`. -/
@[stacks 03IK]
theorem exists_iso_yoneda_spec_of_isDecentSpace_of_etale_fieldSpec
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hdecent : IsDecentSpace B S hS F)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (f : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ F)
    (hsurj : IsSurjective B S hS f)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (_ : Module.Finite k' k)
      (_ : Algebra.IsSeparable k' k) (hk' : B.Contains (Spec (.of k')))
      (b' : Spec (.of k') ⟶ S),
      ∃ (hbase : Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ b' = b)
        (e : F ≅ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))),
        f ≫ e.hom = yoneda.map (Over.homMk
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k' k))) :
            B.obj hk ⟶ B.obj hk') (by
              apply ObjectProperty.hom_ext
              simpa using hbase)) := by
  classical
  -- The given atlas, read as a field-valued point of `F`.
  let q : FieldValuedPoint B S hS F :=
    { carrier := k, contained := hk, toBase := b, value := yonedaEquiv f }
  have hfq : fieldMorphism B S hS F q = f := yonedaEquiv.symm_apply_apply f
  -- Decency supplies a monomorphic field-valued representative of that point.
  obtain ⟨p, hp, hmono⟩ :=
    IsDecentSpace.hasMonomorphicFieldRepresentative B S hS F hdecent (q.class B S hS F)
  have hmono' : Mono (fieldMorphism B S hS F p) := hmono
  -- The atlas factors through it, which is the identification `Spec k' ×_F Spec k = Spec k`.
  obtain ⟨χ, hχval, -⟩ :=
    FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS F hF p q hp
  have hχ : yoneda.map χ ≫ fieldMorphism B S hS F p = f := by
    change yoneda.map χ ≫ yonedaEquiv.symm p.value = f
    rw [yonedaEquiv_symm_naturality_left χ F p.value, hχval]
    exact hfq
  -- A monomorphism cancels, so the factorization square is cartesian and `χ` is étale.
  rw [← hχ] at hetale
  have hχetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map χ) :=
    hetale.property _ (𝟙 _) χ (IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩)
  have hχsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map χ) := by
    change AlgebraicGeometry.Surjective
      (show Spec (.of k) ⟶ Spec (.of p.carrier) from (BigFppfOver.toScheme B S hS).map χ)
    exact ⟨fun z ↦ ⟨Classical.arbitrary (Spec (CommRingCat.of k)), Subsingleton.elim _ z⟩⟩
  -- Hence `k` is a finite separable extension of the field of the representative.
  let α : p.carrier →+* k := (Spec.preimage ((BigFppfOver.toScheme B S hS).map χ)).hom
  let _ : Algebra p.carrier k := α.toAlgebra
  have hα : Spec.map (CommRingCat.ofHom (algebraMap p.carrier k)) =
      (BigFppfOver.toScheme B S hS).map χ := Spec.map_preimage _
  have : Algebra.Etale p.carrier k :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale.{u})
      (φ := CommRingCat.ofHom (algebraMap p.carrier k))).mp (by rwa [hα]))
  have : Module.Finite p.carrier k := Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable p.carrier k := Algebra.FormallyUnramified.isSeparable _ _
  -- Étaleness of the representative descends along `χ`, and it is surjective on points.
  have hgSurj : IsSurjective B S hS (fieldMorphism B S hS F p) := fun y ↦ by
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨pointsMap B S hS _ (yoneda.map χ) z, by rw [← pointsMap_comp_apply, hχ]; exact hz⟩
  have hgiso : IsIso (fieldMorphism B S hS F p) :=
    isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS F)) hF (fieldMorphism B S hS F p)
      (isEtale_of_presheaf_etale B S hS
        (etale_of_comp_surjective_etale B S hS hF χ (fieldMorphism B S hS F p) hetale))
      (universallyInjective_of_mono B S hS (fieldMorphism B S hS F p) hmono') hgSurj
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap p.carrier k)) ≫ p.toBase = b := by
    rw [hα]
    exact congrArg (·.hom) (Over.w χ)
  refine ⟨p.carrier, p.field, inferInstance, inferInstance, inferInstance, p.contained, p.toBase,
    hbase, (asIso (fieldMorphism B S hS F p)).symm, ?_⟩
  change f ≫ inv (fieldMorphism B S hS F p) = _
  rw [← hχ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  congr 1
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact hα.symm

end AlgebraicGeometry.Space

-- Remark 03E0 observes that the quasi-separatedness hypothesis of Stacks 03DZ may be weakened to
-- decency; that weakening is the statement of Stacks 03IK above.
add_to_stacks 03E0 "Stacks 03DZ holds for decent algebraic spaces"
  AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_isDecentSpace_of_etale_fieldSpec

end
