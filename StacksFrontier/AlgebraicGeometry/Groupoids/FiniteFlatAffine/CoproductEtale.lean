module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct

/-!
# Étaleness of the map on invariant rings along a disjoint union

Let `F : G' ⟶ G` be a morphism of groupoid schemes and suppose `G'` is the disjoint union of two
groupoid schemes `G₁` and `G₂`. Then the invariant ring `C'` of `G'` is the product of the two
invariant rings, and `Spec C'` is correspondingly the disjoint union of `Spec C₁` and `Spec C₂`,
each included as an open subscheme. Consequently the map
`Spec C' ⟶ Spec C` induced by `F` is étale at every point of the first piece as soon as the
composite `Spec C₁ ⟶ Spec C' ⟶ Spec C` is étale — with no hypothesis at all on the second piece.

When the first piece is `G` itself, included by a morphism `F₁ : G ⟶ G'` whose map on object
schemes is a section of that of `F`, that composite is the identity, so the hypothesis is
automatic: the map on invariant rings becomes `c ↦ (c, χ c)` and is étale at every point of the
first piece unconditionally.

## Main results

* `AlgebraicGeometry.GroupoidScheme.invariantRingMap_comp_coe`: the composite of the maps on
  invariant rings induced by two morphisms is induced by the composite on object schemes.
* `AlgebraicGeometry.GroupoidScheme.isOpenImmersion_specMap_invariantRingMap`: each piece of a
  disjoint union is an open subscheme of the invariant spectrum.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_etale_left`: **the map on
  invariant rings is étale at every point of the first piece as soon as the first piece is étale
  over `Spec C`.**
* `AlgebraicGeometry.GroupoidScheme.invariantRingMap_comp_eq_id`: a section on object schemes
  induces a retraction of the map on invariant rings.
* `AlgebraicGeometry.GroupoidScheme.invariantRingProdHom_comp_invariantRingMap`: for a split
  disjoint union the map on invariant rings, read through the product decomposition of the
  invariant ring of `G'`, is `c ↦ (c, χ c)`.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap`: **for a split disjoint
  union the map on invariant rings is étale at every point of the first piece**, with no further
  hypothesis.
* `AlgebraicGeometry.GroupoidScheme.etale_specMap_invariantRingMap_of_etale_right`: it is étale
  everywhere as soon as the map out of the second piece is.

## Implementation notes

The hypothesis that `F₁` is a section of `F` is stated on object schemes, as
`F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left`.

## References

* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-! ### The composite of two maps on invariant rings -/

/-- Pullback of an invariant function along two successive morphisms of groupoid schemes is
pullback along the composite of the two maps on object schemes. -/
theorem invariantRingMap_comp_coe {G G' G₁ : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
    (F₁ : GroupoidScheme.Hom G₁ G') (c : invariantRing G) :
    ((invariantRingMap F₁ (invariantRingMap F c) : invariantRing G₁) :
        Γ(G₁.objects.left, ⊤)) =
      (F₁.mapObjects.left ≫ F.mapObjects.left).appTop.hom (c : Γ(G.objects.left, ⊤)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rfl

/-! ### The pieces of the invariant spectrum of a disjoint union -/

section Pieces

variable {G G' G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (F₁ : GroupoidScheme.Hom G₁ G') (F₂ : GroupoidScheme.Hom G₂ G')

/-- The morphism of spectra induced by the first piece of a disjoint union is the first
coproduct injection, read through the presentation of the invariant spectrum of `G'` as a
binary coproduct. -/
theorem specMap_invariantRingMap_eq_inl_comp (h : IsCoproductDecomposition F₁ F₂) :
    Spec.map (CommRingCat.ofHom (invariantRingMap F₁)) =
      coprod.inl ≫ h.invariantSpectrumCoprodIso.hom :=
  (h.inl_invariantSpectrumCoprodIso_hom).symm

/-- **The first piece of the invariant spectrum is an open subscheme.** -/
theorem isOpenImmersion_specMap_invariantRingMap (h : IsCoproductDecomposition F₁ F₂) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (invariantRingMap F₁))) := by
  rw [specMap_invariantRingMap_eq_inl_comp F₁ F₂ h]
  infer_instance

/-- **The map on invariant rings is étale at every point of a piece which is itself étale over
`Spec C`.** Nothing is assumed about the other piece. -/
theorem etaleAt_specMap_invariantRingMap_of_etale_left (h : IsCoproductDecomposition F₁ F₂)
    (hleft : Etale (Spec.map (CommRingCat.ofHom (invariantRingMap F₁)) ≫
      Spec.map (CommRingCat.ofHom (invariantRingMap F))))
    (x : Spec (.of (invariantRing G₁))) :
    EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
      ((Spec.map (CommRingCat.ofHom (invariantRingMap F₁))).base x) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (invariantRingMap F₁))) :=
    isOpenImmersion_specMap_invariantRingMap F₁ F₂ h
  exact Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp
    (Spec.map (CommRingCat.ofHom (invariantRingMap F₁)))
    (Spec.map (CommRingCat.ofHom (invariantRingMap F))) x
    ((etale_iff_forall_etaleAt _).mp hleft x)

end Pieces

/-! ### A split disjoint union -/

section Split

variable {G G' G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (F₁ : GroupoidScheme.Hom G G') (F₂ : GroupoidScheme.Hom G₂ G')

/-- **A section on object schemes gives a retraction on invariant rings.** If the map on object
schemes of `F₁ : G ⟶ G'` is a section of that of `F : G' ⟶ G`, then the map on invariant rings
induced by `F₁` is a retraction of the one induced by `F`. -/
theorem invariantRingMap_comp_eq_id
    (hsec : F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    (invariantRingMap F₁).comp (invariantRingMap F) = RingHom.id (invariantRing G) :=
  RingHom.ext fun c => Subtype.ext <| by
    rw [RingHom.comp_apply, invariantRingMap_comp_coe, hsec, Scheme.Hom.id_appTop]
    rfl

/-- **The map on invariant rings of a split disjoint union is `c ↦ (c, χ c)`.** Read through the
product decomposition of the invariant ring of `G'`, the map on invariant rings induced by `F`
has the identity as its first component and the map induced by the second piece as its
second. -/
theorem invariantRingProdHom_comp_invariantRingMap
    (hsec : F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    (invariantRingProdHom F₁ F₂).comp (invariantRingMap F) =
      RingHom.prod (RingHom.id (invariantRing G))
        ((invariantRingMap F₂).comp (invariantRingMap F)) := by
  refine RingHom.ext fun c => Prod.ext ?_ rfl
  exact congrArg (fun k : invariantRing G →+* invariantRing G => k c)
    (invariantRingMap_comp_eq_id F F₁ hsec)

/-- **On the first piece of a split disjoint union the map on invariant spectra is the
identity.** -/
theorem specMap_invariantRingMap_comp_specMap
    (hsec : F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    Spec.map (CommRingCat.ofHom (invariantRingMap F₁)) ≫
        Spec.map (CommRingCat.ofHom (invariantRingMap F)) =
      𝟙 (Spec (.of (invariantRing G))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, invariantRingMap_comp_eq_id F F₁ hsec]
  simp

/-- **The map on invariant rings is étale at every point of the first piece of a split disjoint
union.** -/
theorem etaleAt_specMap_invariantRingMap (h : IsCoproductDecomposition F₁ F₂)
    (hsec : F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (x : Spec (.of (invariantRing G))) :
    EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
      ((Spec.map (CommRingCat.ofHom (invariantRingMap F₁))).base x) :=
  etaleAt_specMap_invariantRingMap_of_etale_left F F₁ F₂ h
    (by rw [specMap_invariantRingMap_comp_specMap F F₁ hsec]; infer_instance) x

/-- **The map on invariant rings of a split disjoint union is étale as soon as its restriction
to the second piece is.** -/
theorem etale_specMap_invariantRingMap_of_etale_right (h : IsCoproductDecomposition F₁ F₂)
    (hsec : F₁.mapObjects.left ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hright : Etale (Spec.map (CommRingCat.ofHom (invariantRingMap F₂)) ≫
      Spec.map (CommRingCat.ofHom (invariantRingMap F)))) :
    Etale (Spec.map (CommRingCat.ofHom (invariantRingMap F))) := by
  have hdesc : h.invariantSpectrumCoprodIso.hom ≫
      Spec.map (CommRingCat.ofHom (invariantRingMap F)) =
      coprod.desc (𝟙 (Spec (.of (invariantRing G))))
        (Spec.map (CommRingCat.ofHom (invariantRingMap F₂)) ≫
          Spec.map (CommRingCat.ofHom (invariantRingMap F))) := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← Category.assoc, h.inl_invariantSpectrumCoprodIso_hom,
        specMap_invariantRingMap_comp_specMap F F₁ hsec]
    · rw [coprod.inr_desc, ← Category.assoc, h.inr_invariantSpectrumCoprodIso_hom]
  have hcoprod : Etale (coprod.desc (𝟙 (Spec (.of (invariantRing G))))
      (Spec.map (CommRingCat.ofHom (invariantRingMap F₂)) ≫
        Spec.map (CommRingCat.ofHom (invariantRingMap F)))) :=
    etale_coprod _ _ inferInstance hright
  rw [← hdesc] at hcoprod
  have heq : Spec.map (CommRingCat.ofHom (invariantRingMap F)) =
      h.invariantSpectrumCoprodIso.inv ≫ (h.invariantSpectrumCoprodIso.hom ≫
        Spec.map (CommRingCat.ofHom (invariantRingMap F))) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [heq]
  infer_instance

end Split

end AlgebraicGeometry.GroupoidScheme

end

end
