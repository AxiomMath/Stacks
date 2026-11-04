module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFiniteSingularities
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces

/-!
# Strict fullness of the substack of curves with finite singular locus (Stacks 0DZW)

The defining condition `AlgebraicGeometry.IsFiniteNonSmoothLocus` of the subcategory `Curves⁺`
of Stacks 0DZW is invariant under isomorphism of families of curves, so `Curves⁺` is a
*strictly full* subcategory of the category of families of curves: it is cut out by a property
of objects that is closed under isomorphisms, which is the first of the three conditions
making it an open substack.

The condition asks for a closed subspace of the total space whose points are exactly the
non-smooth points, which is reduced and finite over the base. An isomorphism of families of
curves is an isomorphism of total spaces over an isomorphism of base schemes, so the subspace
is transported by taking its image along the isomorphism of total spaces, and each of the four
clauses is transported by one of the invariance lemmas proved here.

## Main definitions

* `CategoryTheory.Subfunctor.mapIso`: the image of a subfunctor along an isomorphism of
  type-valued functors, with `CategoryTheory.Subfunctor.toMapIso` the induced isomorphism of
  the subfunctors themselves.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_mapIso`,
  `AlgebraicGeometry.Space.isClosedSubspace_mapIso`: being an open, resp. closed, subspace is
  carried along an isomorphism of the ambient presheaf.
* `AlgebraicGeometry.Space.isFinite_precomp_iso`,
  `AlgebraicGeometry.Space.isFinite_postcomp_iso`: finiteness of a morphism of algebraic
  spaces is unchanged by composing with an isomorphism on either side.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_of_iso`: an étale-local property of an
  algebraic space is carried along an isomorphism.
* `AlgebraicGeometry.Space.isSmoothAt_iso_iff`: smoothness at a point is unchanged by an
  isomorphism of the source and of the target of the morphism.
* `AlgebraicGeometry.curvesPlus_isStrictlyFull`: **Stacks 0DZW**, strict fullness of
  `Curves⁺`.

## Implementation notes

The invariance lemmas for the subspace conditions and for smoothness go through
`CategoryTheory.MorphismProperty.RespectsIso`, which `CategoryTheory.MorphismProperty.presheaf`
carries because relative representability is stable under base change; no new descent argument
is needed. Finiteness of Stacks 03ZP is not phrased as a `MorphismProperty`, so its two
invariance lemmas transport the defining pullback square by hand.

Only the first of the three conditions defining an open substack is proved here. The other two
— that `Curves⁺` is an algebraic stack and that its inclusion is a representable open immersion
— rest on the algebraicity of the stack of curves (Stacks 0D5A) and are not proved here.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 001D](https://stacks.math.columbia.edu/tag/001D)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F F' : C ⥤ Type w}

/-- The transport of a subfunctor along an isomorphism of type-valued functors: its image
under the isomorphism. -/
def mapIso (e : F ≅ F') (G : Subfunctor F) : Subfunctor F' := G.image e.hom

/-- The morphism from a subfunctor to its transport along an isomorphism of the ambient
functors. It is an isomorphism, by `CategoryTheory.Subfunctor.isIso_toMapIso`. -/
def toMapIso (e : F ≅ F') (G : Subfunctor F) : G.toFunctor ⟶ (G.mapIso e).toFunctor :=
  lift (G.ι ≫ e.hom) (by rw [range_comp, range_ι]; exact le_refl _)

/-- Transporting a subfunctor along an isomorphism commutes with the two inclusions. -/
@[reassoc]
lemma toMapIso_ι (e : F ≅ F') (G : Subfunctor F) :
    G.toMapIso e ≫ (G.mapIso e).ι = G.ι ≫ e.hom := rfl

instance isIso_toMapIso (e : F ≅ F') (G : Subfunctor F) : IsIso (G.toMapIso e) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have h : e.hom.app i x.1 = e.hom.app i y.1 := congrArg Subtype.val hxy
    have hinj : Function.Injective (e.hom.app i) := by
      rw [← mono_iff_injective]; infer_instance
    exact Subtype.ext (hinj h)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The inclusion of the transport of a subfunctor, written through the inclusion of the
subfunctor itself. -/
lemma mapIso_ι (e : F ≅ F') (G : Subfunctor F) :
    (G.mapIso e).ι = CategoryTheory.inv (G.toMapIso e) ≫ G.ι ≫ e.hom := by
  rw [← toMapIso_ι, IsIso.inv_hom_id_assoc]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A property holding on every étale chart of a morphism of algebraic spaces still holds on
every étale chart after precomposing with an isomorphism of the source.

This is the forward implication of the biconditional
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_precomp_iso`. -/
theorem holdsOnEveryEtaleChart_precomp_iso' (P : MorphismProperty Scheme.{u})
    (e : F ≅ G) (f : G ⟶ H) (h : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (e.hom ≫ f) := by
  intro U V a b k ha hb hsq
  exact h U V (a ≫ e.hom) b k
    (MorphismProperty.RespectsIso.postcomp _ e.hom a ha) hb (by rw [hsq]; simp)

/-- A property holding on every étale chart of a morphism of algebraic spaces still holds on
every étale chart after postcomposing with an isomorphism of the target. -/
theorem holdsOnEveryEtaleChart_postcomp_iso (P : MorphismProperty Scheme.{u})
    (f : F ⟶ G) (e : G ≅ H) (h : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (f ≫ e.hom) := by
  intro U V a b k ha hb hsq
  refine h U V a (b ≫ e.inv) k ha
    (MorphismProperty.RespectsIso.postcomp _ e.inv b hb) ?_
  rw [← Category.assoc, hsq]; simp

/-- Finiteness of a morphism of algebraic spaces is unchanged by precomposing with an
isomorphism of the source. -/
theorem isFinite_precomp_iso (e : F ≅ G) (f : G ⟶ H)
    (h : IsFinite B S hS f) : IsFinite B S hS (e.hom ≫ f) := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hp, hpb⟩ := h U hU ξ
  refine ⟨V, p, i ≫ e.inv, hV, hp, ?_⟩
  refine hpb.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

/-- Finiteness of a morphism of algebraic spaces is unchanged by postcomposing with an
isomorphism of the target. -/
theorem isFinite_postcomp_iso (f : F ⟶ G) (e : G ≅ H)
    (h : IsFinite B S hS f) : IsFinite B S hS (f ≫ e.hom) := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hp, hpb⟩ := h U hU (ξ ≫ e.inv)
  refine ⟨V, p, i, hV, hp, ?_⟩
  refine hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_ <;> simp

/-- An étale-local property of an algebraic space is carried along an isomorphism of
presheaves: the atlas witnessing it on the source composes with the isomorphism. -/
theorem hasEtaleLocalProperty_of_iso (P : ObjectProperty Scheme.{u}) (e : F ≅ G)
    (h : HasEtaleLocalProperty B S hS F P) : HasEtaleLocalProperty B S hS G P := by
  obtain ⟨U, f, hfs, hfe, hPU⟩ := h
  exact ⟨U, f ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom f hfs,
    MorphismProperty.RespectsIso.postcomp _ e.hom f hfe, hPU⟩

/-- The transport of an open subspace along an isomorphism of the ambient presheaf is an open
subspace. -/
theorem isOpenSubspace_mapIso (e : F ≅ G) (U : Subfunctor F)
    (h : IsOpenSubspace B S hS U) : IsOpenSubspace B S hS (U.mapIso e) := by
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (U.toMapIso e)) h.1, ?_⟩
  rw [Subfunctor.mapIso_ι]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ e.hom _ h.2)

/-- The transport of a closed subspace along an isomorphism of the ambient presheaf is a
closed subspace. -/
theorem isClosedSubspace_mapIso (e : F ≅ G) (U : Subfunctor F)
    (h : IsClosedSubspace B S hS U) : IsClosedSubspace B S hS (U.mapIso e) := by
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (U.toMapIso e)) h.1, ?_⟩
  rw [Subfunctor.mapIso_ι]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ e.hom _ h.2)

/-- If two morphisms of presheaves compose to the identity, the induced maps on points do too. -/
private theorem pointsMap_pointsMap_of_comp_eq_id {F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F' ⟶ G') (β : G' ⟶ F') (h : α ≫ β = 𝟙 F') (x : points B S hS F') :
    pointsMap B S hS G' β (pointsMap B S hS F' α x) = x := by
  rw [show pointsMap B S hS G' β (pointsMap B S hS F' α x) =
      (pointsMap B S hS G' β ∘ pointsMap B S hS F' α) x from rfl,
    ← pointsMap_comp, h, pointsMap_id, id_eq]

/-- Smoothness at a point is carried along an isomorphism of the source and of the target of
the morphism: the open subspace on which the morphism is smooth is transported by the
isomorphism of the source, and the point by the induced map on points. -/
theorem isSmoothAt_of_iso {K K' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F)
    (hx : IsSmoothAt B S hS f x) :
    IsSmoothAt B S hS g (pointsMap B S hS F e.hom x) := by
  obtain ⟨U, hU, x', hx', hsm⟩ := hx
  refine ⟨U.mapIso e, isOpenSubspace_mapIso B S hS e U hU,
    pointsMap B S hS U.toFunctor (U.toMapIso e) x', ?_, ?_⟩
  · rw [show pointsMap B S hS (U.mapIso e).toFunctor (U.mapIso e).ι
        (pointsMap B S hS U.toFunctor (U.toMapIso e) x') =
        pointsMap B S hS U.toFunctor (U.toMapIso e ≫ (U.mapIso e).ι) x' by
      rw [pointsMap_comp]; rfl]
    rw [Subfunctor.toMapIso_ι, pointsMap_comp]
    simp [hx']
  · rw [Subfunctor.mapIso_ι]
    simp only [Category.assoc]
    rw [hcomm]
    have h2 := holdsOnEveryEtaleChart_precomp_iso' B S hS
      (@AlgebraicGeometry.Smooth.{u}) (asIso (U.toMapIso e)).symm ((U.ι ≫ f) ≫ eK.hom)
      (holdsOnEveryEtaleChart_postcomp_iso B S hS _ (U.ι ≫ f) eK hsm)
    simpa using h2

/-- Smoothness at a point is invariant under an isomorphism of the source and of the target of
the morphism. -/
theorem isSmoothAt_iso_iff {K K' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F) :
    IsSmoothAt B S hS f x ↔ IsSmoothAt B S hS g (pointsMap B S hS F e.hom x) := by
  refine ⟨isSmoothAt_of_iso B S hS e eK f g hcomm x, fun h => ?_⟩
  have hcomm' : e.inv ≫ f = g ≫ eK.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm]; simp
  have h2 := isSmoothAt_of_iso B S hS e.symm eK.symm g f hcomm' _ h
  have h3 := pointsMap_pointsMap_of_comp_eq_id B S hS e.hom e.symm.hom e.hom_inv_id x
  rwa [h3] at h2

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DZW.** Membership in the subcategory `Curves⁺` of families of curves whose
reduced non-smooth locus is finite over the base is invariant under isomorphism, so `Curves⁺`
is a strictly full subcategory. -/
@[stacks 0DZW "open_substack"]
theorem curvesPlus_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsFiniteNonSmoothLocus B hZ).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y ee hX
  obtain ⟨Z, hclosed, hrange, hred, hfin⟩ := hX
  have htot : IsIso ee.hom.totalMap :=
    ⟨ee.inv.totalMap, congrArg CurveFamily.Hom.totalMap ee.hom_inv_id,
      congrArg CurveFamily.Hom.totalMap ee.inv_hom_id⟩
  have hbas : IsIso ee.hom.baseMap :=
    ⟨ee.inv.baseMap, congrArg CurveFamily.Hom.baseMap ee.hom_inv_id,
      congrArg CurveFamily.Hom.baseMap ee.inv_hom_id⟩
  let φ : X.total.obj ≅ Y.total.obj :=
    (ObjectProperty.ι (fun F : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B integerBase hZ F)).mapIso (asIso ee.hom.totalMap)
  let β : (schemeSpace X.base).obj ≅ (schemeSpace Y.base).obj :=
    yoneda.mapIso (asIso ee.hom.baseMap)
  have hcomm : φ.hom ≫ Y.toBase.hom = X.toBase.hom ≫ β.hom :=
    congrArg (fun h : X.total ⟶ schemeSpace Y.base => h.hom) ee.hom.cartesian.w
  have hround := Space.pointsMap_pointsMap_of_comp_eq_id B integerBase hZ φ.inv φ.hom φ.inv_hom_id
  refine ⟨Z.mapIso φ, Space.isClosedSubspace_mapIso B integerBase hZ φ Z hclosed, ?_, ?_, ?_⟩
  · have hpm : Space.pointsMap B integerBase hZ (Z.mapIso φ).toFunctor (Z.mapIso φ).ι
        = (Space.pointsMap B integerBase hZ X.total.obj φ.hom)
          ∘ ((Space.pointsMap B integerBase hZ Z.toFunctor Z.ι)
            ∘ (Space.pointsMap B integerBase hZ (Z.mapIso φ).toFunctor
                (CategoryTheory.inv (Z.toMapIso φ)))) := by
      rw [Subfunctor.mapIso_ι, Space.pointsMap_comp, Space.pointsMap_comp]
      rfl
    have hsurj : Function.Surjective
        (Space.pointsMap B integerBase hZ (Z.mapIso φ).toFunctor
          (CategoryTheory.inv (Z.toMapIso φ))) := by
      intro w
      exact ⟨Space.pointsMap B integerBase hZ Z.toFunctor (Z.toMapIso φ) w,
        Space.pointsMap_pointsMap_of_comp_eq_id B integerBase hZ _ _ (IsIso.hom_inv_id _) w⟩
    rw [hpm, Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
      hrange]
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun hcon => hx ((Space.isSmoothAt_iso_iff B integerBase hZ φ β
        X.toBase.hom Y.toBase.hom hcomm x).mpr hcon)
    · intro hy
      refine ⟨Space.pointsMap B integerBase hZ Y.total.obj φ.inv y, fun hcon => ?_, hround y⟩
      exact hy (hround y ▸ (Space.isSmoothAt_iso_iff B integerBase hZ φ β
        X.toBase.hom Y.toBase.hom hcomm _).mp hcon)
  · exact Space.hasEtaleLocalProperty_of_iso B integerBase hZ
      (fun W : Scheme.{u} => IsReduced W) (asIso (Z.toMapIso φ)) hred
  · rw [Subfunctor.mapIso_ι]
    simp only [Category.assoc]
    rw [hcomm]
    have h4 := Space.isFinite_precomp_iso B integerBase hZ (asIso (Z.toMapIso φ)).symm
      ((Z.ι ≫ X.toBase.hom) ≫ β.hom)
      (Space.isFinite_postcomp_iso B integerBase hZ (Z.ι ≫ X.toBase.hom) β hfin)
    simpa using h4

end AlgebraicGeometry

end
