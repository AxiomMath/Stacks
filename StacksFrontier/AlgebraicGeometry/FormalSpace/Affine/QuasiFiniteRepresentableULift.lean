module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.QuasiFiniteRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Quasi-finite morphisms out of affine formal algebraic spaces at the value universe

Let `S` be a scheme contained in a big fppf site `B`. A morphism of presheaves of `Type (u + 1)`
on the big fppf site of `S` whose source is an affine formal algebraic space, which is
representable by algebraic spaces and whose represented base changes are locally quasi-finite,
is representable by objects of the site. This file proves it relative to the universe-lifted
Yoneda embedding, and, for étale morphisms of fppf sheaves to a target with `u`-small sections,
relative to the sheafified Yoneda embedding.

## Main results

* `AlgebraicGeometry.FormalSpace.holdsOnEveryEtaleChartULift_iso_comp`: a property of scheme
  morphisms holding on every étale chart is unchanged by an isomorphism of the source.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isAffineFormalAlgebraicSpaceULift`:
  a morphism out of an affine formal algebraic space which is representable by algebraic spaces
  with locally quasi-finite base changes is relatively representable along the universe-lifted
  Yoneda embedding.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_sheafifiedYoneda_iff_uliftYoneda`:
  relative representability along the sheafified Yoneda embedding is relative representability
  of the underlying morphism of presheaves along the universe-lifted Yoneda embedding.
* `AlgebraicGeometry.FormalSpace.isEtaleULift_of_iso_source`: étaleness in a value universe
  above the schemes transports along an isomorphism of the source.
* `FormalSpace.relativelyRepresentable_sheafifiedYoneda_of_isAffineFormalAlgebraicSpace`:
  a morphism of fppf sheaves out of an affine formal algebraic space to a sheaf with `u`-small
  sections which is representable by algebraic spaces and étale is relatively representable
  along the sheafified Yoneda embedding.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_atlas_of_isFormalAlgebraicSpace`: each
  arrow of an atlas of a formal algebraic space is representable by objects of the site.

## Implementation notes

Local quasi-finiteness of the base changes is written out as
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartULift` at the property
`LocallyOfFiniteType ⊓ LocallyQuasiFinite`, the body of
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` in the larger value universe.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance (priority := high) hasPullback_presheaf_QuasiFiniteRepresentableULift.{v}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A property of scheme morphisms which holds on every étale chart of a morphism holds on
every étale chart of that morphism precomposed with an isomorphism. -/
theorem holdsOnEveryEtaleChartULift_iso_comp (P : MorphismProperty Scheme.{u})
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F' ≅ F) (f : F ⟶ G)
    (hf : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P f) :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P (e.hom ≫ f) := by
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) := .mk _
    (fun _ _ hf => by let := hf; infer_instance)
    (fun _ _ hf => by let := hf; infer_instance)
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  intro U V a b h ha hb hw
  exact hf U V (a ≫ e.hom) b h (MorphismProperty.RespectsIso.postcomp _ e.hom _ ha) hb
    (by rwa [Category.assoc])

/-- The sheafification of a presheaf of `Type u` lifted to `Type (u + 1)` is an affine formal
algebraic space if the lift is isomorphic to one. -/
private theorem isAffineFormalAlgebraicSpace_sheafification_of_iso_uliftFunctor
    {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (eX : X₀ ⋙ uliftFunctor.{u + 1, u} ≅ X.obj) :
    IsAffineFormalAlgebraicSpace B S hS ((presheafToSheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).obj (X₀ ⋙ uliftFunctor.{u + 1, u})) :=
  isAffineFormalAlgebraicSpace_of_iso B S hS
    (asIso ((sheafificationNatIso (BigFppfOver.topology B S hS) (Type (u + 1))).hom.app X) ≪≫
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso eX).symm) hX

/-- Let `S` be a scheme contained in a big fppf site `B`, let `X` be an affine formal algebraic
space over `S` and let `f : X ⟶ Y` be a morphism to a presheaf of `Type (u + 1)` on the big fppf
site of `S` which is representable by algebraic spaces and whose represented base changes are
locally quasi-finite. Then `f` is representable by objects of the site. -/
@[stacks 0AIG "the tag read at the value universe Type (u+1), where a formal algebraic space \
and the affine formal algebraic spaces of its atlas of Definition 0AIM live, so that the tag \
applies to an atlas member. Nothing is assumed beyond the Type u reading: the smallness that \
one asks of its affine formal algebraic space is supplied by the set-theoretic condition of \
Stacks 0AIS, which an affine formal algebraic space carries, and the smallness of the base \
change by its being an algebraic space"]
theorem relativelyRepresentable_of_isAffineFormalAlgebraicSpaceULift
    {X : FppfSheaf B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X.obj ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f)
    (hlqf : ∀ (T : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y),
      Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        (pullback.fst ξ f)) :
    uliftYoneda.{u + 1}.relativelyRepresentable f := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let L := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  have hXsm : FunctorToTypes.Small.{u} X.obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS X hX.1
  let X₀ : Cᵒᵖ ⥤ Type u := FunctorToTypes.shrink.{u} X.obj
  let eX : L.obj X₀ ≅ X.obj := Space.shrinkCompUliftFunctorIso.{u + 1} X.obj
  have hX₀sheaf : Presheaf.IsSheaf J X₀ :=
    Presheaf.isSheaf_of_isSheaf_comp J X₀ uliftFunctor.{u + 1, u}
      ((Presheaf.isSheaf_of_iso_iff eX).mpr X.property)
  let XS : Sheaf J (Type u) := ⟨X₀, hX₀sheaf⟩
  have hXS := isAffineFormalAlgebraicSpace_sheafification_of_iso_uliftFunctor B S hS hX eX
  have hess : ∀ (T : C) (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y),
      uliftYoneda.{u + 1}.essImage (pullback ξ f) := by
    intro T ξ
    obtain ⟨P₀, hP₀, ⟨eP⟩⟩ :=
      Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS (hf T ξ)
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : P₀ ⟶ yoneda.obj T,
        L.map q₀ = eP.hom ≫ pullback.fst ξ f := L.map_surjective _
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : P₀ ⟶ XS.1,
        L.map r₀ = eP.hom ≫ pullback.snd ξ f ≫ eX.inv := L.map_surjective _
    have hjm : ∀ {Z : Cᵒᵖ ⥤ Type u} (g₁ g₂ : Z ⟶ P₀),
        g₁ ≫ q₀ = g₂ ≫ q₀ → g₁ ≫ r₀ = g₂ ≫ r₀ → g₁ = g₂ := by
      intro Z g₁ g₂ h₁ h₂
      have e₁ := congrArg L.map h₁
      have e₂ := congrArg L.map h₂
      rw [L.map_comp, L.map_comp, hq₀] at e₁
      rw [L.map_comp, L.map_comp, hr₀] at e₂
      refine L.map_injective ((cancel_mono eP.hom).1 (pullback.hom_ext ?_ ?_))
      · simp only [Category.assoc]
        exact e₁
      · exact (cancel_mono eX.inv).1 (by simp only [Category.assoc]; exact e₂)
    have hlqf₀ : Space.IsLocallyQuasiFinite B S hS q₀ := by
      refine (Space.holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS _ q₀).mp ?_
      have hq₀' : Functor.whiskerRight q₀ uliftFunctor.{u + 1, u} =
        eP.hom ≫ pullback.fst ξ f := hq₀
      rw [hq₀']
      exact holdsOnEveryEtaleChartULift_iso_comp B S hS _ eP _ (hlqf T ξ)
    have hrep := isRepresentable_of_isAffineFormalAlgebraicSpace_of_jointlyMono B S hS XS hXS
      hP₀ q₀ r₀ hjm hlqf₀
    exact ⟨P₀.reprX, ⟨(L.mapIso P₀.reprW : uliftYoneda.{u + 1}.obj P₀.reprX ≅ L.obj P₀) ≪≫ eP⟩⟩
  intro T ξ
  obtain ⟨V, ⟨e⟩⟩ := hess T ξ
  refine ⟨V, uliftYoneda.{u + 1}.preimage (e.hom ≫ pullback.fst ξ f),
    e.hom ≫ pullback.snd ξ f, ?_⟩
  refine (IsPullback.of_iso_pullback ⟨?_⟩ e
    ((uliftYoneda.{u + 1}).map_preimage _).symm rfl).flip
  rw [(uliftYoneda.{u + 1}).map_preimage, Category.assoc, Category.assoc, pullback.condition]

/-- Relative representability of a morphism of fppf sheaves along the sheafified Yoneda
embedding is relative representability of the underlying morphism of presheaves along the
universe-lifted Yoneda embedding. -/
theorem relativelyRepresentable_sheafifiedYoneda_iff_uliftYoneda
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f ↔
      (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable f.hom := by
  let J := BigFppfOver.topology B S hS
  let L := sheafToPresheaf J (Type (u + 1))
  exact ⟨fun h => Space.relativelyRepresentable_of_iso_embedding'
      (sheafifiedYonedaCompForgetIso' B S hS) (L.map f)
      ((Space.relativelyRepresentable_comp_map_iff (Sheaf.sheafifiedYoneda J) L f).mpr h),
    fun h => (Space.relativelyRepresentable_comp_map_iff (Sheaf.sheafifiedYoneda J) L f).mp
      (Space.relativelyRepresentable_of_iso_embedding'
        (sheafifiedYonedaCompForgetIso' B S hS).symm (L.map f) h)⟩

/-- Étaleness in a value universe above the schemes transports along an isomorphism of the
source commuting with the two morphisms. -/
theorem isEtaleULift_of_iso_source
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ F')
    {g : F ⟶ G} {g' : F' ⟶ G} (hcomp : e.hom ≫ g' = g)
    (h : Space.IsEtaleULift.{u + 1} B S hS g') :
    Space.IsEtaleULift.{u + 1} B S hS g := by
  intro U φ hφ
  have hφ' := MorphismProperty.RespectsIso.postcomp
    (P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})) e.hom φ hφ
  have := h U (φ ≫ e.hom) hφ'
  rwa [Category.assoc, hcomp] at this

/-- Let `f : X ⟶ Y` be a morphism of fppf sheaves of `Type (u + 1)` on the big fppf site of `S`
with `X` an affine formal algebraic space and `Y` with `u`-small sections. If `f` is
representable by algebraic spaces and each represented base change of `f` is étale over the
point it is taken along, then `f` is representable by objects of the site. -/
theorem relativelyRepresentable_sheafifiedYoneda_of_isAffineFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : FunctorToTypes.Small.{u} Y.obj)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hf) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  obtain ⟨X₀, hX₀, ⟨eX⟩⟩ := exists_comp_uliftFunctor_iso_of_small B S hS
    (small_of_isAffineFormalAlgebraicSpace B S hS hX)
  obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := exists_comp_uliftFunctor_iso_of_small B S hS hY
  let f₀ : X₀ ⟶ Y₀ := H.preimage (eX.hom ≫ f.hom ≫ eY.inv)
  have hf₀map : H.map f₀ = eX.hom ≫ f.hom ≫ eY.inv := H.map_preimage _
  have hsq : IsPullback eX.hom (H.map f₀) f.hom eY.hom := by
    apply IsPullback.of_horiz_isIso
    simp [f₀, H.map_preimage]
  have hf₀ : Space.IsRepresentableByAlgebraicSpaces B S hS f₀ :=
    (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f₀).mp
      (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hsq hf)
  have hXaff := isAffineFormalAlgebraicSpace_sheafification_of_iso_uliftFunctor B S hS hX eX
  have hlqf : ∀ (T : C) (ξ : yoneda.obj T ⟶ Y₀),
      Space.IsLocallyQuasiFinite B S hS (pullback.fst ξ f₀) := by
    intro T ξ
    apply Space.isLocallyQuasiFinite_of_isEtale' B S hS
    rw [← Space.isEtaleULift_whiskerRight_iff.{u + 1} B S hS (pullback.fst ξ f₀)]
    have hpb0 : IsPullback (H.map (pullback.fst ξ f₀)) (H.map (pullback.snd ξ f₀))
        (H.map ξ) (H.map f₀) :=
      Space.isPullback_whiskerRight B S hS (IsPullback.of_hasPullback ξ f₀)
    have hpb : IsPullback (H.map (pullback.fst ξ f₀))
        (H.map (pullback.snd ξ f₀) ≫ eX.hom) (H.map ξ ≫ eY.hom) f.hom :=
      hpb0.of_iso (Iso.refl _) (Iso.refl _) eX eY (by simp) (by simp) (by simp)
        (by simpa using hsq.w.symm)
    exact isEtaleULift_of_iso_source B S hS
      (hpb.isoIsPullback _ _ (IsPullback.of_hasPullback (H.map ξ ≫ eY.hom) f.hom))
      (hpb.isoIsPullback_hom_fst _ _ _) (het T (H.map ξ ≫ eY.hom))
  have h0 := relativelyRepresentable_of_isAffineFormalAlgebraicSpace B S hS
    ⟨X₀, hX₀⟩ Y₀ f₀ hXaff hf₀ hlqf
  have h1 : (uliftYoneda.{u + 1} (C := C)).relativelyRepresentable (H.map f₀) :=
    (Space.relativelyRepresentable_comp_map_iff yoneda H f₀).mpr h0
  rw [hf₀map] at h1
  rw [relativelyRepresentable_sheafifiedYoneda_iff_uliftYoneda]
  have h2 := (MorphismProperty.cancel_left_of_respectsIso
    (P := (uliftYoneda.{u + 1} (C := C)).relativelyRepresentable) eX.hom
    (f.hom ≫ eY.inv)).mp h1
  exact (MorphismProperty.cancel_right_of_respectsIso
    (P := (uliftYoneda.{u + 1} (C := C)).relativelyRepresentable) f.hom eY.inv).mp h2

/-- The arrows of an atlas of a formal algebraic space, each out of an affine formal algebraic
space, representable by algebraic spaces and étale, are representable by objects of the site. -/
theorem relativelyRepresentable_atlas_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hfi : ∀ i, ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hrep)
    (i : I) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable (f i) := by
  obtain ⟨hrep, het⟩ := hfi i
  exact relativelyRepresentable_sheafifiedYoneda_of_isAffineFormalAlgebraicSpace B S hS (f i)
    (hXi i) (small_of_isFormalAlgebraicSpace B S hS hX) hrep het

end AlgebraicGeometry.FormalSpace

end
