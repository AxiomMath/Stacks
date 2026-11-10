module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Properness of large-valued morphisms over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`. A morphism of algebraic spaces over `V`
with values in `Type (u + 1)` is proper exactly when the induced morphism of the presheaves on the
big fppf site of `S` attached by Stacks 04SG is proper; and a morphism of presheaves with values in
`Type (u + 1)` on the big fppf site of `V` is representable by algebraic spaces and proper, in the
sense used for formal algebraic spaces, exactly when the induced morphism over `S` is.

## Main results

* `AlgebraicGeometry.FormalSpace.isProperULift_smallerBaseULiftMap_iff`: properness of morphisms
  of algebraic spaces.
* `AlgebraicGeometry.FormalSpace.representableProper_smallerBaseULiftMap_iff`: representable
  proper morphisms.

## Implementation notes

For morphisms of algebraic spaces both sides are universe lifts of morphisms of algebraic spaces
with values in `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), properness is
unchanged by the universe lift (`AlgebraicGeometry.Space.isProperULift_whiskerRight_iff`), and for
values in `Type u` it is unchanged by the change of base
(`AlgebraicGeometry.Space.isProper_relocalize_iff`).

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- Properness of a morphism of algebraic spaces with values in `Type (u + 1)` depends only on the
arrow up to isomorphism. -/
theorem isProperULift_iff_of_arrowIso {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (hG : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G)
    (hF' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F')
    (hG' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G')
    (f : F ⟶ G) (f' : F' ⟶ G') (e₁ : F ≅ F') (e₂ : G ≅ G') (w : e₁.hom ≫ f' = f ≫ e₂.hom) :
    Space.IsProperULift.{u + 1} B S hS f ↔ Space.IsProperULift.{u + 1} B S hS f' := by
  let P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) =>
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS F
  exact MorphismProperty.arrow_mk_iso_iff (Space.properPropertyULift.{u + 1} B S hS)
    (Arrow.isoMk (ObjectProperty.isoMk P (X := ⟨F, hF⟩) (Y := ⟨F', hF'⟩) e₁)
      (ObjectProperty.isoMk P (X := ⟨G, hG⟩) (Y := ⟨G', hG'⟩) e₂)
      (by ext1; exact w)
      : Arrow.mk (ObjectProperty.homMk f : (⟨F, hF⟩ : Space.AlgebraicSpacesULift.{u + 1} B S hS) ⟶
          ⟨G, hG⟩) ≅ Arrow.mk (ObjectProperty.homMk f' :
          (⟨F', hF'⟩ : Space.AlgebraicSpacesULift.{u + 1} B S hS) ⟶ ⟨G', hG'⟩))

/-- The comparison `AlgebraicGeometry.FormalSpace.smallerBaseULiftWhiskerIso` is natural. -/
@[reassoc]
theorem smallerBaseULiftWhiskerIso_hom_naturality {G₀ G₀' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u}
    (k₀ : G₀ ⟶ G₀') :
    smallerBaseULiftMap B V S hV hS g (Functor.whiskerRight k₀ uliftFunctor.{u + 1}) ≫
        (smallerBaseULiftWhiskerIso B V S hV hS g G₀').hom =
      (smallerBaseULiftWhiskerIso B V S hV hS g G₀).hom ≫
        Functor.whiskerRight ((smallerBasePresheafEquivalence B V S hV hS g).functor.map k₀).left
          uliftFunctor.{u + 1} := by
  ext
  rfl

/-- Properness of the change of base of a morphism of presheaves with values in `Type u` is
computed by either description of the attached presheaf. -/
theorem isProper_smallerBasePresheafEquivalence_map_iff
    {P₀ Q₀ : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u} (k₀ : P₀ ⟶ Q₀) :
    Space.IsProper B S hS ((smallerBasePresheafEquivalence B V S hV hS g).functor.map k₀).left ↔
      Space.IsProper B S hS ((OverShriek.relocalizePresheafFunctor g).map k₀) :=
  ⟨Space.isProper_of_arrowIso B S hS _ _ _ _
      ((smallerBasePresheafForgetIso B V S hV hS g).hom.naturality k₀).symm,
    Space.isProper_of_arrowIso B S hS _ _ _ _
      ((smallerBasePresheafForgetIso B V S hV hS g).inv.naturality k₀).symm⟩

/-- **Properness of morphisms of algebraic spaces does not see the change of base.** -/
theorem isProperULift_smallerBaseULiftMap_iff {P Q : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Space.IsAlgebraicSpaceULift.{u + 1} B V hV P)
    (hQ : Space.IsAlgebraicSpaceULift.{u + 1} B V hV Q) (k : P ⟶ Q) :
    Space.IsProperULift.{u + 1} B S hS (smallerBaseULiftMap B V S hV hS g k) ↔
      Space.IsProperULift.{u + 1} B V hV k := by
  let Ψ := smallerBasePresheafEquivalence B V S hV hS g
  obtain ⟨P₀, hP₀, ⟨eP⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift.{u + 1} B V hV hP
  obtain ⟨Q₀, hQ₀, ⟨eQ⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift.{u + 1} B V hV hQ
  obtain ⟨k₀, hk₀⟩ := Space.exists_whiskerRight_eq.{u + 1} B V hV (F := P₀) (G := Q₀)
    (eP.hom ≫ k ≫ eQ.inv)
  have hΨP : IsAlgebraicSpace B S hS (Ψ.functor.obj P₀).left :=
    ((spacesOverSmallerBaseFunctor B V S hV hS g).obj ⟨P₀, hP₀⟩).2
  have hΨQ : IsAlgebraicSpace B S hS (Ψ.functor.obj Q₀).left :=
    ((spacesOverSmallerBaseFunctor B V S hV hS g).obj ⟨Q₀, hQ₀⟩).2
  have h1 : Space.IsProperULift.{u + 1} B V hV k ↔
      Space.IsProperULift.{u + 1} B V hV (Functor.whiskerRight k₀ uliftFunctor.{u + 1}) :=
    isProperULift_iff_of_arrowIso B V hV hP hQ
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B V hV P₀).mpr hP₀)
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B V hV Q₀).mpr hQ₀) _ _ eP.symm eQ.symm
      (by simp [hk₀])
  have h3 : Space.IsProperULift.{u + 1} B S hS (smallerBaseULiftMap B V S hV hS g k) ↔
      Space.IsProperULift.{u + 1} B S hS
        (Functor.whiskerRight (Ψ.functor.map k₀).left uliftFunctor.{u + 1}) := by
    refine isProperULift_iff_of_arrowIso B S hS
      ((isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g P).mpr hP)
      ((isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g Q).mpr hQ)
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr hΨP)
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr hΨQ) _ _
      ((Over.forget _).mapIso
          ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.mapIso eP.symm) ≪≫
        smallerBaseULiftWhiskerIso B V S hV hS g P₀)
      ((Over.forget _).mapIso
          ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.mapIso eQ.symm) ≪≫
        smallerBaseULiftWhiskerIso B V S hV hS g Q₀) ?_
    have key : smallerBaseULiftMap B V S hV hS g eP.inv ≫
        (smallerBaseULiftWhiskerIso B V S hV hS g P₀).hom ≫
          Functor.whiskerRight (Ψ.functor.map k₀).left uliftFunctor.{u + 1} =
        smallerBaseULiftMap B V S hV hS g k ≫ smallerBaseULiftMap B V S hV hS g eQ.inv ≫
          (smallerBaseULiftWhiskerIso B V S hV hS g Q₀).hom := by
      rw [← smallerBaseULiftWhiskerIso_hom_naturality, hk₀, smallerBaseULiftMap_comp_assoc,
        smallerBaseULiftMap_comp_assoc, Iso.inv_hom_id_assoc]
    change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    rw [Category.assoc]
    exact key
  rw [h3, h1, Space.isProperULift_whiskerRight_iff, Space.isProperULift_whiskerRight_iff,
    isProper_smallerBasePresheafEquivalence_map_iff B V S hV hS g k₀,
    Space.isProper_relocalize_iff B V hV S hS g hP₀ hQ₀]

/-- Properness of a morphism over `S` isomorphic to the change of base of a morphism of algebraic
spaces over `V` is properness of the latter. -/
private theorem isProperULift_iff_of_smallerBaseULiftMap_arrowIso
    {P Q : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Space.IsAlgebraicSpaceULift.{u + 1} B V hV P)
    (hQ : Space.IsAlgebraicSpaceULift.{u + 1} B V hV Q) (k : P ⟶ Q)
    {F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F')
    (hG' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G') (f' : F' ⟶ G')
    (e₁ : smallerBaseULift B V S hV hS g P ≅ F') (e₂ : smallerBaseULift B V S hV hS g Q ≅ G')
    (w : e₁.hom ≫ f' = smallerBaseULiftMap B V S hV hS g k ≫ e₂.hom) :
    Space.IsProperULift.{u + 1} B S hS f' ↔ Space.IsProperULift.{u + 1} B V hV k := by
  rw [← isProperULift_smallerBaseULiftMap_iff B V S hV hS g hP hQ k]
  exact (isProperULift_iff_of_arrowIso B S hS
    ((isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g P).mpr hP)
    ((isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g Q).mpr hQ) hF' hG' _ _ e₁ e₂ w).symm

/-- A morphism of presheaves on the big fppf site of `V` is representable by algebraic spaces and
proper when the induced morphism over `S` is. -/
theorem representableProper_of_smallerBaseULiftMap
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G')
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (smallerBaseULiftMap B V S hV hS g f))
    (he : Space.HasPropertyULift.{u + 1} B S hS (Space.properPropertyULift.{u + 1} B S hS)
      (smallerBaseULiftMap B V S hV hS g f) hf) :
    ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV f,
      Space.HasPropertyULift.{u + 1} B V hV (Space.properPropertyULift.{u + 1} B V hV) f hf := by
  have hf₀ :=
    (isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g f).mp hf
  refine ⟨hf₀, fun U₀ ξ₀ => ?_⟩
  have h1 : Space.IsProperULift.{u + 1} B S hS
      (pullback.fst (smallerBaseChart B V S hV hS g ξ₀) (smallerBaseULiftMap B V S hV hS g f)) :=
    he _ _
  change Space.IsProperULift.{u + 1} B V hV (pullback.fst ξ₀ f)
  have hsq := isPullback_smallerBaseChart_pullback B V S hV hS g f ξ₀
  refine (isProperULift_iff_of_smallerBaseULiftMap_arrowIso B V S hV hS g (hf₀ U₀ ξ₀)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B V hV U₀) _ (hf _ _)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS _) _ hsq.isoPullback
    (smallerBaseULiftYonedaIso B V S hV hS g U₀) ?_).mp h1
  exact hsq.isoPullback_hom_fst

/-- The morphism over `S` induced by a representable proper morphism of presheaves on the big fppf
site of `V` is representable by algebraic spaces and proper. -/
theorem representableProper_smallerBaseULiftMap
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G')
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV f)
    (he : Space.HasPropertyULift.{u + 1} B V hV (Space.properPropertyULift.{u + 1} B V hV) f hf) :
    ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (smallerBaseULiftMap B V S hV hS g f),
      Space.HasPropertyULift.{u + 1} B S hS (Space.properPropertyULift.{u + 1} B S hS)
        (smallerBaseULiftMap B V S hV hS g f) hf := by
  have hf' :=
    (isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g f).mpr hf
  refine ⟨hf', fun U ξ => ?_⟩
  obtain ⟨ψ, hψ, ξ₀, rfl⟩ := exists_smallerBaseChart B V S hV hS g U ξ
  have h1 : Space.IsProperULift.{u + 1} B V hV (pullback.fst ξ₀ f) := he _ _
  change Space.IsProperULift.{u + 1} B S hS (pullback.fst _ _)
  have hsq := isPullback_smallerBaseChart_pullback_relocalize B V S hV hS g f hψ ξ₀
  refine (isProperULift_iff_of_smallerBaseULiftMap_arrowIso B V S hV hS g (hf _ ξ₀)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B V hV _) _ (hf' _ _)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS _) _ hsq.isoPullback
    ((smallerBaseULiftYonedaIso B V S hV hS g _) ≪≫
      (uliftYoneda.{u + 1}.mapIso (asIso (relocalizeBaseHom B V S hV hS g hψ))).symm) ?_).mpr h1
  rw [hsq.isoPullback_hom_fst]
  simp

/-- **Representable proper morphisms do not see the change of base.** A morphism of presheaves
with values in `Type (u + 1)` on the big fppf site of `V` is representable by algebraic spaces
and proper exactly when the induced morphism of attached presheaves is. -/
theorem representableProper_smallerBaseULiftMap_iff
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G') :
    (∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (smallerBaseULiftMap B V S hV hS g f),
      Space.HasPropertyULift.{u + 1} B S hS (Space.properPropertyULift.{u + 1} B S hS)
        (smallerBaseULiftMap B V S hV hS g f) hf) ↔
      ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV f,
        Space.HasPropertyULift.{u + 1} B V hV (Space.properPropertyULift.{u + 1} B V hV) f hf :=
  ⟨fun ⟨hf, he⟩ => representableProper_of_smallerBaseULiftMap B V S hV hS g f hf he,
    fun ⟨hf, he⟩ => representableProper_smallerBaseULiftMap B V S hV hS g f hf he⟩

end AlgebraicGeometry.FormalSpace

end
