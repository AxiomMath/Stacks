module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# Products and fibre products in the category of algebraic spaces

The property of being an algebraic space over `S` is invariant under isomorphism of
presheaves and stable under fibre products, so the category
`AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S` is a full subcategory of
presheaves closed under fibre products. Consequently it has fibre products, its inclusion
into presheaves preserves and reflects them, and the slice over any algebraic space has
binary products.

The presheaf product of two algebraic spaces over `S` is likewise an algebraic space over
`S`, and with the two presheaf projections it is a product in the category of algebraic
spaces over `S`; that category therefore has binary products.

A monomorphism of algebraic spaces, in the sense of Tag 042L, is a categorical monomorphism
in that category; since the category is a full subcategory of presheaves, this is the same as
injectivity of all the components, which is the source's formulation.

## Main definitions

* `AlgebraicGeometry.Space.algebraicSpaceProperty` is the object property of presheaves on the
  big fppf site of `S` cut out by `AlgebraicGeometry.IsAlgebraicSpace`.
* `AlgebraicGeometry.AlgebraicSpaces.product` is the presheaf product of two algebraic spaces,
  equipped with its algebraic-space property.

## Main results

* `AlgebraicGeometry.Space.algebraicSpaceProperty_isClosedUnderIsomorphisms` and
  `AlgebraicGeometry.Space.algebraicSpaceProperty_isClosedUnderLimitsOfShape_walkingCospan`:
  invariance under isomorphism and stability under fibre products.
* `AlgebraicGeometry.Space.hasBinaryProducts_over_algebraicSpace`: products in the category of
  algebraic spaces over a fixed algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_prod`: the presheaf product of two algebraic spaces over
  `S` is an algebraic space over `S`.
* `AlgebraicGeometry.AlgebraicSpaces.isLimitBinaryFanProduct`: it is a product in the category
  of algebraic spaces over `S`, whence `AlgebraicGeometry.AlgebraicSpaces.hasBinaryProducts`.

## References

* [Stacks Project, Tag 02X0](https://stacks.math.columbia.edu/tag/02X0)
* [Stacks Project, Tag 042L](https://stacks.math.columbia.edu/tag/042L)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object property of presheaves on the big fppf site of `S` cut out by being an
algebraic space over `S`; its full subcategory is `AlgebraicGeometry.AlgebraicSpaces`. -/
abbrev algebraicSpaceProperty : ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun F ↦ IsAlgebraicSpace B S hS F

/-- Being an algebraic space over `S` is invariant under isomorphism of presheaves. -/
instance algebraicSpaceProperty_isClosedUnderIsomorphisms :
    (algebraicSpaceProperty B S hS).IsClosedUnderIsomorphisms := by
  refine ⟨?_⟩
  intro F G e hF
  have _ : HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mp hF.isSheaf, ?_, ?_⟩
  · have hnat : diag F ≫ prod.map e.hom e.hom = e.hom ≫ diag G := by
      apply prod.hom_ext <;> simp
    have hcomp : yoneda.relativelyRepresentable (e.hom ≫ diag G) :=
      hnat ▸ MorphismProperty.RespectsIso.postcomp yoneda.relativelyRepresentable
        (prod.map e.hom e.hom) (diag F) hF.diagonal_representable
    simpa using MorphismProperty.RespectsIso.precomp yoneda.relativelyRepresentable
      e.inv (e.hom ≫ diag G) hcomp
  · obtain ⟨U, q, hqSurj, hqEtale⟩ := hF.exists_atlas
    exact ⟨U, q ≫ e.hom,
      MorphismProperty.RespectsIso.postcomp _ e.hom q hqSurj,
      MorphismProperty.RespectsIso.postcomp _ e.hom q hqEtale⟩

/-- Being an algebraic space over `S` is stable under fibre products. -/
instance algebraicSpaceProperty_isClosedUnderLimitsOfShape_walkingCospan :
    (algebraicSpaceProperty B S hS).IsClosedUnderLimitsOfShape WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine (algebraicSpaceProperty B S hS).prop_of_iso
    (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm ?_
  simpa using isAlgebraicSpace_pullback B S hS
    (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)
    (hF WalkingCospan.left) (hF WalkingCospan.right) (hF WalkingCospan.one)

/-- The category of algebraic spaces over `S` equipped with a morphism to a fixed algebraic space
`Z` has binary products, namely the fibre products over `Z`. -/
@[stacks 043C "products over a base algebraic space"]
noncomputable instance hasBinaryProducts_over_algebraicSpace
    (Z : AlgebraicSpaces B S hS) : HasBinaryProducts (Over Z) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-! ### Products of algebraic spaces -/

/-- The presheaf product of two algebraic spaces over `S` is an algebraic space over `S`. -/
@[stacks 02X0 "the product is an algebraic space"]
theorem isAlgebraicSpace_prod (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) :
    IsAlgebraicSpace B S hS (F ⨯ G) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hbc (P : MorphismProperty Scheme.{u}) : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have _ := hbc (@Surjective.{u})
  have _ := hbc (@Etale.{u})
  obtain ⟨U, a, ha₁, ha₂⟩ := hF.exists_atlas
  obtain ⟨V, b, hb₁, hb₂⟩ := hG.exists_atlas
  refine ⟨?_, MorphismProperty.diag_mem_of_prod _ hF.diagonal_representable
    hG.diagonal_representable, U ⨯ V,
    (PreservesLimitPair.iso yoneda U V).hom ≫ prod.map a b, ?_, ?_⟩
  · exact ObjectProperty.prop_of_isLimit _ (c := BinaryFan.mk prod.fst prod.snd) (prodIsProd F G)
      (by rintro ⟨_ | _⟩; exacts [hF.isSheaf, hG.isSheaf])
  · exact MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.prod_map_mem _ ha₁ hb₁)
  · exact MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.prod_map_mem _ ha₂ hb₂)

namespace AlgebraicSpaces

/-- The product in the category of algebraic spaces over `S`: the presheaf product of the two
underlying presheaves. -/
noncomputable def product (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F G : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS :=
  ⟨F.obj ⨯ G.obj, isAlgebraicSpace_prod B S hS F.property G.property⟩

/-- The presheaf product of two algebraic spaces over `S`, with the two presheaf projections, is
a product in the category of algebraic spaces over `S`. -/
@[stacks 02X0 "the universal property"]
noncomputable def isLimitBinaryFanProduct (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F G : AlgebraicSpaces B S hS) :
    IsLimit (BinaryFan.mk
      (ObjectProperty.homMk (prod.fst : F.obj ⨯ G.obj ⟶ F.obj) : product B S hS F G ⟶ F)
      (ObjectProperty.homMk (prod.snd : F.obj ⨯ G.obj ⟶ G.obj) :
        product B S hS F G ⟶ G)) := by
  refine BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk (prod.lift s.fst.hom s.snd.hom))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · exact ObjectProperty.hom_ext _
      (show prod.lift s.fst.hom s.snd.hom ≫ prod.fst = s.fst.hom from prod.lift_fst _ _)
  · exact ObjectProperty.hom_ext _
      (show prod.lift s.fst.hom s.snd.hom ≫ prod.snd = s.snd.hom from prod.lift_snd _ _)
  · have hm₁ : m.hom ≫ prod.fst = s.fst.hom := congrArg (fun k : s.pt ⟶ F => k.hom) h₁
    have hm₂ : m.hom ≫ prod.snd = s.snd.hom := congrArg (fun k : s.pt ⟶ G => k.hom) h₂
    exact ObjectProperty.hom_ext _ (prod.hom_ext
      (hm₁.trans (show prod.lift s.fst.hom s.snd.hom ≫ prod.fst = s.fst.hom from
        prod.lift_fst _ _).symm)
      (hm₂.trans (show prod.lift s.fst.hom s.snd.hom ≫ prod.snd = s.snd.hom from
        prod.lift_snd _ _).symm))

/-- The category of algebraic spaces over `S` has binary products, namely the presheaf
products. -/
noncomputable instance hasBinaryProducts (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasBinaryProducts (AlgebraicSpaces B S hS) := by
  have _ : ∀ F G : AlgebraicSpaces B S hS, HasLimit (pair F G) := fun F G ↦
    HasLimit.mk ⟨_, isLimitBinaryFanProduct B S hS F G⟩
  exact hasBinaryProducts_of_hasLimit_pair _

end AlgebraicSpaces

end AlgebraicGeometry

end
