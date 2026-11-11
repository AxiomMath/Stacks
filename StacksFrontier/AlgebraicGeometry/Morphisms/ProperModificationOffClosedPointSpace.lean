module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperModificationOffClosedPoint

/-!
# Isomorphisms over an open, from schemes to the represented sheaves

Let `g : W ⟶ V` be a morphism of the big fppf site of `S` and `Z` a set of points of the
represented sheaf `h_V`. If the underlying morphism of schemes is an isomorphism over an open
`U ⊆ V` containing every point outside `Z`, then the base change of `h_g : h_W ⟶ h_V` to the open
subspace of `h_V` cut out by the complement of `Z` is an isomorphism. This is the form of the
hypothesis "`U' → U` is an isomorphism" of Stacks 0GDM
(`AlgebraicGeometry.FormalSpace.isFormalModification_completionSheafMap`).

## Main results

* `AlgebraicGeometry.Space.isClosed_preimage_pointsToScheme`: the points of `h_V` over a closed
  subset of `V` form a closed set, as Stacks 0GDM requires of `T`.
* `AlgebraicGeometry.Space.isIso_pullback_snd_yoneda_map_openSubspaceOfPoints`: the translation.
* `AlgebraicGeometry.Space.isIso_pullback_snd_yoneda_map_openSubspaceOfPoints_compl_closedPoint`:
  combined with `AlgebraicGeometry.isIso_morphismRestrict_puncturedSpectrum`, for a proper
  morphism of the site to `Spec A` of a local ring of dimension at least two from an irreducible
  scheme of dimension at most two inducing `A ≅ Γ(W, 𝒪_W)`, with `Z` the closed point.

## Implementation notes

The base change of `h_g` to a subfunctor of `h_V` is an isomorphism exactly when maps from
representables into the subfunctor lift uniquely through `h_g`
(`AlgebraicGeometry.Space.isIso_pullback_snd_ι_iff_existsUnique`). A map from `h_T` into the
open subspace is a morphism `a : T ⟶ V` whose scheme points avoid `Z`, hence lie in `U`; over `U`
the morphism of schemes is an isomorphism, so the morphism of schemes underlying `a` lifts
uniquely, and the lift is automatically a morphism over `S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

attribute [local instance] Space.pointTopology

/-- The set of points of a represented sheaf `h_V` lying over a closed subset of the scheme `V`
is closed in the point topology. -/
theorem isClosed_preimage_pointsToScheme {V : BigFppfOver B S hS} {C : Set ((𝒯).obj V)}
    (hC : IsClosed C) : IsClosed (pointsToScheme B S hS V ⁻¹' C) := by
  rw [isClosed_pointTopology_yoneda_iff_isClosed_image,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS V)]
  exact hC

/-- **An isomorphism over an open of a scheme of the site is an isomorphism of the represented
sheaves over the corresponding open subspace.** Let `g : W ⟶ V` be a morphism of the big fppf
site, `Z` a set of points of `h_V`, and `U` an open of the scheme `V` containing every point
outside `Z`. If the underlying morphism of schemes is an isomorphism over `U`, then the base
change of `h_g` to the open subspace of `h_V` cut out by the complement of `Z` is an
isomorphism. -/
theorem isIso_pullback_snd_yoneda_map_openSubspaceOfPoints {V W : BigFppfOver B S hS}
    (g : W ⟶ V) (Z : Set (points B S hS (yoneda.obj V)))
    (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hZU : ∀ p, p ∉ Z → pointsToScheme B S hS V p ∈ U)
    (hg : IsIso ((BigFppfOver.toScheme B S hS).map g ∣_ U)) :
    IsIso (pullback.snd (yoneda.map g) (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
  have hsnd : IsIso (pullback.snd ((𝒯).map g) U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  -- unique lifting of morphisms of schemes landing in `U`
  have hlift : ∀ {X : Scheme.{u}} (a : X ⟶ (𝒯).obj V), Set.range a ⊆ U →
      ∃! b : X ⟶ (𝒯).obj W, b ≫ (𝒯).map g = a := by
    intro X a ha
    let a' : X ⟶ U.toScheme := IsOpenImmersion.lift U.ι a (by simpa using ha)
    have ha' : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
    refine ⟨a' ≫ inv (pullback.snd ((𝒯).map g) U.ι) ≫ pullback.fst ((𝒯).map g) U.ι, ?_,
      fun b hb ↦ ?_⟩
    · simp only [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, ha']
    · have e : pullback.lift b a' (by rw [hb, ha']) =
          a' ≫ inv (pullback.snd ((𝒯).map g) U.ι) := by
        rw [IsIso.eq_comp_inv, pullback.lift_snd]
      have := congrArg (· ≫ pullback.fst ((𝒯).map g) U.ι) e
      simpa only [pullback.lift_fst, Category.assoc] using this
  rw [isIso_pullback_snd_ι_iff_existsUnique]
  intro W' w
  set x := yonedaEquiv w
  set a : W' ⟶ V := x.1
  have hwa : w ≫ (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι = yoneda.map a := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rfl
  have hpts : Set.range (pointsMap B S hS _ (yoneda.map a)) ⊆ Zᶜ := x.2
  have hrange : Set.range ((𝒯).map a) ⊆ U := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS W' z
    rw [← pointsToScheme_pointsMap_yoneda]
    exact hZU _ (hpts ⟨p, rfl⟩)
  obtain ⟨b', hb', hb'u⟩ := hlift ((𝒯).map a) hrange
  let b : W' ⟶ W := Over.homMk (ObjectProperty.homMk b') (by
    apply B.inclusion.map_injective
    have hgw := Over.w g
    have haw := Over.w a
    change b' ≫ B.inclusion.map W.hom = B.inclusion.map W'.hom
    rw [← hgw, ← haw, Functor.map_comp, Functor.map_comp, ← Category.assoc]
    exact congrArg (· ≫ B.inclusion.map V.hom) hb')
  have hTb : (𝒯).map b = b' := rfl
  have hbg : b ≫ g = a := by
    apply (𝒯).map_injective
    rw [Functor.map_comp, hTb]
    exact hb'
  refine ⟨yoneda.map b, ?_, fun y hy ↦ ?_⟩
  · change yoneda.map b ≫ yoneda.map g = _
    rw [← Functor.map_comp, hbg, hwa]
  · obtain ⟨c, rfl⟩ : ∃ c, yoneda.map c = y := ⟨yoneda.preimage y, yoneda.map_preimage y⟩
    have hcg : c ≫ g = a := yoneda.map_injective (by rw [Functor.map_comp, hy, hwa])
    have hTc : (𝒯).map c = b' := hb'u _ (by
      show (𝒯).map c ≫ (𝒯).map g = (𝒯).map a
      rw [← Functor.map_comp, hcg])
    exact congrArg yoneda.map ((𝒯).map_injective (hTc.trans hTb.symm))

/-- **The hypothesis of Stacks 0GDM for a surface over a two-dimensional local base.** Let `A`
be a local ring of Krull dimension at least two with `Spec A` in the site over `S`, and let
`g : W ⟶ Spec A` be a morphism of the site whose underlying morphism of schemes is proper, from
an irreducible scheme of dimension at most two, and induces `A ≅ Γ(W, 𝒪_W)`. Then the base change
of `h_g` to the open subspace of `h_{Spec A}` complementary to the closed point is an
isomorphism. -/
theorem isIso_pullback_snd_yoneda_map_openSubspaceOfPoints_compl_closedPoint {A : Type u}
    [CommRing A] [IsLocalRing A] (hA : 2 ≤ ringKrullDim A) (hSpec : B.Contains (Spec (.of A)))
    (σ : Spec (.of A) ⟶ S) {W : BigFppfOver B S hS} (g : W ⟶ siteObject B S hS hSpec σ)
    [IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj W)]
    [AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g)]
    [IsIso ((BigFppfOver.toScheme B S hS).map g).appTop]
    (hW : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ≤ 2) :
    IsIso (pullback.snd (yoneda.map g) (openSubspaceOfPoints B S hS
      (yoneda.obj (siteObject B S hS hSpec σ))
      (pointsToScheme B S hS _ ⁻¹' {(closedPoint A : PrimeSpectrum A)})ᶜ).ι) := by
  refine isIso_pullback_snd_yoneda_map_openSubspaceOfPoints g _ (puncturedSpectrum A)
    (fun p hp ↦ hp) ?_
  exact isIso_morphismRestrict_puncturedSpectrum
    ((BigFppfOver.toScheme B S hS).map g : _ ⟶ Spec (.of A)) hA hW

end AlgebraicGeometry.Space

end
