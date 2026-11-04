module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceGlue
public import StacksFrontier.AlgebraicGeometry.FormalScheme.SchemeToFormalScheme

/-!
# Pseudo-discretisation of a scheme commutes with restriction, and Zariski gluing of points

The functor `Schemes ⟶ Formal Schemes` of Stacks 0AI0 sends a scheme to its pseudo-discretisation
as a locally topologically ringed space. This file compares that construction with restriction to
an open subset, and uses the comparison together with
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover` to glue
morphisms from a scheme to a formal scheme along a Zariski open covering of the scheme.

The comparison is an *isomorphism*, not an equality, and it cannot be an equality by definitional
unfolding: `AlgebraicGeometry.pseudoDiscreteTopology` topologises the sections over an open `U` as
an infimum indexed by `AlgebraicGeometry.CompactOpenLE U`, the quasi-compact opens of the
*ambient* space contained in `U`. Restricting to an open subspace replaces the ambient space, and
so replaces the index type of the infimum; the two topologies agree, but only after reindexing
along the inclusion. The underlying spaces and the underlying rings of sections, by contrast, do
agree definitionally. The reindexing is `AlgebraicGeometry.pseudoDiscreteWhiskerIso`, whose
components are the identity on sections.

## Main definitions

* `AlgebraicGeometry.schemeToLTRSRestrictIso`: the comparison isomorphism
  `schemeToLTRSObj ↑V ≅ (schemeToLTRSObj T).restrict V` for an open subset `V` of a scheme `T`.

## Main results

* `AlgebraicGeometry.schemeToLTRSRestrictIso_hom_comp_ofRestrict` and
  `AlgebraicGeometry.schemeToLTRSRestrictIso_hom_comp_resLE`: the comparison isomorphism is
  compatible with the inclusion of an open subset and with the inclusion of one open subset into
  another, so it identifies the restriction diagram of a scheme with that of its
  pseudo-discretisation.
* `AlgebraicGeometry.existsUnique_hom_of_openCover_scheme`: morphisms from the members of a
  Zariski open covering of a scheme `T` to a formal scheme `𝔛`, agreeing on the pairwise
  overlaps, come from a unique morphism `T ⟶ 𝔛`.
* `AlgebraicGeometry.isSheafFor_opensCover_formalSchemePoints`: the sheaf condition of
  Stacks 0AI2 for a covering of a scheme by open subschemes, as the sheaf condition for the
  presieve that covering generates.

## Implementation notes

The compatibility with the inclusion `V.ι` holds definitionally, because both sides have the same
underlying map and both comparison maps on sections are a restriction map of `𝒪_T` composed with
the identity. The compatibility with `AlgebraicGeometry.Scheme.homOfLE` does not, because Mathlib
defines `Scheme.homOfLE` through `AlgebraicGeometry.IsOpenImmersion.lift`, hence through a
pullback, so its map on sections is not available by unfolding. It is instead obtained by
cancelling the monomorphism `AlgebraicGeometry.PresheafedSpace.ofRestrict`, using
`AlgebraicGeometry.Scheme.homOfLE_ι` on the scheme side and
`AlgebraicGeometry.PresheafedSpace.resLE_comp_ofRestrict` on the other.

## References

* [Stacks Project, Tag 0AI0](https://stacks.math.columbia.edu/tag/0AI0)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

namespace AlgebraicGeometry

variable (T : Scheme.{u}) (V W : T.Opens)

/-- Pseudo-discretisation commutes with restriction to an open subset, at the level of presheafed
spaces: the identity on the underlying space, and the identity on each ring of sections, the two
pseudo-discrete topologies agreeing by `AlgebraicGeometry.pseudoDiscreteWhiskerIso`. -/
noncomputable def schemeToLTRSRestrictPsIso :
    (schemeToLTRSObj V.toScheme).toPresheafedSpace
      ≅ ((schemeToLTRSObj T).restrict V).toPresheafedSpace :=
  PresheafedSpace.isoOfComponents (Iso.refl _)
    (pseudoDiscreteWhiskerIso V.inclusion' V.isOpenEmbedding' T.presheaf)

/-- The comparison isomorphism carries the inclusion of the open subspace of the
pseudo-discretisation to the pseudo-discretisation of the inclusion of the open subscheme. This
holds definitionally. -/
theorem schemeToLTRSRestrictPsIso_hom_comp_ofRestrict :
    (schemeToLTRSRestrictPsIso T V).hom
        ≫ (schemeToLTRSObj T).toPresheafedSpace.ofRestrict V.isOpenEmbedding
      = schemeToLTRSHom V.ι := rfl

/-- The comparison isomorphism is compatible with the inclusion of one open subset into
another. Both sides become the pseudo-discretisation of the inclusion `V.ι` after composing with
the monomorphism `ofRestrict`, which is where `Scheme.homOfLE_ι` enters. -/
theorem schemeToLTRSRestrictPsIso_hom_comp_resLE (h : V ≤ W) :
    (schemeToLTRSRestrictPsIso T V).hom ≫ (schemeToLTRSObj T).toPresheafedSpace.resLE h
      = schemeToLTRSHom (T.homOfLE h) ≫ (schemeToLTRSRestrictPsIso T W).hom := by
  have hmono : Mono ((schemeToLTRSObj T).toPresheafedSpace.ofRestrict W.isOpenEmbedding) :=
    PresheafedSpace.ofRestrict_mono (schemeToLTRSObj T).toPresheafedSpace W.inclusion'
      W.isOpenEmbedding
  have e₁ : ((schemeToLTRSRestrictPsIso T V).hom
        ≫ (schemeToLTRSObj T).toPresheafedSpace.resLE h)
          ≫ (schemeToLTRSObj T).toPresheafedSpace.ofRestrict W.isOpenEmbedding
      = schemeToLTRSHom V.ι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => (schemeToLTRSRestrictPsIso T V).hom ≫ m)
          (PresheafedSpace.resLE_comp_ofRestrict
            (schemeToLTRSObj T).toPresheafedSpace h)).trans
        (schemeToLTRSRestrictPsIso_hom_comp_ofRestrict T V))
  have e₂ : (schemeToLTRSHom (T.homOfLE h) ≫ (schemeToLTRSRestrictPsIso T W).hom)
          ≫ (schemeToLTRSObj T).toPresheafedSpace.ofRestrict W.isOpenEmbedding
      = schemeToLTRSHom V.ι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => schemeToLTRSHom (T.homOfLE h) ≫ m)
          (schemeToLTRSRestrictPsIso_hom_comp_ofRestrict T W)).trans
        ((schemeToLTRSHom_comp (T.homOfLE h) W.ι).symm.trans
          (congrArg schemeToLTRSHom (Scheme.homOfLE_ι T h))))
  exact hmono.right_cancellation _ _ (e₁.trans e₂.symm)

/-- Pseudo-discretisation commutes with restriction to an open subset, as an isomorphism of
locally topologically ringed spaces. -/
noncomputable def schemeToLTRSRestrictIso :
    schemeToLTRSObj V.toScheme ≅ (schemeToLTRSObj T).restrict V where
  hom :=
    { toHom := (schemeToLTRSRestrictPsIso T V).hom
      isLocalHom x :=
        @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
          (PresheafedSpace.IsOpenImmersion.stalk_iso (schemeToLTRSRestrictPsIso T V).hom x) }
  inv :=
    { toHom := (schemeToLTRSRestrictPsIso T V).inv
      isLocalHom x :=
        @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
          (PresheafedSpace.IsOpenImmersion.stalk_iso (schemeToLTRSRestrictPsIso T V).inv x) }
  hom_inv_id := Hom.ext' (schemeToLTRSRestrictPsIso T V).hom_inv_id
  inv_hom_id := Hom.ext' (schemeToLTRSRestrictPsIso T V).inv_hom_id

/-- The underlying morphism of presheafed spaces of `(schemeToLTRSRestrictIso T V).hom` is
`(schemeToLTRSRestrictPsIso T V).hom`. -/
@[simp]
theorem schemeToLTRSRestrictIso_hom_toHom :
    (schemeToLTRSRestrictIso T V).hom.toHom = (schemeToLTRSRestrictPsIso T V).hom := rfl

/-- The underlying morphism of presheafed spaces of `(schemeToLTRSRestrictIso T V).inv` is
`(schemeToLTRSRestrictPsIso T V).inv`. -/
@[simp]
theorem schemeToLTRSRestrictIso_inv_toHom :
    (schemeToLTRSRestrictIso T V).inv.toHom = (schemeToLTRSRestrictPsIso T V).inv := rfl

/-- The comparison isomorphism carries the inclusion of the open subspace to the image of the
inclusion of the open subscheme, as morphisms of locally topologically ringed spaces, the latter
read through `AlgebraicGeometry.schemeToLTRS`. -/
theorem schemeToLTRSRestrictIso_hom_comp_ofRestrict_ltrs :
    (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).ofRestrict V
      = schemeToLTRS.map V.ι :=
  Hom.ext' (schemeToLTRSRestrictPsIso_hom_comp_ofRestrict T V)

/-- The pseudo-discretisation of the inclusion of an open subscheme, factored through the
comparison isomorphism. -/
theorem schemeToLTRS_map_ι_eq :
    schemeToLTRS.map V.ι
      = (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).ofRestrict V :=
  (schemeToLTRSRestrictIso_hom_comp_ofRestrict_ltrs T V).symm

/-- The comparison isomorphism is compatible with the inclusion of one open subset into another,
as morphisms of locally topologically ringed spaces. -/
theorem schemeToLTRSRestrictIso_hom_comp_resLE_ltrs (h : V ≤ W) :
    (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).resLE h
      = schemeToLTRS.map (T.homOfLE h) ≫ (schemeToLTRSRestrictIso T W).hom :=
  Hom.ext' (schemeToLTRSRestrictPsIso_hom_comp_resLE T V W h)

/-- The comparison isomorphism carries the inclusion of the open subspace to the image of the
inclusion of the open subscheme, as morphisms of locally topologically ringed spaces. -/
theorem schemeToLTRSRestrictIso_hom_comp_ofRestrict :
    (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).ofRestrict V
      = (schemeToFormalScheme.map V.ι).hom :=
  schemeToLTRSRestrictIso_hom_comp_ofRestrict_ltrs T V

/-- The pseudo-discretisation of the inclusion of an open subscheme, factored through the
comparison isomorphism. -/
theorem map_ι_hom_eq :
    (schemeToFormalScheme.map V.ι).hom
      = (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).ofRestrict V :=
  schemeToLTRS_map_ι_eq T V

/-- The comparison isomorphism is compatible with the inclusion of one open subset into another,
as morphisms of locally topologically ringed spaces. -/
theorem schemeToLTRSRestrictIso_hom_comp_resLE (h : V ≤ W) :
    (schemeToLTRSRestrictIso T V).hom ≫ (schemeToLTRSObj T).resLE h
      = (schemeToFormalScheme.map (T.homOfLE h)).hom ≫ (schemeToLTRSRestrictIso T W).hom :=
  schemeToLTRSRestrictIso_hom_comp_resLE_ltrs T V W h

/-- **The gluing clause for a Zariski open covering.** Let `T` be a scheme covered by open
subsets `V i`, let `Y` be a locally topologically ringed space, and let `g i : V i ⟶ Y` be
morphisms agreeing on the pairwise overlaps `V i ⊓ V j`. Then there is a unique morphism
`T ⟶ Y` restricting to `g i` on each `V i`.

This is the Zariski case of the gluing half of the sheaf condition on the functor of points.
Nothing is asked of `Y` beyond being an object of `LTRS`, so it applies to a formal scheme à la
EGA and to one in the sense of McQuillan alike. The agreement hypothesis is stated on the
overlaps `V i ⊓ V j`, which is the fibre product `V i ×_T V j` by
`AlgebraicGeometry.isPullback_opens_inf`. -/
theorem existsUnique_ltrsHom_of_openCover_scheme {T : Scheme.{u}} {Y : LTRS.{u}} {ι : Type*}
    (V : ι → T.Opens) (hV : iSup V = ⊤)
    (g : ∀ i, schemeToLTRS.obj (V i).toScheme ⟶ Y)
    (hg : ∀ i j, schemeToLTRS.map (T.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) ≫ g i
              = schemeToLTRS.map (T.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) ≫ g j) :
    ∃! f : schemeToLTRS.obj T ⟶ Y, ∀ i, schemeToLTRS.map (V i).ι ≫ f = g i := by
  -- Transport the local morphisms across the comparison isomorphism.
  have step : ∀ (i j k : ι) (hk : V i ⊓ V j ≤ V k),
      (schemeToLTRSRestrictIso T (V i ⊓ V j)).hom
          ≫ ((schemeToLTRSObj T).resLE hk
            ≫ ((schemeToLTRSRestrictIso T (V k)).inv ≫ g k))
        = schemeToLTRS.map (T.homOfLE hk) ≫ g k := fun i j k hk => by
    rw [← Category.assoc, schemeToLTRSRestrictIso_hom_comp_resLE_ltrs]
    erw [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have compat : ∀ i j, (schemeToLTRSObj T).resLE (inf_le_left : V i ⊓ V j ≤ V i)
          ≫ ((schemeToLTRSRestrictIso T (V i)).inv ≫ g i)
        = (schemeToLTRSObj T).resLE (inf_le_right : V i ⊓ V j ≤ V j)
          ≫ ((schemeToLTRSRestrictIso T (V j)).inv ≫ g j) := fun i j =>
    (Iso.cancel_iso_hom_left (schemeToLTRSRestrictIso T (V i ⊓ V j)) _ _).mp
      ((step i j i inf_le_left).trans ((hg i j).trans (step i j j inf_le_right).symm))
  obtain ⟨f₀, hf₀, huniq⟩ := LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover
    (X := schemeToLTRSObj T) (Y := Y) V hV
    (fun i => (schemeToLTRSRestrictIso T (V i)).inv ≫ g i) compat
  refine ⟨f₀, fun i => ?_, fun f' hf' => huniq f' fun i => ?_⟩
  · rw [schemeToLTRS_map_ι_eq]
    erw [Category.assoc, hf₀, Iso.hom_inv_id_assoc]
  · refine (Iso.eq_inv_comp (schemeToLTRSRestrictIso T (V i))).mpr ?_
    erw [← Category.assoc, ← schemeToLTRS_map_ι_eq]
    exact hf' i

/-- **The gluing clause for a Zariski open covering**, for a formal scheme: the morphisms of
formal schemes out of a scheme are the morphisms of `LTRS` out of its pseudo-discretisation. -/
theorem existsUnique_hom_of_openCover_scheme {T : Scheme.{u}} {𝔛 : FormalScheme.{u}} {ι : Type*}
    (V : ι → T.Opens) (hV : iSup V = ⊤)
    (g : ∀ i, schemeToFormalScheme.obj (V i).toScheme ⟶ 𝔛)
    (hg : ∀ i j, schemeToFormalScheme.map (T.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) ≫ g i
              = schemeToFormalScheme.map (T.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) ≫ g j) :
    ∃! f : schemeToFormalScheme.obj T ⟶ 𝔛, ∀ i, schemeToFormalScheme.map (V i).ι ≫ f = g i := by
  obtain ⟨f₀, hf₀, huniq⟩ := existsUnique_ltrsHom_of_openCover_scheme V hV
    (fun i => (g i).hom)
    fun i j => congrArg (fun m : schemeToFormalScheme.obj (V i ⊓ V j).toScheme ⟶ 𝔛 => m.hom)
      (hg i j)
  refine ⟨ObjectProperty.homMk f₀, fun i => InducedCategory.hom_ext (hf₀ i),
    fun f' hf' => InducedCategory.hom_ext (huniq f'.hom fun i =>
      congrArg (fun m : schemeToFormalScheme.obj (V i).toScheme ⟶ 𝔛 => m.hom) (hf' i))⟩

/-- The sheaf condition of Stacks 0AI2 for a covering by open subschemes. The functor of points
of a formal scheme satisfies the sheaf condition for the presieve generated by a covering of a
scheme by open subschemes: a matching family of points on the members of the covering has a unique
amalgamation.

Matching for this presieve is compatibility on every common refinement, and the pairwise overlap
`V i ⊓ V j` is the fibre product `V i ×_T V j` by `AlgebraicGeometry.isPullback_opens_inf`, so the
hypothesis of `AlgebraicGeometry.existsUnique_hom_of_openCover_scheme` is an instance of it. -/
theorem isSheafFor_opensCover_formalSchemePoints {T : Scheme.{u}} (X : FormalScheme.{u})
    {ι : Type*} (V : ι → T.Opens) (hV : iSup V = ⊤) :
    Presieve.IsSheafFor (formalSchemePoints X)
      (Presieve.ofArrows (fun i => (V i).toScheme) (fun i => (V i).ι)) :=
  (Presieve.isSheafFor_arrows_iff _ _).mpr fun x hx =>
    existsUnique_hom_of_openCover_scheme V hV x fun i j =>
      hx i j (V i ⊓ V j).toScheme (T.homOfLE inf_le_left) (T.homOfLE inf_le_right)
        (isPullback_opens_inf (V i) (V j)).w

end AlgebraicGeometry

end
