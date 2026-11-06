module

public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityAscentSpecStalk

/-!
# `Spec 𝒪_{V, v}` as a limit of affine open neighbourhoods inside the site

`AlgebraicGeometry.Space.SpecStalkAffineLimitPresentation` is the input carried by the ascent of
purity of
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityAscentSpecStalk.lean`: every impurity diagram
whose test scheme is `Spec 𝒪_{V, v}` admits a presentation of that test scheme as a cofiltered
limit of affine schemes over `Y`, quasi-finite at the points below the closed point. This file
builds that presentation out of the source's own system — the affine open neighbourhoods of `v`
in `V` — and isolates exactly what is left over.

## The system

For a scheme `V` of the site and a point `v` of it, the affine open neighbourhoods of `v` form a
cofiltered category and `Spec 𝒪_{V, v}` is their inverse limit in schemes; that is
`AlgebraicGeometry.isLimitSpecStalkCone`, proved from `𝒪_{V, v} = colim_U 𝒪(U)` and the fact
that `Spec`, being right adjoint to global sections, turns that colimit of rings into a limit of
spectra. Each such `U` is an open subscheme of `V`, hence small enough to be an object of the
site (`AlgebraicGeometry.Space.contains_coe_opens`), affine, and étale over `Y` as soon as
`V ⟶ Y` is, being an open immersion followed by `V ⟶ Y`.

What this file adds to the scheme-level limit is that the same cone is a limit *in the site*, in
the presheaf-level form the limit descent of impurities consumes:

* `AlgebraicGeometry.Space.affineNhdsStageFunctor` is the system, read in the big fppf category
  over `S`;
* `AlgebraicGeometry.Space.exists_unique_hom_specStalk` identifies the morphisms of the site into
  `Spec 𝒪_{V, v}` with the compatible families of morphisms into the stages, and
  `AlgebraicGeometry.Space.exists_unique_presheafHom_specStalk` promotes that to the universal
  property against an arbitrary presheaf, which is the `isLimit` field of
  `AlgebraicGeometry.Space.AffineLimitPresentation`.

## The cardinality clause, and how it is discharged

`AlgebraicGeometry.Space.AffineLimitPresentation` asks of its index category not only that it be
cofiltered but that it satisfy `AlgebraicGeometry.Space.SiteLimitBound`, which keeps the limits
the descent argument forms inside the size-bounded site. That clause offers two incomparable
packages, and the system of affine open neighbourhoods satisfies the second one.

It does *not* satisfy the first, the source's own bookkeeping `#J < B.cutoff.ord.cof` and
`∀ i j, #(i ⟶ j) < B.cutoff.ord.cof`. The second half is a formality for a thin index category;
the first half is not. The affine open neighbourhoods of a point of a scheme of the site are
bounded by `V.size` and so by `B.cutoff` — but *not* by its cofinality, and on the cutoff that
`AlgebraicGeometry.exists_size_cutoff` produces the cofinality is `ℵ₁`, so that half asks for a
countable system. Nor would restricting to a subsystem help: `Spec 𝒪_{V, v}` is the spectrum of a
local ring and so has no open neighbourhood of its closed point but itself, so any
`AffineLimitPresentation` of the diagram with that test scheme and stages quasi-finite over `Y`
yields a family of `#J`-many affine opens of `V` which is a neighbourhood basis at `v`, and for
`V` the affine plane over an uncountable field and `v` its generic point no countable such family
exists. `AlgebraicGeometry.Space.HasSmallAffineNhdsBasis` names that half of the clause for `v`,
and the forms below carrying it are kept for a caller who has it from elsewhere — a point with a
finite neighbourhood basis, say.

What the system of affine open neighbourhoods does satisfy is the cofinality-free package, on all
three counts and for reasons that have nothing to do with purity or with the module:

* the affine open neighbourhoods of `v` inject into the affine opens of `V`, which
  `AlgebraicGeometry.Scheme.size` bounds, so there are fewer of them than the cutoff
  (`AlgebraicGeometry.Space.mk_affineOpenNhds_lt_cutoff`);
* the system is a partial order, so the single cardinal `ℵ₀` bounds all its Hom-sets
  (`AlgebraicGeometry.Space.mk_hom_fullSubcategory_affineOpenNhds_le_aleph0`);
* its transition morphisms are inclusions of open subschemes of `V`, hence monomorphisms
  (`AlgebraicGeometry.Space.mono_yoneda_map_affineNhdsStageFunctor_map`).

So `AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale` discharges the carried
input of the ascent for an étale chart with nothing else granted. The same gap in the *source's*
bookkeeping is recorded, for the index sets of Stacks 07SF, in the notes of
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianApproximationFromPresentation.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/SiteGluing.lean`; the trade made here is the same one
`AlgebraicGeometry.BigFppfSite.contains_glueData_glued_of_le_power` makes there.

## Main definitions

* `AlgebraicGeometry.Space.openStage`: an open subscheme of `V`, as an object of the big fppf
  category over `S`, with `AlgebraicGeometry.Space.openStageHom` its inclusion into `V`,
  `AlgebraicGeometry.Space.openStageLE` the inclusions between two of them, and
  `AlgebraicGeometry.Space.openStageProj` the canonical morphism from `Spec 𝒪_{V, v}` into one
  containing `v`.
* `AlgebraicGeometry.Space.affineNhdsStageFunctor`: the system of affine open neighbourhoods of
  `v`, read in the site.
* `AlgebraicGeometry.Space.HasSmallAffineNhdsBasis`: the cardinality clause above.

## Main results

* `AlgebraicGeometry.Space.exists_unique_presheafHom_specStalk`: **`Spec 𝒪_{V, v}` is the limit of
  its affine open neighbourhoods in the site**, in the presheaf-level form.
* `AlgebraicGeometry.Space.specStalkAffineLimitPresentation`: the presentation asked for by
  `AlgebraicGeometry.Space.SpecStalkAffineLimitPresentation`, for an étale chart `a : V ⟶ Y` and
  a small affine neighbourhood basis at `v`.
* `AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale`: **the same presentation
  for an étale chart with nothing else granted**, over the system of *all* affine open
  neighbourhoods of `v`; and
  `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove_of_isEtale'` together with
  `Space.relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale'`, the ascent
  and the assassin containment with the smallness hypothesis shed.
* the ascent and the assassin containment of
  `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityAscentSpecStalk.lean`, with the limit
  presentation replaced by those two hypotheses, as
  `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove_of_isEtale` and
  `Space.relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale`

## Implementation notes

Two transparency problems shape the proofs below, and both are worth naming because the
obvious phrasings fail on them silently.

First, as in `StacksFrontier/AlgebraicGeometry/StalkAffineNhdsLimit/Basic.lean`, the coercion out of
`TopologicalSpace.OpenNhds` is not type-correct at the transparency `rw` matches at. Every
step that rewrites is therefore stated over an explicit `U : V.Opens`, and the statements over
`AlgebraicGeometry.AffineOpenNhds` are obtained from those by application only.

Second, the stages are built with `AlgebraicGeometry.BigFppfOver.mk` rather than with
`AlgebraicGeometry.Space.openSubobject`, so that both the underlying scheme of a stage and its
structure morphism to `S` hold by `rfl`; and their morphisms are built with
`AlgebraicGeometry.Space.siteHomMk` rather than with a `Full` functor's `preimage`, whose
`map_preimage` is not `rfl`. That is what lets the scheme-level identities be transported by
`AlgebraicGeometry.Space.hom_ext_toScheme` applied to a bare term.

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CV9](https://stacks.math.columbia.edu/tag/0CV9)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the site from morphisms of schemes over `S` -/

/-- A morphism of schemes over `S` between the schemes underlying two objects of the big fppf
category over `S`, read as a morphism of that category. This is
`AlgebraicGeometry.BigFppfOver.homMk` with the target an arbitrary object rather than one
presented as `AlgebraicGeometry.BigFppfOver.mk`. -/
def siteHomMk {T₁ T₂ : BigFppfOver B S hS}
    (h : (BigFppfOver.toScheme B S hS).obj T₁ ⟶ (BigFppfOver.toScheme B S hS).obj T₂)
    (w : h ≫ B.inclusion.map T₂.hom = B.inclusion.map T₁.hom) : T₁ ⟶ T₂ :=
  Over.homMk (ObjectProperty.homMk h) (by apply ObjectProperty.hom_ext; exact w)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteHomMk` is the given one. -/
theorem toScheme_map_siteHomMk {T₁ T₂ : BigFppfOver B S hS}
    (h : (BigFppfOver.toScheme B S hS).obj T₁ ⟶ (BigFppfOver.toScheme B S hS).obj T₂)
    (w : h ≫ B.inclusion.map T₂.hom = B.inclusion.map T₁.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHomMk B S hS h w) = h := rfl

/-- Two morphisms of the big fppf category over `S` with the same underlying morphism of schemes
are equal; this is `AlgebraicGeometry.BigFppfOver.map_toScheme_injective` in the shape a proof
obligation takes. -/
theorem hom_ext_toScheme {T T' : BigFppfOver B S hS} {f g : T ⟶ T'}
    (h : (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g) : f = g :=
  BigFppfOver.map_toScheme_injective B S hS h

end Space

/-! ### Open subschemes of `V` as stages over `S` -/

/-- The canonical morphism `Spec 𝒪_{X, x} ⟶ U` is compatible with the inclusions between open
neighbourhoods of `x`. -/
theorem Scheme.Opens.fromSpecStalkOfMem_homOfLE {X : Scheme.{u}} {U U' : X.Opens} (x : X)
    (hxU : x ∈ U) (hxU' : x ∈ U') (h : U ≤ U') :
    U.fromSpecStalkOfMem x hxU ≫ X.homOfLE h = U'.fromSpecStalkOfMem x hxU' := by
  rw [← cancel_mono (Scheme.Opens.ι (X := X) U'), Category.assoc, Scheme.homOfLE_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section OpenStages

variable (V : BigFppfOver B S hS)

/-- **An open subscheme of `V`, as an object of the big fppf category over `S`.** It is presented
through `AlgebraicGeometry.BigFppfOver.mk`, so that both its underlying scheme and its structure
morphism to `S` are transparent. -/
noncomputable def openStage (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_coe_opens B S hS V U)
    (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj V) U ≫ B.inclusion.map V.hom)

/-- The scheme underlying a stage is the open subscheme itself. -/
theorem toScheme_obj_openStage (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).obj (openStage B S hS V U) =
      Scheme.Opens.toScheme (X := (BigFppfOver.toScheme B S hS).obj V) U := rfl

/-- The structure morphism of a stage to `S` is the open inclusion followed by that of `V`. -/
theorem inclusion_map_hom_openStage (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    B.inclusion.map (openStage B S hS V U).hom =
      Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj V) U ≫ B.inclusion.map V.hom :=
  rfl

/-- The inclusion of an open subscheme of `V` into `V`, as a morphism of the big fppf category
over `S`. -/
noncomputable def openStageHom (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    openStage B S hS V U ⟶ V :=
  siteHomMk B S hS (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj V) U) rfl

/-- The morphism of schemes underlying the inclusion of a stage into `V` is the open
inclusion. -/
theorem toScheme_map_openStageHom (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).map (openStageHom B S hS V U) =
      Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj V) U := rfl

/-- The inclusion of a stage into `V` is an open immersion of algebraic spaces. -/
theorem isOpenImmersion_yoneda_map_openStageHom
    (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsOpenImmersion B S hS (yoneda.map (openStageHom B S hS V U)) :=
  isOpenImmersion_yoneda_map B S hS (openStageHom B S hS V U)
    (inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
      (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj V) U)))

/-- The inclusion of one open subscheme of `V` into a larger one, as a morphism of the site. -/
noncomputable def openStageLE {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (h : U ≤ U') : openStage B S hS V U ⟶ openStage B S hS V U' :=
  siteHomMk B S hS (((BigFppfOver.toScheme B S hS).obj V).homOfLE h)
    (Scheme.homOfLE_ι_assoc _ _ _)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openStageLE` is
`AlgebraicGeometry.Scheme.homOfLE`. -/
theorem toScheme_map_openStageLE {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (h : U ≤ U') :
    (BigFppfOver.toScheme B S hS).map (openStageLE B S hS V h) =
      ((BigFppfOver.toScheme B S hS).obj V).homOfLE h := rfl

/-- The inclusion of a stage into itself is the identity. -/
theorem openStageLE_refl {U : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U ≤ U) :
    openStageLE B S hS V h = 𝟙 (openStage B S hS V U) :=
  hom_ext_toScheme B S hS (Scheme.homOfLE_rfl ((BigFppfOver.toScheme B S hS).obj V) U)

/-- The inclusions between stages compose. -/
theorem openStageLE_trans {U U' U'' : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (h₁ : U ≤ U') (h₂ : U' ≤ U'') (h₃ : U ≤ U'') :
    openStageLE B S hS V h₁ ≫ openStageLE B S hS V h₂ = openStageLE B S hS V h₃ :=
  hom_ext_toScheme B S hS
    (Scheme.homOfLE_homOfLE ((BigFppfOver.toScheme B S hS).obj V) h₁ h₂)

/-- An inclusion between stages, followed by the inclusion of the larger one into `V`, is the
inclusion of the smaller one. -/
theorem openStageLE_comp_openStageHom {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (h : U ≤ U') :
    openStageLE B S hS V h ≫ openStageHom B S hS V U' = openStageHom B S hS V U :=
  hom_ext_toScheme B S hS (Scheme.homOfLE_ι ((BigFppfOver.toScheme B S hS).obj V) h)

variable (v₀ : (BigFppfOver.toScheme B S hS).obj V)

/-- The structure morphism of `Spec 𝒪_{V, v}` to `S` is the canonical morphism to `V` followed by
that of `V`. -/
theorem inclusion_map_hom_specStalk :
    B.inclusion.map (BigFppfOver.specStalk B S hS V v₀).hom =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v₀ ≫ B.inclusion.map V.hom := by
  rw [← Over.w (BigFppfOver.specStalkTo B S hS V v₀), Functor.map_comp]
  congr 1
  exact BigFppfOver.toScheme_map_specStalkTo B S hS V v₀

/-- **The canonical morphism `Spec 𝒪_{V, v} ⟶ U` of the site**, for `U` an open subscheme of `V`
containing `v`; underlying it is
`AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem`. -/
noncomputable def openStageProj (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hxU : v₀ ∈ U) : BigFppfOver.specStalk B S hS V v₀ ⟶ openStage B S hS V U :=
  siteHomMk B S hS
    (Scheme.Opens.fromSpecStalkOfMem (X := (BigFppfOver.toScheme B S hS).obj V) U v₀ hxU)
    ((Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _).trans
      (inclusion_map_hom_specStalk B S hS V v₀).symm)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openStageProj`. -/
theorem toScheme_map_openStageProj (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hxU : v₀ ∈ U) :
    (BigFppfOver.toScheme B S hS).map (openStageProj B S hS V v₀ U hxU) =
      Scheme.Opens.fromSpecStalkOfMem (X := (BigFppfOver.toScheme B S hS).obj V) U v₀ hxU :=
  rfl

/-- The canonical morphisms from `Spec 𝒪_{V, v}` to the stages are compatible with the inclusions
between them. -/
theorem openStageProj_comp_openStageLE {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (hxU : v₀ ∈ U) (hxU' : v₀ ∈ U') (h : U ≤ U') :
    openStageProj B S hS V v₀ U hxU ≫ openStageLE B S hS V h =
      openStageProj B S hS V v₀ U' hxU' :=
  hom_ext_toScheme B S hS (Scheme.Opens.fromSpecStalkOfMem_homOfLE v₀ hxU hxU' h)

/-- The canonical morphism to a stage, followed by the inclusion of that stage into `V`, is the
canonical morphism `Spec 𝒪_{V, v} ⟶ V`. -/
theorem openStageProj_comp_openStageHom (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hxU : v₀ ∈ U) :
    openStageProj B S hS V v₀ U hxU ≫ openStageHom B S hS V U =
      BigFppfOver.specStalkTo B S hS V v₀ :=
  hom_ext_toScheme B S hS ((Scheme.Opens.fromSpecStalkOfMem_ι _ _ _).trans
    (BigFppfOver.toScheme_map_specStalkTo B S hS V v₀).symm)

/-- The structure morphism of `Spec 𝒪_{V, v}` to `S` factors through any stage containing `v`.
This is the form the over-`S` condition takes when a morphism into `Spec 𝒪_{V, v}` is built out
of its components. -/
theorem inclusion_map_hom_specStalk_eq_comp (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hxU : v₀ ∈ U) :
    B.inclusion.map (BigFppfOver.specStalk B S hS V v₀).hom =
      (BigFppfOver.toScheme B S hS).map (openStageProj B S hS V v₀ U hxU) ≫
        B.inclusion.map (openStage B S hS V U).hom :=
  (inclusion_map_hom_specStalk B S hS V v₀).trans
    (Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _).symm

end OpenStages

/-! ### The system of affine open neighbourhoods, inside the site -/

section System

variable (V : BigFppfOver B S hS) (v₀ : (BigFppfOver.toScheme B S hS).obj V)

/-- **The system of affine open neighbourhoods of `v`, inside the site.** -/
noncomputable def affineNhdsStageFunctor :
    AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀ ⥤ BigFppfOver B S hS where
  obj W := openStage B S hS V W.obj.1
  map {_W _W'} f := openStageLE B S hS V
    (leOfHom ((affineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀).ι.map f))
  map_id _ := openStageLE_refl B S hS V _
  map_comp _ _ := (openStageLE_trans B S hS V _ _ _).symm

/-- The morphism of schemes underlying a transition morphism of the system is the transition
morphism of the scheme-level diagram of affine open neighbourhoods. -/
theorem toScheme_map_affineNhdsStageFunctor_map
    {W W' : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀} (f : W ⟶ W') :
    (BigFppfOver.toScheme B S hS).map ((affineNhdsStageFunctor B S hS V v₀).map f) =
      (affineOpenNhdsDiagram ((BigFppfOver.toScheme B S hS).obj V) v₀).map f := rfl

/-- The inclusion of a stage of the system into `V`. -/
noncomputable def affineNhdsStageHom
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    (affineNhdsStageFunctor B S hS V v₀).obj W ⟶ V :=
  openStageHom B S hS V W.obj.1

/-- **The canonical morphism `Spec 𝒪_{V, v} ⟶ U` of the site**, for `U` an affine open
neighbourhood of `v` in `V`. -/
noncomputable def affineNhdsProj
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    BigFppfOver.specStalk B S hS V v₀ ⟶ (affineNhdsStageFunctor B S hS V v₀).obj W :=
  openStageProj B S hS V v₀ W.obj.1 W.obj.2

/-- The canonical morphisms to the stages are compatible with the transition morphisms. -/
theorem affineNhdsProj_comp
    {W W' : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀} (f : W ⟶ W') :
    affineNhdsProj B S hS V v₀ W ≫ (affineNhdsStageFunctor B S hS V v₀).map f =
      affineNhdsProj B S hS V v₀ W' :=
  openStageProj_comp_openStageLE B S hS V v₀ W.obj.2 W'.obj.2 _

/-- The canonical morphism to a stage, followed by the inclusion of that stage into `V`, is the
canonical morphism `Spec 𝒪_{V, v} ⟶ V`. -/
theorem affineNhdsProj_comp_affineNhdsStageHom
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    affineNhdsProj B S hS V v₀ W ≫ affineNhdsStageHom B S hS V v₀ W =
      BigFppfOver.specStalkTo B S hS V v₀ :=
  openStageProj_comp_openStageHom B S hS V v₀ W.obj.1 W.obj.2

/-- A transition morphism of the system, followed by the inclusion of the later stage, is the
inclusion of the earlier one. -/
theorem affineNhdsStageFunctor_map_comp_affineNhdsStageHom
    {W W' : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀} (f : W ⟶ W') :
    (affineNhdsStageFunctor B S hS V v₀).map f ≫ affineNhdsStageHom B S hS V v₀ W' =
      affineNhdsStageHom B S hS V v₀ W :=
  openStageLE_comp_openStageHom B S hS V _

/-- The structure morphism of `Spec 𝒪_{V, v}` factors through any stage of the system. -/
theorem inclusion_map_hom_specStalk_eq_comp_affineNhdsProj
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    B.inclusion.map (BigFppfOver.specStalk B S hS V v₀).hom =
      (BigFppfOver.toScheme B S hS).map (affineNhdsProj B S hS V v₀ W) ≫
        B.inclusion.map ((affineNhdsStageFunctor B S hS V v₀).obj W).hom :=
  inclusion_map_hom_specStalk_eq_comp B S hS V v₀ W.obj.1 W.obj.2

/-! ### The limit property in the site -/

/-- **The morphisms of the site into `Spec 𝒪_{V, v}` are the compatible families of morphisms
into the stages.** Stated for a system `F` of affine open neighbourhoods of `v` whose
scheme-level cone is a limit cone, which by `AlgebraicGeometry.isLimitSpecStalkCone` is the case
for the whole system and, more generally, for any initial subsystem of it.

The over-`S` condition is free: a morphism into one stage already carries it, and the index
category is nonempty. -/
theorem exists_unique_hom_specStalk {J : Type u} [Category.{u} J] [Nonempty J]
    (F : J ⥤ AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀)
    (hF : IsLimit ((specStalkCone ((BigFppfOver.toScheme B S hS).obj V) v₀).whisker F))
    (Z : BigFppfOver B S hS)
    (φ : ∀ j, Z ⟶ (affineNhdsStageFunctor B S hS V v₀).obj (F.obj j))
    (hφ : ∀ {i j : J} (f : i ⟶ j),
      φ i ≫ (affineNhdsStageFunctor B S hS V v₀).map (F.map f) = φ j) :
    ∃! ψ : Z ⟶ BigFppfOver.specStalk B S hS V v₀,
      ∀ j, ψ ≫ affineNhdsProj B S hS V v₀ (F.obj j) = φ j := by
  obtain ⟨j₀⟩ := ‹Nonempty J›
  let c : Cone (F ⋙ affineOpenNhdsDiagram ((BigFppfOver.toScheme B S hS).obj V) v₀) :=
    { pt := (BigFppfOver.toScheme B S hS).obj Z
      π :=
        { app := fun j ↦ (BigFppfOver.toScheme B S hS).map (φ j)
          naturality := fun i j f ↦ (Category.id_comp _).trans
            ((((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
              (congrArg (BigFppfOver.toScheme B S hS).map (hφ f))).symm) } }
  have h1 : ∀ j, hF.lift c ≫ (BigFppfOver.toScheme B S hS).map
      (affineNhdsProj B S hS V v₀ (F.obj j)) = (BigFppfOver.toScheme B S hS).map (φ j) :=
    fun j ↦ hF.fac c j
  have h2 : (BigFppfOver.toScheme B S hS).map (φ j₀) ≫
      B.inclusion.map ((affineNhdsStageFunctor B S hS V v₀).obj (F.obj j₀)).hom =
      B.inclusion.map Z.hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w (φ j₀)))
  have hover : hF.lift c ≫ B.inclusion.map (BigFppfOver.specStalk B S hS V v₀).hom =
      B.inclusion.map Z.hom :=
    (congrArg (fun t ↦ hF.lift c ≫ t)
        (inclusion_map_hom_specStalk_eq_comp_affineNhdsProj B S hS V v₀ (F.obj j₀))).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun t ↦ t ≫ B.inclusion.map
          ((affineNhdsStageFunctor B S hS V v₀).obj (F.obj j₀)).hom) (h1 j₀))).trans h2)
  refine ⟨siteHomMk B S hS (hF.lift c) hover, fun j ↦ ?_, fun ψ' hψ' ↦ ?_⟩
  · exact hom_ext_toScheme B S hS
      (((BigFppfOver.toScheme B S hS).map_comp _ _).trans (h1 j))
  · refine hom_ext_toScheme B S hS (hF.hom_ext fun j ↦ ?_)
    exact (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (hψ' j))).trans (hF.fac c j).symm

/-- The cone in the site on a system of affine open neighbourhoods of `v`, with vertex
`Spec 𝒪_{V, v}` and the canonical morphisms as its legs. -/
noncomputable def affineNhdsSiteCone {J : Type u} [Category.{u} J]
    (F : J ⥤ AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    Cone (F ⋙ affineNhdsStageFunctor B S hS V v₀) where
  pt := BigFppfOver.specStalk B S hS V v₀
  π :=
    { app := fun j ↦ affineNhdsProj B S hS V v₀ (F.obj j)
      naturality := fun _ _ f ↦ (Category.id_comp _).trans
        (affineNhdsProj_comp B S hS V v₀ (F.map f)).symm }

/-- **`Spec 𝒪_{V, v}` is the limit of the system of its affine open neighbourhoods, in the
site.** -/
noncomputable def isLimitAffineNhdsSiteCone {J : Type u} [Category.{u} J] [Nonempty J]
    (F : J ⥤ AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀)
    (hF : IsLimit ((specStalkCone ((BigFppfOver.toScheme B S hS).obj V) v₀).whisker F)) :
    IsLimit (affineNhdsSiteCone B S hS V v₀ F) :=
  IsLimit.ofExistsUnique fun s ↦
    exists_unique_hom_specStalk B S hS V v₀ F hF s.pt (fun j ↦ s.π.app j)
      fun {_i _j} f ↦ s.w f

/-- **`Spec 𝒪_{V, v}` is the limit of the system of its affine open neighbourhoods in the
category of presheaves on the site.** This is the universal property against an arbitrary
presheaf, which is the `isLimit` field of
`AlgebraicGeometry.Space.AffineLimitPresentation`; it follows from
`AlgebraicGeometry.Space.isLimitAffineNhdsSiteCone` because the Yoneda embedding preserves
limits. -/
theorem exists_unique_presheafHom_specStalk {J : Type u} [Category.{u} J] [Nonempty J]
    (F : J ⥤ AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀)
    (hF : IsLimit ((specStalkCone ((BigFppfOver.toScheme B S hS).obj V) v₀).whisker F))
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (m : ∀ j, G ⟶ yoneda.obj ((affineNhdsStageFunctor B S hS V v₀).obj (F.obj j)))
    (hm : ∀ {i j : J} (f : i ⟶ j),
      m i ≫ yoneda.map ((affineNhdsStageFunctor B S hS V v₀).map (F.map f)) = m j) :
    ∃! h : G ⟶ yoneda.obj (BigFppfOver.specStalk B S hS V v₀),
      ∀ j, h ≫ yoneda.map (affineNhdsProj B S hS V v₀ (F.obj j)) = m j :=
  (isLimitOfPreserves yoneda (isLimitAffineNhdsSiteCone B S hS V v₀ F hF)).existsUnique
    { pt := G
      π :=
        { app := m
          naturality := fun _ _ f ↦ (Category.id_comp _).trans (hm f).symm } }

end System

end Space

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Small bases of affine open neighbourhoods -/

/-- A subsystem of the affine open neighbourhoods of `x` which refines every open neighbourhood
maps into every affine open neighbourhood. -/
private theorem exists_nonempty_hom_fullSubcategory_affineOpenNhds {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x))
    (hQ : ∀ U : OpenNhds x, ∃ W : Q.FullSubcategory, W.obj.obj ≤ U) (d : AffineOpenNhds X x) :
    ∃ W : Q.FullSubcategory, Nonempty (Q.ι.obj W ⟶ d) := by
  obtain ⟨W, hle⟩ := hQ d.obj
  exact ⟨W, ⟨ObjectProperty.homMk (homOfLE hle)⟩⟩

/-- A subsystem of the affine open neighbourhoods of `x` which refines every open neighbourhood
is cofiltered: two of its members both contain a third, because their intersection is an open
neighbourhood. -/
theorem isCofiltered_fullSubcategory_affineOpenNhds {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x))
    (hQ : ∀ U : OpenNhds x, ∃ W : Q.FullSubcategory, W.obj.obj ≤ U) :
    IsCofiltered Q.FullSubcategory :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful Q.ι
    (exists_nonempty_hom_fullSubcategory_affineOpenNhds Q hQ)

/-- A subsystem of the affine open neighbourhoods of `x` which refines every open neighbourhood
is initial, so a limit over all affine open neighbourhoods restricts to a limit over it. -/
theorem initial_ι_fullSubcategory_affineOpenNhds {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x))
    (hQ : ∀ U : OpenNhds x, ∃ W : Q.FullSubcategory, W.obj.obj ≤ U) :
    Q.ι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful Q.ι
    (exists_nonempty_hom_fullSubcategory_affineOpenNhds Q hQ)

/-- A subsystem of the affine open neighbourhoods of `x` is a thin category: its Hom-sets have
at most one element, since the ambient category of open neighbourhoods is a partial order. -/
theorem mk_hom_fullSubcategory_affineOpenNhds_le_one {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x)) (i j : Q.FullSubcategory) :
    #(i ⟶ j) ≤ 1 :=
  Cardinal.le_one_iff_subsingleton.mpr
    ⟨fun _ _ ↦ ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Subsingleton.elim _ _))⟩

/-- A subsystem of the affine open neighbourhoods of `x` is a thin category, so its Hom-sets
satisfy the cardinality bound of `AlgebraicGeometry.Space.AffineLimitPresentation` with no
hypothesis at all. -/
theorem mk_hom_fullSubcategory_affineOpenNhds_lt {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x)) (i j : Q.FullSubcategory) :
    #(i ⟶ j) < B.cutoff.ord.cof :=
  (mk_hom_fullSubcategory_affineOpenNhds_le_one Q i j).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- The Hom-sets of a subsystem of the affine open neighbourhoods of `x` are bounded by the
*single* cardinal `ℵ₀`, which is the form the cofinality-free cardinality package of
`AlgebraicGeometry.Space.SiteLimitBound` asks for. -/
theorem mk_hom_fullSubcategory_affineOpenNhds_le_aleph0 {X : Scheme.{u}} {x : X}
    (Q : ObjectProperty (AffineOpenNhds X x)) (i j : Q.FullSubcategory) :
    #(i ⟶ j) ≤ ℵ₀ :=
  (mk_hom_fullSubcategory_affineOpenNhds_le_one Q i j).trans Cardinal.one_le_aleph0

/-- **There are fewer affine open neighbourhoods of a point of an object of the site than the
site's cutoff.** They inject into the affine opens of the scheme, which
`AlgebraicGeometry.Scheme.size` bounds by definition.

This is the clause that the *cofinality* bound asks for and that no system of affine open
neighbourhoods supplies: see the note at the head of this file. It is exactly what the
cofinality-free package of `AlgebraicGeometry.Space.SiteLimitBound` asks for instead. -/
theorem mk_affineOpenNhds_lt_cutoff {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    #(AffineOpenNhds X x) < B.cutoff := by
  refine lt_of_le_of_lt (le_trans (Cardinal.mk_le_of_injective
    (f := fun W : AffineOpenNhds X x ↦ (⟨W.obj.1, W.property⟩ : X.affineOpens)) ?_)
    X.mk_affineOpens_le_size) hX
  rintro ⟨⟨U, _⟩, _⟩ ⟨⟨U', _⟩, _⟩ ⟨⟩
  rfl

/-- **A small basis of affine open neighbourhoods.** A subsystem of the affine open
neighbourhoods of `x` in `X` which refines every open neighbourhood of `x` and whose index
category is smaller than the cofinality of the site's size cutoff.

This is the left-hand, cofinality package of
`AlgebraicGeometry.Space.SiteLimitBound`, which the system of *all* affine open neighbourhoods
does not supply: that system is bounded by `X.size` and hence by `B.cutoff`, but nothing bounds
it by `B.cutoff.ord.cof`. The clause speaks only of the topology of `X` at `x` and of the site's
cutoff.

It is no longer needed for the presentation of `Spec 𝒪_{V, v}`, which
`AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale` builds over all affine open
neighbourhoods using the *other* package of that disjunction; it is kept for a caller who has a
small basis from elsewhere, for instance a point with a finite one. -/
def HasSmallAffineNhdsBasis (B : BigFppfSite.{u}) (X : Scheme.{u}) (x : X) : Prop :=
  ∃ Q : ObjectProperty (AffineOpenNhds X x),
    #Q.FullSubcategory < B.cutoff.ord.cof ∧
      ∀ U : OpenNhds x, ∃ W : Q.FullSubcategory, W.obj.obj ≤ U

/-- A set of affine open neighbourhoods of `x` which is small for the site and refines every open
neighbourhood witnesses `AlgebraicGeometry.Space.HasSmallAffineNhdsBasis`. -/
theorem hasSmallAffineNhdsBasis_of_set {X : Scheme.{u}} {x : X}
    (𝒰 : Set (AffineOpenNhds X x)) (hsize : #𝒰 < B.cutoff.ord.cof)
    (h𝒰 : ∀ U : OpenNhds x, ∃ W ∈ 𝒰, W.obj ≤ U) :
    HasSmallAffineNhdsBasis B X x := by
  refine ⟨fun W ↦ W ∈ 𝒰, ?_, fun U ↦ ?_⟩
  · exact lt_of_eq_of_lt (Cardinal.mk_congr ⟨fun W ↦ ⟨W.obj, W.property⟩, fun W ↦ ⟨W.1, W.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩) hsize
  · obtain ⟨W, hW, hle⟩ := h𝒰 U
    exact ⟨⟨W, hW⟩, hle⟩

/-- A point with a *finite* basis of affine open neighbourhoods has a small one, on any site. -/
theorem hasSmallAffineNhdsBasis_of_finite {X : Scheme.{u}} {x : X}
    (𝒰 : Set (AffineOpenNhds X x)) [Finite 𝒰]
    (h𝒰 : ∀ U : OpenNhds x, ∃ W ∈ 𝒰, W.obj ≤ U) :
    HasSmallAffineNhdsBasis B X x :=
  hasSmallAffineNhdsBasis_of_set B 𝒰
    ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff_cof) h𝒰

/-! ### The presentation -/

section Presentation

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_SpecStalkAffineNhdsSystem
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B S hS}

/-- **Every transition morphism of a system of affine open neighbourhoods is a
monomorphism**, being the inclusion of one open subscheme of `V` into another. This is the
structural clause of the cofinality-free package of
`AlgebraicGeometry.Space.SiteLimitBound`. -/
theorem mono_yoneda_map_affineNhdsStageFunctor_map (V : BigFppfOver B S hS)
    (v₀ : (BigFppfOver.toScheme B S hS).obj V)
    {W W' : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀} (f : W ⟶ W') :
    Mono (yoneda.map ((affineNhdsStageFunctor B S hS V v₀).map f)) :=
  mono_of_isOpenImmersion B S hS _ (isOpenImmersion_yoneda_map B S hS _
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
      (((BigFppfOver.toScheme B S hS).obj V).homOfLE
        (show W.obj.1 ≤ W'.obj.1 from
          leOfHom ((affineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀).ι.map f))))))

/-- **The limit presentation of `Spec 𝒪_{V, v}` asked for by Stacks 0CV9**, built from a
subsystem of the affine open neighbourhoods of `v` in `V` which refines every open neighbourhood
and is small for the site.

The stages are the members of the subsystem, read as objects of the site; they are affine, the
system is cofiltered because it refines, and its inclusion into all affine open neighbourhoods of
`v` is initial, so the scheme-level limit `AlgebraicGeometry.isLimitSpecStalkCone` restricts to
it. The cardinality clauses are the smallness hypothesis and the thinness of the index. -/
noncomputable def specStalkAffineLimitPresentationOfBasis
    (P : PrePureSituation.{u, u} B S hS) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (t' : points B S hS
      (yoneda.obj (BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v))))
    (xi : points B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f))
    (hxi : pointsMap B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f)
      (pullback.fst (P.specStalkPointedOver V a v hv).g P.f) xi = t')
    (Q : ObjectProperty (AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v)))
    (hbound : SiteLimitBound
      (Q.ι ⋙ affineNhdsStageFunctor B S hS V (pointsToScheme B S hS V v)))
    (hQ : ∀ U : OpenNhds (pointsToScheme B S hS V v),
      ∃ W : Q.FullSubcategory, W.obj.obj ≤ U) :
    AffineLimitPresentation (P.specStalkDiagram V a v hv t' xi hxi) where
  J := Q.FullSubcategory
  cofiltered := isCofiltered_fullSubcategory_affineOpenNhds Q hQ
  stage := Q.ι ⋙ affineNhdsStageFunctor B S hS V (pointsToScheme B S hS V v)
  bound := hbound
  isAffine := fun j ↦ isAffine_affineOpenNhdsDiagram_obj
    ((BigFppfOver.toScheme B S hS).obj V) (pointsToScheme B S hS V v) (Q.ι.obj j)
  proj := fun j ↦ affineNhdsProj B S hS V (pointsToScheme B S hS V v) (Q.ι.obj j)
  proj_comp := fun {_i _j} f ↦ affineNhdsProj_comp B S hS V _ (Q.ι.map f)
  base := fun j ↦
    yoneda.map (affineNhdsStageHom B S hS V (pointsToScheme B S hS V v) (Q.ι.obj j)) ≫ a
  base_comp := fun {_i _j} f ↦ (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ a) ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (affineNhdsStageFunctor_map_comp_affineNhdsStageHom
        B S hS V (pointsToScheme B S hS V v) (Q.ι.map f)))))
  proj_base := fun j ↦ (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ a) ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (affineNhdsProj_comp_affineNhdsStageHom
        B S hS V (pointsToScheme B S hS V v) (Q.ι.obj j)))))
  isLimit := by
    have : IsCofiltered Q.FullSubcategory :=
      isCofiltered_fullSubcategory_affineOpenNhds Q hQ
    have : Nonempty Q.FullSubcategory := IsCofiltered.nonempty
    have : Q.ι.Initial := initial_ι_fullSubcategory_affineOpenNhds Q hQ
    exact fun G m hmcomp ↦ exists_unique_presheafHom_specStalk B S hS V _ Q.ι
      ((Functor.Initial.isLimitWhiskerEquiv Q.ι _).symm
        (isLimitSpecStalkCone ((BigFppfOver.toScheme B S hS).obj V)
          (pointsToScheme B S hS V v))) G m fun {_i _j} f ↦ hmcomp f

/-- Every stage of the system is étale over the base of the situation, when the chart is: a stage
is an open subscheme of the chart, and an open immersion is étale. -/
theorem isEtale_affineNhdsStageHom_comp {P : PrePureSituation.{u, u} B S hS}
    {V : BigFppfOver B S hS} {a : yoneda.obj V ⟶ P.Y} (hetale : IsEtale B S hS a)
    (v₀ : (BigFppfOver.toScheme B S hS).obj V)
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V) v₀) :
    IsEtale B S hS (yoneda.map (affineNhdsStageHom B S hS V v₀ W) ≫ a) :=
  isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS
    (isOpenImmersion_yoneda_map_openStageHom B S hS V W.obj.1)) hetale

/-- **The limit presentation of `Spec 𝒪_{V, v}` with the quasi-finiteness of its stages**, from
a subsystem of the affine open neighbourhoods of `v` which refines every open neighbourhood and
whose cardinality clause is supplied in either of the two ways
`AlgebraicGeometry.Space.SiteLimitBound` allows. Both forms below are this, with a different
discharge of that clause. -/
theorem exists_affineLimitPresentation_of_basis (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hetale : IsEtale B S hS a)
    (t' : points B S hS
      (yoneda.obj (BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v))))
    (xi : points B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f))
    (hxi : pointsMap B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f)
      (pullback.fst (P.specStalkPointedOver V a v hv).g P.f) xi = t')
    (Q : ObjectProperty (AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v)))
    (hbound : SiteLimitBound
      (Q.ι ⋙ affineNhdsStageFunctor B S hS V (pointsToScheme B S hS V v)))
    (hQ : ∀ U : OpenNhds (pointsToScheme B S hS V v),
      ∃ W : Q.FullSubcategory, W.obj.obj ≤ U) :
    ∃ A : AffineLimitPresentation (P.specStalkDiagram V a v hv t' xi hxi),
      ∀ i, IsQuasiFiniteAt B S hS (A.base i) (A.stagePoint i) := by
  refine ⟨specStalkAffineLimitPresentationOfBasis P V a v hv t' xi hxi Q hbound hQ, fun i ↦ ?_⟩
  show IsQuasiFiniteAt B S hS
    (yoneda.map (affineNhdsStageHom B S hS V (pointsToScheme B S hS V v) (Q.ι.obj i)) ≫ a) _
  exact isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
    (isAlgebraicSpace_yoneda B S hS _)
    (isLocallyQuasiFinite_of_isEtale' B S hS
      (isEtale_affineNhdsStageHom_comp hetale _ (Q.ι.obj i))) _

/-- **The carried input of the ascent of purity, for an étale chart with a small basis of affine
open neighbourhoods at `v`.** This discharges
`AlgebraicGeometry.Space.SpecStalkAffineLimitPresentation` from the source's own system — the
affine open neighbourhoods of `v`, over which `𝒪_{V, v}` is the colimit of the sections, so that
`Spec 𝒪_{V, v}` is their limit — the étale hypothesis on the chart giving the quasi-finiteness of
the stages over `Y`, and the smallness being the left-hand package of the cardinality clause of
`AlgebraicGeometry.Space.AffineLimitPresentation`. -/
theorem specStalkAffineLimitPresentation (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hetale : IsEtale B S hS a)
    (hbasis : HasSmallAffineNhdsBasis B ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v)) :
    SpecStalkAffineLimitPresentation P V a v hv := by
  obtain ⟨Q, hsize, hQ⟩ := hbasis
  intro t' xi hxi
  exact exists_affineLimitPresentation_of_basis P V a v hv hetale t' xi hxi Q
    (Or.inl ⟨hsize, fun i j ↦ mk_hom_fullSubcategory_affineOpenNhds_lt B Q i j⟩) hQ

/-- **The carried input of the ascent of purity, for an étale chart, with nothing granted.**
This is `AlgebraicGeometry.Space.specStalkAffineLimitPresentation` with its smallness
hypothesis removed: the system of *all* affine open neighbourhoods of `v` does it.

That system is the source's own one, and the note at the head of this file records why it does
not satisfy the cofinality clause and why no subsystem of it does either. It satisfies the
cofinality-free clause of `AlgebraicGeometry.Space.SiteLimitBound` instead, on all three
counts and for reasons that have nothing to do with purity or with the module: the affine open
neighbourhoods of `v` inject into the affine opens of `V`, so there are fewer of them than the
cutoff (`AlgebraicGeometry.Space.mk_affineOpenNhds_lt_cutoff`); the system is a partial order,
so `ℵ₀` bounds all its Hom-sets at once; and its transition morphisms are inclusions of open
subschemes, hence monomorphisms. -/
theorem specStalkAffineLimitPresentation_of_isEtale (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hetale : IsEtale B S hS a) :
    SpecStalkAffineLimitPresentation P V a v hv := by
  intro t' xi hxi
  let Q : ObjectProperty (AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj V)
    (pointsToScheme B S hS V v)) := fun _ ↦ True
  have hQ : ∀ U : OpenNhds (pointsToScheme B S hS V v),
      ∃ W : Q.FullSubcategory, W.obj.obj ≤ U := by
    intro U
    obtain ⟨W, hW⟩ := exists_affineOpenNhds_le ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v) U
    exact ⟨⟨W, trivial⟩, hW⟩
  have hsize : #Q.FullSubcategory < B.cutoff :=
    lt_of_eq_of_lt (Cardinal.mk_congr ⟨fun W ↦ W.obj, fun W ↦ ⟨W, trivial⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩) (mk_affineOpenNhds_lt_cutoff B V.left.property _)
  exact exists_affineLimitPresentation_of_basis P V a v hv hetale t' xi hxi Q
    (Or.inr (Or.inl ⟨hsize, ℵ₀, B.aleph0_lt_cutoff,
      fun i j ↦ mk_hom_fullSubcategory_affineOpenNhds_le_aleph0 Q i j,
      fun {_i _j} f ↦ mono_yoneda_map_affineNhdsStageFunctor_map V _ (Q.ι.map f)⟩)) hQ

/-! ### The ascent, with the limit presentation discharged -/

/-- **The ascent of purity along `Spec 𝒪_{V, v} ⟶ V ⟶ Y` for an étale chart.** This is
`AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove` with the carried limit
presentation replaced by the two hypotheses that discharge it: the chart is étale over the base,
and `v` has a basis of affine open neighbourhoods small for the site. -/
theorem exists_specializes_fibre_of_isPureAbove_of_isEtale (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hpure : IsPureAbove P)
    (hetale : IsEtale B S hS a)
    (hbasis : HasSmallAffineNhdsBasis B ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v)) :
    ∀ x ∈ relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F,
      ∃ θ : points B S hS (P.specStalkPointedOver V a v hv).baseChange.X,
        x ⤳ θ ∧ pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
            (P.specStalkPointedOver V a v hv).baseChange.f θ =
          (P.specStalkPointedOver V a v hv).baseChange.y :=
  exists_specializes_fibre_of_isPureAbove P V a v hv hpure
    (specStalkAffineLimitPresentation P V a v hv hetale hbasis)

/-- **The ascent of purity along `Spec 𝒪_{V, v} ⟶ V ⟶ Y` for an étale chart, with nothing
granted.** This is `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove_of_isEtale`
with the smallness hypothesis removed, through
`AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale`. -/
theorem exists_specializes_fibre_of_isPureAbove_of_isEtale' (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hpure : IsPureAbove P)
    (hetale : IsEtale B S hS a) :
    ∀ x ∈ relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F,
      ∃ θ : points B S hS (P.specStalkPointedOver V a v hv).baseChange.X,
        x ⤳ θ ∧ pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
            (P.specStalkPointedOver V a v hv).baseChange.f θ =
          (P.specStalkPointedOver V a v hv).baseChange.y :=
  exists_specializes_fibre_of_isPureAbove P V a v hv hpure
    (specStalkAffineLimitPresentation_of_isEtale P V a v hv hetale)

/-- **The assassin containment over `Spec 𝒪_{V, v}` for an étale chart.** This is
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange` with the
carried limit presentation replaced by the two hypotheses that discharge it. -/
theorem relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale
    (P : PrePureSituation.{u, u} B S hS) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (c : EtaleOverSource (P.specStalkPointedOver V a v hv).baseChange)
    (hpure : IsPureAbove P) (hetale : IsEtale B S hS a)
    (hbasis : HasSmallAffineNhdsBasis B ((BigFppfOver.toScheme B S hS).obj V)
      (pointsToScheme B S hS V v))
    (hfibre : pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
          (P.specStalkPointedOver V a v hv).baseChange.f ⁻¹'
        {(P.specStalkPointedOver V a v hv).baseChange.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange P V a v hv c hpure
    (specStalkAffineLimitPresentation P V a v hv hetale hbasis) hfibre

/-- **The assassin containment over `Spec 𝒪_{V, v}` for an étale chart, with nothing granted.**
This is `Space.relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale` with
the smallness hypothesis removed, through
`AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale`. -/
theorem relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale'
    (P : PrePureSituation.{u, u} B S hS) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (c : EtaleOverSource (P.specStalkPointedOver V a v hv).baseChange)
    (hpure : IsPureAbove P) (hetale : IsEtale B S hS a)
    (hfibre : pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
          (P.specStalkPointedOver V a v hv).baseChange.f ⁻¹'
        {(P.specStalkPointedOver V a v hv).baseChange.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange P V a v hv c hpure
    (specStalkAffineLimitPresentation_of_isEtale P V a v hv hetale) hfibre

end Presentation

end Space

end AlgebraicGeometry

end
