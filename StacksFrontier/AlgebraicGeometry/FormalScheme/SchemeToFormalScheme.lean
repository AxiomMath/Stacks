module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrum

/-!
# The functor from schemes to formal schemes

A scheme `(X, 𝒪_X)` becomes a formal scheme à la EGA by replacing `𝒪_X` with the
pseudo-discrete sheaf of topological rings `𝒪'_X` having the same underlying sheaf of rings.
This is compatible with morphisms and so defines the functor of Stacks 0AI0,

`Schemes ⟶ Formal Schemes`,

which is fully faithful because a morphism of the pseudo-discretised spaces is exactly a
morphism of schemes: continuity of the comparison map is automatic, and the stalks are
unchanged.

## Main definitions

* `AlgebraicGeometry.schemeToLTRSObj` and `AlgebraicGeometry.schemeToLTRSHom`: a scheme and a
  morphism of schemes as a locally topologically ringed space and a morphism of such.
* `AlgebraicGeometry.schemeToFormalScheme`: **Stacks 0AI0**, the functor from schemes to formal
  schemes.
* `AlgebraicGeometry.schemeOfLTRSHom`: the morphism of schemes underlying a morphism of the
  pseudo-discretised locally topologically ringed spaces, which is what makes the functor full.

## Main results

* `AlgebraicGeometry.isSheaf_pseudoDiscrete` and
  `AlgebraicGeometry.continuous_pseudoDiscrete_c`: the pseudo-discretisation of the structure
  sheaf of a scheme is a sheaf of topological rings, and the comparison map of a morphism of
  schemes is continuous for the pseudo-discrete topologies. These are the two verifications the
  source leaves to the reader.
* `AlgebraicGeometry.isFormalScheme_schemeToLTRSObj`: the pseudo-discretisation of a scheme is a
  formal scheme.
* `AlgebraicGeometry.schemeToFormalScheme`, with the instances
  `AlgebraicGeometry.full_schemeToFormalScheme` and
  `AlgebraicGeometry.faithful_schemeToFormalScheme`: **Stacks 0AI0**, the functor and its full
  faithfulness.

## Implementation notes

Both verifications deferred by the source rest on the same point: the underlying space of a
scheme has a basis of quasi-compact opens, so a quasi-compact open is refined by finitely many
quasi-compact opens of any covering. Full faithfulness is `Stacks 0AHZ` for pseudo-discrete
sheaves, which here takes the concrete form `AlgebraicGeometry.isLocalHom_stalkMap_iff`
together with the fact that pseudo-discretisation does not change sections or restriction maps.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI0](https://stacks.math.columbia.edu/tag/0AI0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

/-! ### The verifications deferred by the source -/

/-- The gluing step behind `AlgebraicGeometry.isSheaf_pseudoDiscrete`: the ring homomorphism
gluing a compatible family of sections of a scheme's structure sheaf over an open covering is
continuous for the pseudo-discrete topologies. A quasi-compact open of the base is covered by
finitely many quasi-compact opens subordinate to the covering, on each of which the glued
section is locally constant, and sections of a sheaf agreeing on a covering agree. -/
theorem continuous_pseudoDiscrete_gluing (X : Scheme.{u}) {ι : Type u}
    (cover : ι → Opens X)
    (cone : Cone ((ObjectProperty.ι (fun V : Opens X => ∃ i, V ≤ cover i)).op ⋙
      pseudoDiscrete X.presheaf))
    (glue : cone.pt.α →+* X.presheaf.obj (op (iSup cover)))
    (fac : ∀ V : TopCat.Presheaf.SheafCondition.OpensLeCover cover,
      (X.presheaf.map (homOfLE (V.property.choose_spec.trans
        (le_iSup cover V.property.choose))).op).hom.comp glue = (cone.π.app (op V)).1) :
    Continuous[cone.pt.isTopologicalSpace, pseudoDiscreteTopology X.presheaf (iSup cover)]
      glue := by
  let _ : TopologicalSpace cone.pt.α := cone.pt.isTopologicalSpace
  refine continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 ?_
  let _ : TopologicalSpace (X.presheaf.obj (op compactOpen.1)) := ⊥
  let patches := {V : TopCat.Presheaf.SheafCondition.OpensLeCover cover //
    IsCompact (V.obj : Set X) ∧ V.obj ≤ compactOpen.1}
  have hcover : (compactOpen.1 : Set X) ⊆ ⋃ patch : patches, (patch.1.obj : Set X) := by
    intro point hpoint
    obtain ⟨index, hindex⟩ := Opens.mem_iSup.1 (compactOpen.2.2 hpoint)
    obtain ⟨small, ⟨hopen, hcompact⟩, hpointSmall, hsmall⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
        (show point ∈ (compactOpen.1 ⊓ cover index : Opens X) from ⟨hpoint, hindex⟩)
        (compactOpen.1 ⊓ cover index).isOpen
    exact Set.mem_iUnion.2 ⟨⟨⟨⟨small, hopen⟩, index, fun _ hx => (hsmall hx).2⟩,
      hcompact, fun _ hx => (hsmall hx).1⟩, hpointSmall⟩
  obtain ⟨finitePatches, hfiniteCover⟩ := compactOpen.2.1.elim_finite_subcover
    (fun patch : patches => (patch.1.obj : Set X)) (fun patch => patch.1.obj.isOpen) hcover
  let restriction := (X.presheaf.map (homOfLE compactOpen.2.2).op).hom.comp glue
  refine (continuous_iff_continuousAt (f := restriction)).2 fun sectionValue => ?_
  refine Filter.EventuallyEq.continuousAt (y := restriction sectionValue) ?_
  have heventually : ∀ patch ∈ finitePatches,
      ∀ᶠ value in nhds sectionValue,
        (cone.π.app (op patch.1)).1 value = (cone.π.app (op patch.1)).1 sectionValue := by
    intro patch hpatch
    have hcontinuous : Continuous[cone.pt.isTopologicalSpace,
        pseudoDiscreteTopology X.presheaf patch.1.obj] (cone.π.app (op patch.1)).1 :=
      (cone.π.app (op patch.1)).2
    rw [pseudoDiscreteTopology_eq_bot X.presheaf patch.2.1] at hcontinuous
    let _ : TopologicalSpace (X.presheaf.obj (op patch.1.obj)) := ⊥
    have _ : DiscreteTopology (X.presheaf.obj (op patch.1.obj)) := discreteTopology_bot _
    exact ((IsLocallyConstant.iff_continuous _).2 hcontinuous).eventually_eq sectionValue
  filter_upwards [(finitePatches.eventually_all).2 heventually] with value hvalue
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨X.presheaf, X.IsSheaf⟩ : X.toTopCat.Sheaf CommRingCat)
    (fun patch : ↥finitePatches => patch.1.1.obj) compactOpen.1
    (fun patch => homOfLE patch.1.2.2) ?_ (restriction value) (restriction sectionValue) ?_
  · intro point hpoint
    obtain ⟨patch, hmem, hpointPatch⟩ := Set.mem_iUnion₂.1 (hfiniteCover hpoint)
    exact Opens.mem_iSup.2 ⟨⟨patch, hmem⟩, hpointPatch⟩
  · intro patch
    have hcomp : (X.presheaf.map (homOfLE patch.1.2.2).op).hom.comp restriction =
        (cone.π.app (op patch.1.1)).1 := by
      dsimp only [restriction]
      rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
      exact fac patch.1.1
    exact (RingHom.congr_fun hcomp value).trans
      ((hvalue patch.1 patch.2).trans (RingHom.congr_fun hcomp sectionValue).symm)

/-- **Deferred by the source** ("The reader may verify (omitted)"): on a space with a basis of
quasi-compact opens — as the underlying space of a scheme has, its affine opens being a
quasi-compact basis — the pseudo-discrete presheaf of topological rings attached to a sheaf of
rings is a sheaf of topological rings. The point is that over an open covering the sections over
the base are a *subspace* of the product of the sections over the pieces. -/
@[ega "0 3.8.1" "special case", ega "I 10.1.1" "partial"]
theorem isSheaf_pseudoDiscrete (X : Scheme.{u}) : (pseudoDiscrete X.presheaf).IsSheaf := by
  classical
  refine (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).2 fun ι cover => ?_
  let ringLimit := (X.IsSheaf.isSheafOpensLeCover cover).some
  let forget := forget₂ TopCommRingCat.{u} CommRingCat.{u}
  refine ⟨IsLimit.mk (fun cone => ⟨(ringLimit.lift (forget.mapCone cone)).hom, ?_⟩)
    (fun cone V => Subtype.ext (congrArg CommRingCat.Hom.hom
      (ringLimit.fac (forget.mapCone cone) V))) ?_⟩
  · exact continuous_pseudoDiscrete_gluing X cover cone _ fun V =>
      congrArg CommRingCat.Hom.hom (ringLimit.fac (forget.mapCone cone) (op V))
  · exact fun cone morphism hfac => Subtype.ext (congrArg CommRingCat.Hom.hom
      (ringLimit.uniq (forget.mapCone cone) (forget.map morphism)
        fun V => congrArg (fun morphism => forget.map morphism) (hfac V)))

/-- **Deferred by the source** (the construction "is compatible with morphisms"): the comparison
map of a morphism of schemes is continuous for the pseudo-discrete topologies. Given a
quasi-compact open `W ⊆ f⁻¹V` of `X`, its image is a quasi-compact subset of `V`, so it is
contained in a quasi-compact open `V' ⊆ V` with `W ⊆ f⁻¹V'`, and the map factors through the
discrete `𝒪_Y(V')`. -/
theorem continuous_pseudoDiscrete_c {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Opens Y) :
    Continuous[pseudoDiscreteTopology Y.presheaf V,
      pseudoDiscreteTopology X.presheaf ((Opens.map f.base).obj V)] (f.c.app (op V)).hom := by
  refine continuous_iInf_rng.2 fun W => continuous_induced_rng.2 ?_
  obtain ⟨V', hcompact, hopen, hWV', hV'V⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (W.2.1.image f.continuous) V.isOpen (Set.image_subset_iff.2 W.2.2)
  let V₀ : Opens Y := ⟨V', hopen⟩
  have hV₀V : V₀ ≤ V := hV'V
  have hWV₀ : W.1 ≤ (Opens.map f.base).obj V₀ := fun x hx => hWV' ⟨x, hx, rfl⟩
  have hfun : ⇑(X.presheaf.map (homOfLE W.2.2).op).hom ∘ ⇑(f.c.app (op V)).hom =
      (⇑(X.presheaf.map (homOfLE hWV₀).op).hom ∘ ⇑(f.c.app (op V₀)).hom) ∘
        ⇑(Y.presheaf.map (homOfLE hV₀V).op).hom := by
    have heq : f.c.app (op V) ≫ X.presheaf.map (homOfLE W.2.2).op =
        Y.presheaf.map (homOfLE hV₀V).op ≫ f.c.app (op V₀) ≫
          X.presheaf.map (homOfLE hWV₀).op := by
      rw [← Category.assoc, f.c.naturality (homOfLE hV₀V).op, Category.assoc]
      exact congrArg (fun morphism => f.c.app (op V) ≫ morphism)
        (X.presheaf.map_comp ((Opens.map f.base).map (homOfLE hV₀V)).op (homOfLE hWV₀).op)
    exact congrArg (fun morphism : Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op W.1) =>
      ⇑morphism.hom) heq
  rw [hfun]
  let _ : TopologicalSpace (Y.presheaf.obj (op V)) := pseudoDiscreteTopology Y.presheaf V
  let _ : TopologicalSpace (Y.presheaf.obj (op V₀)) := ⊥
  let _ : TopologicalSpace (X.presheaf.obj (op W.1)) := ⊥
  exact (@continuous_of_discreteTopology _ ⊥ (discreteTopology_bot _) _ ⊥ _).comp
    (continuous_pseudoDiscreteTopology_restrict Y.presheaf hcompact hV₀V)

/-! ### The functor -/

/-- The comparison map of a morphism of schemes, as a morphism of the pseudo-discrete sheaves of
topological rings. -/
noncomputable def pseudoDiscreteC {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pseudoDiscrete Y.presheaf ⟶ f.base _* pseudoDiscrete X.presheaf where
  app V := ⟨(f.c.app V).hom, continuous_pseudoDiscrete_c f V.unop⟩
  naturality _ _ i := Subtype.ext (congrArg CommRingCat.Hom.hom (f.c.naturality i))

/-- A scheme `(X, 𝒪_X)` as a locally topologically ringed space `(X, 𝒪'_X)`, where `𝒪'_X` is the
pseudo-discrete sheaf of topological rings whose underlying sheaf of rings is `𝒪_X`. -/
@[ega "0 3.8.1" "special case", ega "I 10.1.1" "partial"]
noncomputable def schemeToLTRSObj (X : Scheme.{u}) : LTRS.{u} where
  carrier := X.toPresheafedSpace.carrier
  presheaf := pseudoDiscrete X.presheaf
  IsSheaf := isSheaf_pseudoDiscrete X
  isLocalRing := fun x => isLocalRing_stalk_pseudoDiscrete X.presheaf x

/-- The locally topologically ringed space attached to a scheme is the pseudo-discretisation of
its presheafed space. -/
theorem schemeToLTRSObj_toPresheafedSpace (X : Scheme.{u}) :
    (schemeToLTRSObj X).toPresheafedSpace = pseudoDiscreteSpace X.toPresheafedSpace := rfl

/-- The morphism of locally topologically ringed spaces underlying the image of a morphism of
schemes: the same continuous map and the same comparison map. -/
noncomputable def schemeToLTRSHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pseudoDiscreteSpace X.toPresheafedSpace ⟶ pseudoDiscreteSpace Y.toPresheafedSpace where
  base := f.base
  c := pseudoDiscreteC f

/-- Forgetting the pseudo-discrete topologies recovers the original morphism of schemes. -/
theorem forgetPseudoDiscreteHom_schemeToLTRSHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    forgetPseudoDiscreteHom (schemeToLTRSHom f) = f.toHom := rfl

/-- **Deferred by the source**: the stalk map of the pseudo-discretised comparison map is, after
forgetting the topologies, the stalk map of the morphism of schemes — stalks of topological
rings are computed on the underlying rings, Stacks 0B24 — hence a local homomorphism. -/
theorem isLocalHom_stalkMap_schemeToLTRSHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom ((schemeToLTRSHom f).stalkMap x).1 :=
  (isLocalHom_stalkMap_iff (schemeToLTRSHom f) x).2 <| by
    rw [forgetPseudoDiscreteHom_schemeToLTRSHom]
    exact f.toLRSHom.prop x

/-- **Deferred by the source** (stated there as the example that `Spf A` is `Spec A` for a
discrete ring `A`): a scheme, pseudo-discretised, is a formal scheme. Every point lies in an
affine open `Spec R`; the discrete topological ring `R` is admissible, and `0` is an initial
object of its ordered family of ideals of definition, so the limit defining the structure sheaf
of `Spf R` is canonically its component at `0`. -/
@[ega "I 10.4.8"]
theorem isFormalScheme_schemeToLTRSObj (X : Scheme.{u}) :
    IsFormalScheme (schemeToLTRSObj X) := by
  intro point
  obtain ⟨U, R, ⟨affineIso⟩⟩ := X.local_affine point
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := discreteTopology_bot R
  refine ⟨U.1, U.2, TopCommRingCat.of R, inferInstance, isAdmissible_discrete R, ?_⟩
  refine ⟨?_ ≪≫ pseudoDiscreteSpaceIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso affineIso)
    ≪≫ discreteSpecSpfIsoOn R (isIdealOfDefinition_bot_discrete R)⟩
  exact PresheafedSpace.isoOfComponents (Iso.refl _)
    (pseudoDiscreteWhiskerIso U.1.inclusion' U.1.isOpenEmbedding' X.presheaf).symm

/-- Pseudo-discretisation respects identities: the underlying continuous map and comparison map
are unchanged, so this holds definitionally. -/
theorem schemeToLTRSHom_id (X : Scheme.{u}) :
    schemeToLTRSHom (𝟙 X) = 𝟙 (schemeToLTRSObj X).toPresheafedSpace := rfl

/-- Pseudo-discretisation respects composition, again definitionally. -/
theorem schemeToLTRSHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeToLTRSHom (f ≫ g) = schemeToLTRSHom f ≫ schemeToLTRSHom g := rfl

/-- The pseudo-discretisation functor `Schemes ⟶ LTRS`: a scheme `(X, 𝒪_X)` goes to
`(X, 𝒪'_X)` with `𝒪'_X` the pseudo-discrete sheaf of topological rings attached to `𝒪_X`, and a
morphism of schemes goes to the morphism of locally topologically ringed spaces with the same
continuous map and the same comparison map.

The functor of Stacks 0AI0 is this one followed by the inclusion of the formal schemes, and the
same functor lands in McQuillan's larger category of formal schemes. -/
@[ega "0 3.8.1" "special case"]
noncomputable def schemeToLTRS : Scheme.{u} ⥤ LTRS.{u} where
  obj X := schemeToLTRSObj X
  map f :=
    { toHom := schemeToLTRSHom f
      isLocalHom := isLocalHom_stalkMap_schemeToLTRSHom f }
  map_id X := LocallyTopologicallyRingedSpace.Hom.ext' (schemeToLTRSHom_id X)
  map_comp f g := LocallyTopologicallyRingedSpace.Hom.ext' (schemeToLTRSHom_comp f g)

/-- **Stacks 0AI0.** The functor `Schemes ⟶ Formal Schemes`: pseudo-discretisation, a scheme
being a formal scheme by `AlgebraicGeometry.isFormalScheme_schemeToLTRSObj`. -/
@[stacks 0AI0]
noncomputable def schemeToFormalScheme : Scheme.{u} ⥤ FormalScheme.{u} :=
  IsFormalScheme.lift schemeToLTRS isFormalScheme_schemeToLTRSObj

/-- The morphism of schemes underlying a morphism of the pseudo-discretised locally
topologically ringed spaces: the same continuous map, and the same comparison map with the
topologies forgotten, which is local on stalks because the stalks are unchanged. -/
noncomputable def schemeOfLTRSHom {X Y : Scheme.{u}}
    (g : schemeToLTRSObj X ⟶ schemeToLTRSObj Y) : X ⟶ Y where
  toLRSHom' :=
    { toHom := forgetPseudoDiscreteHom g.toHom
      prop := fun x => (isLocalHom_stalkMap_iff g.toHom x).1 (g.isLocalHom x) }

/-- Pseudo-discretising the morphism of schemes underlying a morphism of locally topologically
ringed spaces returns that morphism. -/
theorem schemeToLTRSHom_schemeOfLTRSHom {X Y : Scheme.{u}}
    (g : schemeToLTRSObj X ⟶ schemeToLTRSObj Y) :
    schemeToLTRSHom (schemeOfLTRSHom g) = g.toHom := rfl

/-- **Stacks 0AI0.** The functor from schemes to formal schemes is full: a morphism of the
pseudo-discretised spaces has an automatically continuous comparison map, so it is the image of
the morphism of schemes with the same data. -/
@[stacks 0AI0 "full faithfulness: fullness"]
instance full_schemeToFormalScheme : schemeToFormalScheme.{u}.Full where
  map_surjective {X Y} g :=
    ⟨schemeOfLTRSHom (X := X) (Y := Y) g.hom,
      InducedCategory.hom_ext (LocallyTopologicallyRingedSpace.Hom.ext'
        (schemeToLTRSHom_schemeOfLTRSHom (X := X) (Y := Y) g.hom))⟩

/-- **Stacks 0AI0.** The functor from schemes to formal schemes is faithful: a morphism of
schemes is recovered from its pseudo-discretisation by forgetting the topologies. -/
@[stacks 0AI0 "full faithfulness: faithfulness"]
instance faithful_schemeToFormalScheme : schemeToFormalScheme.{u}.Faithful where
  map_injective {X Y} f f' h := by
    have h1 : schemeToLTRSHom f = schemeToLTRSHom f' :=
      congrArg (fun k : schemeToFormalScheme.obj X ⟶ schemeToFormalScheme.obj Y =>
        k.hom.toHom) h
    refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' ?_)
    rw [← forgetPseudoDiscreteHom_schemeToLTRSHom f,
      ← forgetPseudoDiscreteHom_schemeToLTRSHom f', h1]

/-! ### The formal scheme attached to a scheme -/

/-- The formal scheme attached to a scheme is the scheme's own locally topologically ringed
space. -/
@[simp]
theorem schemeToFormalScheme_obj (X : Scheme.{u}) :
    (schemeToFormalScheme.obj X).obj = schemeToLTRSObj X := rfl

/-- The underlying space of the formal scheme attached to a scheme is the space of the
scheme. -/
@[simp]
theorem schemeToLTRSObj_carrier (X : Scheme.{u}) :
    (schemeToLTRSObj X).carrier = X.toPresheafedSpace.carrier := rfl

/-- The underlying sheaf of topological rings of the formal scheme attached to a scheme is the
pseudo-discretisation of `𝒪_X`; by `AlgebraicGeometry.pseudoDiscrete_obj_α` and
`AlgebraicGeometry.pseudoDiscrete_map_val` its underlying sheaf of rings is `𝒪_X` itself. -/
@[simp]
theorem schemeToLTRSObj_presheaf (X : Scheme.{u}) :
    (schemeToLTRSObj X).presheaf = pseudoDiscrete X.presheaf := rfl

/-- The continuous map underlying the image of a morphism of schemes is the morphism's own. -/
@[simp]
theorem schemeToFormalScheme_map_base {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (schemeToFormalScheme.map f).hom.toHom.base = f.base := rfl

/-- The comparison map underlying the image of a morphism of schemes is, forgetting the
topologies, the morphism's own. -/
@[simp]
theorem schemeToFormalScheme_map_c_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : (Opens Y.toPresheafedSpace.carrier)ᵒᵖ) :
    ((schemeToFormalScheme.map f).hom.toHom.c.app V).1 = (f.c.app V).hom := rfl

end AlgebraicGeometry
