module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import StacksFrontier.Topology.Algebra.RingColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discrete presheaves of topological rings

A presheaf of topological rings is *pseudo-discrete* when its ring of sections over every
quasi-compact open is discrete. Every presheaf of rings carries a canonical pseudo-discrete
topology — on the sections over `U`, the one induced from the product of the discrete
topologies on the sections over the quasi-compact opens contained in `U` — and the resulting
construction is functorial, leaves the underlying presheaf of rings and its stalks unchanged,
and is the one the Stacks project uses to regard a scheme as a formal scheme (Stacks 0AHY).

## Main definitions

* `AlgebraicGeometry.IsPseudoDiscrete`: the pseudo-discreteness condition on a presheaf of
  topological rings.
* `AlgebraicGeometry.pseudoDiscreteTopology`: the pseudo-discrete topology on the sections of a
  presheaf of rings over an open set.
* `AlgebraicGeometry.pseudoDiscrete` and `AlgebraicGeometry.pseudoDiscreteFunctor`: the
  pseudo-discrete presheaf of topological rings attached to a presheaf of rings, and its
  functoriality.
* `AlgebraicGeometry.pseudoDiscreteSpace`: a presheafed space of rings regarded as a presheafed
  space of topological rings.
* `AlgebraicGeometry.forgetPseudoDiscreteHom`: the morphism of presheafed spaces of rings
  underlying a morphism of pseudo-discretised presheafed spaces.

## Main results

* `AlgebraicGeometry.pseudoDiscreteTopology_eq_bot` and
  `AlgebraicGeometry.isPseudoDiscrete_pseudoDiscrete`: the construction is pseudo-discrete.
* `AlgebraicGeometry.pseudoDiscreteStalkIso` and
  `AlgebraicGeometry.isLocalRing_stalk_pseudoDiscrete`: its stalks, after forgetting the
  topologies, are those of the original presheaf of rings.
* `AlgebraicGeometry.stalkMap_forgetPseudoDiscreteHom` and
  `AlgebraicGeometry.isLocalHom_stalkMap_iff`: under those identifications the stalk map of a
  morphism of pseudo-discretised presheafed spaces is the stalk map of the underlying morphism
  of presheafed spaces of rings, so one is a local homomorphism exactly when the other is.

## Implementation notes

The pseudo-discrete topology is written as an infimum of topologies induced along restriction
to the quasi-compact opens contained in `U`, which is exactly the topology induced from the
product of the discrete topologies that the source prescribes.

Stalks of presheaves of topological rings are colimits in `TopCommRingCat`, supplied by
`TopCommRingCat.hasColimits` of Stacks 0B24; since the forgetful functor to `CommRingCat`
preserves them, the stalks may equivalently be computed after forgetting the topology, which is
`AlgebraicGeometry.pseudoDiscreteStalkIso`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

/-- Pulling back a ring topology along a ring homomorphism gives a ring topology. -/
theorem IsTopologicalRing.induced {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] (f : R →+* S) :
    @IsTopologicalRing R (TopologicalSpace.induced f inferInstance) _ :=
  let : TopologicalSpace R := TopologicalSpace.induced f inferInstance
  { toContinuousAdd := continuousAdd_induced f
    toContinuousMul := continuousMul_induced f
    toContinuousNeg := ⟨continuous_induced_rng.2 <| by
      rw [show ⇑f ∘ (Neg.neg : R → R) = (Neg.neg : S → S) ∘ ⇑f from funext (map_neg f)]
      exact continuous_neg.comp continuous_induced_dom⟩ }

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-! ### The pseudo-discrete topology -/

/-- A presheaf of topological rings is *pseudo-discrete* when the topology on its ring of
sections over `U` is discrete for every quasi-compact open `U`. -/
def IsPseudoDiscrete (F : X.Presheaf TopCommRingCat.{u}) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) → DiscreteTopology (F.obj (op U)).α

/-- The quasi-compact opens contained in `U`: the index set over which the pseudo-discrete
topology on the sections over `U` is taken. -/
abbrev CompactOpenLE (U : Opens X) : Type u := {V : Opens X // IsCompact (V : Set X) ∧ V ≤ U}

/-- The discrete topology on the sections over a quasi-compact open `V ≤ U`, pulled back to the
sections over `U` along restriction. -/
@[instance_reducible]
def pseudoDiscreteFamily (F : X.Presheaf CommRingCat.{u}) {U : Opens X} (V : CompactOpenLE U) :
    TopologicalSpace (F.obj (op U)) :=
  TopologicalSpace.induced (F.map (homOfLE V.2.2).op).hom ⊥

/-- The *pseudo-discrete topology* on the sections of a presheaf of rings over an open `U`: the
topology induced from the product of the discrete topologies on the sections over the
quasi-compact opens contained in `U`. A topology induced from a product is the infimum of the
topologies induced from its factors, which is how it is written here. -/
@[instance_reducible, ega "0 3.8.1"]
def pseudoDiscreteTopology (F : X.Presheaf CommRingCat.{u}) (U : Opens X) :
    TopologicalSpace (F.obj (op U)) :=
  ⨅ V : CompactOpenLE U, pseudoDiscreteFamily F V

/-- The topology pulled back from the discrete sections over a quasi-compact open is a ring
topology. -/
instance isTopologicalRing_pseudoDiscreteFamily (F : X.Presheaf CommRingCat.{u}) {U : Opens X}
    (V : CompactOpenLE U) :
    @IsTopologicalRing (F.obj (op U)) (pseudoDiscreteFamily F V) _ := by
  let _ : TopologicalSpace (F.obj (op V.1)) := ⊥
  have : DiscreteTopology (F.obj (op V.1)) := discreteTopology_bot _
  exact IsTopologicalRing.induced _

/-- The pseudo-discrete topology is a ring topology, being an infimum of ring topologies. -/
instance isTopologicalRing_pseudoDiscreteTopology (F : X.Presheaf CommRingCat.{u})
    (U : Opens X) : @IsTopologicalRing (F.obj (op U)) (pseudoDiscreteTopology F U) _ :=
  let _ : TopologicalSpace (F.obj (op U)) := pseudoDiscreteTopology F U
  { toContinuousAdd :=
      continuousAdd_iInf fun V => (isTopologicalRing_pseudoDiscreteFamily F V).toContinuousAdd
    toContinuousMul :=
      continuousMul_iInf fun V => (isTopologicalRing_pseudoDiscreteFamily F V).toContinuousMul
    toContinuousNeg :=
      continuousNeg_iInf fun V => (isTopologicalRing_pseudoDiscreteFamily F V).toContinuousNeg }

/-- Restriction to a quasi-compact open is continuous for the pseudo-discrete topology on the
source and the discrete topology on the target. -/
theorem continuous_pseudoDiscreteTopology_restrict (F : X.Presheaf CommRingCat.{u})
    {U V : Opens X} (hV : IsCompact (V : Set X)) (hVU : V ≤ U) :
    Continuous[pseudoDiscreteTopology F U, ⊥] (F.map (homOfLE hVU).op).hom :=
  continuous_iff_le_induced.2 (iInf_le (pseudoDiscreteFamily F) ⟨V, hV, hVU⟩)

/-- Any function out of the sections over a quasi-compact open `V ≤ U`, precomposed with
restriction, is continuous for the pseudo-discrete topology on the sections over `U` and the
discrete topology on the target. -/
private theorem continuous_pseudoDiscreteTopology_comp_restrict (F : X.Presheaf CommRingCat.{u})
    {U V : Opens X} (hV : IsCompact (V : Set X)) (hVU : V ≤ U) {β : Type u}
    (g : F.obj (op V) → β) :
    Continuous[pseudoDiscreteTopology F U, ⊥] (g ∘ (F.map (homOfLE hVU).op).hom) := by
  exact @Continuous.comp _ _ _ (pseudoDiscreteTopology F U) ⊥ ⊥ _ _
    (@continuous_of_discreteTopology _ ⊥ (discreteTopology_bot _) _ ⊥ g)
    (continuous_pseudoDiscreteTopology_restrict F hV hVU)

/-- The pseudo-discrete topology on the sections over a quasi-compact open is discrete: the open
itself occurs in the index set, and restriction along it is the identity. -/
theorem pseudoDiscreteTopology_eq_bot (F : X.Presheaf CommRingCat.{u}) {U : Opens X}
    (hU : IsCompact (U : Set X)) : pseudoDiscreteTopology F U = ⊥ := by
  have hid : ⇑(F.map (homOfLE (le_refl U)).op).hom = id := by
    rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl, F.map_id]
    rfl
  refine le_antisymm ((iInf_le (pseudoDiscreteFamily F)
    (⟨U, hU, le_rfl⟩ : CompactOpenLE U)).trans_eq ?_) bot_le
  rw [pseudoDiscreteFamily, hid]
  exact @induced_id _ ⊥

/-- Restriction between arbitrary opens is continuous for the pseudo-discrete topologies. -/
theorem continuous_pseudoDiscreteTopology_map (F : X.Presheaf CommRingCat.{u}) {U V : Opens X}
    (h : V ≤ U) :
    Continuous[pseudoDiscreteTopology F U, pseudoDiscreteTopology F V]
      (F.map (homOfLE h).op).hom := by
  refine continuous_iInf_rng.2 fun W => ?_
  rw [pseudoDiscreteFamily, continuous_induced_rng]
  have hfun : ⇑(F.map (homOfLE W.2.2).op).hom ∘ ⇑(F.map (homOfLE h).op).hom
      = ⇑(F.map (homOfLE (W.2.2.trans h)).op).hom := by
    ext s
    exact congrArg (fun g : F.obj (op U) ⟶ F.obj (op W.1) => g.hom s) (F.map_comp _ _).symm
  rw [hfun]
  exact continuous_pseudoDiscreteTopology_restrict F W.2.1 (W.2.2.trans h)

/-! ### The pseudo-discrete presheaf of topological rings -/

/-- The ring of sections of a presheaf of rings over `U`, as a topological ring with the
pseudo-discrete topology. -/
def pseudoDiscreteObj (F : X.Presheaf CommRingCat.{u}) (U : Opens X) : TopCommRingCat.{u} :=
  @TopCommRingCat.of (F.obj (op U)) _ (pseudoDiscreteTopology F U)
    (isTopologicalRing_pseudoDiscreteTopology F U)

/-- The *pseudo-discrete presheaf of topological rings* associated to a presheaf of rings: the
same rings of sections and the same restriction maps, with the pseudo-discrete topology on each
ring of sections. -/
@[ega "0 3.8.1"]
def pseudoDiscrete (F : X.Presheaf CommRingCat.{u}) : X.Presheaf TopCommRingCat.{u} where
  obj U := pseudoDiscreteObj F U.unop
  map i := ⟨(F.map i).hom, continuous_pseudoDiscreteTopology_map F (leOfHom i.unop)⟩
  map_id U := Subtype.ext (congrArg CommRingCat.Hom.hom (F.map_id U))
  map_comp f g := Subtype.ext (congrArg CommRingCat.Hom.hom (F.map_comp f g))

/-- The sections of the pseudo-discretisation of `F` are the sections of `F`. -/
@[simp]
theorem pseudoDiscrete_obj_α (F : X.Presheaf CommRingCat.{u}) (U : (Opens X)ᵒᵖ) :
    ((pseudoDiscrete F).obj U).α = F.obj U := rfl

/-- The restriction maps of the pseudo-discretisation of `F` are those of `F`. -/
@[simp]
theorem pseudoDiscrete_map_val (F : X.Presheaf CommRingCat.{u}) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((pseudoDiscrete F).map i).1 = (F.map i).hom := rfl

/-- The pseudo-discrete presheaf of topological rings attached to a presheaf of rings is indeed
pseudo-discrete. -/
theorem isPseudoDiscrete_pseudoDiscrete (F : X.Presheaf CommRingCat.{u}) :
    IsPseudoDiscrete (pseudoDiscrete F) :=
  fun _ hU => ⟨pseudoDiscreteTopology_eq_bot F hU⟩

/-- A morphism of presheaves of rings is automatically continuous for the pseudo-discrete
topologies, because restriction to a quasi-compact open lands in a discrete ring of sections. -/
theorem continuous_pseudoDiscreteTopology_app {F G : X.Presheaf CommRingCat.{u}} (η : F ⟶ G)
    (U : Opens X) :
    Continuous[pseudoDiscreteTopology F U, pseudoDiscreteTopology G U] (η.app (op U)).hom := by
  refine continuous_iInf_rng.2 fun V => continuous_induced_rng.2 ?_
  have hfun : ⇑(G.map (homOfLE V.2.2).op).hom ∘ ⇑(η.app (op U)).hom
      = ⇑(η.app (op V.1)).hom ∘ ⇑(F.map (homOfLE V.2.2).op).hom := by
    ext s
    exact congrArg (fun g : F.obj (op U) ⟶ G.obj (op V.1) => g.hom s)
      (η.naturality (homOfLE V.2.2).op).symm
  rw [hfun]
  exact continuous_pseudoDiscreteTopology_comp_restrict F V.2.1 V.2.2 _

/-- Pseudo-discretisation as a functor from presheaves of rings to presheaves of topological
rings. -/
def pseudoDiscreteFunctor : X.Presheaf CommRingCat.{u} ⥤ X.Presheaf TopCommRingCat.{u} where
  obj F := pseudoDiscrete F
  map η :=
    { app := fun U => ⟨(η.app U).hom, continuous_pseudoDiscreteTopology_app η U.unop⟩
      naturality := fun _ _ i => Subtype.ext (congrArg CommRingCat.Hom.hom (η.naturality i)) }
  map_id _ := NatTrans.ext (funext fun _ => Subtype.ext rfl)
  map_comp _ _ := NatTrans.ext (funext fun _ => Subtype.ext rfl)

/-! ### Stalks -/

/-- Forgetting the topologies, the stalks of the pseudo-discrete presheaf of topological rings
attached to `F` are the stalks of `F`. This is Stacks 0B24: colimits of topological rings are
computed on the underlying rings, so the forgetful functor to rings preserves the colimit
defining a stalk. -/
noncomputable def pseudoDiscreteStalkIso (F : X.Presheaf CommRingCat.{u}) (x : X) :
    (forget₂ TopCommRingCat CommRingCat).obj ((pseudoDiscrete F).stalk x) ≅ F.stalk x :=
  preservesColimitIso (forget₂ TopCommRingCat.{u} CommRingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ pseudoDiscrete F)

/-- The germ of the pseudo-discretisation at `x`, followed by the identification of its stalk
with the stalk of `F`, is the germ of `F`. -/
theorem germ_pseudoDiscreteStalkIso_hom (F : X.Presheaf CommRingCat.{u}) (x : X) (V : Opens X)
    (hx : x ∈ V) :
    (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map ((pseudoDiscrete F).germ V x hx) ≫
      (pseudoDiscreteStalkIso F x).hom = F.germ V x hx :=
  ι_preservesColimitIso_hom (forget₂ TopCommRingCat.{u} CommRingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ pseudoDiscrete F) (op (⟨V, hx⟩ : OpenNhds x))

/-- The germ of `F` at `x`, followed by the inverse identification of stalks, is the germ of the
pseudo-discretisation. -/
theorem germ_pseudoDiscreteStalkIso_inv (F : X.Presheaf CommRingCat.{u}) (x : X) (V : Opens X)
    (hx : x ∈ V) :
    F.germ V x hx ≫ (pseudoDiscreteStalkIso F x).inv =
      (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map ((pseudoDiscrete F).germ V x hx) :=
  ι_preservesColimitIso_inv (forget₂ TopCommRingCat.{u} CommRingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ pseudoDiscrete F) (op (⟨V, hx⟩ : OpenNhds x))

/-- If the stalks of `F` are local rings, so are those of its pseudo-discretisation, once the
topologies are forgotten. -/
theorem isLocalRing_stalk_pseudoDiscrete (F : X.Presheaf CommRingCat.{u}) (x : X)
    [IsLocalRing (F.stalk x)] : IsLocalRing (((pseudoDiscrete F).stalk x).α) :=
  RingEquiv.isLocalRing (pseudoDiscreteStalkIso F x).commRingCatIsoToRingEquiv.symm

/-! ### Pseudo-discretisation of presheafed spaces -/

/-- A presheafed space of rings regarded as a presheafed space of topological rings, by giving
each ring of sections its pseudo-discrete topology. -/
@[reducible, ega "0 3.8.1"]
def pseudoDiscreteSpace (Y : PresheafedSpace CommRingCat.{u}) :
    PresheafedSpace TopCommRingCat.{u} where
  carrier := Y.carrier
  presheaf := pseudoDiscrete Y.presheaf

/-- The morphism of presheafed spaces of rings underlying a morphism of pseudo-discretised
presheafed spaces: the same continuous map, and the same comparison map with the topologies
forgotten. -/
def forgetPseudoDiscreteHom {Y Z : PresheafedSpace CommRingCat.{u}}
    (g : pseudoDiscreteSpace Y ⟶ pseudoDiscreteSpace Z) : Y ⟶ Z where
  base := g.base
  c :=
    { app := fun V => CommRingCat.ofHom (g.c.app V).1
      naturality := fun _ _ i => congrArg (fun k => CommRingCat.ofHom (Subtype.val k))
        (g.c.naturality i) }

/-- Under the identification of the stalks of a pseudo-discretisation with the stalks of the
original presheaf of rings, the stalk map of a morphism of pseudo-discretised presheafed spaces
is the stalk map of the underlying morphism of presheafed spaces of rings. -/
theorem stalkMap_forgetPseudoDiscreteHom {Y Z : PresheafedSpace CommRingCat.{u}}
    (g : pseudoDiscreteSpace Y ⟶ pseudoDiscreteSpace Z) (y : Y) :
    (pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv ≫
        (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
          (pseudoDiscreteStalkIso Y.presheaf y).hom =
      (forgetPseudoDiscreteHom g).stalkMap y := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hy => ?_
  have hmap := (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map_comp
    ((pseudoDiscrete Z.presheaf).germ V (g.base y) hy) (g.stalkMap y)
  have hsplit := (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map_comp (g.c.app (op V))
    ((pseudoDiscrete Y.presheaf).germ ((Opens.map g.base).obj V) y hy)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
        (pseudoDiscreteStalkIso Y.presheaf y).hom))
      (germ_pseudoDiscreteStalkIso_inv Z.presheaf (g.base y) V hy)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (pseudoDiscreteStalkIso Y.presheaf y).hom)
            (hmap.symm.trans ((congrArg (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map
              (PresheafedSpace.stalkMap_germ g V y hy)).trans hsplit))).trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.c.app (op V)) ≫ ·)
                (germ_pseudoDiscreteStalkIso_hom Y.presheaf y
                  ((Opens.map g.base).obj V) hy)).trans
              (PresheafedSpace.stalkMap_germ (forgetPseudoDiscreteHom g) V y hy).symm)))))

/-- The stalk map of a morphism of pseudo-discretised presheafed spaces is a local homomorphism
exactly when the stalk map of the underlying morphism of presheafed spaces of rings is. -/
theorem isLocalHom_stalkMap_iff {Y Z : PresheafedSpace CommRingCat.{u}}
    (g : pseudoDiscreteSpace Y ⟶ pseudoDiscreteSpace Z) (y : Y) :
    IsLocalHom (g.stalkMap y).1 ↔ IsLocalHom ((forgetPseudoDiscreteHom g).stalkMap y).hom := by
  have hsi : IsLocalHom (pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv.hom :=
    isLocalHom_of_iso (pseudoDiscreteStalkIso Z.presheaf (g.base y)).symm
  have hs : IsLocalHom (pseudoDiscreteStalkIso Z.presheaf (g.base y)).hom.hom :=
    isLocalHom_of_iso _
  have hti : IsLocalHom (pseudoDiscreteStalkIso Y.presheaf y).inv.hom :=
    isLocalHom_of_iso (pseudoDiscreteStalkIso Y.presheaf y).symm
  have ht : IsLocalHom (pseudoDiscreteStalkIso Y.presheaf y).hom.hom := isLocalHom_of_iso _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : IsLocalHom ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map
        (g.stalkMap y)).hom := h
    rw [← stalkMap_forgetPseudoDiscreteHom]
    exact @CommRingCat.isLocalHom_comp _ _ _
      (pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv
      ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
        (pseudoDiscreteStalkIso Y.presheaf y).hom)
      (@CommRingCat.isLocalHom_comp _ _ _
        ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y))
        (pseudoDiscreteStalkIso Y.presheaf y).hom ht h1) hsi
  · rw [← stalkMap_forgetPseudoDiscreteHom] at h
    have hcancel : (pseudoDiscreteStalkIso Z.presheaf (g.base y)).hom ≫
        ((pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv ≫
          (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
            (pseudoDiscreteStalkIso Y.presheaf y).hom) ≫
              (pseudoDiscreteStalkIso Y.presheaf y).inv =
        (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) := by
      simp
    change IsLocalHom ((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y)).hom
    rw [← hcancel]
    exact @CommRingCat.isLocalHom_comp _ _ _
      (pseudoDiscreteStalkIso Z.presheaf (g.base y)).hom
      (((pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv ≫
        (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
          (pseudoDiscreteStalkIso Y.presheaf y).hom) ≫
            (pseudoDiscreteStalkIso Y.presheaf y).inv)
      (@CommRingCat.isLocalHom_comp _ _ _
        ((pseudoDiscreteStalkIso Z.presheaf (g.base y)).inv ≫
          (forget₂ TopCommRingCat.{u} CommRingCat.{u}).map (g.stalkMap y) ≫
            (pseudoDiscreteStalkIso Y.presheaf y).hom)
        (pseudoDiscreteStalkIso Y.presheaf y).inv hti h) hs

/-- Pseudo-discretisation commutes with restriction along an open embedding: the sections of a
presheaf of rings over an open subspace, pseudo-discretised there, carry the same topology as
the pseudo-discretisation of the whole presheaf restricted to that subspace. -/
noncomputable def pseudoDiscreteWhiskerIso {S T : TopCat.{u}} (e : S ⟶ T)
    (h : Topology.IsOpenEmbedding e) (F : T.Presheaf CommRingCat.{u}) :
    pseudoDiscrete (h.functor.op ⋙ F) ≅ h.functor.op ⋙ pseudoDiscrete F := by
  have forward (U : Opens S) :
      Continuous[pseudoDiscreteTopology (h.functor.op ⋙ F) U,
        pseudoDiscreteTopology F (h.functor.obj U)] (fun sectionValue => sectionValue) := by
    refine continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 ?_
    have hcontained : (compactOpen.1 : Set T) ⊆ Set.range e :=
      fun _ hp => Set.image_subset_range _ _ (compactOpen.2.2 hp)
    have hcompact : IsCompact (((Opens.map e).obj compactOpen.1 : Opens S) : Set S) :=
      h.isInducing.isCompact_preimage' compactOpen.2.1 hcontained
    have hle : (Opens.map e).obj compactOpen.1 ≤ U := by
      intro point hpoint
      obtain ⟨source, hsource, heq⟩ := compactOpen.2.2 hpoint
      exact h.injective heq ▸ hsource
    have heq : h.functor.obj ((Opens.map e).obj compactOpen.1) = compactOpen.1 :=
      Opens.ext (Set.image_preimage_eq_of_subset hcontained)
    have restrictionEquality :
        (F.map (homOfLE compactOpen.2.2).op).hom =
          (F.map (eqToHom heq.symm).op).hom.comp
            ((h.functor.op ⋙ F).map (homOfLE hle).op).hom := by
      rw [← CommRingCat.hom_comp]
      change (F.map _).hom = (F.map _ ≫ F.map _).hom
      rw [← F.map_comp]
      congr 2
    change Continuous[pseudoDiscreteTopology (h.functor.op ⋙ F) U, ⊥]
      (F.map (homOfLE compactOpen.2.2).op).hom
    rw [restrictionEquality]
    let _ : TopologicalSpace ((h.functor.op ⋙ F).obj (op U)) :=
      pseudoDiscreteTopology (h.functor.op ⋙ F) U
    let _ : TopologicalSpace (F.obj (op (h.functor.obj ((Opens.map e).obj compactOpen.1)))) := ⊥
    let _ : TopologicalSpace (F.obj (op compactOpen.1)) := ⊥
    exact (@continuous_of_discreteTopology _ ⊥ (discreteTopology_bot _) _ ⊥
      (F.map (eqToHom heq.symm).op).hom).comp
      (continuous_pseudoDiscreteTopology_restrict (h.functor.op ⋙ F) hcompact hle)
  have backward (U : Opens S) :
      Continuous[pseudoDiscreteTopology F (h.functor.obj U),
        pseudoDiscreteTopology (h.functor.op ⋙ F) U] (fun sectionValue => sectionValue) :=
    continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 <|
      continuous_pseudoDiscreteTopology_restrict F
        (compactOpen.2.1.image h.continuous) (leOfHom (h.functor.map (homOfLE compactOpen.2.2)))
  exact NatIso.ofComponents (fun U =>
    { hom := ⟨RingHom.id _, forward U.unop⟩
      inv := ⟨RingHom.id _, backward U.unop⟩
      hom_inv_id := Subtype.ext rfl
      inv_hom_id := Subtype.ext rfl }) fun _ => Subtype.ext rfl

/-- The comparison map of a morphism of presheafed spaces of rings whose underlying map is an
open embedding is continuous for the pseudo-discrete topologies: a quasi-compact open of the
source has quasi-compact image, through whose discrete ring of sections the map factors. -/
theorem continuous_pseudoDiscrete_embedding {Y Z : PresheafedSpace CommRingCat.{u}} (f : Y ⟶ Z)
    (hf : Topology.IsOpenEmbedding f.base) (V : Opens Z) :
    Continuous[pseudoDiscreteTopology Z.presheaf V,
      pseudoDiscreteTopology Y.presheaf ((Opens.map f.base).obj V)]
      (f.c.app (op V)).hom := by
  refine continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 ?_
  have hcompact : IsCompact ((hf.functor.obj compactOpen.1 : Opens Z) : Set Z) :=
    compactOpen.2.1.image hf.continuous
  have hle : hf.functor.obj compactOpen.1 ≤ V := by
    rintro _ ⟨point, hpoint, rfl⟩
    exact compactOpen.2.2 hpoint
  have hpreimage : (Opens.map f.base).obj (hf.functor.obj compactOpen.1) = compactOpen.1 :=
    Opens.ext (Set.preimage_image_eq _ hf.injective)
  have heq : (Y.presheaf.map (homOfLE compactOpen.2.2).op).hom.comp
      (f.c.app (op V)).hom =
      (Y.presheaf.map (eqToHom hpreimage.symm).op).hom.comp
        ((f.c.app (op (hf.functor.obj compactOpen.1))).hom.comp
          (Z.presheaf.map (homOfLE hle).op).hom) := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      f.c.naturality, Category.assoc]
    change (f.c.app (op V) ≫ Y.presheaf.map _).hom =
      (f.c.app (op V) ≫ Y.presheaf.map _ ≫ Y.presheaf.map _).hom
    rw [← Y.presheaf.map_comp]
    congr 2
  change Continuous[pseudoDiscreteTopology Z.presheaf V, ⊥]
    ((Y.presheaf.map (homOfLE compactOpen.2.2).op).hom.comp (f.c.app (op V)).hom)
  rw [heq]
  exact continuous_pseudoDiscreteTopology_comp_restrict Z.presheaf hcompact hle
    ((Y.presheaf.map (eqToHom hpreimage.symm).op).hom.comp
      (f.c.app (op (hf.functor.obj compactOpen.1))).hom)

/-- Pseudo-discretisation carries an isomorphism of presheafed spaces of rings to an isomorphism
of presheafed spaces of topological rings. -/
noncomputable def pseudoDiscreteSpaceIso {Y Z : PresheafedSpace CommRingCat.{u}} (e : Y ≅ Z) :
    pseudoDiscreteSpace Y ≅ pseudoDiscreteSpace Z where
  hom :=
    { base := e.hom.base
      c :=
        { app V := ⟨(e.hom.c.app V).hom,
            continuous_pseudoDiscrete_embedding e.hom
              (TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e)).isOpenEmbedding V.unop⟩
          naturality _ _ inclusion := Subtype.ext
            (congrArg CommRingCat.Hom.hom (e.hom.c.naturality inclusion)) } }
  inv :=
    { base := e.inv.base
      c :=
        { app V := ⟨(e.inv.c.app V).hom,
            continuous_pseudoDiscrete_embedding e.inv
              (TopCat.homeoOfIso
                ((PresheafedSpace.forget _).mapIso e.symm)).isOpenEmbedding V.unop⟩
          naturality _ _ inclusion := Subtype.ext
            (congrArg CommRingCat.Hom.hom (e.inv.c.naturality inclusion)) } }
  hom_inv_id := by
    refine PresheafedSpace.ext _ _
      (congrArg (fun morphism : Y ⟶ Y => morphism.base) e.hom_inv_id) ?_
    refine NatTrans.ext (funext fun V => Subtype.ext ?_)
    dsimp [PresheafedSpace.comp, PresheafedSpace.id, pseudoDiscrete, pseudoDiscreteObj]
    dsimp only [CategoryStruct.comp]
    convert (congrArg CommRingCat.Hom.hom
      (PresheafedSpace.congr_app e.hom_inv_id.symm V)).symm using 1
    apply Iff.of_eq
    congr 4
    exact Subsingleton.elim _ _
  inv_hom_id := by
    refine PresheafedSpace.ext _ _
      (congrArg (fun morphism : Z ⟶ Z => morphism.base) e.inv_hom_id) ?_
    refine NatTrans.ext (funext fun V => Subtype.ext ?_)
    dsimp [PresheafedSpace.comp, PresheafedSpace.id, pseudoDiscrete, pseudoDiscreteObj]
    dsimp only [CategoryStruct.comp]
    convert (congrArg CommRingCat.Hom.hom
      (PresheafedSpace.congr_app e.inv_hom_id.symm V)).symm using 1
    apply Iff.of_eq
    congr 4
    exact Subsingleton.elim _ _

end AlgebraicGeometry
