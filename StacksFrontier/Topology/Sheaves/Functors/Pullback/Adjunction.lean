module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Topology.Sheaves.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008F — Pullback ⊣ pushforward on presheaves

Stacks 008F says that for a continuous map `f : X → Y` there is a functor
`f_p : PSh(Y) → PSh(X)` left adjoint to `f_*`, determined by
`f_p G(U) = colim_{f(U) ⊆ V} G(V)`, the colimit being over the open neighbourhoods `V` of
`f(U)` in `Y`, a directed partially ordered set.

Mathlib has the two functors and the adjunction: `TopCat.Presheaf.pushforward` is `f_*`,
`TopCat.Presheaf.pullback` is `f_p` (constructed as the left Kan extension along
`Opens.map f`), and `TopCat.Presheaf.pullbackPushforwardAdjunction` is the adjunction.
`TopCat.Presheaf.pullbackObjObjOfImageOpen` evaluates `f_p G` on an open whose image is open.

This file spells out the colimit formula over the poset of neighbourhoods itself:

* `Stacks.Topology.PresheafPullback.NhdsOfImage f U` is the poset of open neighbourhoods `V`
  of `f(U)` in `Y`; its opposite (reverse inclusion) is filtered, i.e. directed.
* `Stacks.Topology.PresheafPullback.pullbackObjObjIsoColimit` is the isomorphism
  `(f_p G)(U) ≅ colim_{f(U) ⊆ V} G(V)`; `ι_pullbackObjObjIsoColimit_inv` says that it sends
  the germ of `s ∈ G(V)` to the image of `s` under the unit `G(V) → (f_p G)(f⁻¹V)` followed by
  restriction to `U`, and `pullbackObjObjIsoColimit_map` says that the restriction maps of
  `f_p G` are the maps of colimits induced by the inclusions of index posets.
* `Stacks.Topology.PresheafPullback.pullback_presheaf_colimit` bundles these into Stacks 008F.

Everything is stated for presheaves with values in any category `C` with colimits; Stacks
states it for presheaves of sets, `C = Type v`.
-/

@[expose] public section

-- The former @[stacks 008F] definition was `pullbackPushforwardAdjunction`, and the two
-- functors it relates were abbreviations for Mathlib's.
add_to_stacks 008F "the pushforward `f_*` on presheaves" TopCat.Presheaf.pushforward
add_to_sga "4 IV 4.1.1" "(F)" TopCat.Presheaf.pushforward
add_to_ega "0 3.4.1" TopCat.Presheaf.pushforward
add_to_ega "0 3.4.2" TopCat.Presheaf.pushforward
add_to_stacks 008F "the pullback `f_p` on presheaves, the left Kan extension along `Opens.map f`"
  TopCat.Presheaf.pullback
add_to_stacks 008F "`f_p` is left adjoint to `f_*`"
  TopCat.Presheaf.pullbackPushforwardAdjunction
add_to_stacks 008F "the value of `f_p G` on an open with open image"
  TopCat.Presheaf.pullbackObjObjOfImageOpen

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology.PresheafPullback

universe v u

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The open neighbourhoods `V` of `f(U)` in `Y`, ordered by inclusion. -/
abbrev NhdsOfImage (U : Opens X) : Type v :=
  {V : Opens Y // f '' (U : Set X) ⊆ V}

/-- The inclusion of the open neighbourhoods of `f(U)` into the opens of `Y`. -/
abbrev nhdsOfImageIncl (U : Opens X) : NhdsOfImage f U ⥤ Opens Y :=
  (Subtype.mono_coe _).functor

/-- An open neighbourhood `V` of `f(U)` satisfies `U ⊆ f⁻¹V`. -/
lemma le_map_obj (U : Opens X) (V : NhdsOfImage f U) : U ≤ (Opens.map f).obj V.1 :=
  fun x hx ↦ V.2 ⟨x, hx, rfl⟩

/-- The open neighbourhoods of `f(U)` form a codirected poset: it contains `Y` and is closed
under intersections. -/
instance isCofiltered_nhdsOfImage (U : Opens X) : IsCofiltered (NhdsOfImage f U) where
  cone_objs V W := ⟨⟨V.1 ⊓ W.1, Set.subset_inter V.2 W.2⟩,
    homOfLE (show V.1 ⊓ W.1 ≤ V.1 from inf_le_left),
    homOfLE (show V.1 ⊓ W.1 ≤ W.1 from inf_le_right), trivial⟩
  cone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
  nonempty := ⟨⟨⊤, Set.subset_univ _⟩⟩

/-- The open neighbourhoods of `f(U)` ordered by reverse inclusion form a directed poset. -/
instance isFiltered_op_nhdsOfImage (U : Opens X) : IsFiltered (NhdsOfImage f U)ᵒᵖ :=
  isFiltered_op_of_isCofiltered _

/-- If `U₁ ⊆ U₂`, every open neighbourhood of `f(U₂)` is one of `f(U₁)`. -/
abbrev nhdsOfImageRestrict {U₁ U₂ : Opens X} (h : U₁ ≤ U₂) :
    NhdsOfImage f U₂ ⥤ NhdsOfImage f U₁ :=
  Monotone.functor (f := fun V ↦ ⟨V.1, (Set.image_mono h).trans V.2⟩) fun _ _ hVW ↦ hVW

/-- The neighbourhoods of `f(U)`, as the costructured arrows indexing the pointwise left Kan
extension along `(Opens.map f).op` at `U`. -/
@[simps]
def toCostructuredArrow (U : Opens X) :
    (NhdsOfImage f U)ᵒᵖ ⥤ CostructuredArrow (Opens.map f).op (op U) where
  obj V := CostructuredArrow.mk (Y := op V.unop.1) (homOfLE (le_map_obj f U V.unop)).op
  map {V W} g := CostructuredArrow.homMk (homOfLE (show W.unop.1 ≤ V.unop.1 from
    leOfHom g.unop)).op (Subsingleton.elim _ _)
  map_id _ := CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  map_comp _ _ := CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

instance (U : Opens X) : (toCostructuredArrow f U).IsEquivalence where
  faithful := ⟨fun _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  full := ⟨fun {V W} g ↦ ⟨(homOfLE (show W.unop.1 ≤ V.unop.1 from leOfHom g.left.unop)).op,
    CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))⟩⟩
  essSurj := ⟨fun A ↦ ⟨op ⟨A.left.unop, Set.image_subset_iff.mpr (leOfHom A.hom.unop)⟩,
    ⟨CostructuredArrow.isoMk (Iso.refl _) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))⟩⟩⟩

variable {C : Type u} [Category.{v} C]

/-- The diagram `V ↦ G(V)` over the open neighbourhoods of `f(U)`, ordered by reverse
inclusion. -/
abbrev nhdsOfImageDiagram (G : Y.Presheaf C) (U : Opens X) : (NhdsOfImage f U)ᵒᵖ ⥤ C :=
  (nhdsOfImageIncl f U).op ⋙ G

variable [HasColimits C]

/-- The sections of `f_p G` over `U` are the colimit of `G(V)` over the open neighbourhoods `V`
of `f(U)`. -/
noncomputable def pullbackObjObjIsoColimit (G : Y.Presheaf C) (U : Opens X) :
    ((Presheaf.pullback C f).obj G).obj (op U) ≅ colimit (nhdsOfImageDiagram f G U) :=
  (Opens.map f).op.leftKanExtensionObjIsoColimit G (op U) ≪≫
    (Functor.Final.colimitIso (toCostructuredArrow f U) (CostructuredArrow.proj _ _ ⋙ G)).symm

/-- The isomorphism `pullbackObjObjIsoColimit` sends the germ of a section `s ∈ G(V)` to the
image of `s` under the unit `G(V) → (f_p G)(f⁻¹V)` of `f_p ⊣ f_*`, restricted to `U`. -/
@[reassoc (attr := simp)]
theorem ι_pullbackObjObjIsoColimit_inv (G : Y.Presheaf C) (U : Opens X)
    (V : NhdsOfImage f U) :
    colimit.ι (nhdsOfImageDiagram f G U) (op V) ≫ (pullbackObjObjIsoColimit f G U).inv =
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (op V.1) ≫
        ((Presheaf.pullback C f).obj G).map (homOfLE (le_map_obj f U V)).op := by
  change colimit.ι (toCostructuredArrow f U ⋙ CostructuredArrow.proj _ _ ⋙ G) (op V) ≫
    (Functor.Final.colimitIso _ _).hom ≫
      ((Opens.map f).op.leftKanExtensionObjIsoColimit G _).inv = _
  rw [Functor.Final.ι_colimitIso_hom_assoc, Functor.ι_leftKanExtensionObjIsoColimit_inv]
  simp [Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit, Functor.lanUnit,
    Presheaf.pullback, Functor.lan]
  rfl

/-- The restriction maps of `f_p G` correspond, under `pullbackObjObjIsoColimit`, to the maps of
colimits induced by the inclusion of the neighbourhoods of `f(U₂)` among those of `f(U₁)`. -/
theorem pullbackObjObjIsoColimit_map (G : Y.Presheaf C) {U₁ U₂ : Opens X} (h : U₁ ≤ U₂) :
    (pullbackObjObjIsoColimit f G U₂).inv ≫ ((Presheaf.pullback C f).obj G).map (homOfLE h).op ≫
        (pullbackObjObjIsoColimit f G U₁).hom =
      colimit.pre (nhdsOfImageDiagram f G U₁) (nhdsOfImageRestrict f h).op := by
  refine colimit.hom_ext fun ⟨V⟩ ↦ ?_
  have hV : ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app
        (op ((nhdsOfImageRestrict f h).obj V).1) ≫
      ((Presheaf.pullback C f).obj G).map
        (homOfLE (le_map_obj f U₁ ((nhdsOfImageRestrict f h).obj V))).op ≫
        (pullbackObjObjIsoColimit f G U₁).hom =
      colimit.ι (nhdsOfImageDiagram f G U₁) (op ((nhdsOfImageRestrict f h).obj V)) := by
    have := (Iso.comp_inv_eq _).mp
      (ι_pullbackObjObjIsoColimit_inv f G U₁ ((nhdsOfImageRestrict f h).obj V))
    rw [Category.assoc] at this
    exact this.symm
  rw [ι_pullbackObjObjIsoColimit_inv_assoc, ← Functor.map_comp_assoc]
  exact hV.trans
    (colimit.ι_pre (nhdsOfImageDiagram f G U₁) (nhdsOfImageRestrict f h).op (op V)).symm

/-- **Stacks 008F.** Let `f : X → Y` be continuous. The pullback `f_p : PSh(Y) → PSh(X)` is left
adjoint to `f_*`; for a presheaf `G` on `Y` and an open `U ⊆ X` there is an isomorphism
`(f_p G)(U) ≅ colim_{f(U) ⊆ V} G(V)`, the colimit over the open neighbourhoods `V` of `f(U)`,
compatible with the canonical maps `G(V) → (f_p G)(U)` (the unit of the adjunction followed by
restriction) and with the restriction maps of `f_p G`; and these colimits are over directed
partially ordered sets. Stated for presheaves with values in any category with colimits, which
includes the presheaves of sets of Stacks. -/
@[stacks 008F "complete: the adjunction `f_p ⊣ f_*`, the section formula as a colimit over the
open neighbourhoods of `f(U)` compatible with the restriction maps, and directedness of the
index posets"]
theorem pullback_presheaf_colimit :
    Nonempty (Presheaf.pullback C f ⊣ Presheaf.pushforward C f) ∧
      (∀ U : Opens X, IsFiltered (NhdsOfImage f U)ᵒᵖ) ∧
      ∀ G : Y.Presheaf C, ∃ e : ∀ U : Opens X,
        ((Presheaf.pullback C f).obj G).obj (op U) ≅ colimit (nhdsOfImageDiagram f G U),
        (∀ (U : Opens X) (V : NhdsOfImage f U),
          colimit.ι (nhdsOfImageDiagram f G U) (op V) ≫ (e U).inv =
            ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (op V.1) ≫
              ((Presheaf.pullback C f).obj G).map (homOfLE (le_map_obj f U V)).op) ∧
        ∀ {U₁ U₂ : Opens X} (h : U₁ ≤ U₂),
          (e U₂).inv ≫ ((Presheaf.pullback C f).obj G).map (homOfLE h).op ≫ (e U₁).hom =
            colimit.pre (nhdsOfImageDiagram f G U₁) (nhdsOfImageRestrict f h).op :=
  ⟨⟨Presheaf.pullbackPushforwardAdjunction C f⟩, fun _ ↦ inferInstance,
    fun G ↦ ⟨pullbackObjObjIsoColimit f G, ι_pullbackObjObjIsoColimit_inv f G,
      fun h ↦ pullbackObjObjIsoColimit_map f G h⟩⟩

end Stacks.Topology.PresheafPullback
