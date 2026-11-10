module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of set-valued sheaves on a space, in a large value universe

For a continuous map `f : X ⟶ Y` of topological spaces in universe `u`, and sheaves of sets
with values in `Type (max u v)`, this file provides the inverse-image functor `f⁻¹`, its
adjunction with the direct image, and the canonical comparison of `(f ≫ g)⁻¹` with
`g⁻¹ ⋙ f⁻¹`.  It also provides the section-level description of a morphism out of an inverse
image: such a morphism is the same thing as a compatible family of maps
`F(V) → G(U)`, one for every pair of opens with `U ⊆ f⁻¹V`.

## Main definitions

* `TopCat.Sheaf.directImage` and `TopCat.Sheaf.inverseImage` — the two functors.
* `TopCat.Sheaf.inverseImagePushforwardAdjunction` — the adjunction `f⁻¹ ⊣ f_*`.
* `TopCat.Sheaf.inverseImageCompIso` — the canonical comparison for a composition.
* `TopCat.Sheaf.InverseImageSectionFamily` — the componentwise form of a map out of `f⁻¹F`,
  and `TopCat.Sheaf.inverseImageSectionFamilyHom` its transpose.

## Main results

* `TopCat.Sheaf.inverseImageSectionFamily_ext` — a map out of an inverse image is determined
  by its section maps.
* `TopCat.Sheaf.inverseImage_hom_comp` and `TopCat.Sheaf.inverseImage_adjoint_comp` — the
  cocycle identity for maps out of inverse images, in its two transposed forms.
* `TopCat.Sheaf.isIso_inverseImageSectionFamilyHom` — along an open embedding, a family whose
  section maps over an open and its image are bijective transposes to an isomorphism.

## Implementation notes

Spaces live in universe `u` and sheaves take values in `Type (max u v)` for an independent
`v`, so that every value universe at least as large as the universe of the spaces is covered,
including `Type (u + 1)`, which is the one the big-site morphisms of topoi use.
Mathlib's `TopCat.Sheaf.pullback` cannot serve here: it ties the value universe to the
universe of the space.  Sheaf categories are written out as
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) _` rather than as `TopCat.Sheaf _ X`
because the latter is a semireducible definition, which puts every rewrite in the section-
level proofs below out of reach of the elaborator's reducible transparency.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u v

/-- A morphism of sheaves on a space which is an isomorphism is an isomorphism on sections
over every open subset. -/
public theorem CategoryTheory.Sheaf.isIso_hom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] {F G : Sheaf J A}
    (α : F ⟶ G) [IsIso α] (U : Cᵒᵖ) :
    IsIso (α.hom.app U) :=
  ⟨(inv α).hom.app U,
    congrArg (fun m : F ⟶ F => m.hom.app U) (IsIso.hom_inv_id α),
    congrArg (fun m : G ⟶ G => m.hom.app U) (IsIso.inv_hom_id α)⟩

/-- Direct image of set-valued sheaves on topological spaces, for a value universe at least
as large as the universe of the spaces.  This is `TopCat.Sheaf.pushforward` written at the
unfolded type `CategoryTheory.Sheaf (Opens.grothendieckTopology X) _`, which is the form in
which the
small-site comparison of Tag 020X produces its sheaves. -/
@[sga "4 III 1.9.1", sga "4 IV 4.1.1"]
public abbrev TopCat.Sheaf.directImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)) :=
  (Opens.map f).sheafPushforwardContinuous (Type (max u v))
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Inverse image for set-valued sheaves in any universe at least as large as
that of the spaces, using the sites of open subsets. -/
public noncomputable def TopCat.Sheaf.inverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)) :=
  (Opens.map f).sheafPullback (Type (max u v))
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The inverse image is left adjoint to the usual direct image. -/
public noncomputable def TopCat.Sheaf.inverseImagePushforwardAdjunction
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf.inverseImage.{u, v} f ⊣ TopCat.Sheaf.directImage.{u, v} f :=
  (Opens.map f).sheafAdjunctionContinuous (Type (max u v))
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The composite of the two inverse images is also left adjoint to the direct image along
the composition.  The right adjoint is transported along `sheafPushforwardCompIso`, which is
the identity, so that the two adjunctions are stated for literally the same right adjoint. -/
public noncomputable def TopCat.Sheaf.inverseImageCompAdjunction
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.inverseImage.{u, v} g ⋙ TopCat.Sheaf.inverseImage.{u, v} f ⊣
      TopCat.Sheaf.directImage.{u, v} (f ≫ g) :=
  ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} g).comp
    (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f)).ofNatIsoRight
      (sheafPushforwardCompIso f g (Type (max u v))).symm

/-- The canonical composition comparison, obtained from uniqueness of left
adjoints to the direct-image functor along the composition. -/
public noncomputable def TopCat.Sheaf.inverseImageCompIso
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.inverseImage.{u, v} (f ≫ g) ≅
      TopCat.Sheaf.inverseImage.{u, v} g ⋙ TopCat.Sheaf.inverseImage.{u, v} f :=
  (TopCat.Sheaf.inverseImagePushforwardAdjunction (f ≫ g)).leftAdjointUniq
    (TopCat.Sheaf.inverseImageCompAdjunction.{u, v} f g)

/-- The componentwise form of a map out of inverse image.  It records the section maps on all
opens whose images lie in a chosen open of the target. -/
public structure TopCat.Sheaf.InverseImageSectionFamily {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v))) where
  app (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V) :
    F.obj.obj (op V) → G.obj.obj (op U)
  naturality {U U' : Opens X} {V V' : Opens Y}
      (hU : U' ⟶ U) (hV : V' ⟶ V)
      (hUV : U ≤ (Opens.map f).obj V)
      (hUV' : U' ≤ (Opens.map f).obj V') (s : F.obj.obj (op V)) :
    app U' V' hUV' (F.obj.map hV.op s) = G.obj.map hU.op (app U V hUV s)

/-- A morphism `f⁻¹ F ⟶ G` induces the usual compatible section maps. -/
public noncomputable def TopCat.Sheaf.inverseImageSectionFamily {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (α : (TopCat.Sheaf.inverseImage.{u, v} f).obj F ⟶ G) :
    TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G where
  app U V hUV s := G.obj.map (homOfLE hUV).op
    (((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G α).hom.app (op V) s)
  naturality {U U'} {V V'} hU hV hUV hUV' s := by
    let η := ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G α).hom
    change G.obj.map (homOfLE hUV').op (η.app (op V') (F.obj.map hV.op s)) =
      G.obj.map hU.op (G.obj.map (homOfLE hUV).op (η.app (op V) s))
    rw [NatTrans.naturality_apply η hV.op s]
    change G.obj.map (homOfLE hUV').op
        (G.obj.map ((Opens.map f).map hV).op (η.app (op V) s)) =
      G.obj.map hU.op (G.obj.map (homOfLE hUV).op (η.app (op V) s))
    have hcomp :
        G.obj.map ((Opens.map f).map hV).op ≫ G.obj.map (homOfLE hUV').op =
          G.obj.map (homOfLE hUV).op ≫ G.obj.map hU.op := by
      rw [← G.obj.map_comp, ← op_comp, ← G.obj.map_comp, ← op_comp]
      congr 1
    exact congrArg (fun k => k (η.app (op V) s)) hcomp

/-- A compatible family on pairs of opens transposes to a morphism out of inverse image.
This is the universe-polymorphic form of the section-level bridge for `f`-maps. -/
public noncomputable def TopCat.Sheaf.inverseImageSectionFamilyAdjoint {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G) :
    F ⟶ (TopCat.Sheaf.directImage.{u, v} f).obj G := by
  let η : F.obj ⟶ ((TopCat.Sheaf.directImage.{u, v} f).obj G).obj := {
    app V := TypeCat.ofHom (ξ.app ((Opens.map f).obj V.unop) V.unop (le_refl _))
    naturality := by
      intro V V' h
      ext s
      exact ξ.naturality ((Opens.map f).map h.unop) h.unop
        (le_refl _) (le_refl _) s
  }
  exact ObjectProperty.homMk η

/-- The morphism out of the inverse image that a compatible family of section maps
transposes to. -/
public noncomputable def TopCat.Sheaf.inverseImageSectionFamilyHom {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G) :
    (TopCat.Sheaf.inverseImage.{u, v} f).obj F ⟶ G :=
  ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G).symm
    (TopCat.Sheaf.inverseImageSectionFamilyAdjoint f F G ξ)

/-- Restricting the family's section map over the full preimage of `V` to `U` gives its
section map on `U`. -/
private theorem inverseImageSectionFamily_map_app_preimage {X Y : TopCat.{u}} {f : X ⟶ Y}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v))}
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v))}
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G)
    {U : Opens X} {V : Opens Y} (hUV : U ≤ (Opens.map f).obj V) (s : F.1.obj (op V)) :
    G.obj.map (homOfLE hUV).op (ξ.app ((Opens.map f).obj V) V le_rfl s) = ξ.app U V hUV s := by
  simpa using (ξ.naturality (homOfLE hUV) (𝟙 V) le_rfl hUV s).symm

/-- The component family recovered from the transposed morphism is the original family. -/
public theorem TopCat.Sheaf.inverseImageSectionFamilyHom_sectionFamily {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G)
    (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V)
    (s : F.1.obj (op V)) :
    (TopCat.Sheaf.inverseImageSectionFamily f F G
        (TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ)).app U V hUV s =
      ξ.app U V hUV s := by
  let e := (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G
  have happ : (e (e.symm (TopCat.Sheaf.inverseImageSectionFamilyAdjoint f F G ξ))).hom.app (op V) =
      (TopCat.Sheaf.inverseImageSectionFamilyAdjoint f F G ξ).hom.app (op V) :=
    congrArg (fun α => α.hom.app (op V)) (e.apply_symm_apply _)
  change G.obj.map (homOfLE hUV).op
      ((e (TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ)).hom.app (op V) s) = _
  dsimp [TopCat.Sheaf.inverseImageSectionFamilyHom]
  rw [happ]
  dsimp [TopCat.Sheaf.inverseImageSectionFamilyAdjoint]
  exact inverseImageSectionFamily_map_app_preimage ξ hUV s

/-- Over the full preimage of an open the recorded section map is the transpose of the
morphism itself. -/
public theorem TopCat.Sheaf.inverseImageSectionFamily_app_preimage {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (α : (TopCat.Sheaf.inverseImage.{u, v} f).obj F ⟶ G) (V : Opens Y) (s : F.1.obj (op V)) :
    (TopCat.Sheaf.inverseImageSectionFamily f F G α).app ((Opens.map f).obj V) V le_rfl s =
      ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G α).hom.app
        (op V) s := by
  dsimp only [TopCat.Sheaf.inverseImageSectionFamily]
  rw [show (homOfLE (le_rfl : (Opens.map f).obj V ≤ (Opens.map f).obj V)).op = 𝟙 (op _) from rfl,
    G.obj.map_id]
  rfl

/-- On sections over the preimage of an open `V`, the transposed morphism applied to the
unit of the adjunction is the family's own section map over `V`. -/
public theorem TopCat.Sheaf.inverseImageSectionFamilyHom_unit_app {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G) (V : Opens Y)
    (s : F.1.obj (op V)) :
    ((TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ).1.app
        (op ((Opens.map f).obj V)))
        ((((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).unit.app F).1.app
          (op V)) s) =
      ξ.app ((Opens.map f).obj V) V le_rfl s := by
  let adj := TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f
  let α := TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ
  have hunit' := congrArg (fun η => (ConcreteCategory.hom (η.hom.app (op V))) s)
    (adj.homEquiv_unit (f := α))
  change (ConcreteCategory.hom ((adj.homEquiv F G α).hom.app (op V))) s =
    (ConcreteCategory.hom (α.hom.app (op ((Opens.map f).obj V))))
      ((ConcreteCategory.hom ((adj.unit.app F).hom.app (op V))) s) at hunit'
  have hfamily : ((adj.homEquiv F G α).1.app (op V)) s =
      ξ.app ((Opens.map f).obj V) V le_rfl s :=
    (TopCat.Sheaf.inverseImageSectionFamily_app_preimage f F G α V s).symm.trans
      (TopCat.Sheaf.inverseImageSectionFamilyHom_sectionFamily f F G ξ _ V le_rfl s)
  exact hunit'.symm.trans hfamily

/-- A morphism out of inverse image is determined by its maps on all compatible
families of sections. -/
public theorem TopCat.Sheaf.inverseImageSectionFamily_ext {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    {α β : (TopCat.Sheaf.inverseImage.{u, v} f).obj F ⟶ G}
    (h : ∀ (U : Opens X) (V : Opens Y) (hUV : U ≤ (Opens.map f).obj V)
      (s : F.1.obj (op V)),
        (TopCat.Sheaf.inverseImageSectionFamily f F G α).app U V hUV s =
          (TopCat.Sheaf.inverseImageSectionFamily f F G β).app U V hUV s) : α = β := by
  apply ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G).injective
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  change ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G α).hom.app V s =
    ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} f).homEquiv F G β).hom.app V s
  exact ((TopCat.Sheaf.inverseImageSectionFamily_app_preimage f F G α V.unop s).symm.trans
    (h _ V.unop le_rfl s)).trans
      (TopCat.Sheaf.inverseImageSectionFamily_app_preimage f F G β V.unop s)

/-- A cocycle identity for maps out of inverse images, read off from the adjunctions: if the
transposes compose, then the two maps out of `(f ≫ g)⁻¹ F` agree up to the canonical
composition isomorphism. -/
public theorem TopCat.Sheaf.inverseImage_hom_comp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (H : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (a : (TopCat.Sheaf.inverseImage.{u, v} g).obj F ⟶ G)
    (b : (TopCat.Sheaf.inverseImage.{u, v} f).obj G ⟶ H)
    (c : (TopCat.Sheaf.inverseImage.{u, v} (f ≫ g)).obj F ⟶ H)
    (h : (TopCat.Sheaf.inverseImagePushforwardAdjunction g).homEquiv F G a ≫
      (TopCat.Sheaf.directImage.{u, v} g).map
        ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv G H b) =
      (TopCat.Sheaf.inverseImagePushforwardAdjunction (f ≫ g)).homEquiv F H c) :
    (TopCat.Sheaf.inverseImage.{u, v} f).map a ≫ b =
      (TopCat.Sheaf.inverseImageCompIso.{u, v} f g).inv.app F ≫ c := by
  let adj := TopCat.Sheaf.inverseImageCompAdjunction.{u, v} f g
  apply (adj.homEquiv F H).injective
  change adj.homEquiv F H ((TopCat.Sheaf.inverseImage f).map a ≫ b) =
    adj.homEquiv F H ((TopCat.Sheaf.inverseImageCompIso f g).inv.app F ≫ c)
  have hr : adj.homEquiv F H ((TopCat.Sheaf.inverseImageCompIso f g).inv.app F ≫ c) =
      (TopCat.Sheaf.inverseImagePushforwardAdjunction (f ≫ g)).homEquiv F H c := by
    rw [show (TopCat.Sheaf.inverseImageCompIso.{u, v} f g).inv.app F =
        (adj.leftAdjointUniq (TopCat.Sheaf.inverseImagePushforwardAdjunction (f ≫ g))).hom.app F
        from Adjunction.leftAdjointUniq_inv_app _ _ _,
      adj.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit]
  rw [hr]
  simp only [adj, TopCat.Sheaf.inverseImageCompAdjunction, sheafPushforwardCompIso]
  change (TopCat.Sheaf.inverseImagePushforwardAdjunction g).homEquiv F _
    ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv _ H
      ((TopCat.Sheaf.inverseImage f).map a ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact h

/-- The converse of `TopCat.Sheaf.inverseImage_hom_comp`: a cocycle identity for maps out of
inverse images transposes to a cocycle identity for the corresponding maps into direct
images. -/
public theorem TopCat.Sheaf.inverseImage_adjoint_comp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (H : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (a : (TopCat.Sheaf.inverseImage.{u, v} g).obj F ⟶ G)
    (b : (TopCat.Sheaf.inverseImage.{u, v} f).obj G ⟶ H)
    (c : (TopCat.Sheaf.inverseImage.{u, v} (f ≫ g)).obj F ⟶ H)
    (h : (TopCat.Sheaf.inverseImage.{u, v} f).map a ≫ b =
      (TopCat.Sheaf.inverseImageCompIso.{u, v} f g).inv.app F ≫ c) :
    (TopCat.Sheaf.inverseImagePushforwardAdjunction g).homEquiv F G a ≫
      (TopCat.Sheaf.directImage.{u, v} g).map
        ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv G H b) =
      (TopCat.Sheaf.inverseImagePushforwardAdjunction (f ≫ g)).homEquiv F H c := by
  let e := (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} (f ≫ g)).homEquiv F H
  let d := (TopCat.Sheaf.inverseImagePushforwardAdjunction g).homEquiv F G a ≫
    (TopCat.Sheaf.directImage.{u, v} g).map
      ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv G H b)
  have hd := TopCat.Sheaf.inverseImage_hom_comp f g F G H a b (e.symm d) (e.apply_symm_apply d).symm
  have hc : e.symm d = c :=
    (cancel_epi ((TopCat.Sheaf.inverseImageCompIso.{u, v} f g).inv.app F)).mp (hd.symm.trans h)
  exact (e.apply_symm_apply d).symm.trans (congrArg e hc)

/-- A compatible family along an open embedding transposes to an isomorphism as soon as each
of its section maps over an open and its image is bijective. -/
public theorem TopCat.Sheaf.isIso_inverseImageSectionFamilyHom
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)))
    (ξ : TopCat.Sheaf.InverseImageSectionFamily.{u, v} f F G)
    (hξ : ∀ U, Function.Bijective
      (ξ.app U (hf.functor.obj U) (hf.isOpenMap.adjunction.unit.app U).le)) :
    IsIso (TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ) := by
  let inst : hf.functor.IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
    hf.functor_isContinuous
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type (max u v)) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type (max u v)) :=
    hf.functor.sheafPushforwardContinuous (Type (max u v))
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let adj : L ⊣ TopCat.Sheaf.directImage.{u, v} f :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (E := Type (max u v)) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let a := (adj.homEquiv F G).symm (TopCat.Sheaf.inverseImageSectionFamilyAdjoint f F G ξ)
  have ha (U : Opens X) : a.hom.app (op U) =
      TypeCat.ofHom (ξ.app U (hf.functor.obj U)
        (hf.isOpenMap.adjunction.unit.app U).le) := by
    rw [show a = L.map (TopCat.Sheaf.inverseImageSectionFamilyAdjoint f F G ξ) ≫
        adj.counit.app G from Adjunction.homEquiv_counit ..]
    ext s
    exact inverseImageSectionFamily_map_app_preimage ξ
      (hf.isOpenMap.adjunction.unit.app U).le s
  have hiso : ∀ U, IsIso (a.hom.app U) := fun U => by
    rw [ha U.unop]
    exact (CategoryTheory.isIso_iff_bijective _).mpr (hξ U.unop)
  have : IsIso a.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map a) := inferInstanceAs (IsIso a.hom)
  have : IsIso a := isIso_of_fully_faithful (sheafToPresheaf _ _) a
  have hc : TopCat.Sheaf.inverseImageSectionFamilyHom f F G ξ =
      ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).leftAdjointUniq adj).hom.app F ≫ a := by
    apply ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv F G).injective
    rw [Adjunction.homEquiv_naturality_right,
      show ((TopCat.Sheaf.inverseImagePushforwardAdjunction f).homEquiv F (L.obj F))
          (((TopCat.Sheaf.inverseImagePushforwardAdjunction f).leftAdjointUniq adj).hom.app F)
          = adj.unit.app F from Adjunction.homEquiv_leftAdjointUniq_hom_app ..,
      ← Adjunction.homEquiv_unit]
    exact (Equiv.apply_symm_apply _ _).trans (Equiv.apply_symm_apply _ _).symm
  rw [hc]
  infer_instance
