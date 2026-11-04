module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsOrder

/-!
# Operators on local sections across an open immersion

Let `j : Z ⟶ W` be an open immersion of schemes and let `M` be a sheaf of modules on `W`. The
sections of the restriction of `M` to `Z` over an open `V` of `Z` are the sections of `M` over the
image `j ''ᵁ V`, and the opens of `Z` correspond to the opens of `W` contained in the image of
`j`. Consequently an operator on the local sections of `M` defined over all opens contained in the
image of `j` is the same datum as a global operator on the local sections of the restriction of
`M`, and the same holds for the inverse image in place of the restriction.

## Main definitions

* `DiffOp.transportSections`: an additive map on sections over an open, conjugated by restriction
  maps into an additive map on sections over another open.
* `DiffOp.globalOpEquivRawOpTop`: a global operator on local sections is the same datum as an
  operator over the base open `⊤`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSectionsIso`: the sections of the inverse image of `M`
  along an open immersion `j` over `V` are the sections of `M` over `j ''ᵁ V`.
* `AlgebraicGeometry.globalOpCongr`: conjugation of global operators by isomorphisms of the two
  module sheaves.
* `AlgebraicGeometry.rawOpEquivGlobalOpRestrict`: operators over the base open `j.opensRange` are
  the same datum as global operators between the restrictions.
* `AlgebraicGeometry.rawOpEquivGlobalOpPullback`: the same statement for the inverse image.

## Implementation notes

The identification of the sections of the restriction with the sections over the image is an
equality of types in Mathlib, so the forward map of the equivalence needs no transport at all; the
inverse map has to transport along the equality `j ''ᵁ (j ⁻¹ᵁ V) = V`, valid for `V` contained in
the image of `j`. The two transport lemmas are stated for arbitrary restriction morphisms rather
than for a chosen one, since the opens of a space form a thin category and any two parallel
morphisms agree; this makes them applicable whichever spelling of the restriction map a goal
presents.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace DiffOp

variable {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X} {F G : SheafOfModules.{u} O}

/-- An additive map on the sections of `F` over `V`, conjugated by restriction maps into an
additive map on the sections over `V'`. -/
noncomputable def transportSections {V V' : Opens X} (i : op V' ⟶ op V) (i' : op V ⟶ op V')
    (D : F.val.obj (op V) →+ G.val.obj (op V)) : F.val.obj (op V') →+ G.val.obj (op V') :=
  ((G.val.presheaf.map i').hom.comp D).comp (F.val.presheaf.map i).hom

/-- The transported map sends a section `x` over `V'` to the restriction to `V'` of the value of
`D` at the restriction of `x` to `V`. -/
theorem transportSections_apply {V V' : Opens X} (i : op V' ⟶ op V) (i' : op V ⟶ op V')
    (D : F.val.obj (op V) →+ G.val.obj (op V)) (x : F.val.obj (op V')) :
    transportSections i i' D x = G.val.presheaf.map i' (D (F.val.presheaf.map i x)) := rfl

/-- Transporting an additive map on sections to the same open changes nothing. -/
theorem transportSections_self {V : Opens X} (i i' : op V ⟶ op V)
    (D : F.val.obj (op V) →+ G.val.obj (op V)) : transportSections i i' D = D := by
  obtain rfl : i = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : i' = 𝟙 _ := Subsingleton.elim _ _
  apply AddMonoidHom.ext
  intro x
  simp only [transportSections_apply, CategoryTheory.Functor.map_id]
  rfl

/-- The value of a raw operator over an open of its base, transported to an equal open, is its
value there. -/
theorem RawOp.transportSections_apply_eq {U : Opens X} (D : RawOp F G U) {V V' : Opens X}
    (h : V = V') (hV : V ≤ U) (hV' : V' ≤ U) (i : op V' ⟶ op V) (i' : op V ⟶ op V') :
    transportSections i i' (D (Over.mk (homOfLE hV))) = D (Over.mk (homOfLE hV')) := by
  subst h
  exact transportSections_self i i' _

/-- The value of a global operator over an open, transported to an equal open, is its value
there. -/
theorem GlobalOp.transportSections_apply_eq (E : GlobalOp F G) {V V' : Opens X} (h : V = V')
    (i : op V' ⟶ op V) (i' : op V ⟶ op V') :
    transportSections i i' (E (op V)) = E (op V') := by
  subst h
  exact transportSections_self i i' _

/-- A global operator on local sections is the same datum as an operator over the base open `⊤`:
every open is contained in `⊤`. -/
def globalOpEquivRawOpTop : GlobalOp F G ≃ RawOp F G ⊤ where
  toFun D := D.restrict ⊤
  invFun D V := D (Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))
  left_inv _ := rfl
  right_inv _ := rfl

end DiffOp

namespace AlgebraicGeometry

open Scheme

/-- Conjugating a global operator on local sections by isomorphisms of the source and target
module sheaves. -/
noncomputable def globalOpCongr {Y : Scheme.{u}} {M M' N N' : Y.Modules} (eM : M ≅ M')
    (eN : N ≅ N') : DiffOp.GlobalOp M N ≃ DiffOp.GlobalOp M' N' where
  toFun D V := ((eN.hom.app V.unop).hom.comp (D V)).comp (eM.inv.app V.unop).hom
  invFun D V := ((eN.inv.app V.unop).hom.comp (D V)).comp (eM.hom.app V.unop).hom
  left_inv D := by
    funext V
    apply AddMonoidHom.ext
    intro x
    have hM : eM.hom.app V.unop ≫ eM.inv.app V.unop = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, eM.hom_inv_id, Scheme.Modules.Hom.id_app]
    have hN : eN.hom.app V.unop ≫ eN.inv.app V.unop = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, eN.hom_inv_id, Scheme.Modules.Hom.id_app]
    change (eN.inv.app V.unop).hom ((eN.hom.app V.unop).hom
      (D V ((eM.inv.app V.unop).hom ((eM.hom.app V.unop).hom x)))) = D V x
    rw [show (eM.inv.app V.unop).hom ((eM.hom.app V.unop).hom x) = x from
        ConcreteCategory.congr_hom hM x,
      show (eN.inv.app V.unop).hom ((eN.hom.app V.unop).hom (D V x)) = D V x from
        ConcreteCategory.congr_hom hN (D V x)]
  right_inv D := by
    funext V
    apply AddMonoidHom.ext
    intro x
    have hM : eM.inv.app V.unop ≫ eM.hom.app V.unop = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, eM.inv_hom_id, Scheme.Modules.Hom.id_app]
    have hN : eN.inv.app V.unop ≫ eN.hom.app V.unop = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, eN.inv_hom_id, Scheme.Modules.Hom.id_app]
    change (eN.hom.app V.unop).hom ((eN.inv.app V.unop).hom
      (D V ((eM.hom.app V.unop).hom ((eM.inv.app V.unop).hom x)))) = D V x
    rw [show (eM.hom.app V.unop).hom ((eM.inv.app V.unop).hom x) = x from
        ConcreteCategory.congr_hom hM x,
      show (eN.hom.app V.unop).hom ((eN.inv.app V.unop).hom (D V x)) = D V x from
        ConcreteCategory.congr_hom hN (D V x)]

variable {Z W : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j]

/-- Restriction of sections of the restriction of `M` along an open immersion is restriction of
sections of `M` between the images, for any choice of the two restriction morphisms. -/
theorem Scheme.Modules.restrict_val_presheaf_map (M : W.Modules) {V V' : Z.Opens}
    (i : op V' ⟶ op V) (k : op (j ''ᵁ V') ⟶ op (j ''ᵁ V)) :
    (M.restrict j).val.presheaf.map i = M.val.presheaf.map k :=
  congrArg M.val.presheaf.map (Subsingleton.elim (j.opensFunctor.op.map i) k)

/-- Transporting an additive map on the sections of `M` across an open immersion may be computed
either with the restriction maps of `M` between the images or with those of the restriction of `M`
along the immersion. -/
theorem transportSections_restrict (M M' : W.Modules) {V V' : Z.Opens}
    (i : op V' ⟶ op V) (i' : op V ⟶ op V') (k : op (j ''ᵁ V') ⟶ op (j ''ᵁ V))
    (k' : op (j ''ᵁ V) ⟶ op (j ''ᵁ V'))
    (D : M.val.obj (op (j ''ᵁ V)) →+ M'.val.obj (op (j ''ᵁ V))) :
    DiffOp.transportSections (F := M) (G := M') k k' D =
      DiffOp.transportSections (F := M.restrict j) (G := M'.restrict j) i i' D := rfl

/-- The sections of the inverse image of `M` along an open immersion `j` over an open `V` are the
sections of `M` over the image `j ''ᵁ V`. -/
noncomputable def Scheme.Modules.pullbackSectionsIso (M : W.Modules) (V : Z.Opens) :
    Γ((Scheme.Modules.pullback j).obj M, V) ≅ Γ(M, j ''ᵁ V) :=
  (asIso (((Scheme.Modules.restrictFunctorIsoPullback j).app M).hom.app V)).symm

/-- The image of an open of the source of an open immersion, viewed as an open of the target below
the image of the immersion. -/
abbrev imageOver (V : Z.Opens) : Over (j.opensRange) :=
  Over.mk (homOfLE (j.image_le_opensRange V))

/-- For an open of the target contained in the image of an open immersion, its preimage has that
open as image. -/
theorem image_preimage_eq_of_le {V : W.Opens} (hV : V ≤ j.opensRange) : j ''ᵁ (j ⁻¹ᵁ V) = V :=
  (j.image_preimage_eq_opensRange_inf V).trans (inf_eq_right.2 hV)

/-- Two objects of a slice category over an open of a space with the same underlying open are
equal. -/
theorem Scheme.overMk_congr {X : Scheme.{u}} {U V V' : X.Opens} (h : V = V') (hV : V ≤ U)
    (hV' : V' ≤ U) : (Over.mk (homOfLE hV) : Over U) = Over.mk (homOfLE hV') := by
  subst h
  rfl

/-- Every open of the target of an open immersion contained in the image of the immersion is the
image of an open of the source. -/
theorem exists_imageOver (Y : Over (j.opensRange)) : ∃ V : Z.Opens, imageOver j V = Y :=
  ⟨j ⁻¹ᵁ Y.left,
    Scheme.overMk_congr (image_preimage_eq_of_le j Y.hom.le) (j.image_le_opensRange _) Y.hom.le⟩

/-- An open of the target of an open immersion below the image of an open of the source is the
image of an open of the source below it. -/
theorem exists_imageOver_of_le {V : Z.Opens} (Y : Over (j ''ᵁ V)) :
    ∃ V' : Z.Opens, ∃ h : V' ≤ V, Over.mk (homOfLE (j.image_mono h)) = Y :=
  ⟨j ⁻¹ᵁ Y.left, (j.image_le_image_iff _ _).1
      ((image_preimage_eq_of_le j (Y.hom.le.trans (j.image_le_opensRange V))).trans_le Y.hom.le),
    Scheme.overMk_congr (image_preimage_eq_of_le j (Y.hom.le.trans (j.image_le_opensRange V)))
      _ Y.hom.le⟩

/-- **Operators across an open immersion.** An operator on the local sections of `M` over the opens
contained in the image of an open immersion `j : Z ⟶ W` is the same datum as a global operator on
the local sections of the restriction of `M` to `Z`. -/
noncomputable def rawOpEquivGlobalOpRestrict (M M' : W.Modules) :
    DiffOp.RawOp M M' j.opensRange ≃ DiffOp.GlobalOp (M.restrict j) (M'.restrict j) where
  toFun D V := D (imageOver j V.unop)
  invFun E Y :=
    DiffOp.transportSections
      (homOfLE (image_preimage_eq_of_le j Y.hom.le).le).op
      (homOfLE (image_preimage_eq_of_le j Y.hom.le).ge).op (E (op (j ⁻¹ᵁ Y.left)))
  left_inv D := by
    funext Y
    exact D.transportSections_apply_eq (image_preimage_eq_of_le j Y.hom.le)
      (j.image_le_opensRange _) Y.hom.le _ _
  right_inv E := by
    funext V
    exact (transportSections_restrict j M M'
      (homOfLE (j.preimage_image_eq V.unop).le).op
      (homOfLE (j.preimage_image_eq V.unop).ge).op _ _ _).trans
      (E.transportSections_apply_eq (j.preimage_image_eq V.unop) _ _)

/-- The global operator corresponding to an operator over the image of an open immersion is its
value at the image of the open. -/
theorem rawOpEquivGlobalOpRestrict_apply (M M' : W.Modules)
    (D : DiffOp.RawOp M M' j.opensRange) (V : Z.Opens) :
    rawOpEquivGlobalOpRestrict j M M' D (op V) = D (imageOver j V) := rfl

/-- The operator over the image of an open immersion corresponding to a global operator is its
value at the preimage of the open, transported along the restriction maps. -/
theorem rawOpEquivGlobalOpRestrict_symm_apply (M M' : W.Modules)
    (E : DiffOp.GlobalOp (M.restrict j) (M'.restrict j)) (Y : Over (j.opensRange)) :
    (rawOpEquivGlobalOpRestrict j M M').symm E Y =
      DiffOp.transportSections
        (homOfLE (image_preimage_eq_of_le j Y.hom.le).le).op
        (homOfLE (image_preimage_eq_of_le j Y.hom.le).ge).op (E (op (j ⁻¹ᵁ Y.left))) := rfl

/-- **Operators across an open immersion, for the inverse image.** An operator on the local
sections of `M` over the opens contained in the image of an open immersion `j : Z ⟶ W` is the same
datum as a global operator on the local sections of the inverse image of `M` along `j`. -/
noncomputable def rawOpEquivGlobalOpPullback (M M' : W.Modules) :
    DiffOp.RawOp M M' j.opensRange ≃
      DiffOp.GlobalOp ((Scheme.Modules.pullback j).obj M) ((Scheme.Modules.pullback j).obj M') :=
  (rawOpEquivGlobalOpRestrict j M M').trans
    (globalOpCongr ((Scheme.Modules.restrictFunctorIsoPullback j).app M)
      ((Scheme.Modules.restrictFunctorIsoPullback j).app M'))

end AlgebraicGeometry

end
