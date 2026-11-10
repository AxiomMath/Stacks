module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Sections of a sheaf pullback along a factored continuous functor

Let `a : C ⥤ D` be a continuous functor of sites and suppose it is factored through a third
site, `a ⋙ i ≅ j` for continuous `i : D ⥤ H` and `j : C ⥤ H`. If each comparison arrow
`ε.app U` is an initial object of the structured-arrow category over `i.op`, then the pointwise
right Kan extension along `i.op` computes the direct image along `a`, and consequently the
sheaf pullback along `a` is the composite of the pullback along `j` with the direct image
along `i`:

`a⁻¹ ≅ j⁻¹ ⋙ i_*`.

Evaluating at a terminal object of `D` turns this into a description of the sections of `j⁻¹F`
on `i.obj T` as the global sections of `a⁻¹F`, and the whole family of such descriptions, for
varying `a`, is compatible with the canonical restriction maps between the pullbacks.

## Main definitions

* `CategoryTheory.sheafPullbackRestriction` — for a factorization `a ⋙ b ≅ c` of continuous
  functors, the mate `a⁻¹F ⟶ b_* c⁻¹F` of the unit of the adjunction for `c`.
* `CategoryTheory.sheafPullbackSectionsRestriction` — the induced map of global sections,
  obtained by evaluating the previous map at a terminal object.
* `CategoryTheory.sheafPushforwardRanComparison` — the comparison `i_* j_* ⟶ a_*` induced by
  `ε : a ⋙ i ⟶ j`, where `i_*` is the cocontinuous direct image, i.e. right Kan extension.
* `CategoryTheory.sheafPullbackIsoOfInitial` — the isomorphism `a⁻¹ ≅ P ⋙ i_*` obtained by
  uniqueness of left adjoints once `sheafPushforwardRanComparison` is invertible.
* `CategoryTheory.sheafPushforwardRestriction` — the arrow `i_* G ⟶ b_* i'_* G` attached to a
  natural transformation `θ : b ⋙ i' ⟶ i`.
* `CategoryTheory.sheafPullbackSectionsIso` — the comparison of the sections of `P` at
  `i.obj T` with the global sections of a sheaf pullback.

## Main results

* `CategoryTheory.sheafPushforwardRanComparison_isIso` — the Kan extension comparison is
  invertible as soon as every `ε.app U` is initial in the relevant structured-arrow category.
* `CategoryTheory.sheafPullbackIsoOfInitial_unit` — the comparison is compatible with the two
  adjunction units, which is what pins it down.
* `CategoryTheory.sheafPullbackRestriction_comp` — compatibility of two such comparisons with
  `sheafPullbackRestriction`, for a transformation `θ` compatible with the factorizations.
* `CategoryTheory.sheafPullbackSectionsIso_restriction` — the resulting commuting square of
  global sections and restriction maps.
* `CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app` — the isomorphism identifying global
  sections with sections at a terminal object is the canonical restriction map.

## Implementation notes

`sheafPullbackIsoOfInitial` is defined by uniqueness of left adjoints, so it carries no
computational content by itself; `sheafPullbackIsoOfInitial_unit` is the equation that
determines it and the only property used downstream.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

section Restriction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

/-- For a factorization `a ⋙ b ≅ c` of continuous functors of sites, the mate of the unit of
the adjunction for `c` under the adjunction for `a`: a canonical arrow
`a⁻¹F ⟶ b_* c⁻¹F`. -/
public def sheafPullbackRestriction (e : a ⋙ b ≅ c) (F : Sheaf J (Type w)) :
    (a.sheafPullback (Type w) J K).obj F ⟶
      (b.sheafPushforwardContinuous (Type w) K L).obj
        ((c.sheafPullback (Type w) J L).obj F) :=
  ((a.sheafAdjunctionContinuous (Type w) J K).homEquiv _ _).symm
    ((c.sheafAdjunctionContinuous (Type w) J L).unit.app F ≫
      (Functor.sheafPushforwardContinuousComp' e (Type w) J K L).inv.app _)

/-- The defining property of `CategoryTheory.sheafPullbackRestriction`: composing it with the
unit of the adjunction for `a` gives the unit for `c` followed by restriction along the
factorization. -/
public lemma sheafPullbackRestriction_unit (e : a ⋙ b ≅ c) (F : Sheaf J (Type w)) (U : Cᵒᵖ) :
    ((a.sheafAdjunctionContinuous (Type w) J K).unit.app F).hom.app U ≫
        (sheafPullbackRestriction J K L a b c e F).hom.app (a.op.obj U) =
      ((c.sheafAdjunctionContinuous (Type w) J L).unit.app F).hom.app U ≫
        ((c.sheafPullback (Type w) J L).obj F).obj.map (e.hom.app U.unop).op := by
  have h := (a.sheafAdjunctionContinuous (Type w) J K).homEquiv _ _ |>.apply_symm_apply
    ((c.sheafAdjunctionContinuous (Type w) J L).unit.app F ≫
      (Functor.sheafPushforwardContinuousComp' e (Type w) J K L).inv.app _)
  have h' := congrArg (fun t => t.hom.app U) h
  simp only [Functor.id_obj,
    Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app] at h'
  exact h'

variable [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]

/-- The map of global sections induced by `CategoryTheory.sheafPullbackRestriction`, obtained
by evaluating it at a terminal object `T` of `D` whose image under `b` is again terminal. -/
public def sheafPullbackSectionsRestriction (e : a ⋙ b ≅ c) {T : D}
    (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w)) :
    (Sheaf.Γ K (Type w)).obj ((a.sheafPullback (Type w) J K).obj F) ⟶
      (Sheaf.Γ L (Type w)).obj ((c.sheafPullback (Type w) J L).obj F) :=
  (Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.app _ ≫
    (sheafPullbackRestriction J K L a b c e F).hom.app (Opposite.op T) ≫
    (Sheaf.ΓNatIsoSheafSections L (Type w) hbT).inv.app _

end Restriction

section GlobalSections

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasTerminal C] [HasWeakSheafify J (Type w)]

/-- The isomorphism of the global sections functor with the sections functor at a terminal
object is given by the canonical restriction map `CategoryTheory.Sheaf.ΓRes`. -/
public lemma Sheaf.ΓNatIsoSheafSections_hom_app (T : C) (hT : IsTerminal T)
    (F : Sheaf J (Type w)) :
    (Sheaf.ΓNatIsoSheafSections J (Type w) hT).hom.app F = F.ΓRes (Opposite.op T) := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (constantSheafΓAdj J (Type w)) (constantSheafAdj J (Type w) hT) F
  have hh := congrArg ((constantSheafAdj J (Type w) hT).homEquiv _ _) h
  rw [Equiv.apply_symm_apply] at hh
  refine hh.trans ?_
  change ((constantPresheafAdj (Type w) hT).homEquiv _ F.obj)
      (((sheafificationAdjunction J (Type w)).homEquiv _ F)
        ((constantSheafΓAdj J (Type w)).counit.app F)) =
    (((sheafificationAdjunction J (Type w)).homEquiv _ F)
      (((constantSheafΓAdj J (Type w)).homEquiv _ F).symm (𝟙 _))).app (Opposite.op T)
  have hc : (((constantSheafΓAdj J (Type w)).homEquiv _ F).symm (𝟙 _)) =
      (constantSheafΓAdj J (Type w)).counit.app F := by
    rw [Adjunction.homEquiv_counit, (constantSheaf J (Type w)).map_id]
    exact Category.id_comp _
  rw [hc, Adjunction.homEquiv_unit]
  exact Category.id_comp _

/-- The isomorphisms of the global sections functor with the sections functors at two terminal
objects are compatible with restriction along the unique arrow between them. -/
public lemma Sheaf.ΓNatIsoSheafSections_hom_app_map {T T' : C} (hT : IsTerminal T)
    (hT' : IsTerminal T') (f : T' ⟶ T) (F : Sheaf J (Type w)) :
    (Sheaf.ΓNatIsoSheafSections J (Type w) hT).hom.app F ≫ F.obj.map f.op =
      (Sheaf.ΓNatIsoSheafSections J (Type w) hT').hom.app F := by
  rw [Sheaf.ΓNatIsoSheafSections_hom_app, Sheaf.ΓNatIsoSheafSections_hom_app]
  exact F.ΓRes_map f.op

end GlobalSections

section Canonical

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (i : D ⥤ E) (j : C ⥤ E)
  [a.IsContinuous J K] [i.IsContinuous K L] [j.IsContinuous J L]
  [i.IsCocontinuous K L]
  [∀ F : Dᵒᵖ ⥤ Type w, i.op.HasPointwiseRightKanExtension F]
  (ε : a ⋙ i ⟶ j)

/-- The comparison of the composite of the cocontinuous direct image along `i` with the
continuous direct image along `j` with the continuous direct image along `a`, induced by a
natural transformation `ε : a ⋙ i ⟶ j`. -/
public def sheafPushforwardRanComparison :
    i.sheafPushforwardCocontinuous (Type w) K L ⋙
        j.sheafPushforwardContinuous (Type w) J L ⟶
      a.sheafPushforwardContinuous (Type w) J K where
  app G := ⟨{
    app U := ((i.sheafPushforwardCocontinuous (Type w) K L).obj G).obj.map
      (ε.app U.unop).op ≫ (i.op.ranCounit.app G.obj).app (a.op.obj U)
    naturality := by
      intro U V f
      change (i.op.ran.obj G.obj).map (j.op.map f) ≫
          (i.op.ran.obj G.obj).map (ε.app V.unop).op ≫
            (i.op.ranCounit.app G.obj).app (a.op.obj V) =
        ((i.op.ran.obj G.obj).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app G.obj).app (a.op.obj U)) ≫ G.obj.map (a.op.map f)
      have hn := (i.op.ranCounit.app G.obj).naturality (a.op.map f)
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.whiskeringLeft_obj_obj] at hn
      rw [Category.assoc, ← hn,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
      exact congrArg Quiver.Hom.op (ε.naturality f.unop).symm }⟩
  naturality := by
    intro G H f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (i.op.ran.map f.hom).app (j.op.obj U) ≫
        ((i.op.ran.obj H.obj).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app H.obj).app (a.op.obj U)) =
      ((i.op.ran.obj G.obj).map (ε.app U.unop).op ≫
        (i.op.ranCounit.app G.obj).app (a.op.obj U)) ≫ f.hom.app (a.op.obj U)
    rw [← Category.assoc, ← NatTrans.naturality, Category.assoc, Category.assoc]
    congr 1
    exact NatTrans.congr_app (i.op.ranCounit.naturality f.hom) (a.op.obj U)

omit [i.IsContinuous K L] in
/-- If each comparison arrow `ε.app U` is initial among the structured arrows over `i.op`, then
the Kan extension comparison is an isomorphism: it is then one of the components of the
pointwise right Kan extension at an initial object. -/
public lemma sheafPushforwardRanComparison_isIso
    (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op))) :
    IsIso (sheafPushforwardRanComparison J K L a i j ε) := by
  have hG (G : Sheaf K (Type w)) :
      IsIso ((sheafPushforwardRanComparison J K L a i j ε).app G) := by
    have hU (U : Cᵒᵖ) :
        IsIso (((sheafPushforwardRanComparison J K L a i j ε).app G).hom.app U) :=
      (i.op.isPointwiseRightKanExtensionRanCounit G.obj
          (j.op.obj U)).isIso_π_app_of_isInitial
        (StructuredArrow.mk (T := i.op) ((ε.app U.unop).op)) (hε U.unop)
    have : IsIso ((sheafToPresheaf J (Type w)).map
        ((sheafPushforwardRanComparison J K L a i j ε).app G)) :=
      NatIso.isIso_of_isIso_app ((sheafPushforwardRanComparison J K L a i j ε).app G).hom
    exact isIso_of_reflects_iso ((sheafPushforwardRanComparison J K L a i j ε).app G)
      (sheafToPresheaf J (Type w))
  exact NatIso.isIso_of_isIso_app _

variable (P : Sheaf J (Type w) ⥤ Sheaf L (Type w))
  (adjP : P ⊣ j.sheafPushforwardContinuous (Type w) J L)
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op)))

/-- Under the initiality hypothesis of `sheafPushforwardRanComparison_isIso`, the sheaf
pullback along `a` is the pullback along `j` followed by the direct image along `i`. -/
public def sheafPullbackIsoOfInitial :
    a.sheafPullback (Type w) J K ≅ P ⋙ i.sheafPushforwardContinuous (Type w) K L := by
  letI := sheafPushforwardRanComparison_isIso J K L a i j ε hε
  exact Adjunction.leftAdjointUniq (a.sheafAdjunctionContinuous (Type w) J K)
    ((adjP.comp (i.sheafAdjunctionCocontinuous (Type w) K L)).ofNatIsoRight
      (asIso (sheafPushforwardRanComparison J K L a i j ε)))

/-- The unit of the right Kan extension adjunction, followed by restriction along an arrow in
the image of `i.op` and the Kan extension counit, is restriction along that arrow. -/
public lemma ran_unit_map_ranCounit (i : D ⥤ E)
    [∀ F : Dᵒᵖ ⥤ Type w, i.op.HasPointwiseRightKanExtension F]
    (G : Eᵒᵖ ⥤ Type w) {X : Eᵒᵖ} {Y : Dᵒᵖ} (f : X ⟶ i.op.obj Y) :
    ((i.op.ranAdjunction (Type w)).unit.app G).app X ≫
        (i.op.ran.obj (i.op ⋙ G)).map f ≫ (i.op.ranCounit.app (i.op ⋙ G)).app Y =
      G.map f := by
  have hn := ((i.op.ranAdjunction (Type w)).unit.app G).naturality f
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    Functor.ranCounit_app_app_ranAdjunction_unit_app_app]
  exact Category.comp_id _

/-- The equation pinning down `sheafPullbackIsoOfInitial`: it carries the unit of the
adjunction for `a` to the unit of the adjunction for `P`, followed by restriction along
`ε`. -/
public lemma sheafPullbackIsoOfInitial_unit (F : Sheaf J (Type w)) (U : Cᵒᵖ) :
    ((a.sheafAdjunctionContinuous (Type w) J K).unit.app F).hom.app U ≫
        ((sheafPullbackIsoOfInitial J K L a i j ε P adjP hε).hom.app F).hom.app (a.op.obj U) =
      (adjP.unit.app F).hom.app U ≫ (P.obj F).obj.map (ε.app U.unop).op := by
  let := sheafPushforwardRanComparison_isIso J K L a i j ε hε
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (a.sheafAdjunctionContinuous (Type w) J K)
    ((adjP.comp (i.sheafAdjunctionCocontinuous (Type w) K L)).ofNatIsoRight
      (asIso (sheafPushforwardRanComparison J K L a i j ε))) F
  have h' := congrArg (fun t => t.hom.app U) h
  refine h'.trans ?_
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.whiskerLeft_app,
    asIso_hom, sheafPushforwardRanComparison, Category.assoc]
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  change (adjP.unit.app F).hom.app U ≫
      ((i.op.ranAdjunction (Type w)).unit.app (P.obj F).obj).app (j.op.obj U) ≫
        (i.op.ran.obj (i.op ⋙ (P.obj F).obj)).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app (i.op ⋙ (P.obj F).obj)).app (a.op.obj U) = _
  congr 1
  exact ran_unit_map_ranCounit i (P.obj F).obj (ε.app U.unop).op

end Canonical

section Compatibility

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) (M : GrothendieckTopology H)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  (i : D ⥤ H) (i' : E ⥤ H) (j : C ⥤ H)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [i.IsContinuous K M] [i'.IsContinuous L M] [j.IsContinuous J M]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

/-- The arrow `i_* G ⟶ b_* i'_* G` of direct images attached to a natural transformation
`θ : b ⋙ i' ⟶ i`, given by restriction along `θ`. -/
public def sheafPushforwardRestriction (θ : b ⋙ i' ⟶ i) (G : Sheaf M (Type w)) :
    (i.sheafPushforwardContinuous (Type w) K M).obj G ⟶
      (b.sheafPushforwardContinuous (Type w) K L).obj
        ((i'.sheafPushforwardContinuous (Type w) L M).obj G) :=
  ⟨Functor.whiskerRight (NatTrans.op θ) G.obj⟩

/-- `CategoryTheory.sheafPushforwardRestriction` is, on sections over `U`, restriction along
`θ.app U`. -/
public lemma sheafPushforwardRestriction_hom_app (θ : b ⋙ i' ⟶ i) (G : Sheaf M (Type w))
    (U : Dᵒᵖ) :
    (sheafPushforwardRestriction K L M b i i' θ G).hom.app U =
      G.obj.map (θ.app U.unop).op :=
  rfl

variable (P : Sheaf J (Type w) ⥤ Sheaf M (Type w))
  (η : 𝟭 (Sheaf J (Type w)) ⟶ P ⋙ j.sheafPushforwardContinuous (Type w) J M)
  (ε : a ⋙ i ⟶ j) (ε' : c ⋙ i' ⟶ j)
  (m : a.sheafPullback (Type w) J K ⟶ P ⋙ i.sheafPushforwardContinuous (Type w) K M)
  (m' : c.sheafPullback (Type w) J L ⟶ P ⋙ i'.sheafPushforwardContinuous (Type w) L M)
  (hm : ∀ F U, ((a.sheafAdjunctionContinuous (Type w) J K).unit.app F).hom.app U ≫
    (m.app F).hom.app (a.op.obj U) = (η.app F).hom.app U ≫
      (P.obj F).obj.map (ε.app U.unop).op)
  (hm' : ∀ F U, ((c.sheafAdjunctionContinuous (Type w) J L).unit.app F).hom.app U ≫
    (m'.app F).hom.app (c.op.obj U) = (η.app F).hom.app U ≫
      (P.obj F).obj.map (ε'.app U.unop).op)

include hm hm' in
/-- Two comparisons `m`, `m'` pinned down by the same unit `η`, as in
`sheafPullbackIsoOfInitial_unit`, are compatible with `sheafPullbackRestriction` and
`sheafPushforwardRestriction`, provided `θ` is compatible with the factorizations. -/
public lemma sheafPullbackRestriction_comp (e : a ⋙ b ≅ c) (θ : b ⋙ i' ⟶ i)
    (hθ : ∀ U, θ.app (a.obj U) ≫ ε.app U = i'.map (e.hom.app U) ≫ ε'.app U)
    (F : Sheaf J (Type w)) :
    m.app F ≫ sheafPushforwardRestriction K L M b i i' θ (P.obj F) =
      sheafPullbackRestriction J K L a b c e F ≫
        (b.sheafPushforwardContinuous (Type w) K L).map (m'.app F) := by
  apply ((a.sheafAdjunctionContinuous (Type w) J K).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, sheafPushforwardRestriction_hom_app]
  have hPθ : (P.obj F).obj.map (ε.app U.unop).op ≫
        (P.obj F).obj.map (θ.app (a.obj U.unop)).op =
      (P.obj F).obj.map (ε'.app U.unop).op ≫
        (P.obj F).obj.map (i'.map (e.hom.app U.unop)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hθ U.unop]
  have hn : ((c.sheafPullback (Type w) J L).obj F).obj.map (e.hom.app U.unop).op ≫
        (m'.app F).hom.app (b.op.obj (a.op.obj U)) =
      (m'.app F).hom.app (c.op.obj U) ≫
        (P.obj F).obj.map (i'.map (e.hom.app U.unop)).op :=
    (m'.app F).hom.naturality (e.hom.app U.unop).op
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (hm F U =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= hPθ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((hm' F U).symm =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= hn.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((sheafPullbackRestriction_unit J K L a b c e F U).symm =≫ _).trans ?_
  exact Category.assoc _ _ _

end Compatibility

section SectionsComparison

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) (M : GrothendieckTopology H)
  [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E) (i : D ⥤ H) (i' : E ⥤ H)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [i.IsContinuous K M] [i'.IsContinuous L M]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]
  (P : Sheaf J (Type w) ⥤ Sheaf M (Type w))

/-- Sections of `P` at `i.obj T`, for `T` terminal in `D`, are the global sections of a sheaf
pullback `A` presented as `P ⋙ i_*`. -/
public def sheafPullbackSectionsIso (A : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (m : A ≅ P ⋙ i.sheafPushforwardContinuous (Type w) K M)
    {T : D} (hT : IsTerminal T) :
    P ⋙ (sheafSections M (Type w)).obj (Opposite.op (i.obj T)) ≅ A ⋙ Sheaf.Γ K (Type w) :=
  (Functor.isoWhiskerRight m ((sheafSections K (Type w)).obj (Opposite.op T))).symm ≪≫
    Functor.isoWhiskerLeft A (Sheaf.ΓNatIsoSheafSections K (Type w) hT).symm

/-- The comparisons of `sheafPullbackSectionsIso` for two factorizations commute with
restriction along `g` on the one side and with `sheafPullbackSectionsRestriction` on the
other. -/
public lemma sheafPullbackSectionsIso_restriction
    (m : a.sheafPullback (Type w) J K ≅ P ⋙ i.sheafPushforwardContinuous (Type w) K M)
    (m' : c.sheafPullback (Type w) J L ≅ P ⋙ i'.sheafPushforwardContinuous (Type w) L M)
    (e : a ⋙ b ≅ c) (θ : b ⋙ i' ⟶ i)
    {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T))
    {T' : E} (hT' : IsTerminal T') (g : i'.obj T' ⟶ i.obj T)
    (hg : i'.map (hbT.from T') ≫ θ.app T = g)
    (F : Sheaf J (Type w))
    (hm : m.hom.app F ≫ sheafPushforwardRestriction K L M b i i' θ (P.obj F) =
      sheafPullbackRestriction J K L a b c e F ≫
        (b.sheafPushforwardContinuous (Type w) K L).map (m'.hom.app F)) :
    (sheafPullbackSectionsIso J K M i P _ m hT).hom.app F ≫
        sheafPullbackSectionsRestriction J K L a b c e hT hbT F =
      (P.obj F).obj.map g.op ≫ (sheafPullbackSectionsIso J L M i' P _ m' hT').hom.app F := by
  apply (cancel_epi ((sheafPullbackSectionsIso J K M i P _ m hT).inv.app F)).mp
  apply (cancel_mono ((sheafPullbackSectionsIso J L M i' P _ m' hT').inv.app F)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  change sheafPullbackSectionsRestriction J K L a b c e hT hbT F ≫
      ((Sheaf.ΓNatIsoSheafSections L (Type w) hT').hom.app _ ≫
        (m'.hom.app F).hom.app (Opposite.op T')) =
    ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.app _ ≫
      (m.hom.app F).hom.app (Opposite.op T)) ≫ (P.obj F).obj.map g.op
  have heval := congrArg (fun t => t.hom.app (Opposite.op T)) hm
  change (m.hom.app F).hom.app (Opposite.op T) ≫ (P.obj F).obj.map (θ.app T).op =
    (sheafPullbackRestriction J K L a b c e F).hom.app (Opposite.op T) ≫
      (m'.hom.app F).hom.app (Opposite.op (b.obj T)) at heval
  have hΓ := Sheaf.ΓNatIsoSheafSections_hom_app_map L hbT hT' (hbT.from T')
    ((c.sheafPullback (Type w) J L).obj F)
  have hn := (m'.hom.app F).hom.naturality (hbT.from T').op
  change ((c.sheafPullback (Type w) J L).obj F).obj.map (hbT.from T').op ≫
      (m'.hom.app F).hom.app (Opposite.op T') =
    (m'.hom.app F).hom.app (Opposite.op (b.obj T)) ≫
      (P.obj F).obj.map (i'.map (hbT.from T')).op at hn
  dsimp only [sheafPullbackSectionsRestriction]
  rw [← hΓ]
  simp only [Category.assoc]
  rw [hn]
  have hgP : (P.obj F).obj.map (θ.app T).op ≫
      (P.obj F).obj.map (i'.map (hbT.from T')).op = (P.obj F).obj.map g.op := by
    rw [← Functor.map_comp, ← op_comp, hg]
  refine (_ ≫= (Category.assoc _ _ _).trans
    (_ ≫= Iso.inv_hom_id_app_assoc _ _ _)).trans ?_
  refine (_ ≫= (Category.assoc _ _ _).symm).trans ?_
  refine (_ ≫= (heval.symm =≫ _)).trans ?_
  refine (_ ≫= Category.assoc _ _ _).trans ?_
  refine (_ ≫= (_ ≫= hgP)).trans ?_
  exact (Category.assoc _ _ _).symm

end SectionsComparison

end CategoryTheory
