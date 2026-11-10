module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Comparing right Kan extensions along two functors with the same hom-sets

Let `κ : C ⥤ D` and `v : C ⥤ E` be two functors out of the same category, and let `W : O ⥤ D`
and `m : O ⥤ E` be functors into their targets. Suppose we are given a bijection
`(κ.obj X ⟶ W.obj Y) ≃ (v.obj X ⟶ m.obj Y)`, natural in `X : C` and in `Y : O`. Such a datum
is packaged as a `CategoryTheory.RanComparison`; it is exactly what is needed to identify the
two restricted right Kan extensions

  `P ↦ W.op ⋙ κ.op.ran.obj P`  and  `P ↦ m.op ⋙ v.op.ran.obj P`

on presheaves with values in any coefficient category `A` admitting the relevant pointwise
right Kan extensions. Indeed, a pointwise right Kan extension along `κ.op` evaluated at
`op (W.obj Y)` is the limit of `P` over the category `StructuredArrow (op (W.obj Y)) κ.op`,
whose objects are pairs consisting of an object `X : C` and a morphism `κ.obj X ⟶ W.obj Y`; the
comparison datum turns this index category into `StructuredArrow (op (m.obj Y)) v.op` without
moving the underlying object `X`, so the two limits agree.

The typical source of a `RanComparison` is a pair of adjunctions, or a morphism of sites
presented in two different ways; the point of isolating the hom-set bijection is that no
adjointness, continuity or smallness hypothesis is needed for the comparison itself.

## Main definitions

* `CategoryTheory.RanComparison`: a natural bijection `(κ.obj X ⟶ W.obj Y) ≃ (v.obj X ⟶ m.obj Y)`.
* `CategoryTheory.RanComparison.symm`: the comparison datum read backwards.
* `CategoryTheory.RanComparison.structuredArrowEquiv`: the induced equivalence between the two
  index categories computing the two right Kan extensions.
* `CategoryTheory.RanComparison.ranObjIso`: the induced isomorphism between the two right Kan
  extensions evaluated at a single object.

## Main results

* `CategoryTheory.ranComparisonIso`: the natural isomorphism of functors
  `(Cᵒᵖ ⥤ A) ⥤ (Oᵒᵖ ⥤ A)` between `κ.op.ran` restricted along `W.op` and `v.op.ran` restricted
  along `m.op`.
* `CategoryTheory.ranComparisonSheafIso`: the same comparison on sheaves, between the composite of
  the pushforward along the cocontinuous `κ` with the pushforward along the continuous `W`, and
  the composite of the pushforward along the cocontinuous `v` with the pushforward along the
  continuous `m`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe v₁ v₂ v₃ v₄ w' u₁ u₂ u₃ u₄ w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {O : Type u₄} [Category.{v₄} O]

/-- **A hom-set comparison between two functors out of a common source.** The datum of a
bijection `(κ.obj X ⟶ W.obj Y) ≃ (v.obj X ⟶ m.obj Y)` which is natural in both variables.

This is the minimal input identifying the right Kan extension along `κ.op`, restricted along
`W.op`, with the right Kan extension along `v.op`, restricted along `m.op`: the two Kan
extensions are computed by limits over index categories whose objects are precisely the elements
of the two hom-sets being matched. -/
structure RanComparison (κ : C ⥤ D) (v : C ⥤ E) (W : O ⥤ D) (m : O ⥤ E) where
  /-- The bijection between the hom-sets `κ.obj X ⟶ W.obj Y` and `v.obj X ⟶ m.obj Y`. -/
  equiv (X : C) (Y : O) : (κ.obj X ⟶ W.obj Y) ≃ (v.obj X ⟶ m.obj Y)
  /-- Naturality of `equiv` in the source variable `X`. -/
  equiv_comp_left {X X' : C} (g : X ⟶ X') (Y : O) (a : κ.obj X' ⟶ W.obj Y) :
    equiv X Y (κ.map g ≫ a) = v.map g ≫ equiv X' Y a
  /-- Naturality of `equiv` in the target variable `Y`. -/
  equiv_comp_right (X : C) {Y Y' : O} (b : Y ⟶ Y') (a : κ.obj X ⟶ W.obj Y) :
    equiv X Y' (a ≫ W.map b) = equiv X Y a ≫ m.map b

namespace RanComparison

variable {κ : C ⥤ D} {v : C ⥤ E} {W : O ⥤ D} {m : O ⥤ E} (h : RanComparison κ v W m)

/-- **The inverse bijections of a comparison datum are natural in the source variable.**
Apply the bijection to both sides and use its naturality together with `Equiv.apply_symm_apply`. -/
lemma symm_equiv_comp_left {X X' : C} (g : X ⟶ X') (Y : O) (b : v.obj X' ⟶ m.obj Y) :
    (h.equiv X Y).symm (v.map g ≫ b) = κ.map g ≫ (h.equiv X' Y).symm b := by
  rw [Equiv.symm_apply_eq, h.equiv_comp_left, Equiv.apply_symm_apply]

/-- **The inverse bijections of a comparison datum are natural in the target variable.**
Apply the bijection to both sides and use its naturality together with `Equiv.apply_symm_apply`. -/
lemma symm_equiv_comp_right (X : C) {Y Y' : O} (b : Y ⟶ Y') (a : v.obj X ⟶ m.obj Y) :
    (h.equiv X Y').symm (a ≫ m.map b) = (h.equiv X Y).symm a ≫ W.map b := by
  rw [Equiv.symm_apply_eq, h.equiv_comp_right, Equiv.apply_symm_apply]

/-- **A comparison datum read backwards.** The inverse bijections are again natural in both
variables, by `RanComparison.symm_equiv_comp_left` and `RanComparison.symm_equiv_comp_right`. -/
def symm : RanComparison v κ m W where
  equiv X Y := (h.equiv X Y).symm
  equiv_comp_left := h.symm_equiv_comp_left
  equiv_comp_right := h.symm_equiv_comp_right

/-- The bijections of `RanComparison.symm` are the inverses of the original bijections. -/
@[simp]
lemma symm_equiv (X : C) (Y : O) : h.symm.equiv X Y = (h.equiv X Y).symm := rfl

/-- **The comparison datum transports structured arrows.** An object of
`StructuredArrow (op (W.obj Z)) κ.op` is an object `X : C` together with a morphism
`κ.obj X ⟶ W.obj Z`; applying the bijection to that morphism, and the identity to `X`, gives an
object of `StructuredArrow (op (m.obj Z)) v.op`, and naturality in the source variable says that
this is functorial. -/
def structuredArrowFunctor (Z : O) :
    StructuredArrow (op (W.obj Z)) κ.op ⥤ StructuredArrow (op (m.obj Z)) v.op where
  obj g := StructuredArrow.mk (Y := g.right) (h.equiv g.right.unop Z g.hom.unop).op
  map {g g'} φ := StructuredArrow.homMk φ.right (by
    have hw : g'.hom.unop = κ.map φ.right.unop ≫ g.hom.unop := by
      conv_lhs => rw [← StructuredArrow.w φ]
      simp
    apply Quiver.Hom.unop_inj
    simp [hw, h.equiv_comp_left])
  map_id g := by ext; simp
  map_comp φ ψ := by ext; simp

/-- The transport of a structured arrow has the same underlying object of `Cᵒᵖ`. -/
@[simp]
lemma structuredArrowFunctor_obj_right (Z : O) (g : StructuredArrow (op (W.obj Z)) κ.op) :
    ((h.structuredArrowFunctor Z).obj g).right = g.right := rfl

/-- The morphism of the transport of a structured arrow is the image of its morphism under the
comparison bijection. -/
@[simp]
lemma structuredArrowFunctor_obj_hom (Z : O) (g : StructuredArrow (op (W.obj Z)) κ.op) :
    ((h.structuredArrowFunctor Z).obj g).hom = (h.equiv g.right.unop Z g.hom.unop).op := rfl

/-- The transport of a morphism of structured arrows has the same underlying morphism of `Cᵒᵖ`. -/
@[simp]
lemma structuredArrowFunctor_map_right (Z : O) {g g' : StructuredArrow (op (W.obj Z)) κ.op}
    (φ : g ⟶ g') : ((h.structuredArrowFunctor Z).map φ).right = φ.right := rfl

/-- **The transport of structured arrows is compatible with the projections to the source
category.**  Both functors send a structured arrow to its underlying object of `C` and a morphism
to its underlying morphism, so they are equal. -/
lemma structuredArrowFunctor_comp_proj (Z : O) :
    h.structuredArrowFunctor Z ⋙ StructuredArrow.proj (op (m.obj Z)) v.op =
      StructuredArrow.proj (op (W.obj Z)) κ.op := rfl

/-- **The two index categories computing the two right Kan extensions are equivalent.** The
functor and its inverse are the transports of structured arrows along the comparison datum and
along its inverse; the unit and counit are the identity on the underlying object of `C`, since
the two bijections are mutually inverse. -/
def structuredArrowEquiv (Z : O) :
    StructuredArrow (op (W.obj Z)) κ.op ≌ StructuredArrow (op (m.obj Z)) v.op where
  functor := h.structuredArrowFunctor Z
  inverse := h.symm.structuredArrowFunctor Z
  unitIso := NatIso.ofComponents
    (fun g => StructuredArrow.isoMk (Iso.refl _) (by
      apply Quiver.Hom.unop_inj
      simp only [Functor.id_obj, Functor.comp_obj, Iso.refl_hom, Functor.map_id,
        Category.comp_id, Quiver.Hom.unop_op, structuredArrowFunctor_obj_hom,
        structuredArrowFunctor_obj_right, symm_equiv]
      exact (Equiv.symm_apply_apply _ _).symm))
    (fun _ => StructuredArrow.ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))
  counitIso := NatIso.ofComponents
    (fun s => StructuredArrow.isoMk (Iso.refl _) (by
      apply Quiver.Hom.unop_inj
      simp only [Functor.id_obj, Functor.comp_obj, Iso.refl_hom, Functor.map_id,
        Category.comp_id, Quiver.Hom.unop_op, structuredArrowFunctor_obj_hom,
        structuredArrowFunctor_obj_right, symm_equiv]
      exact Equiv.apply_symm_apply _ _))
    (fun _ => StructuredArrow.ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp _ := StructuredArrow.ext _ _ (Category.comp_id _)

/-- The functor of `RanComparison.structuredArrowEquiv` is
`RanComparison.structuredArrowFunctor`. -/
@[simp]
lemma structuredArrowEquiv_functor (Z : O) :
    (h.structuredArrowEquiv Z).functor = h.structuredArrowFunctor Z := rfl

/-- The inverse of `RanComparison.structuredArrowEquiv` is the transport of structured arrows
along `RanComparison.symm`. -/
@[simp]
lemma structuredArrowEquiv_inverse (Z : O) :
    (h.structuredArrowEquiv Z).inverse = h.symm.structuredArrowFunctor Z := rfl

/-- The counit of `RanComparison.structuredArrowEquiv` is the identity on underlying objects. -/
@[simp]
lemma structuredArrowEquiv_counit_app_right (Z : O)
    (s : StructuredArrow (op (m.obj Z)) v.op) :
    ((h.structuredArrowEquiv Z).counit.app s).right = 𝟙 s.right := rfl

section

variable (A : Type w) [Category.{w'} A]
  [∀ P : Cᵒᵖ ⥤ A, κ.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension P]

omit [∀ P : Cᵒᵖ ⥤ A, κ.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension P] in
/-- **The transport of structured arrows is compatible with the projections, after evaluating a
presheaf.**  This is `RanComparison.structuredArrowFunctor_comp_proj` composed with `P`. -/
lemma structuredArrowFunctor_comp_proj_comp (P : Cᵒᵖ ⥤ A) (Z : O) :
    h.structuredArrowFunctor Z ⋙ StructuredArrow.proj (op (m.obj Z)) v.op ⋙ P =
      StructuredArrow.proj (op (W.obj Z)) κ.op ⋙ P := rfl

/-- **The two right Kan extensions agree at each object.** Both values are limits of `P` over a
structured-arrow category, and `RanComparison.structuredArrowEquiv` is an equivalence between
those two index categories commuting with the projections to `Cᵒᵖ`. -/
noncomputable def ranObjIso (P : Cᵒᵖ ⥤ A) (Z : O) :
    (κ.op.ran.obj P).obj (op (W.obj Z)) ≅ (v.op.ran.obj P).obj (op (m.obj Z)) :=
  κ.op.ranObjObjIsoLimit P (op (W.obj Z)) ≪≫
    HasLimit.isoOfEquivalence (h.structuredArrowEquiv Z)
      (eqToIso (h.structuredArrowFunctor_comp_proj_comp A P Z)) ≪≫
    (v.op.ranObjObjIsoLimit P (op (m.obj Z))).symm

/-- **The object-level comparison isomorphism, computed against the limit cone presenting the
target.** Composing with the leg of that cone indexed by a structured arrow `s` gives the leg
indexed by the structured arrow obtained from `s` through the inverse comparison datum. -/
@[reassoc]
lemma ranObjIso_hom_comp (P : Cᵒᵖ ⥤ A) (Z : O) (s : StructuredArrow (op (m.obj Z)) v.op) :
    (h.ranObjIso A P Z).hom ≫
        (v.op.ran.obj P).map s.hom ≫ (v.op.ranCounit.app P).app s.right =
      (κ.op.ran.obj P).map ((h.equiv s.right.unop Z).symm s.hom.unop).op ≫
        (κ.op.ranCounit.app P).app s.right := by
  simp only [ranObjIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Functor.ranObjObjIsoLimit_inv_π]
  rw [HasLimit.isoOfEquivalence_hom_π]
  change (κ.op.ranObjObjIsoLimit P (op (W.obj Z))).hom ≫
      limit.π (StructuredArrow.proj (op (W.obj Z)) κ.op ⋙ P)
          ((h.structuredArrowEquiv Z).inverse.obj s) ≫
        𝟙 ((StructuredArrow.proj (op (W.obj Z)) κ.op ⋙ P).obj
            ((h.structuredArrowEquiv Z).inverse.obj s)) ≫
          (StructuredArrow.proj (op (W.obj Z)) κ.op ⋙ P).map
            (𝟙 ((h.structuredArrowEquiv Z).inverse.obj s)) = _
  rw [Functor.map_id, Category.comp_id, Category.comp_id,
    Functor.ranObjObjIsoLimit_hom_π]
  simp

/-- **`RanComparison.ranObjIso_hom_comp` phrased for a bare morphism.** A morphism
`op (m.obj Z) ⟶ v.op.obj X` is the same thing as an object of
`StructuredArrow (op (m.obj Z)) v.op` with underlying object `X`. -/
@[reassoc]
lemma ranObjIso_hom_comp' (P : Cᵒᵖ ⥤ A) (Z : O) {X : Cᵒᵖ} (φ : op (m.obj Z) ⟶ v.op.obj X) :
    (h.ranObjIso A P Z).hom ≫ (v.op.ran.obj P).map φ ≫ (v.op.ranCounit.app P).app X =
      (κ.op.ran.obj P).map ((h.equiv X.unop Z).symm φ.unop).op ≫
        (κ.op.ranCounit.app P).app X :=
  h.ranObjIso_hom_comp A P Z (StructuredArrow.mk φ)

/-- Maps into `(v.op.ran.obj P).obj (op (m.obj Z))` are equal if they agree after composing with
every leg of the limit cone presenting it. -/
private lemma ran_obj_hom_ext (P : Cᵒᵖ ⥤ A) (Z : O) {T : A}
    (f g : T ⟶ (v.op.ran.obj P).obj (op (m.obj Z)))
    (H : ∀ s : StructuredArrow (op (m.obj Z)) v.op,
      f ≫ (v.op.ran.obj P).map s.hom ≫ (v.op.ranCounit.app P).app s.right =
        g ≫ (v.op.ran.obj P).map s.hom ≫ (v.op.ranCounit.app P).app s.right) :
    f = g := by
  refine (Iso.cancel_iso_hom_right _ _ (v.op.ranObjObjIsoLimit P (op (m.obj Z)))).mp ?_
  refine limit.hom_ext fun s => ?_
  simpa using H s

/-- **The object-level comparison isomorphisms are natural in the object of `O`.** Both sides,
tested against the limit cone presenting the target, reduce to the inverse comparison datum
applied to a composite, and the two answers agree by naturality in the target variable. -/
lemma ranObjIso_naturality (P : Cᵒᵖ ⥤ A) {Z Z' : O} (b : Z' ⟶ Z) :
    (κ.op.ran.obj P).map (W.map b).op ≫ (h.ranObjIso A P Z').hom =
      (h.ranObjIso A P Z).hom ≫ (v.op.ran.obj P).map (m.map b).op := by
  refine ran_obj_hom_ext A P Z' _ _ fun s => ?_
  have key : ((h.equiv s.right.unop Z).symm ((m.map b).op ≫ s.hom).unop).op =
      (W.map b).op ≫ ((h.equiv s.right.unop Z').symm s.hom.unop).op := by
    apply Quiver.Hom.unop_inj
    simpa using h.symm_equiv_comp_right s.right.unop b s.hom.unop
  simp only [assoc]
  rw [← Functor.map_comp_assoc (v.op.ran.obj P) (m.map b).op s.hom,
    h.ranObjIso_hom_comp', h.ranObjIso_hom_comp', key, Functor.map_comp, assoc]

/-- **The object-level comparison isomorphisms are natural in the presheaf.** Both sides, tested
against the limit cone presenting the target, reduce to the same composite once the map induced
by the morphism of presheaves is pushed through the counit of the Kan extension adjunction. -/
lemma ranObjIso_naturality_app (Z : O) {P P' : Cᵒᵖ ⥤ A} (η : P ⟶ P') :
    (κ.op.ran.map η).app (op (W.obj Z)) ≫ (h.ranObjIso A P' Z).hom =
      (h.ranObjIso A P Z).hom ≫ (v.op.ran.map η).app (op (m.obj Z)) := by
  refine ran_obj_hom_ext A P' Z _ _ fun s => ?_
  have hκ := congr_app (κ.op.ranCounit.naturality η) s.right
  have hv := congr_app (v.op.ranCounit.naturality η) s.right
  dsimp at hκ hv
  have hv' : (v.op.ran.map η).app (v.op.obj s.right) ≫ (v.op.ranCounit.app P').app s.right =
      (v.op.ranCounit.app P).app s.right ≫ η.app s.right := hv
  simp only [assoc]
  rw [h.ranObjIso_hom_comp', ← NatTrans.naturality_assoc, hκ, ← NatTrans.naturality_assoc, hv',
    h.ranObjIso_hom_comp'_assoc]

end

end RanComparison

section

variable {κ : C ⥤ D} {v : C ⥤ E} {W : O ⥤ D} {m : O ⥤ E}

/-- **The right Kan extension along `κ.op` restricted along `W.op` agrees with the right Kan
extension along `v.op` restricted along `m.op`.** This is the natural isomorphism of functors
`(Cᵒᵖ ⥤ A) ⥤ (Oᵒᵖ ⥤ A)` induced by a hom-set comparison datum: at each presheaf `P` and each
object of `O` the two values are limits of `P` over equivalent index categories
(`CategoryTheory.RanComparison.ranObjIso`), and those identifications are natural in both
arguments. -/
noncomputable def ranComparisonIso (h : RanComparison κ v W m)
    (A : Type w) [Category.{w'} A]
    [∀ P : Cᵒᵖ ⥤ A, κ.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension P] :
    κ.op.ran ⋙ (Functor.whiskeringLeft Oᵒᵖ Dᵒᵖ A).obj W.op ≅
      v.op.ran ⋙ (Functor.whiskeringLeft Oᵒᵖ Eᵒᵖ A).obj m.op :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents (fun Y => h.ranObjIso A P Y.unop)
      (fun {_ Y'} f => h.ranObjIso_naturality A P f.unop))
    (fun {_ _} η => by
      ext Y
      simpa using h.ranObjIso_naturality_app A Y.unop η)

end

section

variable {κ : C ⥤ D} {v : C ⥤ E} {W : O ⥤ D} {m : O ⥤ E}

/-- **The sheaf-level comparison of pushforwards.** For sites `(C, J)`, `(D, K)`, `(E, L)` and
`(O, M)` with `κ` and `v` cocontinuous and `W` and `m` continuous, the pushforward along `κ`
followed by the pushforward along `W` agrees with the pushforward along `v` followed by the
pushforward along `m`.

Both pushforwards are induced by the corresponding operations on presheaves, so composing with
the fully faithful inclusion `sheafToPresheaf M A` turns both composites into
`sheafToPresheaf J A` followed by the two restricted right Kan extensions compared by
`CategoryTheory.ranComparisonIso`; the inclusion may then be cancelled. -/
noncomputable def ranComparisonSheafIso (h : RanComparison κ v W m)
    (A : Type w) [Category.{w'} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    (M : GrothendieckTopology O)
    [κ.IsCocontinuous J K] [v.IsCocontinuous J L]
    [W.IsContinuous M K] [m.IsContinuous M L]
    [∀ P : Cᵒᵖ ⥤ A, κ.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension P] :
    κ.sheafPushforwardCocontinuous A J K ⋙ W.sheafPushforwardContinuous A M K ≅
      v.sheafPushforwardCocontinuous A J L ⋙ m.sheafPushforwardContinuous A M L :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf M A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J A) (ranComparisonIso h A))

end

end CategoryTheory

end
