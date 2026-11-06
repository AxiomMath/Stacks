module

import StacksFrontier.CategoryTheory.RelativeInertia
public import StacksCore.CategoryTheory.Inertia
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import StacksCore.Tactic.StacksAttribute


/-!
# The relative inertia as a 2-fibre product, and its fibredness (Stacks 034H)

Fix a category `C`, let `p : S ⥤ C` and `p' : S' ⥤ C` be fibred categories over `C` and
let `F : S ⥤ S'` be a 1-morphism of fibred categories over `C`. The relative inertia
`I_{S/S'}` is the canonical `CategoryTheory.RelativeInertia F` of Stacks 034I: objects are
pairs `(x, α)` with `α` an automorphism of `x` satisfying `F α = id`.

Stacks 034H has two parts. Part (1) identifies `I_{S/S'}` with the 2-fibre product
`S ×_{Δ, S ×_{S'} S, Δ} S` along the diagonal: an equivalence `Φ : I_{S/S'} ⥤ Δ ⊡ Δ`,
`(x, α) ↦ (x, x, (α, id))`, with explicit quasi-inverse `Ψ`, `(x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)`,
satisfying `Ψ ∘ Φ = 𝟭` on the nose and `Φ ∘ Ψ ≅ 𝟭` via the isomorphism with component
`(id, κ)`. Part (2) is that `I_{S/S'}`, with its structure functor `π ⋙ p`, is a fibred
category over `C`.

## Notes on the Mathlib rendering

`Limits.CategoricalPullback F G` (notation `F ⊡ G`) has as objects the triples `(a, c, e)`
with `e : F a ≅ G c`, and a morphism `(a, c, e) → (a', c', e')` is a pair `(f₁, f₂)` with
`F f₁ ≫ e' = e ≫ G f₂`. This is the base-free rendering of the underlying categories: the
"over `C`" bookkeeping is carried by the structure functors to `C` (the composites with the
projections), and "equivalence over `C`" is recorded by `Φ` and `Ψ` commuting with those
structure functors (`toDiagonalPullback_comp_proj`, `fromDiagonalPullback_comp_proj`) and
by the counit projecting to an identity (`counitIso_proj_eq_id`). Since the diagonal has no
verticality restriction on `ι`, `κ`, part (1) as stated is if anything stronger than the
source's statement in the (2,1)-category of categories over `C`.

The fibred hypotheses on `p` and `F` enter only in part (2), which is
`CategoryTheory.RelativeInertia.isFibered`; part (1) is purely 1-categorical.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {S : Type u₂} {S' : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S] [Category.{v₃} S']

namespace RelativeInertia

/-! ## The diagonal functor `Δ : S ⥤ (F ⊡ F)` -/

/-- The diagonal functor `Δ : S ⥤ F ⊡ F`, `x ↦ (x, x, id)` and `φ ↦ (φ, φ)`, into the
2-fibre product `S ×_{S'} S`. -/
@[implicit_reducible]
def diagonal (F : S ⥤ S') : S ⥤ CategoricalPullback F F where
  obj x := { fst := x, snd := x, iso := Iso.refl (F.obj x) }
  map {x y} φ := { fst := φ, snd := φ, w := by simp }

/-- The `X`-component of `Δ x` is `x`. -/
@[simp] lemma diagonal_obj_fst (F : S ⥤ S') (x : S) : ((diagonal F).obj x).fst = x := rfl
/-- The `Y`-component of `Δ x` is also `x`. -/
@[simp] lemma diagonal_obj_snd (F : S ⥤ S') (x : S) : ((diagonal F).obj x).snd = x := rfl
/-- The gluing isomorphism of `Δ x` is the identity of `F x`. -/
@[simp] lemma diagonal_obj_iso (F : S ⥤ S') (x : S) :
    ((diagonal F).obj x).iso = Iso.refl (F.obj x) := rfl
/-- The `X`-component of `Δ φ` is `φ`. -/
@[simp] lemma diagonal_map_fst (F : S ⥤ S') {x y : S} (φ : x ⟶ y) :
    ((diagonal F).map φ).fst = φ := rfl
/-- The `Y`-component of `Δ φ` is also `φ`. -/
@[simp] lemma diagonal_map_snd (F : S ⥤ S') {x y : S} (φ : x ⟶ y) :
    ((diagonal F).map φ).snd = φ := rfl

variable {F : S ⥤ S'}

/-! ## The comparison functor `Φ : I_{S/S'} ⥤ Δ ⊡ Δ` -/

/-- The isomorphism `(α, id) : (x, x, id) ≅ (x, x, id)` of `F ⊡ F` underlying `Φ (x, α)`. -/
def toDiagonalPullbackObjIso (t : RelativeInertia F) :
    (diagonal F).obj t.obj ≅ (diagonal F).obj t.obj :=
  CategoricalPullback.mkIso t.auto.asIso (Iso.refl t.obj) (by simp [t.cond])

/-- The `X`-component of the isomorphism underlying `Φ (x, α)` is `α`. -/
@[simp] lemma toDiagonalPullbackObjIso_hom_fst (t : RelativeInertia F) :
    (toDiagonalPullbackObjIso t).hom.fst = t.auto.asIso.hom := rfl

/-- The `Y`-component of the isomorphism underlying `Φ (x, α)` is the identity. -/
@[simp] lemma toDiagonalPullbackObjIso_hom_snd (t : RelativeInertia F) :
    (toDiagonalPullbackObjIso t).hom.snd = 𝟙 t.obj := rfl

/-- The `X`-component of the inverse of the isomorphism underlying `Φ (x, α)` is `α⁻¹`. -/
@[simp] lemma toDiagonalPullbackObjIso_inv_fst (t : RelativeInertia F) :
    (toDiagonalPullbackObjIso t).inv.fst = t.auto.asIso.inv := rfl

/-- The `Y`-component of the inverse of the isomorphism underlying `Φ (x, α)` is the
identity. -/
@[simp] lemma toDiagonalPullbackObjIso_inv_snd (t : RelativeInertia F) :
    (toDiagonalPullbackObjIso t).inv.snd = 𝟙 t.obj := rfl

/-- The object part of `Φ`: `(x, α) ↦ (x, x, (α, id))`. -/
@[implicit_reducible]
def toDiagonalPullbackObj (t : RelativeInertia F) :
    CategoricalPullback (diagonal F) (diagonal F) where
  fst := t.obj
  snd := t.obj
  iso := toDiagonalPullbackObjIso t

/-- The `X`-component of `Φ (x, α)` is `x`. -/
@[simp] lemma toDiagonalPullbackObj_fst (t : RelativeInertia F) :
    (toDiagonalPullbackObj t).fst = t.obj := rfl
/-- The `Y`-component of `Φ (x, α)` is also `x`. -/
@[simp] lemma toDiagonalPullbackObj_snd (t : RelativeInertia F) :
    (toDiagonalPullbackObj t).snd = t.obj := rfl

/-- The comparison functor `Φ : I_{S/S'} ⥤ Δ ⊡ Δ` of Stacks 034H (1), sending
`(x, α) ↦ (x, x, (α, id))` on objects and `φ ↦ (φ, φ)` on morphisms. -/
@[implicit_reducible]
def toDiagonalPullback (F : S ⥤ S') :
    RelativeInertia F ⥤ CategoricalPullback (diagonal F) (diagonal F) where
  obj t := toDiagonalPullbackObj t
  map {x y} f :=
    { fst := f.hom
      snd := f.hom
      w := by
        apply CategoricalPullback.hom_ext <;> simp [toDiagonalPullbackObj, f.comm] }
  map_id := by
    intro x; apply CategoricalPullback.hom_ext <;> simp [toDiagonalPullbackObj]
  map_comp := by
    intro x y z f g; apply CategoricalPullback.hom_ext <;> simp [toDiagonalPullbackObj]

/-- `Φ` acts on objects by `toDiagonalPullbackObj`. -/
@[simp] lemma toDiagonalPullback_obj (t : RelativeInertia F) :
    (toDiagonalPullback F).obj t = toDiagonalPullbackObj t := rfl
/-- `Φ` sends a morphism `φ` of the inertia to `φ` in the `X`-component. -/
@[simp] lemma toDiagonalPullback_map_fst {x y : RelativeInertia F} (f : x ⟶ y) :
    ((toDiagonalPullback F).map f).fst = f.hom := rfl
/-- `Φ` sends a morphism `φ` of the inertia to `φ` in the `Y`-component too. -/
@[simp] lemma toDiagonalPullback_map_snd {x y : RelativeInertia F} (f : x ⟶ y) :
    ((toDiagonalPullback F).map f).snd = f.hom := rfl

/-! ## The quasi-inverse `Ψ : Δ ⊡ Δ ⥤ I_{S/S'}` -/

/-- For an object `(x, y, (ι, κ))` of `Δ ⊡ Δ`, the first underlying isomorphism
`ι : x ≅ y` of `S`, read off the `fst`-component of the gluing isomorphism. -/
def diagonalPullbackFstIso (t : CategoricalPullback (diagonal F) (diagonal F)) :
    t.fst ≅ t.snd where
  hom := t.iso.hom.fst
  inv := t.iso.inv.fst
  hom_inv_id := by
    have h := congrArg CategoricalPullback.Hom.fst t.iso.hom_inv_id
    rw [CategoricalPullback.comp_fst, CategoricalPullback.id_fst] at h
    exact h
  inv_hom_id := by
    have h := congrArg CategoricalPullback.Hom.fst t.iso.inv_hom_id
    rw [CategoricalPullback.comp_fst, CategoricalPullback.id_fst] at h
    exact h

/-- The second underlying isomorphism `κ : x ≅ y` of an object `(x, y, (ι, κ))` of
`Δ ⊡ Δ`. -/
def diagonalPullbackSndIso (t : CategoricalPullback (diagonal F) (diagonal F)) :
    t.fst ≅ t.snd where
  hom := t.iso.hom.snd
  inv := t.iso.inv.snd
  hom_inv_id := by
    have h := congrArg CategoricalPullback.Hom.snd t.iso.hom_inv_id
    rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h
    exact h
  inv_hom_id := by
    have h := congrArg CategoricalPullback.Hom.snd t.iso.inv_hom_id
    rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h
    exact h

/-- The forward map of `ι` is the `fst`-component of the gluing isomorphism. -/
@[simp] lemma diagonalPullbackFstIso_hom
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (diagonalPullbackFstIso t).hom = t.iso.hom.fst := rfl
/-- The forward map of `κ` is the `snd`-component of the gluing isomorphism. -/
@[simp] lemma diagonalPullbackSndIso_hom
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (diagonalPullbackSndIso t).hom = t.iso.hom.snd := rfl
/-- The inverse of `κ` is the `snd`-component of the inverse gluing isomorphism. -/
@[simp] lemma diagonalPullbackSndIso_inv
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (diagonalPullbackSndIso t).inv = t.iso.inv.snd := rfl

/-- The equality `F ι = F κ`, extracted from the compatibility condition satisfied by the
gluing isomorphism of an object of `Δ ⊡ Δ`. -/
lemma map_fst_eq_map_snd (t : CategoricalPullback (diagonal F) (diagonal F)) :
    F.map t.iso.hom.fst = F.map t.iso.hom.snd := by
  have hw := t.iso.hom.w
  simp only [diagonal, Iso.refl_hom, Category.comp_id, Category.id_comp] at hw
  exact hw

/-- The object part of `Ψ`: `(x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)`. The automorphism is
`ι ≫ κ⁻¹`, and `F (κ⁻¹ ∘ ι) = id` follows from `F ι = F κ`. -/
@[implicit_reducible]
def fromDiagonalPullbackObj (t : CategoricalPullback (diagonal F) (diagonal F)) :
    RelativeInertia F where
  obj := t.fst
  auto := .of (diagonalPullbackFstIso t ≪≫ (diagonalPullbackSndIso t).symm)
  cond := by
    have key : F.map t.iso.hom.fst = F.map t.iso.hom.snd := map_fst_eq_map_snd t
    simp only [Iso.trans_hom, Iso.symm_hom, diagonalPullbackFstIso, diagonalPullbackSndIso,
      F.map_comp]
    rw [key, ← F.map_comp]
    have hsnd : t.iso.hom.snd ≫ t.iso.inv.snd = 𝟙 t.fst := by
      have h := congrArg CategoricalPullback.Hom.snd t.iso.hom_inv_id
      rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h
      exact h
    rw [hsnd]
    simp

/-- The underlying object of `Ψ (x, y, (ι, κ))` is `x`. -/
@[simp] lemma fromDiagonalPullbackObj_obj
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (fromDiagonalPullbackObj t).obj = t.fst := rfl

/-- The automorphism attached to `Ψ (x, y, (ι, κ))` is `κ⁻¹ ∘ ι`. -/
@[simp] lemma fromDiagonalPullbackObj_auto_hom
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (fromDiagonalPullbackObj t).auto.asIso.hom = t.iso.hom.fst ≫ t.iso.inv.snd := by
  simp [fromDiagonalPullbackObj, diagonalPullbackFstIso, diagonalPullbackSndIso]

/-- The quasi-inverse `Ψ : Δ ⊡ Δ ⥤ I_{S/S'}` of Stacks 034H (1), sending
`(x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)` on objects and `(φ, φ') ↦ φ` on morphisms. -/
@[implicit_reducible]
def fromDiagonalPullback (F : S ⥤ S') :
    CategoricalPullback (diagonal F) (diagonal F) ⥤ RelativeInertia F where
  obj t := fromDiagonalPullbackObj t
  map {x y} f :=
    { hom := f.fst
      comm := by
        have hw := f.w
        have hfst := congrArg CategoricalPullback.Hom.fst hw
        have hsnd := congrArg CategoricalPullback.Hom.snd hw
        simp only [CategoricalPullback.comp_fst, CategoricalPullback.comp_snd, diagonal]
          at hfst hsnd
        rw [fromDiagonalPullbackObj_auto_hom, fromDiagonalPullbackObj_auto_hom]
        have hyinv : y.iso.hom.snd ≫ y.iso.inv.snd = 𝟙 y.fst := by
          have h := congrArg CategoricalPullback.Hom.snd y.iso.hom_inv_id
          rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h; exact h
        have hxinv : x.iso.inv.snd ≫ x.iso.hom.snd = 𝟙 x.snd := by
          have h := congrArg CategoricalPullback.Hom.snd x.iso.inv_hom_id
          rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h; exact h
        have e1 : x.iso.inv.snd ≫ f.fst ≫ y.iso.hom.snd = f.snd := by
          rw [hsnd, ← Category.assoc, hxinv]; simp
        have step : f.snd ≫ y.iso.inv.snd = x.iso.inv.snd ≫ f.fst := by
          rw [← e1, Category.assoc, Category.assoc, hyinv, Category.comp_id]
        rw [← Category.assoc, hfst, Category.assoc, step]
        simp }
  map_id := by intro x; apply RelativeInertiaHom.ext; simp
  map_comp := by intro x y z f g; apply RelativeInertiaHom.ext; simp

/-- `Ψ` acts on objects by `fromDiagonalPullbackObj`. -/
@[simp] lemma fromDiagonalPullback_obj (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (fromDiagonalPullback F).obj t = fromDiagonalPullbackObj t := rfl
/-- `Ψ` sends a morphism `(φ, φ')` to its `X`-component `φ`. -/
@[simp] lemma fromDiagonalPullback_map_hom
    {x y : CategoricalPullback (diagonal F) (diagonal F)} (f : x ⟶ y) :
    ((fromDiagonalPullback F).map f).hom = f.fst := rfl

/-- `Ψ ∘ Φ = 𝟭`: the composite of the comparison functor with its quasi-inverse is the
identity of `I_{S/S'}` on the nose. -/
theorem fromDiagonalPullback_comp_toDiagonalPullback (F : S ⥤ S') :
    toDiagonalPullback F ⋙ fromDiagonalPullback F = 𝟭 (RelativeInertia F) := by
  refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y f => ?_)
  · refine RelativeInertia.obj_ext rfl ?_
    simp [toDiagonalPullback, fromDiagonalPullback, fromDiagonalPullbackObj,
      toDiagonalPullbackObj, diagonalPullbackFstIso, diagonalPullbackSndIso]
  · apply RelativeInertiaHom.ext
    simp

/-- The component at `(x, y, (ι, κ))` of the isomorphism `Φ ∘ Ψ ≅ 𝟭`: the isomorphism
`(id_x, κ) : (x, x, (κ⁻¹ ∘ ι, id_x)) ≅ (x, y, (ι, κ))` of `Δ ⊡ Δ`. -/
def counitIsoApp (t : CategoricalPullback (diagonal F) (diagonal F)) :
    (fromDiagonalPullback F ⋙ toDiagonalPullback F).obj t ≅ t :=
  CategoricalPullback.mkIso (Iso.refl t.fst) (diagonalPullbackSndIso t)
    (by
      apply CategoricalPullback.hom_ext
      · rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
        simp only [Functor.comp_obj, toDiagonalPullback_obj, toDiagonalPullbackObj,
          toDiagonalPullbackObjIso_hom_fst, diagonal_map_fst,
          Iso.refl_hom, fromDiagonalPullback_obj, fromDiagonalPullbackObj_auto_hom,
          diagonalPullbackSndIso_hom]
        have hxinv : t.iso.inv.snd ≫ t.iso.hom.snd = 𝟙 t.snd := by
          have h := congrArg CategoricalPullback.Hom.snd t.iso.inv_hom_id
          rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h; exact h
        rw [Category.assoc, hxinv]; simp
      · rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
        simp only [Functor.comp_obj, toDiagonalPullback_obj, toDiagonalPullbackObj,
          toDiagonalPullbackObjIso_hom_snd, diagonal_map_snd,
          Iso.refl_hom, diagonalPullbackSndIso_hom]
        simp)

/-- `Φ ∘ Ψ ≅ 𝟭` via the natural isomorphism whose component at `(x, y, (ι, κ))` is
`(id_x, κ)`. -/
def counitIso (F : S ⥤ S') :
    fromDiagonalPullback F ⋙ toDiagonalPullback F
      ≅ 𝟭 (CategoricalPullback (diagonal F) (diagonal F)) :=
  NatIso.ofComponents counitIsoApp (by
    intro x y f
    apply CategoricalPullback.hom_ext
    · rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, counitIsoApp,
        CategoricalPullback.mkIso_hom_fst, Iso.refl_hom, toDiagonalPullback_map_fst,
        fromDiagonalPullback_map_hom]
      simp
    · rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, counitIsoApp,
        CategoricalPullback.mkIso_hom_snd, diagonalPullbackSndIso_hom,
        toDiagonalPullback_map_snd, fromDiagonalPullback_map_hom]
      have hw := f.w
      have hsnd := congrArg CategoricalPullback.Hom.snd hw
      simp only [CategoricalPullback.comp_snd, diagonal] at hsnd
      exact hsnd)

/-- The `fst`-component of the counit at `(x, y, (ι, κ))` is `id_x`. -/
@[simp] lemma counitIso_app_hom_fst (t : CategoricalPullback (diagonal F) (diagonal F)) :
    ((counitIso F).hom.app t).fst = 𝟙 t.fst := by
  simp [counitIso, counitIsoApp]

/-- The `snd`-component of the counit at `(x, y, (ι, κ))` is `κ`. -/
@[simp] lemma counitIso_app_hom_snd (t : CategoricalPullback (diagonal F) (diagonal F)) :
    ((counitIso F).hom.app t).snd = t.iso.hom.snd := by
  simp [counitIso, counitIsoApp, diagonalPullbackSndIso]

/-- The comparison functor `Φ : I_{S/S'} ⥤ Δ ⊡ Δ` is an equivalence of categories, with explicit
quasi-inverse `Ψ`, unit coming from the equality `Ψ ∘ Φ = 𝟭` and counit the isomorphism with
component `(id, κ)`. -/
@[stacks 034H "(1)"]
def diagonalPullbackEquivalence (F : S ⥤ S') :
    RelativeInertia F ≌ CategoricalPullback (diagonal F) (diagonal F) :=
  CategoryTheory.Equivalence.mk (toDiagonalPullback F) (fromDiagonalPullback F)
    (eqToIso (fromDiagonalPullback_comp_toDiagonalPullback F).symm)
    (counitIso F)

/-- The forward functor of the equivalence is `Φ`. -/
@[simp] lemma diagonalPullbackEquivalence_functor (F : S ⥤ S') :
    (diagonalPullbackEquivalence F).functor = toDiagonalPullback F := rfl
/-- The inverse functor of the equivalence is `Ψ`. -/
@[simp] lemma diagonalPullbackEquivalence_inverse (F : S ⥤ S') :
    (diagonalPullbackEquivalence F).inverse = fromDiagonalPullback F := rfl

/-- The comparison functor `Φ` is an equivalence of categories. -/
theorem toDiagonalPullback_isEquivalence (F : S ⥤ S') : (toDiagonalPullback F).IsEquivalence :=
  (diagonalPullbackEquivalence F).isEquivalence_functor

/-! ### Compatibility of the equivalence with the structure functors to `C` -/

/-- The structure functor to `C` of the target `Δ ⊡ Δ`: the first projection followed
by `p`. -/
abbrev diagonalPullbackProj (F : S ⥤ S') (p : S ⥤ C) :
    CategoricalPullback (diagonal F) (diagonal F) ⥤ C :=
  CategoricalPullback.π₁ (diagonal F) (diagonal F) ⋙ p

section StructureFunctors

-- `Functor.ext` leaves `eqToHom`s between `(Φ ⋙ π₁ ⋙ p).obj x` and `p.obj x.obj`, which agree
-- only after unfolding `CategoricalPullback.π₁` and `RelativeInertia.π`.
set_option backward.isDefEq.respectTransparency false

/-- `Φ` commutes on the nose with the structure functors to `C`. -/
theorem toDiagonalPullback_comp_proj (F : S ⥤ S') (p : S ⥤ C) :
    toDiagonalPullback F ⋙ diagonalPullbackProj F p = RelativeInertia.π F ⋙ p := by
  apply CategoryTheory.Functor.ext
  · intro x y f; simp [diagonalPullbackProj, CategoricalPullback.π₁]
  · intro x; rfl

/-- `Ψ` commutes on the nose with the structure functors to `C`. -/
theorem fromDiagonalPullback_comp_proj (F : S ⥤ S') (p : S ⥤ C) :
    fromDiagonalPullback F ⋙ (RelativeInertia.π F ⋙ p) = diagonalPullbackProj F p := by
  apply CategoryTheory.Functor.ext
  · intro x y f; simp [diagonalPullbackProj, CategoricalPullback.π₁, RelativeInertia.π]
  · intro x; rfl

end StructureFunctors

/-- Every component of the counit projects to an identity of `C`, i.e. it is a 2-morphism
in the (2,1)-category of categories over `C`. -/
theorem counitIso_proj_eq_id (F : S ⥤ S') (p : S ⥤ C)
    (t : CategoricalPullback (diagonal F) (diagonal F)) :
    p.map ((CategoricalPullback.π₁ (diagonal F) (diagonal F)).map
      ((counitIso F).hom.app t)) = 𝟙 (p.obj t.fst) := by
  have h : (CategoricalPullback.π₁ (diagonal F) (diagonal F)).map
      ((counitIso F).hom.app t) = 𝟙 t.fst := by
    simp [CategoricalPullback.π₁]
  exact (congrArg p.map h).trans (p.map_id t.fst)

/-! ## Part (2): the relative inertia is fibred over `C` -/

/-- For an object `(x, α)` of the relative inertia, the automorphism `α` projects to the
identity under the structure functor `p` to `C`: indeed `p = F ⋙ p'` and `F α = 𝟙`. -/
theorem struct_map_auto_eq_id (p : S ⥤ C) (p' : S' ⥤ C) (hF : F ⋙ p' = p)
    (t : RelativeInertia F) : p.map t.auto.asIso.hom = 𝟙 (p.obj t.obj) := by
  subst hF
  simp [t.cond]

add_to_stacks 034H "(2)" CategoryTheory.RelativeInertia.isFibered

end RelativeInertia

end CategoryTheory
