module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Maps of stalks induced by maps of sections over the refinements of one neighbourhood

Let `Φ` be a point of a site `(C, J)`, `V` an object of `C` with `v` in the fibre of `Φ` at `V`,
and `P`, `Q` presheaves of abelian groups on `C`. Additive maps `f_g : P(W) ⟶ Q(W)`, one for each
morphism `g : W ⟶ V`, compatible with restriction, induce an additive map of stalks `P_Φ ⟶ Q_Φ`
(`Stacks.EtaleCohomology.Purity.presheafFiberOverMap`) sending the germ of `z` at a point `w` over
`v` to the germ of `f_g z` (`Stacks.EtaleCohomology.Purity.presheafFiberOverMap_germ`): every germ
is the germ of a section over a refinement of `V`, and two refinements are dominated by a third one
on which the two morphisms to `V` agree, the category of elements of the fibre being cofiltered. It
is bijective when every `f_g` is (`Stacks.EtaleCohomology.Purity.bijective_presheafFiberOverMap`).

The typical `f_g` are the components over the refinements of `V` of a morphism between the
restrictions of `P` and `Q` to the slice over `V`, or the value of a local operation such as
the evaluation of a local morphism at a section over `V`.

## Main definitions

* `Stacks.EtaleCohomology.Purity.presheafFiberOverMap`: the additive map of stalks `P_Φ ⟶ Q_Φ`
  induced by compatible additive maps `f_g`.

## Main results

* `Stacks.EtaleCohomology.Purity.presheafFiberOverMap_germ`: the map sends the germ of `z` at a
  point over `v` to the germ of `f_g z`.
* `Stacks.EtaleCohomology.Purity.bijective_presheafFiberOverMap`: the map is bijective when every
  `f_g` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite GrothendieckTopology

universe w v u t

namespace Stacks.EtaleCohomology.Purity

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

/-- Two points of the fibre are dominated by a common one. -/
theorem exists_fiber_cone_of_point {U U' : C} (u : Φ.fiber.obj U) (u' : Φ.fiber.obj U') :
    ∃ (W : C) (w : Φ.fiber.obj W) (g : W ⟶ U) (g' : W ⟶ U'),
      Φ.fiber.map g w = u ∧ Φ.fiber.map g' w = u' := by
  obtain ⟨W, f, f', -⟩ := @IsCofilteredOrEmpty.cone_objs Φ.fiber.Elements _ _
    (Φ.fiber.elementsMk U u) (Φ.fiber.elementsMk U' u')
  exact ⟨W.obj, W.val, f.hom, f'.hom, f.map_val, f'.map_val⟩

/-- Two morphisms to `V` sending a point of the fibre to the same point are equalized on a
refinement of that point. -/
theorem exists_fiber_equalizer {W V : C} (w : Φ.fiber.obj W) (g g' : W ⟶ V)
    (h : Φ.fiber.map g w = Φ.fiber.map g' w) :
    ∃ (W' : C) (w' : Φ.fiber.obj W') (a : W' ⟶ W), Φ.fiber.map a w' = w ∧ a ≫ g = a ≫ g' := by
  let e : Φ.fiber.elementsMk W w ⟶ Φ.fiber.elementsMk V (Φ.fiber.map g w) := Functor.Elements.homMk g rfl
  let e' : Φ.fiber.elementsMk W w ⟶ Φ.fiber.elementsMk V (Φ.fiber.map g w) := Functor.Elements.homMk g' h.symm
  obtain ⟨W', a, ha⟩ := @IsCofilteredOrEmpty.cone_maps Φ.fiber.Elements _ _ _ _ e e'
  exact ⟨W'.obj, W'.val, a.hom, a.map_val, congrArg Functor.Elements.Hom.hom ha⟩

variable [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} AddCommGrpCat.{t}]
  [PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{t})]
  {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{t}} {V : C} (v : Φ.fiber.obj V)
  (f : ∀ {W : C}, (W ⟶ V) → ToType (P.obj (op W)) →+ ToType (Q.obj (op W)))
  (hf : ∀ {W W' : C} (g : W ⟶ V) (h : W' ⟶ W) (z : ToType (P.obj (op W))),
    f (h ≫ g) (P.map h.op z) = Q.map h.op (f g z))

omit [LocallySmall.{w} C] [PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{t})] in
include hf in
/-- The germ of `f_g z` does not depend on the morphism `g` to `V` sending the point to `v`. -/
theorem toPresheafFiber_overMap_eq_of_eq {W : C} (w : Φ.fiber.obj W) (g g' : W ⟶ V)
    (h : Φ.fiber.map g w = Φ.fiber.map g' w) (z : ToType (P.obj (op W))) :
    Φ.toPresheafFiber W w Q (f g z) = Φ.toPresheafFiber W w Q (f g' z) := by
  obtain ⟨W', w', a, rfl, ha⟩ := exists_fiber_equalizer Φ w g g' h
  rw [← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply, ← hf, ← hf, ha]

include hf in
/-- The germ of `f_g z` depends only on the germ of `z`. -/
theorem toPresheafFiber_overMap_eq {W₁ W₂ : C} (w₁ : Φ.fiber.obj W₁) (w₂ : Φ.fiber.obj W₂)
    (g₁ : W₁ ⟶ V) (g₂ : W₂ ⟶ V) (h₁ : Φ.fiber.map g₁ w₁ = v) (h₂ : Φ.fiber.map g₂ w₂ = v)
    (z₁ : ToType (P.obj (op W₁))) (z₂ : ToType (P.obj (op W₂)))
    (hz : Φ.toPresheafFiber W₁ w₁ P z₁ = Φ.toPresheafFiber W₂ w₂ P z₂) :
    Φ.toPresheafFiber W₁ w₁ Q (f g₁ z₁) = Φ.toPresheafFiber W₂ w₂ Q (f g₂ z₂) := by
  obtain ⟨W, w, a, b, rfl, rfl⟩ := exists_fiber_cone_of_point Φ w₁ w₂
  rw [← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply] at hz
  obtain ⟨Y, c, y, rfl, hc⟩ := (Φ.toPresheafFiber_eq_iff' W _ _ _).1 hz
  rw [← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply, ← hf, ← hf,
    ← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply (f := c), ← hf, ← hf]
  have e : Φ.fiber.map (c ≫ a ≫ g₁) y = Φ.fiber.map (c ≫ b ≫ g₂) y := by
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, h₁, h₂]
  refine (toPresheafFiber_overMap_eq_of_eq Φ f hf y _ _ e _).trans ?_
  congr 2

/-- Two germs are represented by sections over one refinement of `V`. -/
private theorem exists_germ_over_two (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (W : C) (w : Φ.fiber.obj W) (g : W ⟶ V) (z₁ z₂ : ToType (P.obj (op W))),
      Φ.fiber.map g w = v ∧ Φ.toPresheafFiber W w P z₁ = p₁ ∧
        Φ.toPresheafFiber W w P z₂ = p₂ := by
  obtain ⟨X, x, z₁, z₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ p₁ p₂
  obtain ⟨W, w, a, b, rfl, hb⟩ := exists_fiber_cone_of_point Φ x v
  exact ⟨W, w, b, P.map a.op z₁, P.map a.op z₂, hb, Φ.toPresheafFiber_w_apply a w P z₁,
    Φ.toPresheafFiber_w_apply a w P z₂⟩

/-- A representative of a germ by a section over a refinement of `V`. -/
theorem exists_germ_over (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (W : C) (w : Φ.fiber.obj W) (g : W ⟶ V) (z : ToType (P.obj (op W))),
      Φ.fiber.map g w = v ∧ Φ.toPresheafFiber W w P z = p := by
  obtain ⟨W, w, g, z, -, hg, h, -⟩ := exists_germ_over_two Φ v p p
  exact ⟨W, w, g, z, hg, h⟩

/-- Two germs are represented by sections over one refinement of `V`. -/
theorem exists_germ_over₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (W : C) (w : Φ.fiber.obj W) (g : W ⟶ V) (z₁ z₂ : ToType (P.obj (op W))),
      Φ.fiber.map g w = v ∧ Φ.toPresheafFiber W w P z₁ = p₁ ∧
        Φ.toPresheafFiber W w P z₂ = p₂ :=
  exists_germ_over_two Φ v p₁ p₂

/-- The function underlying `Stacks.EtaleCohomology.Purity.presheafFiberOverMap`. -/
def presheafFiberOverFun (p : ToType (Φ.presheafFiber.obj P)) :
    ToType (Φ.presheafFiber.obj Q) :=
  Φ.toPresheafFiber (exists_germ_over Φ v p).choose (exists_germ_over Φ v p).choose_spec.choose Q
    (f (exists_germ_over Φ v p).choose_spec.choose_spec.choose
      (exists_germ_over Φ v p).choose_spec.choose_spec.choose_spec.choose)

include hf in
/-- `presheafFiberOverFun` sends the germ of `z` at a point `w` over `v` along `g` to the germ
of `f g z`. -/
theorem presheafFiberOverFun_germ {W : C} (w : Φ.fiber.obj W) (g : W ⟶ V)
    (hg : Φ.fiber.map g w = v) (z : ToType (P.obj (op W))) :
    presheafFiberOverFun Φ v f (Φ.toPresheafFiber W w P z) = Φ.toPresheafFiber W w Q (f g z) :=
  have h := (exists_germ_over Φ v (Φ.toPresheafFiber W w P z)).choose_spec.choose_spec.choose_spec
  toPresheafFiber_overMap_eq Φ v f hf _ _ _ _ h.choose_spec.1 hg _ _ h.choose_spec.2

/-- **The map of stalks induced by compatible additive maps on the sections over the refinements
of a neighbourhood `V` of the point.** -/
def presheafFiberOverMap : ToType (Φ.presheafFiber.obj P) →+ ToType (Φ.presheafFiber.obj Q) where
  toFun := presheafFiberOverFun Φ v f
  map_zero' := by
    obtain ⟨W, w, g, z, hg, -⟩ := exists_germ_over Φ v (0 : ToType (Φ.presheafFiber.obj P))
    have h0 : Φ.toPresheafFiber W w P 0 = 0 := map_zero _
    rw [← h0, presheafFiberOverFun_germ Φ v f hf w g hg, map_zero, map_zero]
  map_add' p₁ p₂ := by
    obtain ⟨W, w, g, z₁, z₂, hg, rfl, rfl⟩ := exists_germ_over₂ Φ v p₁ p₂
    rw [← map_add, presheafFiberOverFun_germ Φ v f hf w g hg,
      presheafFiberOverFun_germ Φ v f hf w g hg, presheafFiberOverFun_germ Φ v f hf w g hg,
      map_add, map_add]

/-- `presheafFiberOverMap` sends the germ of `z` at a point `w` over `v` along `g` to the germ of
`f g z`. -/
theorem presheafFiberOverMap_germ {W : C} (w : Φ.fiber.obj W) (g : W ⟶ V)
    (hg : Φ.fiber.map g w = v) (z : ToType (P.obj (op W))) :
    presheafFiberOverMap Φ v f hf (Φ.toPresheafFiber W w P z) = Φ.toPresheafFiber W w Q (f g z) :=
  presheafFiberOverFun_germ Φ v f hf w g hg z

/-- `presheafFiberOverMap` is bijective when every `f g` is. -/
theorem bijective_presheafFiberOverMap (hb : ∀ {W : C} (g : W ⟶ V), Function.Bijective (f g)) :
    Function.Bijective (presheafFiberOverMap Φ v f hf) := by
  constructor
  · intro p₁ p₂ h
    obtain ⟨W, w, g, z₁, z₂, hg, rfl, rfl⟩ := exists_germ_over₂ Φ v p₁ p₂
    rw [presheafFiberOverMap_germ Φ v f hf w g hg, presheafFiberOverMap_germ Φ v f hf w g hg] at h
    obtain ⟨Y, c, y, rfl, hc⟩ := (Φ.toPresheafFiber_eq_iff' W _ _ _).1 h
    rw [← hf, ← hf] at hc
    rw [← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply, (hb (c ≫ g)).1 hc]
  · intro q
    obtain ⟨W, w, g, z, hg, rfl⟩ := exists_germ_over Φ v q
    obtain ⟨y, hy⟩ := (hb g).2 z
    exact ⟨Φ.toPresheafFiber W w P y, by rw [presheafFiberOverMap_germ Φ v f hf w g hg, hy]⟩

end Stacks.EtaleCohomology.Purity

end
