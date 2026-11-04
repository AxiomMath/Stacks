module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Fibres of `TwoFibreProductOver` (Stacks 02XI)

Stacks 02XI says that the fibre of a 2-fibre product of categories over `𝒞`, taken at an object
`U` of `𝒞`, is the 2-fibre product of the fibre categories. It is proved in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres` for the model
`CategoryTheory.Limits.CategoricalPullbackOver`, but the 2-fibre product the rest of the
development is built from is `CategoryTheory.TwoFibreProductOver`, so this file states 02XI for
that one.

The two models differ only in how a morphism records its base: `CategoricalPullbackOver.Hom`
carries the equation saying the two components induce the same morphism of `𝒞`, whereas
`TwoFibreProductOver.Hom` carries the base morphism as data together with the two `IsHomLift`
witnesses. The second shape is the one that makes the comparison here cheap: a morphism of the
fibre at `U` is one whose base morphism is `𝟙 U`, which is exactly a pair of morphisms of the
fibre categories.

The comparison functors `toFiberPullback` and `ofFiberPullback` are mutually inverse, so the
fibre `(𝒳 ×_𝒮 𝒴)_U` is *isomorphic*, not merely equivalent, to
`𝒳_U ×_{𝒮_U} 𝒴_U`; `fiberEquiv` packages that as an equivalence of categories.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒮 : Type u₄} [Category.{v₄} 𝒮]
variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

namespace TwoFibreProductOver

open Limits


/-- **Stacks 02XI.** The canonical functor `(𝒳 ×_𝒮 𝒴)_U ⥤ 𝒳_U ×_{𝒮_U} 𝒴_U`, sending
`(U, x, y, φ)` to `(x, y, φ)` and `(a, b)` to `(a, b)`. -/
@[stacks 02XI, implicit_reducible]
def toFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U ⥤
      CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U) where
  obj P :=
    { fst := ⟨P.1.x, P.1.hx.trans P.2⟩
      snd := ⟨P.1.y, P.1.hy.trans P.2⟩
      iso := Functor.fiberIsoOfLift p𝒮 P.1.iso (by
        have hb : P.1.base = U := P.2
        have := P.1.vertical; rw [hb] at this; exact this) }
  map {P Q} φ :=
    { fst := ⟨Hom.a φ.1, isHomLift_a φ.1 (𝟙 U) φ.2⟩
      snd := ⟨Hom.b φ.1, isHomLift_b φ.1 (𝟙 U) φ.2⟩
      w := Subtype.ext φ.1.w }
  map_id P := by apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl
  map_comp {P Q R} φ ψ := by apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl

/-- **Stacks 02XI.** The canonical functor `𝒳_U ×_{𝒮_U} 𝒴_U ⥤ (𝒳 ×_𝒮 𝒴)_U` inverse to
`toFiberPullback`, sending `(x, y, φ)` to `(U, x, y, φ)` and `(a, b)` to `(a, b)` over `𝟙 U`. -/
@[stacks 02XI, implicit_reducible]
def ofFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U) ⥤
      (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U where
  obj T :=
    ⟨{ base := U
       x := T.fst.1
       y := T.snd.1
       hx := T.fst.2
       hy := T.snd.2
       iso := { hom := T.iso.hom.1, inv := T.iso.inv.1,
                hom_inv_id := congrArg Subtype.val T.iso.hom_inv_id
                inv_hom_id := congrArg Subtype.val T.iso.inv_hom_id }
       vertical := T.iso.hom.2 }, rfl⟩
  map {T T'} m :=
    ⟨{ hbase := 𝟙 U
       a := m.fst.1
       b := m.snd.1
       ha := m.fst.2
       hb := m.snd.2
       w := congrArg Subtype.val m.w }, IsHomLift.of_fac' _ (𝟙 U) _ rfl rfl
        (((Category.id_comp (𝟙 U ≫ 𝟙 U)).trans (Category.id_comp (𝟙 U))).symm)⟩
  map_id T := by apply Subtype.ext; apply Hom.ext' <;> rfl
  map_comp {T T' T''} m m' := by
    apply Subtype.ext; apply Hom.ext' <;> rfl

/-! ### The explicit formulas for the two comparison functors -/

/-- `toFiberPullback` keeps the `𝒳`-component of an object unchanged. -/
@[simp] theorem toFiberPullback_obj_fst (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).fst.1 = P.1.x := rfl

/-- `toFiberPullback` keeps the `𝒴`-component of an object unchanged. -/
@[simp] theorem toFiberPullback_obj_snd (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).snd.1 = P.1.y := rfl

/-- `toFiberPullback` keeps the comparison isomorphism unchanged; only its ambient category
changes, from `𝒮` to the fibre `𝒮_U`. -/
@[simp] theorem toFiberPullback_obj_iso (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).iso.hom.1 = P.1.iso.hom := rfl

/-- `toFiberPullback` keeps the `𝒳`-component of a morphism unchanged. -/
@[simp] theorem toFiberPullback_map_fst (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U} (φ : P ⟶ Q) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).map φ).fst.1 = Hom.a φ.1 := rfl

/-- `toFiberPullback` keeps the `𝒴`-component of a morphism unchanged. -/
@[simp] theorem toFiberPullback_map_snd (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U} (φ : P ⟶ Q) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).map φ).snd.1 = Hom.b φ.1 := rfl

/-- `ofFiberPullback` reinstates the base object as the literal `U`. -/
@[simp] theorem ofFiberPullback_obj_base (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (T : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)) :
    ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj T).1.base = U := rfl

/-- `ofFiberPullback` keeps the `𝒳`-component of an object unchanged. -/
@[simp] theorem ofFiberPullback_obj_x (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (T : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)) :
    ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj T).1.x = T.fst.1 := rfl

/-- `ofFiberPullback` keeps the `𝒴`-component of an object unchanged. -/
@[simp] theorem ofFiberPullback_obj_y (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (T : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)) :
    ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj T).1.y = T.snd.1 := rfl

/-- `ofFiberPullback` keeps the comparison isomorphism unchanged, reading it in `𝒮` rather than
in the fibre `𝒮_U`. -/
@[simp] theorem ofFiberPullback_obj_iso (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    (T : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)) :
    ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj T).1.iso.hom = T.iso.hom.1 := rfl

/-- `ofFiberPullback` keeps the `𝒳`-component of a morphism unchanged. -/
@[simp] theorem ofFiberPullback_map_a (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    {T T' : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)}
    (m : T ⟶ T') : Hom.a ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).map m).1 = m.fst.1 := rfl

/-- `ofFiberPullback` keeps the `𝒴`-component of a morphism unchanged. -/
@[simp] theorem ofFiberPullback_map_b (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)
    {T T' : CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)}
    (m : T ⟶ T') : Hom.b ((ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).map m).1 = m.snd.1 := rfl

/-- The underlying morphism of a composite in a `structureFunctor`-fibre is the composite of the
underlying morphisms. -/
theorem fiber_coe_comp {U : 𝒞} {A B D : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U}
    (g : A ⟶ B) (k : B ⟶ D) : ((g ≫ k).1 : A.1 ⟶ D.1) = g.1 ≫ k.1 := rfl

/-- The underlying morphism of an `eqToHom` in a `structureFunctor`-fibre is an `eqToHom`. -/
theorem fiber_coe_eqToHom {U : 𝒞} {A B : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U} (e : A = B) :
    ((eqToHom e : A ⟶ B).1 : A.1 ⟶ B.1) = eqToHom (congrArg Subtype.val e) := by
  cases e; rfl

/-- **Stacks 02XI.** Composing the comparison functor with its inverse gives the identity on the
fibre `(𝒳 ×_𝒮 𝒴)_U`: the round trip forgets the base object and reinstates it as the literal
`U`, which is the same object because it lies over `U`, and both functors are the identity on the
underlying pair of components. -/
@[stacks 02XI]
theorem toFiberPullback_comp_ofFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙ ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun P => ?_) (fun P Q φ => ?_)
  · obtain ⟨P, hP⟩ := P
    cases hP
    rfl
  · apply Subtype.ext
    apply Hom.ext' <;> simp [fiber_coe_comp, fiber_coe_eqToHom]

/-- **Stacks 02XI.** Composing the inverse comparison functor with the comparison functor gives
the identity on `𝒳_U ×_{𝒮_U} 𝒴_U`: the base coordinate `U` is added and then forgotten, so the
triple `(x, y, φ)` is rebuilt unchanged. Together with `toFiberPullback_comp_ofFiberPullback`
this says the fibre of the 2-fibre product over `𝒞` at `U` is *isomorphic*, not merely
equivalent, to the 2-fibre product of the fibres. -/
@[stacks 02XI]
theorem ofFiberPullback_comp_toFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙ toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U = 𝟭 _ := by
  apply Functor.hext
  · intro T
    rfl
  · intro T T' m
    rfl

/-- **Stacks 02XI**, as an equivalence of categories: the fibre of the 2-fibre product over `𝒞`
at `U` is the 2-fibre product of the fibre categories. Both unit and counit are identities, the
two functors being strictly mutually inverse. -/
@[stacks 02XI]
def fiberEquiv (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U ≌
      CategoricalPullback (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U) where
  functor := toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U
  inverse := ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U
  unitIso := eqToIso (toFiberPullback_comp_ofFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).symm
  counitIso := eqToIso (ofFiberPullback_comp_toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U)
  functor_unitIso_comp X := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

end TwoFibreProductOver

end CategoryTheory
