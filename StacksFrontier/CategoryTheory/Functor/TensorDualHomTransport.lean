module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Whiskering

/-!
# Tensoring with an object as internal Hom out of its dual, through an equivalence

Let `e : D ≌ D'` be an equivalence, `T` a bifunctor on `D` and `T'` a bifunctor on `D'` with an
isomorphism `τ : T(-, -) ⋙ e ≅ T'(e -, e -)`, and on `D'` an internal Hom `H'`, an object `O`, a
transformation `β : T' ⟶ T'.flip`, the double-dual map `𝟭 ⟶ (-)^∨∨` with `(-)^∨ = H'(-, O)` and a
transformation `N ⊗ P^∨ ⟶ H'(P, N)`. Transporting `H'` along `e` gives
`H(A, B) = e⁻¹ H'(e A, e B)` on `D`, and the composite

`A ⊗ B ⟶ e⁻¹ e (A ⊗ B) ≅ e⁻¹ (e A ⊗ e B) ⟶ e⁻¹ (e B ⊗ e A) ⟶ e⁻¹ (e B ⊗ (e A)^∨∨)
  ⟶ e⁻¹ H'((e A)^∨, e B) ⟶ e⁻¹ H'(e e⁻¹ (e A)^∨, e B) = H(e⁻¹ (e A)^∨, B)`

is natural in `A` and `B`.

## Main definitions

* `CategoryTheory.Functor.tensorDualHomTransport`, with its components invertible under
  `CategoryTheory.Functor.isIso_tensorDualHomTransportApp`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {D D' : Type*} [Category D] [Category D'] (e : D ≌ D')
  (T : D ⥤ D ⥤ D) (T' : D' ⥤ D' ⥤ D') (H' : D'ᵒᵖ ⥤ D' ⥤ D') (O : D')
  (τ : Functor.uncurry.obj T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj T')
  (β : T' ⟶ T'.flip) (bid : 𝟭 D' ⟶ (H'.flip.obj O).rightOp ⋙ H'.flip.obj O)
  (jj : H'.flip.obj O ⋙ T'.flip ⟶ H')

/-- The component at `(A, B)` of `tensorDualHomTransport`. -/
def tensorDualHomTransportApp (A B : D) :
    (T.obj A).obj B ⟶ e.inverse.obj ((H'.obj (op (e.functor.obj (e.inverse.obj
      ((H'.obj (op (e.functor.obj A))).obj O))))).obj (e.functor.obj B)) :=
  e.unit.app ((T.obj A).obj B) ≫ e.inverse.map (τ.hom.app (A, B) ≫
    (β.app (e.functor.obj A)).app (e.functor.obj B) ≫
    (T'.obj (e.functor.obj B)).map (bid.app (e.functor.obj A)) ≫
    (jj.app (op ((H'.obj (op (e.functor.obj A))).obj O))).app (e.functor.obj B) ≫
    (H'.map (e.counit.app ((H'.obj (op (e.functor.obj A))).obj O)).op).app (e.functor.obj B))

/-- The components `tensorDualHomTransportApp … A B` are natural in `B`. -/
lemma tensorDualHomTransportApp_naturality_right (A : D) {B B' : D} (g : B ⟶ B') :
    (T.obj A).map g ≫ tensorDualHomTransportApp e T T' H' O τ β bid jj A B' =
      tensorDualHomTransportApp e T T' H' O τ β bid jj A B ≫
        e.inverse.map ((H'.obj (op (e.functor.obj (e.inverse.obj
          ((H'.obj (op (e.functor.obj A))).obj O))))).map (e.functor.map g)) := by
  have hτ := τ.hom.naturality (X := (A, B)) (Y := (A, B')) (Prod.mkHom (𝟙 A) g)
  have hβ := (β.app (e.functor.obj A)).naturality (e.functor.map g)
  have hT := (T'.map (e.functor.map g)).naturality (bid.app (e.functor.obj A))
  have hj := (jj.app (op ((H'.obj (op (e.functor.obj A))).obj O))).naturality (e.functor.map g)
  have hH := (H'.map (e.counit.app ((H'.obj (op (e.functor.obj A))).obj O)).op).naturality
    (e.functor.map g)
  have hu := e.unit.naturality ((T.obj A).map g)
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.comp_map, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.prod_obj,
    Functor.prod_map, Prod.mkHom, Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Functor.id_map, Functor.rightOp_obj] at hτ hβ hT hj hH hu
  simp only [tensorDualHomTransportApp, Category.assoc]
  rw [reassoc_of% hu, ← e.inverse.map_comp, ← e.inverse.map_comp]
  congr 2
  simp only [Category.assoc]
  rw [reassoc_of% hτ, reassoc_of% hβ, ← reassoc_of% hT, reassoc_of% hj, hH]

/-- **Tensoring with an object as internal Hom out of its dual, through an equivalence**: the
composite `A ⊗ B ⟶ H(e⁻¹ (e A)^∨, B)` of the module docstring, natural in `A` and `B`. -/
def tensorDualHomTransport :
    T ⟶ (e.functor ⋙ (H'.flip.obj O).rightOp ⋙ e.inverse.op) ⋙
      (e.functor.op ⋙ H' ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse) where
  app A :=
    { app B := tensorDualHomTransportApp e T T' H' O τ β bid jj A B
      naturality _ _ g := tensorDualHomTransportApp_naturality_right e T T' H' O τ β bid jj A g }
  naturality A A' f := by
    ext B
    have hτ := τ.hom.naturality (X := (A, B)) (Y := (A', B)) (Prod.mkHom f (𝟙 B))
    have hβ := congr_app (β.naturality (e.functor.map f)) (e.functor.obj B)
    have hb := bid.naturality (e.functor.map f)
    have hj := congr_app (jj.naturality
      ((H'.map (e.functor.map f).op).app O).op) (e.functor.obj B)
    have hc := e.counit.naturality ((H'.map (e.functor.map f).op).app O)
    have hu := e.unit.naturality ((T.map f).app B)
    simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.comp_map, Functor.uncurry_obj_map,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.prod_obj,
      Functor.prod_map, Prod.mkHom, Functor.flip_obj_obj, Functor.flip_obj_map,
      Functor.flip_map_app, NatTrans.comp_app, Functor.id_obj, Functor.id_map,
      Functor.rightOp_obj, Functor.rightOp_map] at hτ hβ hb hj hc hu
    simp only [NatTrans.comp_app, Functor.comp_obj, Functor.comp_map, tensorDualHomTransportApp,
      Category.assoc, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
      Functor.whiskeringLeft_obj_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.op_map, Functor.rightOp_map, Functor.rightOp_obj,
      Functor.op_obj, Functor.flip_obj_map, Functor.flip_obj_obj, Quiver.Hom.unop_op]
    rw [reassoc_of% hu, ← e.inverse.map_comp, ← e.inverse.map_comp]
    congr 1
    rw [reassoc_of% hτ, reassoc_of% hβ, ← Functor.map_comp_assoc, hb, Functor.map_comp_assoc,
      reassoc_of% hj]
    simp only [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, hc]

/-- The component of `tensorDualHomTransport` at `(A, B)` is `tensorDualHomTransportApp … A B`. -/
@[simp]
lemma tensorDualHomTransport_app_app (A B : D) :
    ((tensorDualHomTransport e T T' H' O τ β bid jj).app A).app B =
      tensorDualHomTransportApp e T T' H' O τ β bid jj A B :=
  rfl

/-- The component of `tensorDualHomTransport` at `(A, B)` is invertible as soon as the
components of `β`, of the double-dual map and of `jj` it involves are. -/
lemma isIso_tensorDualHomTransportApp (A B : D)
    (hβ : IsIso ((β.app (e.functor.obj A)).app (e.functor.obj B)))
    (hb : IsIso (bid.app (e.functor.obj A)))
    (hj : IsIso ((jj.app (op ((H'.obj (op (e.functor.obj A))).obj O))).app (e.functor.obj B))) :
    IsIso (tensorDualHomTransportApp e T T' H' O τ β bid jj A B) := by
  unfold tensorDualHomTransportApp
  infer_instance

end CategoryTheory.Functor
