module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Conjugating a pseudofunctor by dualities

Let `D_A : Aᵒᵖ ⥤ A`, `D_B : Bᵒᵖ ⥤ B`, … be contravariant functors with biduality morphisms
`η : 𝟭 ⟶ D ∘ D`, and let `P_f : B ⥤ A`, `P_g : C ⥤ B`, … be functors with composition
isomorphisms `P_g ⋙ P_f ≅ P_{f ≫ g}` satisfying the associativity of a pseudofunctor. The
conjugates `f^! = D_A ∘ P_f ∘ D_B` then come with comparison morphisms
`f^! ∘ g^! ⟶ (f ≫ g)^!`, the composition isomorphism of the `P` preceded by `η` in the middle,
and these satisfy the associativity of a pseudofunctor; with an identification `P_𝟙 ≅ 𝟭` and the
triangle identity `η_{D X} ≫ D(η_X) = 1` they also satisfy the two unit laws.

In a closed symmetric monoidal category `D = [-, ω]` has the biduality morphism
`X ⟶ [[X, ω], ω]`, the transpose of the evaluation after the symmetry, and it satisfies the
triangle identity (`closedBiduality_triangle`).

## Main definitions

* `CategoryTheory.dualConj` — `D_A ∘ P ∘ D_B`.
* `CategoryTheory.dualConjComp` — the comparison `g^! ⋙ f^! ⟶ (f ≫ g)^!`.
* `CategoryTheory.dualConjUnit` — the comparison `𝟭 ⟶ 𝟙^!`.
* `CategoryTheory.MonoidalClosed.closedBiduality` — the biduality `X ⟶ [[X, ω], ω]`.

## Main results

* `CategoryTheory.dualConjComp_assoc`, `CategoryTheory.dualConjUnit_comp_dualConjComp`,
  `CategoryTheory.map_dualConjUnit_comp_dualConjComp` — the pseudofunctor laws.
* `CategoryTheory.MonoidalClosed.closedBiduality_triangle` — the triangle identity.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 003F](https://stacks.math.columbia.edu/tag/003F)
-/

@[expose] public section

open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

/-- The conjugate `D_A ∘ P ∘ D_B` of a functor `P : B ⥤ A` by two contravariant functors. -/
abbrev dualConj (DA : Aᵒᵖ ⥤ A) (DB : Bᵒᵖ ⥤ B) (P : B ⥤ A) : B ⥤ A :=
  DB.rightOp ⋙ P.op ⋙ DA

/-- The action of `dualConj DA DB P` on a morphism `φ` is `D_A (P (D_B φ))`. -/
theorem dualConj_map (DA : Aᵒᵖ ⥤ A) (DB : Bᵒᵖ ⥤ B) (P : B ⥤ A) {M M' : B} (φ : M ⟶ M') :
    (dualConj DA DB P).map φ = DA.map (P.map (DB.map φ.op)).op :=
  rfl

variable {DA : Aᵒᵖ ⥤ A} {DB : Bᵒᵖ ⥤ B} {DC : Cᵒᵖ ⥤ C} {DD : Dᵒᵖ ⥤ D}

/-- For a contravariant functor `F`, `F a.op ≫ F b.op = F (b ≫ a).op`. -/
theorem map_op_comp_map_op (F : Aᵒᵖ ⥤ A) {X Y Z : A} (a : Y ⟶ X) (b : Z ⟶ Y) :
    F.map a.op ≫ F.map b.op = F.map (b ≫ a).op := by
  rw [← F.map_comp, ← op_comp]

/-- The comparison `f^! ∘ g^! ⟶ (f ≫ g)^!` of conjugates: `D_A` applied to the composition
isomorphism of the `P` followed by `P_f(η_B)`. -/
def dualConjComp (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB) {Pf : B ⥤ A} {Pg : C ⥤ B} {Pk : C ⥤ A}
    (c : Pg ⋙ Pf ≅ Pk) : dualConj DB DC Pg ⋙ dualConj DA DB Pf ⟶ dualConj DA DC Pk where
  app M := DA.map (c.inv.app (DC.obj (op M)) ≫ Pf.map (ηB.app (Pg.obj (DC.obj (op M))))).op
  naturality M M' φ := by
    have h1 : ηB.app (Pg.obj (DC.obj (op M'))) ≫ DB.map (DB.map (Pg.map (DC.map φ.op)).op).op =
        Pg.map (DC.map φ.op) ≫ ηB.app _ := (ηB.naturality (Pg.map (DC.map φ.op))).symm
    have h2 : Pk.map (DC.map φ.op) ≫ c.inv.app _ = c.inv.app _ ≫ Pf.map (Pg.map (DC.map φ.op)) :=
      c.inv.naturality (DC.map φ.op)
    have key : c.inv.app (DC.obj (op M')) ≫ Pf.map (ηB.app (Pg.obj (DC.obj (op M')))) ≫
        Pf.map (DB.map (DB.map (Pg.map (DC.map φ.op)).op).op) =
          Pk.map (DC.map φ.op) ≫ c.inv.app (DC.obj (op M)) ≫
            Pf.map (ηB.app (Pg.obj (DC.obj (op M)))) := by
      rw [← Pf.map_comp, h1, Pf.map_comp, reassoc_of% h2]
    dsimp only [dualConj, Functor.comp_map, Functor.op_map, Functor.rightOp_map, Functor.comp_obj,
      Functor.op_obj, Functor.rightOp_obj]
    rw [← DA.map_comp, ← DA.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
    exact key

/-- The component of `dualConjComp ηB c` at `M` is `D_A` of `c⁻¹_{D_C M} ≫ P_f(η_B)`. -/
theorem dualConjComp_app (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB) {Pf : B ⥤ A} {Pg : C ⥤ B} {Pk : C ⥤ A}
    (c : Pg ⋙ Pf ≅ Pk) (M : C) :
    (dualConjComp (DA := DA) (DC := DC) ηB c).app M =
      DA.map (c.inv.app (DC.obj (op M)) ≫ Pf.map (ηB.app (Pg.obj (DC.obj (op M))))).op :=
  rfl

/-- The two comparisons `f^! ∘ g^! ∘ h^! ⟶ (f ≫ g ≫ h)^!` agree, given the associativity of the
composition isomorphisms of the `P`. -/
theorem dualConjComp_assoc (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB) (ηC : 𝟭 C ⟶ DC.rightOp ⋙ DC)
    {Pf : B ⥤ A} {Pg : C ⥤ B} {Ph : D ⥤ C} {Pgf : C ⥤ A} {Phg : D ⥤ B} {Phgf : D ⥤ A}
    (cfg : Pg ⋙ Pf ≅ Pgf) (cgh : Ph ⋙ Pg ≅ Phg) (cgfh : Ph ⋙ Pgf ≅ Phgf)
    (cfhg : Phg ⋙ Pf ≅ Phgf)
    (hassoc : ∀ N, Pf.map (cgh.hom.app N) ≫ cfhg.hom.app N =
      cfg.hom.app (Ph.obj N) ≫ cgfh.hom.app N) (M : D) :
    (dualConj DA DB Pf).map ((dualConjComp (DC := DD) ηC cgh).app M) ≫
        (dualConjComp (DA := DA) (DC := DD) ηB cfhg).app M =
      (dualConjComp (DA := DA) ηB cfg).app ((dualConj DC DD Ph).obj M) ≫
        (dualConjComp (DA := DA) (DC := DD) ηC cgfh).app M := by
  have hinv : ∀ N, cfhg.inv.app N ≫ Pf.map (cgh.inv.app N) =
      cgfh.inv.app N ≫ cfg.inv.app (Ph.obj N) := fun N => by
    calc cfhg.inv.app N ≫ Pf.map (cgh.inv.app N) =
          (cgfh.inv.app N ≫ cfg.inv.app (Ph.obj N)) ≫ (cfg.hom.app (Ph.obj N) ≫ cgfh.hom.app N) ≫
            cfhg.inv.app N ≫ Pf.map (cgh.inv.app N) := by simp
      _ = (cgfh.inv.app N ≫ cfg.inv.app (Ph.obj N)) ≫ (Pf.map (cgh.hom.app N) ≫ cfhg.hom.app N) ≫
            cfhg.inv.app N ≫ Pf.map (cgh.inv.app N) := by rw [hassoc]
      _ = _ := by simp [← Functor.map_comp]
  have h1 := ηB.naturality (cgh.inv.app (DD.obj (op M)) ≫
    Pg.map (ηC.app (Ph.obj (DD.obj (op M)))))
  have h2 := cfg.inv.naturality (ηC.app (Ph.obj (DD.obj (op M))))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Functor.rightOp_obj, Functor.rightOp_map] at h1 h2
  have key : cfhg.inv.app (DD.obj (op M)) ≫ Pf.map (ηB.app (Phg.obj (DD.obj (op M)))) ≫
      Pf.map (DB.map (DB.map (cgh.inv.app (DD.obj (op M)) ≫
        Pg.map (ηC.app (Ph.obj (DD.obj (op M))))).op).op) =
      cgfh.inv.app (DD.obj (op M)) ≫ Pgf.map (ηC.app (Ph.obj (DD.obj (op M)))) ≫
        cfg.inv.app (DC.obj (op (DC.obj (op (Ph.obj (DD.obj (op M))))))) ≫
          Pf.map (ηB.app (Pg.obj (DC.obj (op (DC.obj (op (Ph.obj (DD.obj (op M))))))))) := by
    rw [← Pf.map_comp, ← h1, Pf.map_comp, Pf.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (hinv _), ← reassoc_of% h2]
  dsimp only [dualConj, dualConjComp, Functor.comp_map, Functor.op_map, Functor.rightOp_map,
      Functor.comp_obj, Functor.op_obj, Functor.rightOp_obj, Functor.id_obj, NatTrans.comp_app]
  rw [← DA.map_comp, ← DA.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
  exact key

/-- The unit comparison `𝟭 ⟶ 𝟙^!`: `η` followed by `D_B` of an identification `P_𝟙 ≅ 𝟭`. -/
def dualConjUnit (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB) {Pid : B ⥤ B} (e : Pid ≅ 𝟭 B) :
    𝟭 B ⟶ dualConj DB DB Pid where
  app M := ηB.app M ≫ DB.map (e.hom.app (DB.obj (op M))).op
  naturality M M' φ := by
    have h1 := ηB.naturality φ
    have h2 := e.hom.naturality (DB.map φ.op)
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
      Functor.rightOp_obj, Functor.rightOp_map] at h1 h2
    dsimp only [dualConj, Functor.comp_map, Functor.op_map, Functor.rightOp_map,
        Functor.comp_obj, Functor.op_obj, Functor.rightOp_obj, Functor.id_obj, NatTrans.comp_app]
    simp only [Functor.id_map, Category.assoc, Quiver.Hom.unop_op]
    rw [reassoc_of% h1, ← DB.map_comp, ← DB.map_comp, ← op_comp, ← op_comp, h2]

/-- The component of `dualConjUnit ηB e` at `M` is `η_M ≫ D_B(e_{D_B M})`. -/
theorem dualConjUnit_app (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB) {Pid : B ⥤ B} (e : Pid ≅ 𝟭 B) (M : B) :
    (dualConjUnit ηB e).app M = ηB.app M ≫ DB.map (e.hom.app (DB.obj (op M))).op :=
  rfl

/-- The left unit law: `𝟙^!(g^! M) ⟵ g^! M` followed by the comparison `𝟙^! ∘ g^! ⟶ g^!` is the
identity, given the triangle identity of `η` and the left unit law of the `P`. -/
theorem dualConjUnit_comp_dualConjComp (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB)
    (hT : ∀ X, ηB.app (DB.obj (op X)) ≫ DB.map (ηB.app X).op = 𝟙 (DB.obj (op X)))
    {Pid : B ⥤ B} (e : Pid ≅ 𝟭 B) {Pg : C ⥤ B} (c : Pg ⋙ Pid ≅ Pg)
    (hc : ∀ N, c.hom.app N = e.hom.app (Pg.obj N)) (M : C) :
    (dualConjUnit ηB e).app ((dualConj DB DC Pg).obj M) ≫ (dualConjComp ηB c).app M =
      𝟙 ((dualConj DB DC Pg).obj M) := by
  rw [dualConjUnit_app, dualConjComp_app, Category.assoc, map_op_comp_map_op]
  have h2 : Pid.map (ηB.app (Pg.obj (DC.obj (op M)))) ≫
      e.hom.app (DB.obj (op (DB.obj (op (Pg.obj (DC.obj (op M))))))) =
        e.hom.app (Pg.obj (DC.obj (op M))) ≫ ηB.app (Pg.obj (DC.obj (op M))) :=
    e.hom.naturality (ηB.app (Pg.obj (DC.obj (op M))))
  have hci : c.inv.app (DC.obj (op M)) ≫ e.hom.app (Pg.obj (DC.obj (op M))) = 𝟙 _ := by
    rw [← hc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.op_obj, Functor.rightOp_obj, Functor.id_obj]
  rw [Category.assoc, h2, reassoc_of% hci, hT]

/-- The right unit law: `f^!` of `M ⟶ 𝟙^! M` followed by the comparison `f^! ∘ 𝟙^! ⟶ f^!` is the
identity, given the triangle identity of `η` and the right unit law of the `P`. -/
theorem map_dualConjUnit_comp_dualConjComp (ηB : 𝟭 B ⟶ DB.rightOp ⋙ DB)
    (hT : ∀ X, ηB.app (DB.obj (op X)) ≫ DB.map (ηB.app X).op = 𝟙 (DB.obj (op X)))
    {Pid : B ⥤ B} (e : Pid ≅ 𝟭 B) {Pf : B ⥤ A} (c : Pid ⋙ Pf ≅ Pf)
    (hc : ∀ N, c.hom.app N = Pf.map (e.hom.app N)) (M : B) :
    (dualConj DA DB Pf).map ((dualConjUnit ηB e).app M) ≫ (dualConjComp ηB c).app M =
      𝟙 ((dualConj DA DB Pf).obj M) := by
  rw [dualConjUnit_app, dualConjComp_app, dualConj_map, map_op_comp_map_op]
  have h1 := ηB.naturality (e.hom.app (DB.obj (op M)))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Functor.rightOp_obj, Functor.rightOp_map] at h1
  have hci : c.inv.app (DB.obj (op M)) ≫ Pf.map (e.hom.app (DB.obj (op M))) = 𝟙 _ := by
    rw [← hc, Iso.inv_hom_id_app]
  have key : ηB.app (Pid.obj (DB.obj (op M))) ≫
      DB.map (ηB.app M ≫ DB.map (e.hom.app (DB.obj (op M))).op).op =
        e.hom.app (DB.obj (op M)) := by
    rw [op_comp, DB.map_comp, ← Category.assoc, ← h1, Category.assoc, hT, Category.comp_id]
  rw [Category.assoc, ← Pf.map_comp, key, hci, op_id]
  exact DA.map_id _

/-! ### Biduality in a closed symmetric monoidal category -/

namespace MonoidalClosed

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E] [MonoidalClosed E]

/-- The duality `[-, ω] : Eᵒᵖ ⥤ E`. -/
def dualInto (ω : E) : Eᵒᵖ ⥤ E := internalHom.flip.obj ω

/-- The duality `[-, ω]` sends `K` to `[K, ω]`. -/
@[simp]
theorem dualInto_obj (ω K : E) : (dualInto ω).obj (op K) = (ihom K).obj ω :=
  rfl

variable [SymmetricCategory E]

/-- The biduality morphism `X ⟶ [[X, ω], ω]`: the transpose of the evaluation `[X, ω] ⊗ X ⟶ ω`
after the symmetry. -/
def closedBidualityApp (ω X : E) : X ⟶ (ihom ((ihom X).obj ω)).obj ω :=
  curry ((β_ ((ihom X).obj ω) X).hom ≫ (ihom.ev X).app ω)

/-- The uncurried biduality morphism is the symmetry followed by the evaluation. -/
theorem uncurry_closedBidualityApp (ω X : E) :
    uncurry (closedBidualityApp ω X) = (β_ ((ihom X).obj ω) X).hom ≫ (ihom.ev X).app ω :=
  uncurry_curry _

/-- The biduality morphisms `X ⟶ [[X, ω], ω]` are natural in `X`. -/
theorem closedBidualityApp_naturality (ω : E) {X Y : E} (φ : X ⟶ Y) :
    φ ≫ closedBidualityApp ω Y = closedBidualityApp ω X ≫ (pre ((pre φ).app ω)).app ω := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_closedBidualityApp, uncurry_pre_app,
    uncurry_closedBidualityApp, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc, id_tensor_pre_app_comp_ev]

/-- The triangle identity of biduality: `η_{[X, ω]} ≫ [η_X, ω] = 1`. -/
theorem closedBidualityApp_triangle (ω X : E) :
    closedBidualityApp ω ((ihom X).obj ω) ≫ (pre (closedBidualityApp ω X)).app ω =
      𝟙 ((ihom X).obj ω) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_id_eq_ev, uncurry_closedBidualityApp,
    BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq, uncurry_closedBidualityApp,
    SymmetricCategory.symmetry_assoc]

/-- The biduality morphisms, as a natural transformation `𝟭 ⟶ [[-, ω], ω]`. -/
def closedBiduality (ω : E) : 𝟭 E ⟶ (dualInto ω).rightOp ⋙ dualInto ω where
  app X := closedBidualityApp ω X
  naturality _ _ φ := closedBidualityApp_naturality ω φ

/-- The component of `closedBiduality ω` at `X` is `closedBidualityApp ω X`. -/
theorem closedBiduality_app (ω X : E) : (closedBiduality ω).app X = closedBidualityApp ω X :=
  rfl

/-- The triangle identity of the biduality natural transformation `closedBiduality ω`. -/
theorem closedBiduality_triangle (ω X : E) :
    (closedBiduality ω).app ((dualInto ω).obj (op X)) ≫
        (dualInto ω).map ((closedBiduality ω).app X).op = 𝟙 ((dualInto ω).obj (op X)) :=
  closedBidualityApp_triangle ω X

end MonoidalClosed

end CategoryTheory

end
