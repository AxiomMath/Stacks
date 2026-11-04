module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Adjoint pushforwards of presheaves of modules

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, and let `S` and `R` be presheaves of rings on `C`
and `D` with maps `φ : S ⟶ F_* R` and `ψ : R ⟶ G_* S` compatible with the unit and the counit.
Then the pushforward of presheaves of modules along `φ` is left adjoint to the pushforward along
`ψ`. In particular the pushforward along `φ` is then the pullback along `ψ`, the left adjoint of
the pushforward along `ψ`.

## Main definitions

* `PresheafOfModules.pushforwardPushforwardAdjunction`: the adjunction, the presheaf version of
  Mathlib's `SheafOfModules.pushforwardPushforwardAdj`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_eq_leftAdjointUniq_hom_app_comp`: comparison of the
  hom-set bijections of two adjunctions with the same right adjoint.
-/

@[expose] public section

open CategoryTheory

universe v v₁ v₂ u₁ u₂ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ Functor.whiskerLeft G.op φ)
  (H₂ : φ ≫ Functor.whiskerLeft F.op ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

/-- **If `F ⊣ G`, then the pushforwards of presheaves of modules along `F` and `G` are adjoint**,
as soon as the two maps of rings are compatible with the unit and the counit: the composite
`R ⟶ G_* S ⟶ G_* F_* R` is restriction along the counit (`H₁`), and the composite
`S ⟶ F_* R ⟶ F_* G_* S ⟶ S` is the identity, the last map being restriction along the unit
(`H₂`).

The unit and the counit of the adjunction are restriction along the counit and the unit of
`F ⊣ G`. This is the presheaf version of `SheafOfModules.pushforwardPushforwardAdj`. -/
noncomputable def pushforwardPushforwardAdjunction :
    pushforward.{v} φ ⊣ pushforward.{v} ψ :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun M => homMk (Functor.whiskerRight (NatTrans.op adj.counit) M.presheaf)
            (fun U r m => by
              have h₁ := congrArg (fun k => (k.app U).hom r) H₁
              refine (M.map_smul (adj.counit.app U.unop).op r m).trans ?_
              dsimp at h₁ ⊢
              rw [h₁]
              rfl)
          naturality := fun M N f => by
            ext U m
            exact (CategoryTheory.congr_fun (f.naturality (adj.counit.app U.unop).op) m).symm }
      counit :=
        { app := fun N => homMk (Functor.whiskerRight (NatTrans.op adj.unit) N.presheaf)
            (fun V s n => by
              have h₂ := congrArg (fun k => (k.app V).hom s) H₂
              refine (N.map_smul (adj.unit.app V.unop).op _ n).trans ?_
              dsimp at h₂ ⊢
              exact congrArg (· • _) h₂)
          naturality := fun M N f => by
            ext V n
            exact (CategoryTheory.congr_fun (f.naturality (adj.unit.app V.unop).op) n).symm }
      left_triangle := by
        ext M V m
        dsimp
        change (M.presheaf.map (adj.counit.app (F.obj V.unop)).op ≫
          M.presheaf.map (F.map (adj.unit.app V.unop)).op) m = m
        rw [← Functor.map_comp, ← op_comp,
          show F.map (adj.unit.app V.unop) ≫ adj.counit.app (F.obj V.unop) = 𝟙 _ from
            adj.left_triangle_components V.unop]
        simp only [Functor.id_obj, presheaf_obj_coe, op_id, CategoryTheory.Functor.map_id,
          AddCommGrpCat.hom_id]
        rfl
      right_triangle := by
        ext N U n
        dsimp
        change (N.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
          N.presheaf.map (adj.unit.app (G.obj U.unop)).op) n = n
        rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
        simp only [Functor.id_obj, presheaf_obj_coe, op_id, CategoryTheory.Functor.map_id,
          AddCommGrpCat.hom_id]
        rfl }

end PresheafOfModules

namespace CategoryTheory.Adjunction

/-- For two left adjoints of the same functor, the inverse of the hom-set bijection of the first
adjunction is that of the second preceded by the canonical isomorphism between the two left
adjoints. -/
theorem homEquiv_symm_eq_leftAdjointUniq_hom_app_comp {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {X : C} {Y : D} (f : X ⟶ G.obj Y) :
    (adj1.homEquiv X Y).symm f =
      (leftAdjointUniq adj1 adj2).hom.app X ≫ (adj2.homEquiv X Y).symm f := by
  rw [homEquiv_counit, homEquiv_counit, ← leftAdjointUniq_hom_app_counit adj1 adj2,
    ← Category.assoc, ← Category.assoc, ← (leftAdjointUniq adj1 adj2).hom.naturality]

end CategoryTheory.Adjunction

end
