module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialModules

/-!
# Ideal modules on the point simplicial site

For a cosimplicial commutative ring `A` and a system of ideals `Iₙ ⊆ Aₙ` carried into each other by
the ring maps of `A`, this file builds the sheaf of modules on the total site of the constant
simplicial site on the point with sections `Iₙ` in degree `n`, together with its inclusion into
the structure sheaf `𝒪 = 𝒪 ⧸ 0`. It also records that a morphism out of a cartesian module which
vanishes in degree zero is zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.PointSimplicialSite

noncomputable section

variable (A : SimplexCategory ⥤ CommRingCat.{u}) (I : ∀ n : SimplexCategory, Ideal (A.obj n))
  (hI : ∀ {m n : SimplexCategory} (φ : m ⟶ n), I m ≤ (I n).comap (A.map φ).hom)

/-- The cosimplicial abelian group `n ↦ Iₙ`. -/
def idealFunctor : SimplexCategory ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (I n)
  map φ := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨(A.map φ).hom x, hI φ x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  map_id n := by
    ext x
    change (A.map (𝟙 n)).hom x.1 = x.1
    rw [A.map_id]
    rfl
  map_comp φ ψ := by
    ext x
    change (A.map (φ ≫ ψ)).hom x.1 = (A.map ψ).hom ((A.map φ).hom x.1)
    rw [A.map_comp]
    rfl

/-- The sheaf of modules on the total site with sections `Iₙ` in degree `n`. -/
def idealModule : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)) where
  val := @PresheafOfModules.ofPresheaf _ _ _
    (situation.{u}.totalSimplexDegree.op ⋙ unopUnop SimplexCategory ⋙ idealFunctor A I hI)
    (fun X => inferInstanceAs (Module (A.obj X.unop.base.unop) (I X.unop.base.unop)))
    (fun _ _ f r m => Subtype.ext (map_mul (A.map f.unop.base.unop).hom r m.1))
  isSheaf := isSheaf_total _

/-- The structure sheaf, as the quotient module by the zero ideals. -/
abbrev unitModule : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A)) :=
  quotModule A (fun _ => ⊥) (fun _ => bot_le)

/-- The structure sheaf is cartesian. -/
theorem unitModule_isCartesian :
    situation.{u}.IsCartesianModule (ringSheaf A) (unitModule A) :=
  quotModule_isCartesian A _ (fun _ => bot_le) (fun _ => bot_le)

/-- The inclusion of the ideal module into the structure sheaf. -/
def idealIncl : idealModule A I hI ⟶ unitModule A where
  val := PresheafOfModules.homMk
    { app := fun X => AddCommGrpCat.ofHom
        ((Ideal.Quotient.mk (⊥ : Ideal (A.obj X.unop.base.unop))).toAddMonoidHom.comp
          (I X.unop.base.unop).subtype.toAddMonoidHom)
      naturality := fun X Y f => by
        ext x
        rfl }
    (fun X r m => map_mul (Ideal.Quotient.mk (⊥ : Ideal (A.obj X.unop.base.unop))) r m.1)

/-- In degree `n` the inclusion of the ideal module sends `x ∈ Iₙ` to its class in `Aₙ ⧸ 0`. -/
theorem idealIncl_app (n : SimplexCategory) (x : I n) :
    (idealIncl A I hI).val.app (op (tot n)) x = Ideal.Quotient.mk ⊥ x.1 := rfl

variable {A}

/-- **A morphism out of a cartesian module which vanishes in degree zero is zero.** -/
theorem eq_zero_of_isCartesian
    {X Y : SheafOfModules.{u} (situation.{u}.totalRingSheaf (ringSheaf A))}
    (hX : situation.{u}.IsCartesianModule (ringSheaf A) X) (g : X ⟶ Y)
    (h0 : ∀ y, g.val.app (op (tot ⦋0⦌)) y = 0) : g = 0 := by
  apply tot_hom_ext
  intro n x
  have hn : situation.{u}.componentModuleMap (ringSheaf A) g n = 0 := by
    apply comp_hom_ext_of_isCartesian hX (SimplexCategory.const ⦋0⦌ n 0)
    intro y
    change g.val.app (op (tot n)) _ = 0
    rw [PresheafOfModules.naturality_apply g.val _ y, h0, map_zero]
    rfl
  exact congrArg (fun f => f.val.app (op pt) x) hn

end

end CategoryTheory.PointSimplicialSite

end
