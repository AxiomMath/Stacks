module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing

/-!
# Sections of a constant abelian sheaf over an irreducible étale scheme

The sections of the constant abelian sheaf `M̲` on Mathlib's small étale site over an object
whose underlying scheme is irreducible are the constants: the canonical map `M ⟶ M̲(U)` is
bijective. This is the abelian-group counterpart of
`AlgebraicGeometry.Scheme.bijective_toSheafify_const_app_of_irreducibleSpace`, which treats
constant sheaves of modules, and it is proved the same way: two constants with the same image
agree on a covering, which has a member unless the object is sheaf theoretically empty, and over a
final object a section is locally a constant, these constants agreeing on common refinements.

## Main results

* `Stacks.ConstantSheaf.injective_toSheafify_const_app_of_bot_not_mem_addCommGrpCat` and
  `Stacks.ConstantSheaf.surjective_toSheafify_const_app_of_forall_exists_refinement_addCommGrpCat`
  — the two site-level statements.
* `AlgebraicGeometry.Scheme.bijective_toSheafify_const_app_of_irreducibleSpace_addCommGrpCat` —
  the statement on the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

omit [HasSheafify J AddCommGrpCat.{max u v}] in
/-- **The canonical map from an abelian group to the sections of the constant sheaf it generates
is injective over an object which is not sheaf theoretically empty.** -/
theorem injective_toSheafify_const_app_of_bot_not_mem_addCommGrpCat (M : AddCommGrpCat.{max u v})
    (X : C) (hX : (⊥ : Sieve X) ∉ J X) :
    Function.Injective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X)) := by
  intro x y hxy
  by_contra hne
  refine hX (J.superset_covering ?_
    (Presheaf.equalizerSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj M)) x y hxy))
  intro Y f hf
  exact hne (by simpa [Presheaf.equalizerSieve_apply] using hf)

omit [HasSheafify J AddCommGrpCat.{max u v}] in
/-- **Over a final object, the sections of a constant abelian sheaf are the constants**, when any
two objects which are not sheaf theoretically empty have a common refinement which is not sheaf
theoretically empty either. -/
theorem surjective_toSheafify_const_app_of_forall_exists_refinement_addCommGrpCat
    (M : AddCommGrpCat.{max u v}) {T : C} (hT : IsTerminal T) (hbot : (⊥ : Sieve T) ∉ J T)
    (href : ∀ Y Z : C, (⊥ : Sieve Y) ∉ J Y → (⊥ : Sieve Z) ∉ J Z →
      ∃ (Q : C) (_ : Q ⟶ Y) (_ : Q ⟶ Z), (⊥ : Sieve Q) ∉ J Q) :
    Function.Surjective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T)) := by
  classical
  intro s
  have hsheaf : Presieve.IsSheaf J
      (sheafify J ((Functor.const Cᵒᵖ).obj M) ⋙ forget AddCommGrpCat.{max u v}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _
        ((presheafToSheaf J AddCommGrpCat.{max u v}).obj ((Functor.const Cᵒᵖ).obj M)).property)
  have hS : Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj M)) s ∈ J T :=
    Presheaf.imageSieve_mem J _ s
  have hex : ∃ (Y : C) (g : Y ⟶ T),
      Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj M)) s g ∧
        (⊥ : Sieve Y) ∉ J Y := by
    by_contra hcon
    refine hbot (J.transitive hS ⊥ fun {Y} g hg => ?_)
    have h0 : (⊥ : Sieve T).pullback g = ⊥ := le_antisymm (fun _ k hk => hk) bot_le
    rw [h0]
    by_contra hY
    exact hcon ⟨Y, g, hg, hY⟩
  obtain ⟨Y₀, g₀, ⟨a₀, ha₀⟩, hY₀⟩ := hex
  refine ⟨a₀, (hsheaf _ hS).isSeparatedFor.ext fun {Y} g hg => ?_⟩
  have hres : ∀ {Z Y' : C} (k : Z ⟶ Y') (v : M),
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map k.op
          ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Y') v) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Z) v :=
    fun k v => (NatTrans.naturality_apply (toSheafify J ((Functor.const Cᵒᵖ).obj M)) k.op v).symm
  change (sheafify J ((Functor.const Cᵒᵖ).obj M)).map g.op
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) a₀) = _
  rw [hres g a₀]
  obtain ⟨a, ha⟩ := hg
  by_cases hY : (⊥ : Sieve Y) ∈ J Y
  · exact (hsheaf ⊥ hY).isSeparatedFor.ext fun _ _ h => h.elim
  obtain ⟨Q, q, r, hQ⟩ := href Y Y₀ hY hY₀
  have hcomm : q ≫ g = r ≫ g₀ := hT.hom_ext _ _
  have h1 : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Q) a =
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map (q ≫ g).op s := by
    rw [← hres q a, ha, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have h2 : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Q) a₀ =
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map (r ≫ g₀).op s := by
    rw [← hres r a₀, ha₀, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have hvv : a = a₀ :=
    injective_toSheafify_const_app_of_bot_not_mem_addCommGrpCat J M Q hQ (by rw [h1, h2, hcomm])
  rwa [← hvv]

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.Scheme

open Stacks.ConstantSheaf

variable {X : Scheme.{u}}

/-- **The constants are exactly the sections of a constant abelian sheaf over an irreducible
object of Mathlib's small étale site.** -/
theorem bijective_toSheafify_const_app_of_irreducibleSpace_addCommGrpCat
    (M : AddCommGrpCat.{u + 1}) (U : X.Etale) [IrreducibleSpace U.left] :
    Function.Bijective ((toSheafify X.smallEtaleTopology
      ((Functor.const (X.Etale)ᵒᵖ).obj M)).app (op U)) := by
  have hbot : (⊥ : Sieve (Over.mk (𝟙 U))) ∉ (X.smallEtaleTopology.over U) (Over.mk (𝟙 U)) := by
    rw [GrothendieckTopology.mem_over_iff, OrderIso.map_bot]
    exact bot_not_mem_smallEtaleTopology (‹IrreducibleSpace U.left›.toNonempty.some)
  have hbij : Function.Bijective ((toSheafify (X.smallEtaleTopology.over U)
      ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U)))) :=
    ⟨injective_toSheafify_const_app_of_bot_not_mem_addCommGrpCat _ M _ hbot,
      surjective_toSheafify_const_app_of_forall_exists_refinement_addCommGrpCat _ M
        (Over.mkIdTerminal (X := U)) hbot
        (fun P Q hP hQ ↦ exists_refinement_over_bot_not_mem_of_irreducibleSpace U P Q hP hQ)⟩
  have hcomp : (toSheafify (X.smallEtaleTopology.over U)
        ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U))) ≫
        ((overPullbackConstantSheafIso X.smallEtaleTopology
          AddCommGrpCat.{u + 1} U).hom.app M).hom.app (op (Over.mk (𝟙 U))) =
      (toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj M)).app (op U) :=
    Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso_app
      X.smallEtaleTopology AddCommGrpCat.{u + 1} U M (op (Over.mk (𝟙 U)))
  have hbij2 := (ConcreteCategory.isIso_iff_bijective
    (((overPullbackConstantSheafIso X.smallEtaleTopology
      AddCommGrpCat.{u + 1} U).hom.app M).hom.app (op (Over.mk (𝟙 U))))).1 inferInstance
  have hfun : ⇑(ConcreteCategory.hom ((toSheafify X.smallEtaleTopology
        ((Functor.const (X.Etale)ᵒᵖ).obj M)).app (op U))) =
      (⇑(ConcreteCategory.hom (((overPullbackConstantSheafIso X.smallEtaleTopology
          AddCommGrpCat.{u + 1} U).hom.app M).hom.app (op (Over.mk (𝟙 U)))))) ∘
        (⇑(ConcreteCategory.hom ((toSheafify (X.smallEtaleTopology.over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U)))))) := by
    rw [← hcomp]
    rfl
  rw [hfun]
  exact hbij2.comp hbij

end AlgebraicGeometry.Scheme

end
