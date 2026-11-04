module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLift

/-!
# Base change from a terminal object along a ring transport

Let `O` be a presheaf of rings with commutative sections on a category `C` with a terminal
object `X`, so that every `O(X)`-module `N` has a base change `U ↦ O(U) ⊗_{O(X)} N`, the
presheaf of modules `Stacks.TerminalBaseChange.baseChangePresheaf`. Given an equivalence
`e : C ≌ D`, a presheaf of rings `O'` on `D` with a terminal object `X'`, and a ring transport
`T : RingTransport e O O'` (ring isomorphisms `O'(Y) ≃+* O(e⁻¹ Y)`, the two presheaves of rings
possibly in different universes), the transport of a base change is a base change: this file
constructs the isomorphism

  `T(O ⊗_{O(X)} N) ≅ O' ⊗_{O'(X')} N'`

where `N'` is the `O'(X')`-module `N` read through the ring isomorphism
`O'(X') ≃+* O(e⁻¹ X') ≃+* O(X)` (the second one induced by an isomorphism `e⁻¹ X' ≅ X`).

## Main definitions

* `PresheafOfModules.evaluationIsoOfIso`: evaluation at isomorphic objects agrees up to
  restriction of scalars along the induced ring isomorphism.
* `SheafOfModules.evaluationIsoOfIso`: the same for sheaves of modules.
* `Stacks.UniverseLift.RingTransport.terminalRingEquiv`: the ring isomorphism
  `O'(X') ≃+* O(X)`.
* `Stacks.UniverseLift.RingTransport.baseChangeTransportIso`: the transport of base changes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v₁ v₂ u₁ u₂ r₁ r₂

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ RingCat.{r₁})

/-- The restriction map of `M` along an isomorphism `g : A ≅ B` of `Cᵒᵖ`, as an `O(A)`-linear
isomorphism `M(A) ≅ M(B)` when `M(B)` is read through `O(g)`. -/
noncomputable def evaluationIsoOfIsoApp {A B : Cᵒᵖ} (g : A ≅ B) (M : PresheafOfModules.{t} O) :
    M.obj A ≅ (ModuleCat.restrictScalars (O.map g.hom).hom).obj (M.obj B) :=
  LinearEquiv.toModuleIso (R := O.obj A) (X₁ := M.obj A)
    (X₂ := (ModuleCat.restrictScalars (O.map g.hom).hom).obj (M.obj B))
    (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
    { toFun := M.map g.hom
      map_add' := map_add _
      map_smul' := M.map_smul g.hom
      invFun := M.map g.inv
      left_inv := Stacks.UniverseLift.RingTransport.map_map_of_comp_eq_id M g.hom g.inv
        g.hom_inv_id
      right_inv := Stacks.UniverseLift.RingTransport.map_map_of_comp_eq_id M (X := B) g.inv
        g.hom g.inv_hom_id }

/-- Evaluating a presheaf of modules at isomorphic objects: along `g : A ≅ B` in `Cᵒᵖ`, the
restriction maps along `g` are isomorphisms `M(A) ≅ M(B)`, linear over `O(g)`, natural in
`M`. -/
noncomputable def evaluationIsoOfIso {A B : Cᵒᵖ} (g : A ≅ B) :
    evaluation.{t} O A ≅ evaluation.{t} O B ⋙ ModuleCat.restrictScalars (O.map g.hom).hom :=
  NatIso.ofComponents (evaluationIsoOfIsoApp O g) fun φ ↦ by
    ext x
    exact (PresheafOfModules.naturality_apply φ g.hom x).symm

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]

/-- **Evaluating a sheaf of modules at isomorphic objects of the site.** Along an isomorphism
`g : A ≅ B` of `Cᵒᵖ` the restriction maps give isomorphisms `M(A) ≅ M(B)`, semilinear over the
ring map `R(g)`, naturally in `M`. -/
noncomputable def evaluationIsoOfIso {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r₁})
    {A B : Cᵒᵖ} (g : A ≅ B) :
    evaluation.{t} R A ≅ evaluation.{t} R B ⋙ ModuleCat.restrictScalars (R.obj.map g.hom).hom :=
  Functor.isoWhiskerLeft (SheafOfModules.forget.{t} R)
    (PresheafOfModules.evaluationIsoOfIso R.obj g)

end SheafOfModules

namespace Stacks.UniverseLift.RingTransport

open Stacks.TerminalBaseChange

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {O : Cᵒᵖ ⥤ RingCat.{r₁}} {O' : Dᵒᵖ ⥤ RingCat.{r₂}} (T : RingTransport e O O')
  {X : C} {X' : D} (γ : e.inverse.obj X' ≅ X)

/-- The ring isomorphism `O'(X') ≃+* O(e⁻¹ X') ≃+* O(X)` induced by the ring transport and an
isomorphism `e⁻¹ X' ≅ X`. -/
noncomputable def terminalRingEquiv : O'.obj (op X') ≃+* O.obj (op X) :=
  (T.iso (op X')).trans (O.mapIso γ.op.symm).ringCatIsoToRingEquiv

/-- The ring isomorphism `O'(X') ≃+* O(X)` as a composite of ring homomorphisms. -/
lemma terminalRingEquiv_toRingHom :
    (T.terminalRingEquiv γ).toRingHom =
      (O.map γ.inv.op).hom.comp (T.iso (op X')).toRingHom := rfl

/-- Evaluation at `X` followed by restriction of scalars along `O'(X') ≃+* O(X)` is evaluation
at `e⁻¹ X'` followed by restriction of scalars along `O'(X') ≃+* O(e⁻¹ X')`. -/
noncomputable def evaluationTerminalRingEquivIso :
    PresheafOfModules.evaluation.{max t r₁ r₂} O (op X) ⋙
        ModuleCat.restrictScalars (T.terminalRingEquiv γ).toRingHom ≅
      PresheafOfModules.evaluation.{max t r₁ r₂} O (e.inverse.op.obj (op X')) ⋙
        ModuleCat.restrictScalars (T.iso (op X')).toRingHom :=
  Functor.isoWhiskerLeft (PresheafOfModules.evaluation O (op X))
      (ModuleCat.restrictScalarsComp' (T.iso (op X')).toRingHom (O.map γ.inv.op).hom
        (T.terminalRingEquiv γ).toRingHom rfl) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (PresheafOfModules.evaluationIsoOfIso O γ.op.symm).symm
      (ModuleCat.restrictScalars (T.iso (op X')).toRingHom)

/-- Evaluation at `X'` of a presheaf of `O'`-modules, computed on its transport back to `C`:
it is evaluation at `X` followed by restriction of scalars along `O'(X') ≃+* O(X)`. -/
noncomputable def evaluationTransportIso :
    T.symm.functor ⋙ PresheafOfModules.evaluation.{max t r₁ r₂} O (op X) ⋙
        ModuleCat.restrictScalars (T.terminalRingEquiv γ).toRingHom ≅
      PresheafOfModules.evaluation.{max t r₁ r₂} O' (op X') :=
  Functor.isoWhiskerLeft T.symm.functor (T.evaluationTerminalRingEquivIso γ) ≪≫
    Functor.isoWhiskerLeft T.symm.functor (T.functorCompEvaluation (op X')).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight T.counitIso _ ≪≫ Functor.leftUnitor _

variable [CommSections O] [CommSections O'] (hX : IsTerminal X) (hX' : IsTerminal X')

/-- **The transport of a base change from a terminal object is a base change.** For an
`O'(X')`-module `N'`, the transport along `T` of `O ⊗_{O(X)} N'` (with `N'` read as an
`O(X)`-module through `O'(X') ≃+* O(X)`) is `O' ⊗_{O'(X')} N'`, naturally in `N'`. -/
noncomputable def baseChangeTransportIso :
    ModuleCat.restrictScalars (T.terminalRingEquiv γ).symm.toRingHom ⋙
        baseChangePresheaf.{max t r₂} O hX ⋙ T.functor ≅
      baseChangePresheaf.{max t r₁} O' hX' :=
  Adjunction.leftAdjointUniq
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (T.terminalRingEquiv γ).symm).toAdjunction.comp
      ((baseChangeAdj.{max t r₂} O hX).comp T.equivalence.toAdjunction))
    ((baseChangeAdj.{max t r₁} O' hX').ofNatIsoRight (T.evaluationTransportIso γ).symm)

end Stacks.UniverseLift.RingTransport
