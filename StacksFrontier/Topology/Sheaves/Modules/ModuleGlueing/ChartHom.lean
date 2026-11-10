module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# The comparison of a glued sheaf of `O`-modules with its members

Let `O` be a sheaf of rings on a topological space `X` and let `N i` be sheaves of `O`-modules
on `X`, glued over a family of opens `U i` by `Stacks.SheafOfModules.OModuleGlueData.ofModules`.
The chart isomorphisms of Stacks 00AM identify the sections of the glued sheaf with those of
`N i` over the opens contained in `U i` only. When the sections of `N i` over an open `T` are
already those over `T ⊓ U i` — that is, the restriction from `T` to `T ⊓ U i` is bijective, as
for a module pushed forward from `U i` — the chart isomorphisms extend to a morphism of sheaves of
modules from the glued sheaf to `N i` on all of `X`. This file builds it.

## Main definitions

* `Stacks.SheafOfModules.OModuleGlueData.chartHom`: the comparison morphism.

## Main results

* `Stacks.SheafOfModules.OModuleGlueData.chartHom_app_of_le`: over an open contained in `U i` it
  is the chart isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.OModuleGlueData

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {ι : Type u}
  {U : ι → Opens X}
  (N : ι → _root_.SheafOfModules.{u} O)
  (trans : ∀ (i j : ι) {V : Opens X} (_hi : V ≤ U i) (_hj : V ≤ U j),
    (N i).val.obj (op V) ≃ₗ[ToType (O.obj.obj (op V))] (N j).val.obj (op V))
  (trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
    (s : ToType ((N i).val.obj (op V))),
    trans i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
      = (N j).val.map (homOfLE hWV).op (trans i j hi hj s))
  (trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
    (s : ToType ((N i).val.obj (op V))),
    trans j k hj hk (trans i j hi hj s) = trans i k hi hk s)
  (hN : ∀ i (T : Opens X),
    Function.Bijective ((N i).val.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op))

/-- Two composites of restriction maps of a presheaf of modules between the same opens agree. -/
lemma restrict_restrict {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{u} R)
    {A A₁ A₂ A' : Opens X} (h₁ : A₁ ≤ A) (g₁ : A' ≤ A₁) (h₂ : A₂ ≤ A) (g₂ : A' ≤ A₂)
    (x : ToType (P.obj (op A))) :
    P.map (homOfLE g₁).op (P.map (homOfLE h₁).op x) =
      P.map (homOfLE g₂).op (P.map (homOfLE h₂).op x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  rfl

include hN in
/-- The restriction from `T` to `T ⊓ U i` of the `i`-th member is an isomorphism. -/
lemma isIso_map_inf (i : ι) (T : Opens X) :
    IsIso ((N i).val.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (hN i T)

/-- Cancelling an inverse after applying the morphism. -/
lemma hom_inv_apply {R : Type u} [Ring R] {A B C : ModuleCat.{u} R} (f : A ⟶ B)
    (g : C ⟶ B) [IsIso g] (x : A) : g ((f ≫ inv g) x) = f x := by
  change ((f ≫ inv g) ≫ g) x = f x
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The comparison of the glued sheaf with the `i`-th member over an arbitrary open `T`: the
`i`-th chart of the restriction to `T ⊓ U i`, transported back along the restriction from `T`
to `T ⊓ U i`. -/
def chartApp (i : ι) (T : Opens X) :
    (ofModules N trans trans_map trans_trans).glued.val.obj (op T) ⟶ (N i).val.obj (op T) :=
  (ofModules N trans trans_map trans_trans).glued.val.map
      (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op ≫
    (ModuleCat.restrictScalars (O.obj.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op).hom).map
      ((ofModules N trans trans_map trans_trans).chartIso i
        (inf_le_right : T ⊓ U i ≤ U i)).hom ≫
    @CategoryTheory.inv _ _ _ _ ((N i).val.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op)
      (isIso_map_inf N hN i T)

/-- Restricting the comparison `chartApp` from `T` to `T ⊓ U i` gives the `i`-th chart
isomorphism applied to the restriction of the section of the glued sheaf. -/
lemma restrict_chartApp (i : ι) (T : Opens X)
    (s : ToType ((ofModules N trans trans_map trans_trans).glued.val.obj (op T))) :
    (N i).val.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op
        (chartApp N trans trans_map trans_trans hN i T s) =
      ((ofModules N trans trans_map trans_trans).chartIso i (inf_le_right : T ⊓ U i ≤ U i)).hom
        ((ofModules N trans trans_map trans_trans).glued.val.map
          (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op s) :=
  @hom_inv_apply _ _ _ _ _ ((ofModules N trans trans_map trans_trans).glued.val.map
      (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op ≫
    (ModuleCat.restrictScalars (O.obj.map (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op).hom).map
      ((ofModules N trans trans_map trans_trans).chartIso i
        (inf_le_right : T ⊓ U i ≤ U i)).hom) _ (isIso_map_inf N hN i T) s

/-- The comparison `chartApp` commutes with restriction from `T` to an open `T' ≤ T`. -/
lemma chartApp_restrict (i : ι) {T T' : Opens X} (h : T' ≤ T)
    (s : ToType ((ofModules N trans trans_map trans_trans).glued.val.obj (op T))) :
    chartApp N trans trans_map trans_trans hN i T'
        ((ofModules N trans trans_map trans_trans).glued.val.map (homOfLE h).op s) =
      (N i).val.map (homOfLE h).op (chartApp N trans trans_map trans_trans hN i T s) := by
  refine (hN i T').1 ((restrict_chartApp N trans trans_map trans_trans hN i T' _).trans ?_)
  refine Eq.trans ?_ (restrict_restrict (N i).val inf_le_left
    (inf_le_inf_right (U i) h) h inf_le_left (chartApp N trans trans_map trans_trans hN i T s))
  refine Eq.trans ?_
    (congrArg _ (restrict_chartApp N trans trans_map trans_trans hN i T s)).symm
  refine Eq.trans ?_ ((ofModules N trans trans_map trans_trans).chartIso_hom_restrictₛₗ i
    (inf_le_right : T ⊓ U i ≤ U i) (inf_le_inf_right (U i) h)
    ((ofModules N trans trans_map trans_trans).glued.val.map
      (homOfLE (inf_le_left : T ⊓ U i ≤ T)).op s))
  exact congrArg _ (restrict_restrict (ofModules N trans trans_map trans_trans).glued.val h
    inf_le_left inf_le_left (inf_le_inf_right (U i) h) s)

/-- **The comparison of the glued sheaf of modules with its `i`-th member**, for members whose
restriction from an open `T` to `T ⊓ U i` is bijective. -/
def chartHom (i : ι) : (ofModules N trans trans_map trans_trans).glued ⟶ N i :=
  ⟨{ app := fun T => chartApp N trans trans_map trans_trans hN i T.unop
     naturality := fun {T T'} f => by
      ext x
      obtain ⟨T⟩ := T
      obtain ⟨T'⟩ := T'
      have h : T' ≤ T := leOfHom f.unop
      have hf : f = (homOfLE h).op := Subsingleton.elim _ _
      subst hf
      exact chartApp_restrict N trans trans_map trans_trans hN i h x }⟩

/-- Over an open contained in the `i`-th member, the comparison is the chart isomorphism of the
glued sheaf. -/
lemma chartHom_app_of_le (i : ι) {T : Opens X} (hT : T ≤ U i)
    (s : ToType ((ofModules N trans trans_map trans_trans).glued.val.obj (op T))) :
    (chartHom N trans trans_map trans_trans hN i).val.app (op T) s =
      ((ofModules N trans trans_map trans_trans).chartIso i hT).hom s := by
  change chartApp N trans trans_map trans_trans hN i T s = _
  refine (hN i T).1 ((restrict_chartApp N trans trans_map trans_trans hN i T s).trans ?_)
  exact (ofModules N trans trans_map trans_trans).chartIso_hom_restrictₛₗ i hT inf_le_left s

end Stacks.SheafOfModules.OModuleGlueData

end
