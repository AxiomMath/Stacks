module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTransport

/-!
# Maps out of a presheaf of modules cartesian over a terminal object

Let `R` be a presheaf of commutative rings on a category `C` with a terminal object `t`, and let
`M` be a presheaf of `R`-modules which is cartesian over every map to `t`: for each object `V`
the base-change comparison `R(V) ⊗_{R(t)} M(t) ⟶ M(V)` is an isomorphism.  Then a morphism of
presheaves of modules out of `M` is determined by its component at `t`, and every
`R(t)`-linear map out of `M(t)` is such a component: evaluation at `t`,
`Hom(M, N) ⟶ Hom_{R(t)}(M(t), N(t))`, is a bijection for every presheaf of modules `N`.

On the small étale site of an affine scheme this is the statement that a quasi-coherent module is
determined by its global sections, read on the affine objects, where quasi-coherence is the
cartesian condition (Stacks 0H04).

## Main results

* `Stacks.PresheafOfModules.ext_of_isTerminal`: two maps out of `M` agreeing at `t` are equal.
* `Stacks.PresheafOfModules.homOfIsTerminal`: the map out of `M` with a prescribed component at
  `t`.
* `Stacks.PresheafOfModules.bijective_app_of_isTerminal`: evaluation at `t` is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
  {t : C} (ht : IsTerminal t)
  (hM : ∀ V : C, IsIso (restrictionBaseChange M (ht.from V).op))

include hM in
/-- **A map out of a presheaf of modules cartesian over a terminal object is determined by its
component there.** -/
theorem ext_of_isTerminal {N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    {u u' : M ⟶ N} (h : u.app (op t) = u'.app (op t)) : u = u' := by
  ext V : 1
  have := hM V.unop
  have key := eq_of_isIso_restrictionBaseChange M (ht.from V.unop).op (RingHom.id _)
    (u.app V).hom.toAddMonoidHom (u'.app V).hom.toAddMonoidHom
    (fun a y => (u.app V).hom.map_smul a y) (fun a y => (u'.app V).hom.map_smul a y)
    (fun x => by
      change u.app V (M.map (ht.from V.unop).op x) = u'.app V (M.map (ht.from V.unop).op x)
      rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, h])
  exact ModuleCat.hom_ext (LinearMap.ext fun y => DFunLike.congr_fun key y)

variable {N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
  (l : M.obj (op t) ⟶ N.obj (op t))

/-- The component at `V` of the map out of `M` with component `l` at `t`: invert the base-change
comparison of `M`, extend `l` by scalars, and apply the base-change comparison of `N`. -/
noncomputable def homOfIsTerminalApp (V : C) : M.obj (op V) ⟶ N.obj (op V) :=
  have := hM V
  inv (restrictionBaseChange M (ht.from V).op) ≫
    (ModuleCat.extendScalars (R.map (ht.from V).op).hom).map l ≫
      restrictionBaseChange N (ht.from V).op

/-- The component `homOfIsTerminalApp M ht hM l V` sends the restriction `M.map f x` of a section
`x` of `M` over `t` to the restriction `N.map f (l x)` of its image under `l`. -/
theorem homOfIsTerminalApp_map (V : C) (f : op t ⟶ op V) (x : M.obj (op t)) :
    homOfIsTerminalApp M ht hM l V (M.map f x) = N.map f (l x) := by
  obtain rfl : f = (ht.from V).op := Quiver.Hom.unop_inj (ht.hom_ext _ _)
  have := hM V
  have h2 : inv (restrictionBaseChange M (ht.from V).op) (M.map (ht.from V).op x) =
      (1 : R.obj (op V)) ⊗ₜ[R.obj (op t), (R.map (ht.from V).op).hom] x := by
    rw [← restrictionBaseChange_one_tmul M (ht.from V).op x]
    exact (asIso (restrictionBaseChange M (ht.from V).op)).hom_inv_id_apply _
  change restrictionBaseChange N (ht.from V).op
      ((ModuleCat.extendScalars (R.map (ht.from V).op).hom).map l
        (inv (restrictionBaseChange M (ht.from V).op) (M.map (ht.from V).op x))) = _
  rw [h2]
  exact (congrArg (restrictionBaseChange N (ht.from V).op)
    (ModuleCat.ExtendScalars.map_tmul (R.map (ht.from V).op).hom l 1 x)).trans
      (restrictionBaseChange_one_tmul N (ht.from V).op (l x))

/-- **The map out of `M` with a prescribed component at the terminal object.** -/
noncomputable def homOfIsTerminal : M ⟶ N where
  app V := homOfIsTerminalApp M ht hM l V.unop
  naturality {V V'} g := by
    have := hM V.unop
    let g₁ : M.obj V →+ N.obj V' :=
      AddMonoidHom.mk' (fun y => homOfIsTerminalApp M ht hM l V'.unop (M.map g y))
        (fun y y' => by
          dsimp only
          rw [map_add]
          exact LinearMap.map_add _ _ _)
    let g₂ : M.obj V →+ N.obj V' :=
      AddMonoidHom.mk' (fun y => N.map g (homOfIsTerminalApp M ht hM l V.unop y))
        (fun y y' => by
          dsimp only
          rw [map_add]
          exact map_add (N.map g).hom _ _)
    have key : g₁ = g₂ :=
      eq_of_isIso_restrictionBaseChange M (ht.from V.unop).op (R.map g).hom g₁ g₂
      (fun a y => by
        change homOfIsTerminalApp M ht hM l V'.unop (M.map g (a • y)) =
          (R.map g).hom a • homOfIsTerminalApp M ht hM l V'.unop (M.map g y)
        rw [PresheafOfModules.map_smul]
        exact (homOfIsTerminalApp M ht hM l V'.unop).hom.map_smul _ _)
      (fun a y => by
        change N.map g (homOfIsTerminalApp M ht hM l V.unop (a • y)) =
          (R.map g).hom a • N.map g (homOfIsTerminalApp M ht hM l V.unop y)
        rw [(homOfIsTerminalApp M ht hM l V.unop).hom.map_smul, PresheafOfModules.map_smul]
        rfl)
      (fun x => by
        change homOfIsTerminalApp M ht hM l V'.unop (M.map g (M.map (ht.from V.unop).op x)) =
          N.map g (homOfIsTerminalApp M ht hM l V.unop (M.map (ht.from V.unop).op x))
        rw [← PresheafOfModules.map_comp_apply, homOfIsTerminalApp_map,
          homOfIsTerminalApp_map, ← PresheafOfModules.map_comp_apply])
    ext y
    exact DFunLike.congr_fun key y

/-- The component of `homOfIsTerminal M ht hM l` at the terminal object `t` is `l`. -/
theorem homOfIsTerminal_app_terminal : (homOfIsTerminal M ht hM l).app (op t) = l := by
  ext x
  have h := homOfIsTerminalApp_map M ht hM l t (𝟙 _) x
  simp only [PresheafOfModules.map_id] at h
  exact h

include hM in
/-- **Evaluation at a terminal object is bijective on maps out of a presheaf of modules which is
cartesian over every map to it.** -/
theorem bijective_app_of_isTerminal :
    Function.Bijective (fun u : M ⟶ N => u.app (op t)) :=
  ⟨fun _ _ h => ext_of_isTerminal M ht hM h,
    fun l => ⟨homOfIsTerminal M ht hM l, homOfIsTerminal_app_terminal M ht hM l⟩⟩

end Stacks.PresheafOfModules

end
