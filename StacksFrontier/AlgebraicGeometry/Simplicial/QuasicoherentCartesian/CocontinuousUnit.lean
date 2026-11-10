module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModulePushforwardCocontinuous

/-!
# The inverse image of the structure sheaf along a cocontinuous functor of sites with final objects

For a cocontinuous functor `w : X ⥤ Y` between sites with final objects and a structure map
`O_Y ⟶ w_*O_X`, a morphism `O_Y ⟶ w_*O_X` whose global section has leg `1` at the final object
transposes to an isomorphism `w^*O_Y ⟶ O_X`, whatever left adjoint `w^*` of the direct image is
used. Both sides corepresent global sections: those of `w_*N` at the final object are, through the
leg at the final object of the source, those of `N`.

## Main results

* `Stacks.SheafOfModules.isIso_homEquiv_symm_of_ranπ_one`: for a cocontinuous functor between
  sites with final objects, the transpose `w^*O_Y ⟶ O_X` of a morphism `O_Y ⟶ w_*O_X` whose global
  section has leg `1` at the final object is an isomorphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules

section Terminal

variable {X : Type u} [SmallCategory X] {R : Xᵒᵖ ⥤ RingCat.{u}} {x₀ : X} (hx : IsTerminal x₀)

/-- Two morphisms out of the opposite of a terminal object are equal. -/
private theorem eq_of_isTerminal_op {C : Type u} [SmallCategory C] {c : C} (hc : IsTerminal c)
    {A : Cᵒᵖ} (f g : op c ⟶ A) : f = g :=
  Quiver.Hom.unop_inj (hc.hom_ext _ _)

include hx in
/-- On a category with a final object, a section of a presheaf of modules is its value there. -/
theorem bijective_sections_eval_of_isTerminal (M : PresheafOfModules.{u} R) :
    Function.Bijective (fun s : M.sections => s.eval (op x₀)) := by
  constructor
  · intro s t hst
    refine PresheafOfModules.sections_ext s t fun Y => ?_
    have hs := s.2 (hx.from Y.unop).op
    have ht := t.2 (hx.from Y.unop).op
    refine hs.symm.trans (Eq.trans ?_ ht)
    exact congrArg _ hst
  · intro x
    refine ⟨PresheafOfModules.sectionsMk (fun Y => M.map (hx.from Y.unop).op x) ?_, ?_⟩
    · intro Y Y' f
      refine (PresheafOfModules.map_comp_apply M _ _ x).symm.trans ?_
      exact congrArg (fun g : op x₀ ⟶ Y' => M.map g x) (eq_of_isTerminal_op hx _ _)
    · change M.map (hx.from x₀).op x = x
      refine (congrArg (fun g : op x₀ ⟶ op x₀ => M.map g x)
        (eq_of_isTerminal_op hx (hx.from x₀).op (𝟙 _))).trans ?_
      exact ConcreteCategory.congr_hom (M.map_id (op x₀)) x

end Terminal

variable {X Y : Type u} [SmallCategory X] [SmallCategory Y]
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} (w : X ⥤ Y) [w.IsCocontinuous JX JY]
  {OX : Sheaf JX RingCat.{u}} {OY : Sheaf JY RingCat.{u}}
  (fSharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{u} JX JY).obj OX)
  {x₀ : X} (hx : IsTerminal x₀) {y₀ : Y} (hy : IsTerminal y₀)

/-- The index `(x₀, w x₀ ⟶ y₀)` of the limit computing the direct image at `y₀`. -/
abbrev terminalIndex (x₀ : X) : StructuredArrow (op y₀) w.op :=
  StructuredArrow.mk (Y := op x₀) (hy.from (w.obj x₀)).op

include hx in
/-- At the final object, a section of the direct image is determined by its leg at the final
object of the source. -/
theorem ranπ_terminalIndex_injective (N : Xᵒᵖ ⥤ AddCommGrpCat.{u})
    (z z' : (w.op.ran.obj N).obj (op y₀))
    (hzz : (ranπ w.op N (op y₀) (terminalIndex w hy x₀)).hom z =
      (ranπ w.op N (op y₀) (terminalIndex w hy x₀)).hom z') : z = z' := by
  refine Concrete.isLimit_ext _ (ranIsLimit w.op N (op y₀)) z z' fun j => ?_
  have e : terminalIndex w hy x₀ ⟶ j :=
    StructuredArrow.homMk (hx.from j.right.unop).op (eq_of_isTerminal_op hy _ _)
  change (ranπ w.op N (op y₀) j).hom z = (ranπ w.op N (op y₀) j).hom z'
  rw [← ranπ_naturality w.op N e]
  exact congrArg (N.map e.right).hom hzz

include hx hy in
/-- **The adjoint of the structure map is invertible on the structure sheaf**, for a cocontinuous
functor between sites with final objects: a morphism `O_Y ⟶ w_*O_X` whose global section has leg
`1` at the final object transposes to an isomorphism `w^*O_Y ⟶ O_X`. -/
theorem isIso_homEquiv_symm_of_ranπ_one {L : SheafOfModules.{u} OY ⥤ SheafOfModules.{u} OX}
    (adj : L ⊣ pushforwardCocontinuous.{u} w fSharp)
    (η : SheafOfModules.unit OY ⟶
      (pushforwardCocontinuous.{u} w fSharp).obj (SheafOfModules.unit OX))
    (hη : (ranπ w.op (SheafOfModules.unit OX).val.presheaf (op y₀) (terminalIndex w hy x₀)).hom
        ((η.val.app (op y₀)).hom (1 : OY.obj.obj (op y₀))) = (1 : OX.obj.obj (op x₀))) :
    IsIso ((adj.homEquiv _ _).symm η) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro N
  have e : (fun g : SheafOfModules.unit OX ⟶ N => (adj.homEquiv _ _).symm η ≫ g) =
      (adj.homEquiv _ _).symm ∘ (fun g => η ≫ (pushforwardCocontinuous.{u} w fSharp).map g) :=
    funext fun g => (adj.homEquiv_naturality_right_symm η g).symm
  rw [e]
  refine (adj.homEquiv _ _).symm.bijective.comp ?_
  have hX := (bijective_sections_eval_of_isTerminal hx N.val).comp N.unitHomEquiv.bijective
  have hY := (bijective_sections_eval_of_isTerminal hy
    ((pushforwardCocontinuous.{u} w fSharp).obj N).val).comp
      (((pushforwardCocontinuous.{u} w fSharp).obj N).unitHomEquiv).bijective
  have key : ∀ g : SheafOfModules.unit OX ⟶ N,
      (ranπ w.op N.val.presheaf (op y₀) (terminalIndex w hy x₀)).hom
        (((η ≫ (pushforwardCocontinuous.{u} w fSharp).map g).val.app (op y₀)).hom
          (1 : OY.obj.obj (op y₀))) = (g.val.app (op x₀)).hom (1 : OX.obj.obj (op x₀)) := fun g =>
    (ConcreteCategory.congr_hom (ranπ_map_functor w.op
      ((PresheafOfModules.toPresheaf _).map g.val) (op y₀) (terminalIndex w hy x₀))
      ((η.val.app (op y₀)).hom (1 : OY.obj.obj (op y₀)))).trans
      (congrArg (g.val.app (op x₀)).hom hη)
  constructor
  · intro g g' hgg
    refine hX.1 ?_
    change (g.val.app (op x₀)).hom (1 : OX.obj.obj (op x₀)) =
      (g'.val.app (op x₀)).hom (1 : OX.obj.obj (op x₀))
    exact (key g).symm.trans ((congrArg (fun t => (ranπ w.op N.val.presheaf (op y₀)
      (terminalIndex w hy x₀)).hom ((t.val.app (op y₀)).hom (1 : OY.obj.obj (op y₀)))) hgg).trans
      (key g'))
  · intro t
    obtain ⟨g, hg⟩ := hX.2 ((ranπ w.op N.val.presheaf (op y₀) (terminalIndex w hy x₀)).hom
      ((t.val.app (op y₀)).hom (1 : OY.obj.obj (op y₀))))
    refine ⟨g, hY.1 (ranπ_terminalIndex_injective w hx hy N.val.presheaf _ _ ?_)⟩
    exact (key g).trans hg

end Stacks.SheafOfModules

end
