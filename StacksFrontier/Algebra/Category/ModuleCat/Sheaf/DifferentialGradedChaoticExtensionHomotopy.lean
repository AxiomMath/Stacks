module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionHomotopy

/-!
# Homotopies and the extension from a subcategory of a chaotic site

The extension `E(X)(U) = colim_{U → F U'} X(U') ⊗_{A(F U')} A(U)` and the restriction along a
functor `F : C' ⥤ C` of chaotic sites carry homotopies to homotopies: a homotopy of presheaves of
section modules along `F` is tensored with `A(U)` term by term and passed to the colimit. So do
the identification of presheaves of section modules over the restriction `A'` with presheaves
along `F`, and the passage from a right differential graded module to its presheaf of section
modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.AlongSystem.Homotopy`: a homotopy of
  presheaves of section modules along `F`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.extHomotopy`: the extension of a
  homotopy.
* `SheafOfModules.DifferentialGradedModule.sectionSystemHomotopy`: the homotopy of presheaves of
  section modules induced by a homotopy of right differential graded modules.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open DifferentialGraded.Bimodule (tensorCompFunctor regular)

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule

/-- **The homotopy of presheaves of section modules induced by a homotopy of right differential
graded modules**: over `U` it is the homotopy on sections over `U`. -/
def sectionSystemHomotopy {C : Type u} [Category.{u} C]
    [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {M N : DifferentialGradedModule.{u, u, u} B} {f g : M ⟶ N} (h : Homotopy f g) :
    SectionSystem.Homotopy ((sectionSystemFunctor B).map f) ((sectionSystemFunctor B).map g) where
  app U := h.sections U
  naturality a x := h.sectionRestrictAdd_sectionsAdd a x

/-- The passage to presheaves of section modules carries homotopic morphisms to homotopic
morphisms. -/
theorem sectionSystem_realize_homotopic {C : Type u} [Category.{u} C]
    [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {M N : DifferentialGradedModule.{u, u, u} B} {f g : M ⟶ N} (h : Homotopy f g) :
    Homotopic ((SectionSystem.realizeFunctor B).map ((sectionSystemFunctor B).map f))
      ((SectionSystem.realizeFunctor B).map ((sectionSystemFunctor B).map g)) :=
  SectionSystem.realizeMap_homotopic (sectionSystemHomotopy h)

namespace ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] {F : C' ⥤ C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

/-- **A homotopy of presheaves of section modules along `F`**: homotopies over every object,
commuting with the restriction homomorphisms. -/
structure AlongSystem.Homotopy {X Y : AlongSystem F A} (f g : X ⟶ Y) where
  /-- The homotopy over `U'`. -/
  app (U' : C'ᵒᵖ) : _root_.DifferentialGradedModule.Homotopy (f.app U') (g.app U')
  /-- The homotopies commute with restriction. -/
  naturality {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (x : (X.obj V').M) :
    Y.restrFun a ((app V').toLinearMap x) = (app U').toLinearMap (X.restrFun a x)

/-- The restriction along `F` of a homotopy of presheaves of section modules. -/
def restrictHomotopy {Y Y' : SectionSystem A} {f g : Y ⟶ Y'} (h : SectionSystem.Homotopy f g) :
    AlongSystem.Homotopy ((restrictFunctor F A).map f) ((restrictFunctor F A).map g) where
  app U' := h.app (F.op.obj U')
  naturality a x := h.naturality (F.op.map a) x

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- A homotopy of presheaves of section modules over `A'`, read along `F`. -/
def toAlongHomotopy {X X' : SectionSystem (A.restrict F)} {f g : X ⟶ X'}
    (h : SectionSystem.Homotopy f g) :
    AlongSystem.Homotopy ((toAlong F A).map f) ((toAlong F A).map g) where
  app U' := _root_.DifferentialGradedModule.Homotopy.restrictScalars _ (h.app U')
  naturality a x := h.naturality a x

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- A homotopy of presheaves of section modules along `F`, read over `A'`. -/
def ofAlongHomotopy {Z Z' : AlongSystem F A} {f g : Z ⟶ Z'} (h : AlongSystem.Homotopy f g) :
    SectionSystem.Homotopy ((ofAlong F A).map f) ((ofAlong F A).map g) where
  app U' := _root_.DifferentialGradedModule.Homotopy.restrictScalars _ (h.app U')
  naturality a x := h.naturality a x

/-- Two composites of additive maps out of `X ⊗_B C` agreeing on the homogeneous pure tensors
agree everywhere. -/
private theorem tensor_comp_eq_of_pure
    {B B' : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ)} (ψ : B.Hom B')
    {X : _root_.DifferentialGradedModule.{u, u, u} B} {Q Q' P : Type*}
    [AddCommGroup Q] [AddCommGroup Q'] [AddCommGroup P]
    (f₁ : ((tensorCompFunctor (regular ψ)).obj X).M →+ Q) (g₁ : Q →+ P)
    (f₂ : ((tensorCompFunctor (regular ψ)).obj X).M →+ Q') (g₂ : Q' →+ P)
    (h : ∀ (p : ℤ) (x : X.grading p) (c : B'.A),
      g₁ (f₁ ((DifferentialGraded.Bimodule.tensorPure (regular ψ) X).toLinearMap (x : X.M) c)) =
        g₂ (f₂ ((DifferentialGraded.Bimodule.tensorPure (regular ψ) X).toLinearMap (x : X.M) c)))
    (z : ((tensorCompFunctor (regular ψ)).obj X).M) : g₁ (f₁ z) = g₂ (f₂ z) :=
  DFunLike.congr_fun (tensor_addHom_ext (f := g₁.comp f₁) (g := g₂.comp f₂) ψ h) z

variable {X Y : AlongSystem F A} {f g : X ⟶ Y} (h : AlongSystem.Homotopy f g)

/-- A homotopy, tensored with `A(U)` at the term `b`. -/
abbrev termHomotopy {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    _root_.DifferentialGradedModule.Homotopy (termMap f b) (termMap g b) :=
  tensorHomotopy (regular (arrowHom F A b)) (h.app (Opposite.op b.right))

/-- The tensored homotopy at the term `b` sends `x ⊗ c` to `h(x) ⊗ c`. -/
theorem termHomotopy_pure {U : Cᵒᵖ} (b : StructuredArrow U.unop F)
    (x : (X.obj (Opposite.op b.right)).M) (c : (A.sectionAlgebra U).A) :
    (termHomotopy h b).toLinearMap (pure X b x c) =
      pure Y b ((h.app (Opposite.op b.right)).toLinearMap x) c :=
  tensorHomotopy_pure (regular (arrowHom F A b)) (h.app (Opposite.op b.right)) x c

/-- The tensored homotopies at the terms commute with the transition maps of the diagram. -/
theorem termHomotopy_transition {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (φ : b' ⟶ b)
    (z : (term X b).M) :
    (termHomotopy h b').toLinearMap ((transition X φ).toFun z) =
      (transition Y φ).toFun ((termHomotopy h b).toLinearMap z) := by
  refine tensor_comp_eq_of_pure _ (transition X φ).toFun.toAddMonoidHom
    (termHomotopy h b').toLinearMap.toAddMonoidHom (termHomotopy h b).toLinearMap.toAddMonoidHom
    (transition Y φ).toFun.toAddMonoidHom (fun p x c => ?_) z
  refine (congrArg (termHomotopy h b').toLinearMap (transition_pure X φ p x c)).trans ?_
  refine (termHomotopy_pure h b' _ c).trans ?_
  refine Eq.trans ?_ (congrArg (transition Y φ).toFun (termHomotopy_pure h b x c)).symm
  refine Eq.trans ?_ (transition_pure Y φ (p - 1)
    ⟨_, (h.app (Opposite.op b.right)).map_grading p x x.2⟩ c).symm
  exact congrArg (fun w => pure Y b' w c) (h.naturality φ.right.op x).symm

/-- The tensored homotopies at the terms commute with the restriction legs along `a : V ⟶ U`. -/
theorem termHomotopy_restrLeg {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F)
    (z : (term X b).M) :
    (restrLeg Y a b).toFun ((termHomotopy h b).toLinearMap z) =
      (termHomotopy h (pre F a b)).toLinearMap ((restrLeg X a b).toFun z) := by
  refine tensor_comp_eq_of_pure _ (termHomotopy h b).toLinearMap.toAddMonoidHom
    (restrLeg Y a b).toFun.toAddMonoidHom (restrLeg X a b).toFun.toAddMonoidHom
    (termHomotopy h (pre F a b)).toLinearMap.toAddMonoidHom (fun p x c => ?_) z
  refine (congrArg (restrLeg Y a b).toFun (termHomotopy_pure h b x c)).trans ?_
  refine (restrLeg_pure Y a b (p - 1)
    ⟨_, (h.app (Opposite.op b.right)).map_grading p x x.2⟩ c).trans ?_
  refine Eq.trans ?_ (congrArg (termHomotopy h (pre F a b)).toLinearMap
    (restrLeg_pure X a b p x c)).symm
  exact (termHomotopy_pure h (pre F a b) _ _).symm

/-- The extension of a homotopy over `U`. -/
def extHomotopyApp (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.Homotopy ((extMap f).app U) ((extMap g).app U) :=
  _root_.DifferentialGradedModule.FilteredColimit.mapHomotopy
    (fun j => termHomotopy h j.unop) fun _ _ φ z => termHomotopy_transition h φ.unop z

/-- The extension of a homotopy over `U` sends the germ of `w` at `b` to the germ of the tensored
homotopy applied to `w`. -/
theorem extHomotopyApp_germ {U : Cᵒᵖ} (b : StructuredArrow U.unop F) (w : (term X b).M) :
    (extHomotopyApp h U).toLinearMap (germ X b w) = germ Y b ((termHomotopy h b).toLinearMap w) :=
  _root_.DifferentialGradedModule.FilteredColimit.homotopyLinear_germ (T := diagram X U)
    (T' := diagram Y U) (τ := diagramMap f U) (τ' := diagramMap g U)
    (fun j => termHomotopy h j.unop) (fun _ _ φ z => termHomotopy_transition h φ.unop z)
    (Opposite.op b) w

/-- The extended homotopies commute with restriction along `a : V ⟶ U` on the germ at `b`. -/
theorem extHomotopyApp_naturality_germ {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F)
    (w : (term X b).M) :
    (extSystem Y).restrFun a ((extHomotopyApp h V).toLinearMap (germ X b w)) =
      (extHomotopyApp h U).toLinearMap ((extSystem X).restrFun a (germ X b w)) := by
  refine (congrArg ((extSystem Y).restrFun a) (extHomotopyApp_germ h b w)).trans ?_
  refine (extSystem_restrFun_germ Y a b _).trans ?_
  refine Eq.trans ?_ (congrArg (extHomotopyApp h U).toLinearMap
    (extSystem_restrFun_germ X a b w)).symm
  refine Eq.trans ?_ (extHomotopyApp_germ h (pre F a b) _).symm
  exact congrArg (germ Y (pre F a b)) (termHomotopy_restrLeg h a b w)

/-- **The extension of a homotopy** of presheaves of section modules along `F`: over `U` the
homotopies `h(U') ⊗ A(U)` passed to the colimit. -/
def extHomotopy : SectionSystem.Homotopy (extMap f) (extMap g) where
  app U := extHomotopyApp h U
  naturality {U V} a z := by
    obtain ⟨j, w, rfl⟩ := _root_.DifferentialGradedModule.FilteredColimit.exists_germ
      (diagram X V) z
    exact extHomotopyApp_naturality_germ h a j.unop w

end ChaoticExtension

end DifferentialGradedModule

end SheafOfModules

end
