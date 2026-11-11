module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerExtendAfterShrinking
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionFromNeighborhoods
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of finite étale covers extend near a closed subscheme

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with ideal sheaf `I`, and `𝒱` the open
subschemes of `X` containing `Y`, ordered by reverse inclusion. [Stacks, Tag 0ELA] asserts that the
restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful as soon as the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully faithful on the finite locally free objects. This file
proves it under exactly that hypothesis, condition (4) of [Stacks, Tag 0EK2], which in this library
is `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`.

The proof follows the source. By the internal hom of finite étale coverings, the reduction
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme` shows it
suffices to extend sections. Let `U` be finite étale over a neighbourhood `V`, with direct image
algebra `A = f_* 𝒪_U`, whose underlying module is finite locally free. Then:

* A section `t` of `U` over `Y` lifts uniquely to the infinitesimal neighbourhoods `Y_n`
  ([Stacks, Tag 0BQB]). By the universal property of the relative spectrum these lifts are
  compatible morphisms of algebra sheaves `A ⟶ (Y_n ⟶ V)_* 𝒪_{Y_n}`.
* The completion hypothesis, read through
  `Stacks.Algebraization.TowerUnit.exists_hom`, algebraizes the underlying module maps to a module
  map `σ : A ⟶ (W ⟶ V)_* 𝒪_W` on some smaller neighbourhood `W`.
* `σ` is not yet a morphism of algebra sheaves. Its unit square and its multiplication square,
  whose source `A ⊗ A` is finite locally free, commute on every `Y_n`. So by the faithfulness
  half of the hypothesis (`Stacks.Algebraization.TowerUnit.eq_of_forall`) they commute after a
  further shrinking. This is the source's last step.
* Two sections agreeing on `Y` agree on every `Y_n`, so their module maps agree after shrinking.

## Main results

* `Stacks.FundamentalGroup.sectionsExtendNearSubscheme_of_completionFullyFaithfulComplete`: the
  section-extension property `Stacks.FundamentalGroup.SectionsExtendNearSubscheme`, the
  shrinking form of the conclusion of [Stacks, Tag 0EL8], derived from full faithfulness of
  completion.
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete`:
  [Stacks, Tag 0ELA].
* `Stacks.FundamentalGroup.SectionsNearTower.exists_section` and `eq_section`: the same two
  statements for an abstract tower over a scheme, from which the neighbourhood statements are
  instantiated.

## Implementation notes

The morphisms into direct images are typed as morphisms into
`AlgebraSheaf.underlyingModule (pushforwardAlgebra g)`, never into
`(Scheme.Modules.pushforward g).obj (Scheme.unitModule G)`. The two are definitionally equal, but
composing a morphism typed the second way with the multiplication of an algebra sheaf makes the
elaborator unfold the tensor product of sheaves, and that exhausts its budget.

The multiplicativity criterion
`Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective` cannot be used as it stands.
It asks for joint injectivity of the restrictions to the `Y_n` on all morphisms into
`(W ⟶ V)_* 𝒪_W`, and that holds only after shrinking `W`, by an amount that depends on the
morphisms. The two squares are therefore shrunk separately, and the morphism of algebra sheaves is
built directly with `Stacks.RelativeSpec.AlgebraSheaf.homOfMultiplicative`.

## References

* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Stacks.Algebraization
open Stacks.SheafOfModules.TensorStalkRingedSpace TensorProduct

universe u

namespace Stacks.FundamentalGroup

/-! ### Multiplicativity of a morphism of underlying modules, one restriction at a time -/

section Multiplicativity

variable {S : Scheme.{u}}

/-- The tensor square of a morphism of sheaves of modules. -/
abbrev tensorSquareMap {M N : S.Modules} (σ : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.presheaf, S.IsSheaf⟩).obj M).obj M ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.presheaf, S.IsSheaf⟩).obj N).obj N :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.presheaf, S.IsSheaf⟩).map σ).app _ ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.presheaf, S.IsSheaf⟩).obj _).map σ

/-- If a morphism `σ` of underlying modules becomes a morphism of algebra sheaves `ψ` after
composition with a morphism of algebra sheaves `r`, then the multiplication square of `σ`
commutes after composition with `r`. -/
theorem multiplication_comp_eq_of_comp_eq {A C D : AlgebraSheaf S}
    (σ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule C) (r : C ⟶ D)
    (ψ : A ⟶ D) (hψ : σ ≫ AlgebraSheaf.underlyingModuleMap r = AlgebraSheaf.underlyingModuleMap ψ) :
    (AlgebraSheaf.multiplication A ≫ σ) ≫ AlgebraSheaf.underlyingModuleMap r =
      (tensorSquareMap σ ≫ AlgebraSheaf.multiplication C) ≫
        AlgebraSheaf.underlyingModuleMap r := by
  have hcomp : ∀ (U : (S.Opens)ᵒᵖ) (z : (AlgebraSheaf.underlyingModule A).val.obj U),
      ((AlgebraSheaf.underlyingModuleMap r).val.app U).hom ((σ.val.app U).hom z)
        = ((AlgebraSheaf.underlyingModuleMap ψ).val.app U).hom z := fun U z =>
    congrArg (fun t : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule D =>
      (t.val.app U).hom z) hψ
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun t => AlgebraSheaf.multiplication A ≫ t) hψ)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine hom_ext_toTensorSheafSection S.toRingedSpace _ _ fun U x y => ?_
  refine (AlgebraSheaf.multiplication_comp_tmul (AlgebraSheaf.underlyingModuleMap ψ) U x y).trans ?_
  refine Eq.trans ?_ (AlgebraSheaf.tensorSheafMap_comp_tmul σ
    (AlgebraSheaf.multiplication C ≫ AlgebraSheaf.underlyingModuleMap r) U x y).symm
  refine Eq.trans ?_ (AlgebraSheaf.multiplication_comp_tmul (AlgebraSheaf.underlyingModuleMap r) U
    ((σ.val.app U).hom x) ((σ.val.app U).hom y)).symm
  refine (AlgebraSheaf.underlyingModuleMap_mulSection ψ U x y).trans ?_
  refine Eq.trans ?_ (AlgebraSheaf.underlyingModuleMap_mulSection r U
    ((σ.val.app U).hom x) ((σ.val.app U).hom y)).symm
  rw [hcomp U x, hcomp U y]

/-- If the multiplication square of `σ` commutes after composition with a morphism of algebra
sheaves `r`, then `σ ≫ r` is multiplicative on sections. -/
theorem mulSection_of_multiplication_comp_eq {A C D : AlgebraSheaf S}
    (σ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule C) (r : C ⟶ D)
    (h : (AlgebraSheaf.multiplication A ≫ σ) ≫ AlgebraSheaf.underlyingModuleMap r =
      (tensorSquareMap σ ≫ AlgebraSheaf.multiplication C) ≫ AlgebraSheaf.underlyingModuleMap r)
    (U : (S.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    ((σ ≫ AlgebraSheaf.underlyingModuleMap r).val.app U).hom (AlgebraSheaf.mulSection A U x y) =
      AlgebraSheaf.mulSection D U
        (((σ ≫ AlgebraSheaf.underlyingModuleMap r).val.app U).hom x)
        (((σ ≫ AlgebraSheaf.underlyingModuleMap r).val.app U).hom y) := by
  have e1 : AlgebraSheaf.multiplication A ≫ σ ≫ AlgebraSheaf.underlyingModuleMap r =
      tensorSquareMap σ ≫ AlgebraSheaf.multiplication C ≫ AlgebraSheaf.underlyingModuleMap r :=
    (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
  refine (AlgebraSheaf.multiplication_comp_tmul (σ ≫ AlgebraSheaf.underlyingModuleMap r)
    U x y).symm.trans ?_
  refine (congrArg (fun t => (t.val.app U).hom (toTensorSheafSection S.toRingedSpace
    (AlgebraSheaf.underlyingModule A) (AlgebraSheaf.underlyingModule A) U
      (x ⊗ₜ[S.presheaf.obj U] y))) e1).trans ?_
  refine (AlgebraSheaf.tensorSheafMap_comp_tmul σ
    (AlgebraSheaf.multiplication C ≫ AlgebraSheaf.underlyingModuleMap r) U x y).trans ?_
  refine (AlgebraSheaf.multiplication_comp_tmul (AlgebraSheaf.underlyingModuleMap r) U
    ((σ.val.app U).hom x) ((σ.val.app U).hom y)).trans ?_
  exact AlgebraSheaf.underlyingModuleMap_mulSection r U _ _

/-- If `σ ≫ r` is a morphism of algebra sheaves, the unit square of `σ` commutes after
composition with `r`. -/
theorem unitModuleMap_comp_eq_of_comp_eq {A C D : AlgebraSheaf S}
    (σ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule C) (r : C ⟶ D)
    (ψ : A ⟶ D) (hψ : σ ≫ AlgebraSheaf.underlyingModuleMap r = AlgebraSheaf.underlyingModuleMap ψ) :
    (AlgebraSheaf.unitModuleMap A ≫ σ) ≫ AlgebraSheaf.underlyingModuleMap r =
      AlgebraSheaf.unitModuleMap C ≫ AlgebraSheaf.underlyingModuleMap r :=
  (Category.assoc _ _ _).trans ((congrArg (fun t => AlgebraSheaf.unitModuleMap A ≫ t) hψ).trans
    ((AlgebraSheaf.unitModuleMap_comp ψ).trans (AlgebraSheaf.unitModuleMap_comp r).symm))

/-- If the unit square of `σ` commutes after composition with a morphism of algebra sheaves
`r`, then `σ ≫ r` is unital on sections. -/
theorem oneSection_of_unitModuleMap_comp_eq {A C D : AlgebraSheaf S}
    (σ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule C) (r : C ⟶ D)
    (h : (AlgebraSheaf.unitModuleMap A ≫ σ) ≫ AlgebraSheaf.underlyingModuleMap r =
      AlgebraSheaf.unitModuleMap C ≫ AlgebraSheaf.underlyingModuleMap r)
    (U : (S.Opens)ᵒᵖ) :
    ((σ ≫ AlgebraSheaf.underlyingModuleMap r).val.app U).hom (AlgebraSheaf.oneSection A U) =
      AlgebraSheaf.oneSection D U := by
  rw [AlgebraSheaf.unitModuleMap_comp r] at h
  refine (AlgebraSheaf.unitModuleMap_comp_one (σ ≫ AlgebraSheaf.underlyingModuleMap r)
    U).symm.trans ?_
  refine (congrArg (fun t : SheafOfModules.unit S.ringCatSheaf ⟶ AlgebraSheaf.underlyingModule D =>
    (t.val.app U).hom (1 : S.presheaf.obj U)) ((Category.assoc _ _ _).symm.trans h)).trans ?_
  exact AlgebraSheaf.unitModuleMap_one D U

/-- A morphism of algebra sheaves is determined by its morphism of underlying modules. -/
theorem algebraSheafHom_ext_of_underlyingModuleMap {A B : AlgebraSheaf S} {f g : A ⟶ B}
    (h : AlgebraSheaf.underlyingModuleMap f = AlgebraSheaf.underlyingModuleMap g) : f = g := by
  have happ : ∀ (U : (S.Opens)ᵒᵖ) (x : (A.right.obj.obj U : Type u)),
      (f.right.hom.app U).hom x = (g.right.hom.app U).hom x := fun U x =>
    congrArg (fun φ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule B =>
      φ.val.app U x) h
  refine Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
  exact CommRingCat.hom_ext (RingHom.ext (happ U))

end Multiplicativity

/-! ### Sections of an affine morphism as morphisms of algebra sheaves -/

section Sections

variable {S V : Scheme.{u}} (f : V ⟶ S) [IsAffineHom f]

/-- **Sections of an affine morphism over a morphism `g` are morphisms of algebra sheaves**
`f_* 𝒪_V ⟶ g_* 𝒪_G`, by the universal property of the relative spectrum. -/
def sectionAlgebraHomEquiv {G : Scheme.{u}} (g : G ⟶ S) :
    {s : G ⟶ V // s ≫ f = g} ≃ (pushforwardAlgebra f ⟶ pushforwardAlgebra g) :=
  haveI : IsAffineHom (Over.mk f : Over S).hom := ‹IsAffineHom f›
  ({ toFun := fun s => (Over.homMk s.1 s.2 : (Over.mk g : Over S) ⟶ Over.mk f)
     invFun := fun u => ⟨u.left, Over.w u⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
      {s : G ⟶ V // s ≫ f = g} ≃ ((Over.mk g : Over S) ⟶ Over.mk f)).trans
    (overHomEquivAlgebraHom (Over.mk g) (Over.mk f))

/-- `sectionAlgebraHomEquiv` is the canonical morphism of direct image algebras. -/
theorem sectionAlgebraHomEquiv_apply {G : Scheme.{u}} (g : G ⟶ S) (s : {s : G ⟶ V // s ≫ f = g}) :
    sectionAlgebraHomEquiv f g s =
      pushforwardAlgebraMap (Over.homMk s.1 s.2 : (Over.mk g : Over S) ⟶ Over.mk f) :=
  have : IsAffineHom (Over.mk f : Over S).hom := ‹IsAffineHom f›
  overHomEquivAlgebraHom_apply _

/-- Restricting a section along `h` is composition with the restriction map of direct images. -/
theorem underlyingModuleMap_sectionAlgebraHomEquiv_comp {G G' : Scheme.{u}} (g : G ⟶ S)
    (s : {s : G ⟶ V // s ≫ f = g}) (h : G' ⟶ G) (g' : G' ⟶ S) (hh : h ≫ g = g') :
    AlgebraSheaf.underlyingModuleMap
        (sectionAlgebraHomEquiv f g' ⟨h ≫ s.1, show (h ≫ s.1) ≫ f = g' by
          rw [Category.assoc, s.2, hh]⟩) =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f g s) ≫
        pushforwardUnitRestriction g h g' hh := by
  rw [sectionAlgebraHomEquiv_apply, sectionAlgebraHomEquiv_apply, pushforwardUnitRestriction,
    pushforwardAlgebraRestriction]
  have e : (Over.homMk (h ≫ s.1) (show (h ≫ s.1) ≫ f = g' by rw [Category.assoc, s.2, hh]) :
      (Over.mk g' : Over S) ⟶ Over.mk f) =
        (Over.homMk h hh : (Over.mk g' : Over S) ⟶ Over.mk g) ≫
          (Over.homMk s.1 s.2 : (Over.mk g : Over S) ⟶ Over.mk f) :=
    Over.OverMorphism.ext rfl
  rw [e, pushforwardAlgebraMap_comp]
  exact (AlgebraSheaf.underlyingModuleFunctor S).map_comp _ _

end Sections

/-! ### Sections near the support of a tower -/

namespace SectionsNearTower

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (T : InfinitesimalTower S)
  (hT : ∀ P : S.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
    T.IsHomsComplete P (Scheme.unitModule S))
include hT

/-- **A compatible system of sections of a finite étale cover over the terms of a tower comes
from a section over a neighbourhood of the support**, granted condition (4) of
[Stacks, Tag 0EK2] for all pairs `(P, 𝒪_S)` with `P` finite locally free. -/
theorem exists_section (U : FiniteEtaleOver S) (τ : ∀ n : ℕ, (T.obj n).left ⟶ U.left)
    (hτ : ∀ n : ℕ, τ n ≫ U.hom = (T.obj n).hom)
    (hcompat : ∀ (n m : ℕ) (h : n ≤ m), (T.trans n m h).left ≫ τ m = τ n) :
    ∃ (W : S.Opens) (hW : T.support ⊆ W) (s : W.toScheme ⟶ U.left),
      s ≫ U.hom = W.ι ∧ ∀ n : ℕ, T.homToOpen hW n ≫ s = τ n := by
  have : IsFinite U.hom := U.prop.1
  have : Etale U.hom := U.prop.2
  have hN := ExtendedEtale.isFiniteLocallyFree_underlyingModule_pushforwardAlgebra
    (U := S) (V := U.left) U.hom
  let α : ∀ n : ℕ, AlgebraSheaf.underlyingModule (pushforwardAlgebra U.hom) ⟶
      (Scheme.Modules.pushforward (T.obj n).hom).obj (Scheme.unitModule (T.obj n).left) :=
    fun n => AlgebraSheaf.underlyingModuleMap
      (sectionAlgebraHomEquiv U.hom (T.obj n).hom ⟨τ n, hτ n⟩)
  have hα : ∀ (n m : ℕ) (h : n ≤ m), α m ≫
      pushforwardUnitRestriction (T.obj m).hom (T.trans n m h).left
      (T.obj n).hom (Over.w (T.trans n m h)) = α n :=
    fun n m h => (underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom (T.obj m).hom
      ⟨τ m, hτ m⟩ (T.trans n m h).left (T.obj n).hom (Over.w (T.trans n m h))).symm.trans
      (congrArg (fun z => AlgebraSheaf.underlyingModuleMap
        (sectionAlgebraHomEquiv U.hom (T.obj n).hom z)) (Subtype.ext (hcompat n m h)))
  obtain ⟨W, hW, σ, hσ⟩ := TowerUnit.exists_hom T _ (hT _ hN) α hα
  obtain ⟨W₁, hW₁, h₁, he₁⟩ := TowerUnit.eq_of_forall T _
    (hT _ (AlgebraSheaf.isFiniteLocallyFree_tensorSquare _ hN)) W hW _ _
    fun n => multiplication_comp_eq_of_comp_eq σ _ _ (hσ n)
  obtain ⟨W₂, hW₂, h₂, he₂⟩ := TowerUnit.eq_of_forall T _
    (hT _ (AlgebraSheaf.isFiniteLocallyFree_unitModule S)) W hW _ _
    fun n => unitModuleMap_comp_eq_of_comp_eq σ _ _ (hσ n)
  have hW₃ : T.support ⊆ W₁ ⊓ W₂ := fun x hx => ⟨hW₁ hx, hW₂ hx⟩
  have h₁₃ : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have h₂₃ : W₁ ⊓ W₂ ≤ W₂ := inf_le_right
  have h₃ : W₁ ⊓ W₂ ≤ W := h₁₃.trans h₁
  have e : ∀ {W₀ : S.Opens} (h₀ : W₀ ≤ W) (h₀' : W₁ ⊓ W₂ ≤ W₀),
      (σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₀) W₀.ι (S.homOfLE_ι h₀)) ≫
        pushforwardUnitRestriction W₀.ι (S.homOfLE h₀') (W₁ ⊓ W₂).ι (S.homOfLE_ι h₀') =
        σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι (S.homOfLE_ι h₃) :=
    fun h₀ h₀' => (Category.assoc _ _ _).trans (congrArg (fun t => σ ≫ t)
      (pushforwardUnitRestriction_comp _ _ _ _ _ _ _ (S.homOfLE h₃) (S.homOfLE_homOfLE h₀' h₀)))
  have hmul : ∀ (U' : (S.Opens)ᵒᵖ) (x y : (pushforwardAlgebra U.hom).right.obj.obj U'),
      (((σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι
          (S.homOfLE_ι h₃)).val.app U').hom
          (AlgebraSheaf.mulSection _ U' x y)) =
        AlgebraSheaf.mulSection _ U'
          (((σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι
            (S.homOfLE_ι h₃)).val.app U').hom x)
          (((σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι
            (S.homOfLE_ι h₃)).val.app U').hom y) := by
    intro U' x y
    rw [← e h₁ h₁₃]
    refine (congrArg (fun z => ((pushforwardUnitRestriction W₁.ι (S.homOfLE h₁₃) (W₁ ⊓ W₂).ι
        (S.homOfLE_ι h₁₃)).val.app U').hom z)
      (mulSection_of_multiplication_comp_eq σ _ he₁ U' x y)).trans ?_
    exact AlgebraSheaf.underlyingModuleMap_mulSection _ U' _ _
  have hone : ∀ U' : (S.Opens)ᵒᵖ,
      (((σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι
          (S.homOfLE_ι h₃)).val.app U').hom
          (AlgebraSheaf.oneSection _ U')) = AlgebraSheaf.oneSection _ U' := by
    intro U'
    rw [← e h₂ h₂₃]
    refine (congrArg (fun z => ((pushforwardUnitRestriction W₂.ι (S.homOfLE h₂₃) (W₁ ⊓ W₂).ι
        (S.homOfLE_ι h₂₃)).val.app U').hom z)
      (oneSection_of_unitModuleMap_comp_eq σ _ he₂ U')).trans ?_
    exact AlgebraSheaf.underlyingModuleMap_oneSection _ U'
  let ψ := AlgebraSheaf.homOfMultiplicative
    (σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι (S.homOfLE_ι h₃)) hone hmul
  let s := (sectionAlgebraHomEquiv U.hom (W₁ ⊓ W₂).ι).symm ψ
  refine ⟨W₁ ⊓ W₂, hW₃, s.1, s.2, fun n => ?_⟩
  have hk : T.homToOpen hW₃ n ≫ S.homOfLE h₃ = T.homToOpen hW n :=
    (cancel_mono W.ι).1 (by
      rw [Category.assoc, Scheme.homOfLE_ι, T.homToOpen_ι, T.homToOpen_ι])
  have hs : AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv U.hom (W₁ ⊓ W₂).ι s) =
      σ ≫ pushforwardUnitRestriction W.ι (S.homOfLE h₃) (W₁ ⊓ W₂).ι (S.homOfLE_ι h₃) :=
    (congrArg AlgebraSheaf.underlyingModuleMap
      ((sectionAlgebraHomEquiv U.hom (W₁ ⊓ W₂).ι).apply_symm_apply ψ)).trans
      (AlgebraSheaf.underlyingModuleMap_homOfMultiplicative _ hone hmul)
  have key := ((underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom (W₁ ⊓ W₂).ι s
    (T.homToOpen hW₃ n) (T.obj n).hom (T.homToOpen_ι hW₃ n)).trans
      (congrArg (fun t => t ≫
        pushforwardUnitRestriction (W₁ ⊓ W₂).ι (T.homToOpen hW₃ n) (T.obj n).hom
        (T.homToOpen_ι hW₃ n)) hs)).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun t => σ ≫ t)
      (pushforwardUnitRestriction_comp _ _ _ _ _ _ _ _ hk)).trans (hσ n)))
  exact congrArg Subtype.val ((sectionAlgebraHomEquiv U.hom (T.obj n).hom).injective
    (algebraSheafHom_ext_of_underlyingModuleMap key))

/-- **Two sections of a finite étale cover over a neighbourhood of the support of a tower that
agree on every term of the tower agree on a smaller neighbourhood**, granted condition (4) of
[Stacks, Tag 0EK2] for all pairs `(P, 𝒪_S)` with `P` finite locally free. -/
theorem eq_section (U : FiniteEtaleOver S) (W : S.Opens) (hW : T.support ⊆ W)
    (s₁ s₂ : W.toScheme ⟶ U.left) (hs₁ : s₁ ≫ U.hom = W.ι) (hs₂ : s₂ ≫ U.hom = W.ι)
    (h : ∀ n : ℕ, T.homToOpen hW n ≫ s₁ = T.homToOpen hW n ≫ s₂) :
    ∃ (W' : S.Opens) (_ : T.support ⊆ W') (hle : W' ≤ W),
      S.homOfLE hle ≫ s₁ = S.homOfLE hle ≫ s₂ := by
  have : IsFinite U.hom := U.prop.1
  have : Etale U.hom := U.prop.2
  have hN := ExtendedEtale.isFiniteLocallyFree_underlyingModule_pushforwardAlgebra
    (U := S) (V := U.left) U.hom
  obtain ⟨W', hW', hle, he⟩ := TowerUnit.eq_of_forall T _ (hT _ hN) W hW
    (AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv U.hom W.ι ⟨s₁, hs₁⟩))
    (AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv U.hom W.ι ⟨s₂, hs₂⟩))
    (fun n => (underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom W.ι ⟨s₁, hs₁⟩
        (T.homToOpen hW n) (T.obj n).hom (T.homToOpen_ι hW n)).symm.trans
      ((congrArg (fun z => AlgebraSheaf.underlyingModuleMap
        (sectionAlgebraHomEquiv U.hom (T.obj n).hom z)) (Subtype.ext (h n))).trans
      (underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom W.ι ⟨s₂, hs₂⟩
        (T.homToOpen hW n) (T.obj n).hom (T.homToOpen_ι hW n))))
  refine ⟨W', hW', hle, ?_⟩
  have he' := ((underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom W.ι ⟨s₁, hs₁⟩
      (S.homOfLE hle) W'.ι (S.homOfLE_ι hle)).trans he).trans
    (underlyingModuleMap_sectionAlgebraHomEquiv_comp U.hom W.ι ⟨s₂, hs₂⟩
      (S.homOfLE hle) W'.ι (S.homOfLE_ι hle)).symm
  exact congrArg Subtype.val ((sectionAlgebraHomEquiv U.hom W'.ι).injective
    (algebraSheafHom_ext_of_underlyingModuleMap he'))

end SectionsNearTower

/-! ### The tower of infinitesimal neighbourhoods read over a neighbourhood -/

section Neighbourhoods

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- A neighbourhood of the closed subscheme contains the image of its closed immersion. -/
theorem range_subschemeι_subset_open (V : Neighborhood X Y) :
    Set.range Y.subschemeι.base ⊆ (Neighborhood.open X Y V : Set X) := by
  rw [Y.range_subschemeι]
  exact Neighborhood.support_subset_open X Y V

/-- The inclusion of the closed subscheme into its `n`-th infinitesimal neighbourhood, with the
neighbourhood spelled as the `n`-th term of the tower read over an open `V`. -/
def nbhdInclusion (V : X.Opens) (hV : Set.range Y.subschemeι.base ⊆ V) (n : ℕ) :
    Y.subscheme ⟶ ((nbhdTower Y.subschemeι V hV).obj n).left :=
  Stacks.Thickenings.nthOrderInclusion Y.subschemeι n

/-- The inclusion into the `n`-th infinitesimal neighbourhood is a thickening. -/
theorem isThickening_nbhdInclusion (V : X.Opens) (hV : Set.range Y.subschemeι.base ⊆ V)
    (n : ℕ) : Stacks.Thickenings.IsThickening (nbhdInclusion X Y V hV n) :=
  Stacks.Thickenings.nthOrderInclusion_isThickening Y.subschemeι n

/-- The inclusion into the `n`-th infinitesimal neighbourhood factors the closed immersion. -/
theorem nbhdInclusion_ι (V : X.Opens) (hV : Set.range Y.subschemeι.base ⊆ V) (n : ℕ) :
    nbhdInclusion X Y V hV n ≫ nthInfinitesimalNeighbourhoodι Y.subschemeι n = Y.subschemeι :=
  Stacks.Thickenings.nthOrderInclusion_toBase Y.subschemeι n

/-- The inclusion of the closed subscheme into the `n`-th infinitesimal neighbourhood, followed by
the structure morphism of that neighbourhood read over an open `V`, is any factorization of the
closed immersion through `V`. -/
theorem nbhdInclusion_comp_hom (V : X.Opens) (hV : Set.range Y.subschemeι.base ⊆ V)
    (r : Y.subscheme ⟶ V.toScheme) (hr : r ≫ V.ι = Y.subschemeι) (n : ℕ) :
    nbhdInclusion X Y V hV n ≫ ((nbhdTower Y.subschemeι V hV).obj n).hom = r :=
  (cancel_mono V.ι).1 ((Category.assoc _ _ _).trans
    ((congrArg (fun k => nbhdInclusion X Y V hV n ≫ k)
      (nbhdOver_hom_ι Y.subschemeι V hV n)).trans
      ((nbhdInclusion_ι X Y V hV n).trans hr.symm)))

/-- The inclusion of the closed subscheme into the `n`-th infinitesimal neighbourhood, followed by
the map of that neighbourhood into an open `W` of `V` containing the support, is the closed
immersion into `V`. -/
private theorem nbhdInclusion_comp_homToOpen_comp_ι (V : Neighborhood X Y)
    (hV : Set.range Y.subschemeι.base ⊆ (Neighborhood.open X Y V : Set X))
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (nbhdTower Y.subschemeι _ hV).support ⊆ W) (n : ℕ) :
    nbhdInclusion X Y _ hV n ≫ (nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ W.ι =
      Neighborhood.toSchemeHom X Y V := by
  rw [InfinitesimalTower.homToOpen_ι,
    nbhdInclusion_comp_hom X Y _ hV _ (Neighborhood.toSchemeHom_fac X Y V)]

/-- The inclusions of the closed subscheme into its infinitesimal neighbourhoods are compatible
with the transition morphisms of the tower. -/
theorem nbhdInclusion_comp_trans (V : X.Opens) (hV : Set.range Y.subschemeι.base ⊆ V)
    {n m : ℕ} (h : n ≤ m) :
    nbhdInclusion X Y V hV n ≫ ((nbhdTower Y.subschemeι V hV).trans n m h).left =
      nbhdInclusion X Y V hV m := by
  have : Mono (nthInfinitesimalNeighbourhoodι Y.subschemeι m) :=
    (inferInstance : Mono (Stacks.Thickenings.nthOrderToBase Y.subschemeι m))
  refine (cancel_mono (nthInfinitesimalNeighbourhoodι Y.subschemeι m)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine ((congrArg (fun k => nbhdInclusion X Y V hV n ≫ k)
    (Over.w (nthInfinitesimalNeighbourhoodTransition Y.subschemeι h))).trans ?_)
  exact (nbhdInclusion_ι X Y V hV n).trans (nbhdInclusion_ι X Y V hV m).symm

/-- **Sections over the infinitesimal neighbourhoods are sections over the closed subscheme**
([Stacks, Tag 0BQB]): restriction of sections of a finite étale cover of `V` from the `n`-th
infinitesimal neighbourhood to the closed subscheme is bijective, because the inclusion is a
thickening. -/
theorem bijective_restrictSection_nbhdInclusion (V : X.Opens)
    (hV : Set.range Y.subschemeι.base ⊆ V) (r : Y.subscheme ⟶ V.toScheme)
    (hr : r ≫ V.ι = Y.subschemeι) (U : FiniteEtaleOver V.toScheme) (n : ℕ) :
    (∀ t : Y.subscheme ⟶ U.left, t ≫ U.hom = r →
      ∃ a : ((nbhdTower Y.subschemeι V hV).obj n).left ⟶ U.left,
        a ≫ U.hom = ((nbhdTower Y.subschemeι V hV).obj n).hom ∧
          nbhdInclusion X Y V hV n ≫ a = t) ∧
    ∀ a b : ((nbhdTower Y.subschemeι V hV).obj n).left ⟶ U.left,
      a ≫ U.hom = ((nbhdTower Y.subschemeι V hV).obj n).hom →
      b ≫ U.hom = ((nbhdTower Y.subschemeι V hV).obj n).hom →
      nbhdInclusion X Y V hV n ≫ a = nbhdInclusion X Y V hV n ≫ b → a = b := by
  have hE : (finiteEtaleBaseChange (nbhdInclusion X Y V hV n)).IsEquivalence :=
    finiteEtaleBaseChange_isEquivalence_of_isThickening _ (isThickening_nbhdInclusion X Y V hV n)
  have hb := bijective_restrictSection_of_fullyFaithful _ (nbhdInclusion X Y V hV n) r
    (nbhdInclusion_comp_hom X Y V hV r hr n) (.ofFullyFaithful _) U
  refine ⟨fun t ht => ?_, fun a b ha hb' hab => ?_⟩
  · obtain ⟨⟨a, ha⟩, hat⟩ := hb.2 ⟨t, ht⟩
    exact ⟨a, ha, congrArg Subtype.val hat⟩
  · exact congrArg Subtype.val (hb.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb'⟩) (Subtype.ext hab))

/-- The support of the tower of infinitesimal neighbourhoods read over a neighbourhood `V` is the
image of the closed subscheme in `V`. -/
theorem nbhdTower_support (V : Neighborhood X Y) (hV : Set.range Y.subschemeι.base ⊆
      (Neighborhood.open X Y V : Set X)) :
    (nbhdTower Y.subschemeι _ hV).support = Set.range (Neighborhood.toSchemeHom X Y V).base := by
  have e : nbhdImmersion Y.subschemeι _ hV = Neighborhood.toSchemeHom X Y V :=
    (cancel_mono (Neighborhood.open X Y V).ι).1
      ((nbhdImmersion_ι Y.subschemeι _ hV).trans (Neighborhood.toSchemeHom_fac X Y V).symm)
  change Set.range (nbhdImmersion Y.subschemeι _ hV).base = _
  rw [e]

/-- An open of a neighbourhood containing the support of the tower receives the closed
subscheme. -/
theorem exists_lift_of_support_subset (V : Neighborhood X Y) (hV : Set.range Y.subschemeι.base ⊆
      (Neighborhood.open X Y V : Set X)) (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (nbhdTower Y.subschemeι _ hV).support ⊆ W) :
    ∃ r : Y.subscheme ⟶ W.toScheme, r ≫ W.ι = Neighborhood.toSchemeHom X Y V := by
  rw [nbhdTower_support X Y V hV] at hW
  exact ⟨IsOpenImmersion.lift W.ι (Neighborhood.toSchemeHom X Y V)
    (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩

/-- The image in `X` of an open of a neighbourhood that receives the closed subscheme, as a
neighbourhood. -/
def Neighborhood.ofOpen (V : Neighborhood X Y) (W : (Neighborhood.open X Y V).toScheme.Opens)
    (r : Y.subscheme ⟶ W.toScheme) (hr : r ≫ W.ι = Neighborhood.toSchemeHom X Y V) :
    Neighborhood X Y :=
  OrderDual.toDual ⟨(Neighborhood.open X Y V).ι ''ᵁ W,
    r ≫ ((Neighborhood.open X Y V).ι.isoImage W).hom,
    (Category.assoc _ _ _).trans ((congrArg (fun k => r ≫ k)
      (Scheme.Hom.isoImage_hom_ι (Neighborhood.open X Y V).ι W)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ (Neighborhood.open X Y V).ι)
        hr).trans (Neighborhood.toSchemeHom_fac X Y V))))⟩

/-- The image of an open of a neighbourhood lies in that neighbourhood. -/
theorem Neighborhood.ofOpen_le (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens) (r : Y.subscheme ⟶ W.toScheme)
    (hr : r ≫ W.ι = Neighborhood.toSchemeHom X Y V) :
    V ≤ Neighborhood.ofOpen X Y V W r hr :=
  ((Neighborhood.open X Y V).ι.image_le_opensRange W).trans
    (Scheme.Opens.opensRange_ι (Neighborhood.open X Y V)).le

end Neighbourhoods

/-! ### Tag 0ELA -/

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- **Sections of finite étale covers extend near the closed subscheme, from full faithfulness
of completion** (the shrinking form of [Stacks, Tag 0EL8]). Let `X` be a Noetherian scheme and
`Y ⊆ X` a closed subscheme. If the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully
faithful on the finite locally free objects, then for every open neighbourhood `V` of `Y` and
every finite étale cover `U` of `V`, every section of `U` over `Y` extends to a section over a
smaller neighbourhood, and two sections over a neighbourhood that agree over `Y` agree over a
smaller one. -/
theorem sectionsExtendNearSubscheme_of_completionFullyFaithfulComplete [IsNoetherian X]
    (h : NeighbourhoodCompletion.CompletionFullyFaithfulComplete Y.subschemeι) :
    SectionsExtendNearSubscheme X Y := by
  have hT : ∀ (V : Neighborhood X Y) (P : (Neighborhood.open X Y V).toScheme.Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
      (nbhdTower Y.subschemeι _ (range_subschemeι_subset_open X Y V)).IsHomsComplete P
        (Scheme.unitModule _) := fun V P hP =>
    h _ _ P _ hP (AlgebraSheaf.isFiniteLocallyFree_unitModule _)
  have hbij := fun V U => bijective_restrictSection_nbhdInclusion X Y _
    (range_subschemeι_subset_open X Y V) _ (Neighborhood.toSchemeHom_fac X Y V) U
  refine ⟨fun V U t ht => ?_, fun V V' iVV' U s₁ s₂ hs₁ hs₂ hs => ?_⟩
  · have hV := range_subschemeι_subset_open X Y V
    have hT := hT V
    have hbij := hbij V U
    choose a ha hat using fun n => (hbij n).1 t ht
    have hcompat : ∀ (n m : ℕ) (hnm : n ≤ m),
        ((nbhdTower Y.subschemeι _ hV).trans n m hnm).left ≫ a m = a n := by
      intro n m hnm
      refine (hbij n).2 _ _ ?_ (ha n) ?_
      · rw [Category.assoc, ha m]
        exact Over.w ((nbhdTower Y.subschemeι _ hV).trans n m hnm)
      · rw [← Category.assoc, nbhdInclusion_comp_trans X Y _ hV hnm, hat m, hat n]
    obtain ⟨W, hW, s, hsU, hsn⟩ := SectionsNearTower.exists_section _ hT U a ha hcompat
    obtain ⟨r, hr⟩ := exists_lift_of_support_subset X Y V hV W hW
    have hfac : Neighborhood.toSchemeHom X Y (Neighborhood.ofOpen X Y V W r hr) ≫
        ((Neighborhood.open X Y V).ι ''ᵁ W).ι = Y.subschemeι :=
      Neighborhood.toSchemeHom_fac X Y _
    have h1 : ((((Neighborhood.open X Y V).ι.isoImage W).inv ≫ s) ≫ U.hom) ≫
        (Neighborhood.open X Y V).ι = ((Neighborhood.open X Y V).ι ''ᵁ W).ι := by
      rw [Category.assoc, Category.assoc, ← Category.assoc s, hsU, Scheme.Hom.isoImage_inv_ι]
    have hR : (nbhdInclusion X Y _ hV 0 ≫ (nbhdTower Y.subschemeι _ hV).homToOpen hW 0) ≫
        W.ι ≫ (Neighborhood.open X Y V).ι = Y.subschemeι := by
      rw [Category.assoc, ← Category.assoc _ W.ι, ← Category.assoc,
        nbhdInclusion_comp_homToOpen_comp_ι, Neighborhood.toSchemeHom_fac]
    have hq : Neighborhood.toSchemeHom X Y (Neighborhood.ofOpen X Y V W r hr) ≫
        ((Neighborhood.open X Y V).ι.isoImage W).inv =
          nbhdInclusion X Y _ hV 0 ≫ (nbhdTower Y.subschemeι _ hV).homToOpen hW 0 :=
      (cancel_mono (W.ι ≫ (Neighborhood.open X Y V).ι)).1
        (((Category.assoc _ _ _).trans ((congrArg
          (fun k => Neighborhood.toSchemeHom X Y (Neighborhood.ofOpen X Y V W r hr) ≫ k)
          (Scheme.Hom.isoImage_inv_ι (Neighborhood.open X Y V).ι W)).trans hfac)).trans hR.symm)
    refine ⟨Neighborhood.ofOpen X Y V W r hr, homOfLE (Neighborhood.ofOpen_le X Y V W r hr),
      ((Neighborhood.open X Y V).ι.isoImage W).inv ≫ s,
      (cancel_mono (Neighborhood.open X Y V).ι).1 (h1.trans (Scheme.homOfLE_ι X _).symm), ?_⟩
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ s) hq).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => nbhdInclusion X Y _ hV 0 ≫ k)
        (hsn 0)).trans (hat 0))))
  · have hV := range_subschemeι_subset_open X Y V
    have hT := hT V
    have hbij := hbij V U
    let W : (Neighborhood.open X Y V).toScheme.Opens :=
      (Neighborhood.open X Y V).ι ⁻¹ᵁ (Neighborhood.open X Y V')
    let φ : W.toScheme ⟶ (Neighborhood.open X Y V').toScheme :=
      (Neighborhood.open X Y V).ι.resLE (Neighborhood.open X Y V') W le_rfl
    have hφ : φ ≫ (Neighborhood.open X Y V').ι = W.ι ≫ (Neighborhood.open X Y V).ι :=
      Scheme.Hom.resLE_comp_ι _ _
    have hle1 : Neighborhood.open X Y V' ≤ Neighborhood.open X Y V := iVV'.le
    have hσ : ∀ s : (Neighborhood.open X Y V').toScheme ⟶ U.left,
        s ≫ U.hom = X.homOfLE hle1 → (φ ≫ s) ≫ U.hom = W.ι := fun s hs =>
      (cancel_mono (Neighborhood.open X Y V).ι).1 (by
        rw [Category.assoc, Category.assoc, ← Category.assoc s, hs, Scheme.homOfLE_ι, hφ])
    have hW : (nbhdTower Y.subschemeι _ hV).support ⊆ W := by
      rw [nbhdTower_support X Y V hV]
      rintro _ ⟨y, rfl⟩
      have e1 : (Neighborhood.open X Y V).ι.base ((Neighborhood.toSchemeHom X Y V).base y) =
          Y.subschemeι.base y :=
        congrArg (fun f => f.base y) (Neighborhood.toSchemeHom_fac X Y V)
      have e2 : (Neighborhood.open X Y V').ι.base ((Neighborhood.toSchemeHom X Y V').base y) =
          Y.subschemeι.base y :=
        congrArg (fun f => f.base y) (Neighborhood.toSchemeHom_fac X Y V')
      have hmem : (Neighborhood.open X Y V').ι.base ((Neighborhood.toSchemeHom X Y V').base y) ∈
          Set.range (Neighborhood.open X Y V').ι.base := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι, e2, ← e1] at hmem
    have hq : ∀ n : ℕ, nbhdInclusion X Y _ hV n ≫
        (nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ φ = Neighborhood.toSchemeHom X Y V' :=
      fun n => (cancel_mono (Neighborhood.open X Y V').ι).1 (by
        rw [Category.assoc, Category.assoc, hφ, ← Category.assoc _ W.ι, ← Category.assoc,
          nbhdInclusion_comp_homToOpen_comp_ι, Neighborhood.toSchemeHom_fac,
          Neighborhood.toSchemeHom_fac])
    have hsec : ∀ (n : ℕ) (s : (Neighborhood.open X Y V').toScheme ⟶ U.left),
        s ≫ U.hom = X.homOfLE hle1 →
        ((nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ φ ≫ s) ≫ U.hom =
          ((nbhdTower Y.subschemeι _ hV).obj n).hom := fun n s hs => by
      rw [Category.assoc, hσ s hs, InfinitesimalTower.homToOpen_ι]
    have hagree : ∀ n : ℕ, (nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ φ ≫ s₁ =
        (nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ φ ≫ s₂ := fun n => by
      have e : ∀ s : (Neighborhood.open X Y V').toScheme ⟶ U.left,
          nbhdInclusion X Y _ hV n ≫ (nbhdTower Y.subschemeι _ hV).homToOpen hW n ≫ φ ≫ s =
            Neighborhood.toSchemeHom X Y V' ≫ s := fun s => by
        rw [← hq n]
        simp only [Category.assoc]
      exact (hbij n).2 _ _ (hsec n s₁ hs₁) (hsec n s₂ hs₂) ((e s₁).trans (hs.trans (e s₂).symm))
    obtain ⟨W'', hW'', hle, heq⟩ := SectionsNearTower.eq_section _ hT U W hW (φ ≫ s₁) (φ ≫ s₂)
      (hσ s₁ hs₁) (hσ s₂ hs₂) hagree
    obtain ⟨r, hr⟩ := exists_lift_of_support_subset X Y V hV W'' hW''
    have hle2 : (Neighborhood.open X Y V).ι ''ᵁ W'' ≤ Neighborhood.open X Y V' :=
      (((Neighborhood.open X Y V).ι.image_le_image_iff W'' W).2 hle).trans
        ((Neighborhood.open X Y V).ι.image_preimage_le (Neighborhood.open X Y V'))
    have hκ : X.homOfLE hle2 = ((Neighborhood.open X Y V).ι.isoImage W'').inv ≫
        Scheme.homOfLE _ hle ≫ φ := (cancel_mono (Neighborhood.open X Y V').ι).1 (by
      rw [Scheme.homOfLE_ι, Category.assoc, Category.assoc, hφ, ← Category.assoc _ W.ι,
        Scheme.homOfLE_ι, Scheme.Hom.isoImage_inv_ι])
    refine ⟨Neighborhood.ofOpen X Y V W'' r hr, homOfLE hle2, ?_⟩
    have hfin : X.homOfLE hle2 ≫ s₁ = X.homOfLE hle2 ≫ s₂ := by
      rw [hκ]
      simp only [Category.assoc]
      rw [heq]
    exact hfin

/-- **[Stacks, Tag 0ELA].** Let `X` be a Noetherian scheme and let `Y ⊆ X` be a closed subscheme
with ideal sheaf `I`. Let `𝒱` be the set of open subschemes `V ⊆ X` containing `Y`, ordered by
reverse inclusion. Assume the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`, `ℱ ↦ ℱ^∧`, is
fully faithful on the full subcategory of finite locally free objects. Then the restriction
functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful.

The completion condition is the source's, condition (4) of [Stacks, Tag 0EK2],
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`, at the closed
immersion of `Y`: for every neighbourhood `V` and all finite locally free `𝒪_V`-modules `𝒢`, `ℱ`,
the map `colim_{W ⊆ V} Hom(𝒢|_W, ℱ|_W) ⟶ lim_n Hom(𝒢|_{Y_n}, ℱ|_{Y_n})` is bijective, which is
full faithfulness of `ℱ ↦ ℱ^∧` on these objects since a morphism of `Coh(X, I)` between
completions is a compatible family of morphisms on the `Y_n`. The conclusion is
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`,
full faithfulness spelled through the directed-colimit description of the hom sets of
`colim_𝒱 FÉt_V`. The proof is the source's: the internal hom reduces the statement to the
extension of sections of one finite étale cover
(`finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme`), and that extension is
`sectionsExtendNearSubscheme_of_completionFullyFaithfulComplete`. -/
@[stacks 0ELA "the full statement: full faithfulness of completion on the finite locally free \
objects of the neighbourhood colimit gives full faithfulness of restriction of finite étale covers"]
theorem finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete [IsNoetherian X]
    (h : NeighbourhoodCompletion.CompletionFullyFaithfulComplete Y.subschemeι) :
    FiniteEtaleColimitFullyFaithful X Y :=
  finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme X Y
    (sectionsExtendNearSubscheme_of_completionFullyFaithfulComplete X Y h)

end Stacks.FundamentalGroup

end
