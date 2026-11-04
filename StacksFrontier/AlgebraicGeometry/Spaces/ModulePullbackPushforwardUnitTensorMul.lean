module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitTensorMultiplication
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# Pulling back the multiplication `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y`

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces, `A = f_*𝒪_Y` and
`φ : ℰ ⟶ A` a map of `𝒪_X`-modules. `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom φ` is
the multiplication `ℰ ⊗ A ⟶ A`, `e ⊗ b ↦ b φ(e)`, and the proof of Stacks 0GV1 asks whether its
composite with the cokernel map of `φ` vanishes. In the limit argument of that proof the
question is moved along a morphism `g : X' ⟶ X` (a projection of a limit, or a transition
morphism of the system): there `A` pulls back to the direct image `A' = f'_*𝒪_{Y'}` of a base
change `f' : Y' ⟶ X'`, through an isomorphism `β : g^*A ≅ A'`. This file proves that the
multiplication and the vanishing of the composite move with it.

The isomorphism `β` is an argument. What is asked of it is that it be an isomorphism of
algebras: it carries the inverse image `g^*μ_A` of the multiplication `μ_A : A ⊗ A ⟶ A`, read
through the comparison `g^*(A ⊗ A) ≅ g^*A ⊗ g^*A` of Stacks 03EL
(`Stacks.SheafOfModules.pullbackTensorIso`), to the multiplication of `A'`:

`g^*μ_A ≫ β = δ_{A,A} ≫ (β ⊗ β) ≫ μ_{A'}`.

## Main results

* `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom_comp_left`: the multiplication is natural
  in `ℰ`, `μ_{u ≫ φ} = (u ⊗ 𝟙) ≫ μ_φ`.
* `AlgebraicGeometry.Space.modulePullback_map_pushforwardUnitTensorMulHom_comp`: **the inverse
  image of the multiplication of `φ` is the multiplication of `g^*φ ≫ β`**, read through Stacks
  03EL and `𝟙 ⊗ β`.
* `Space.modulePullback_map_pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_iff`:
  **the composite `ℰ ⊗ A ⟶ A ⟶ coker φ` has vanishing inverse image along `g` exactly when the
  composite `g^*ℰ ⊗ A' ⟶ A' ⟶ coker (g^*φ ≫ β)` vanishes.** The inverse image preserves cokernels,
  being a left adjoint (Stacks 03D7), and the two other factors are isomorphisms.

## Implementation notes

Morphisms out of the tensor product sheaf are compared on the objectwise tensor product of the
underlying presheaves, through `Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom`. The tensor
product of morphisms is written as the two functor actions of
`Stacks.SheafOfModules.Tensor.sheafTensor`, never through `Functor.uncurry`: the composites the
proofs rewrite have to share their intermediate objects syntactically, and a pair spelled through
`Functor.uncurry` does not, so `rw` falls back on a definitional check that times out. For the
same reason the main computation is a chain of `Eq.trans` and `congrArg` rather than one `rw`.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} {f : Y ⟶ X} {hf : yoneda.relativelyRepresentable f.hom}

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModulesPullbackTensorMul
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- **The multiplication `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y` is natural in `ℰ`**: for `u : ℰ' ⟶ ℰ`, the
multiplication of `u ≫ φ` is `u ⊗ 𝟙` followed by the multiplication of `φ`. Both sides send
`e ⊗ b` to `b φ(u e)`. -/
theorem pushforwardUnitTensorMulHom_comp_left {E E' : Modules.{u, u} B S hS X.1 X.2}
    (u : E' ⟶ E) (φ : E ⟶ chartBaseChangeStructureModule B S hS f hf) :
    pushforwardUnitTensorMulHom (u ≫ φ) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        u).app (chartBaseChangeStructureModule B S hS f hf) ≫ pushforwardUnitTensorMulHom φ := by
  apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom.injective
  have h12 : ∀ {F : Modules.{u, u} B S hS X.1 X.2}
      (ψ : F ⟶ chartBaseChangeStructureModule B S hS f hf),
      Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom (pushforwardUnitTensorMulHom ψ) =
        pushforwardUnitTensorMulPresheafHom ψ := fun _ =>
    Equiv.apply_symm_apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom _
  have h3 : Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        u).app (chartBaseChangeStructureModule B S hS f hf) ≫ pushforwardUnitTensorMulHom φ) =
      PresheafOfModules.tensorHom (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj) u.val
          (𝟙 (chartBaseChangeStructureModule B S hS f hf).val) ≫
        Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom (pushforwardUnitTensorMulHom φ) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).homEquiv_naturality_left _ _
  rw [h12, h3, h12]
  ext U : 1
  exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl

/-- The multiplication of `φ` is `φ ⊗ 𝟙` followed by the multiplication of `𝟙`. -/
private theorem pushforwardUnitTensorMulHom_eq_tensor_map_comp
    {E : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ chartBaseChangeStructureModule B S hS f hf) :
    pushforwardUnitTensorMulHom φ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        φ).app (chartBaseChangeStructureModule B S hS f hf) ≫
        pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf)) := by
  simpa using pushforwardUnitTensorMulHom_comp_left φ
    (𝟙 (chartBaseChangeStructureModule B S hS f hf))

/-- The multiplication of `ψ ≫ β` read through `β ⊗ β`: for `ψ : M ⟶ P` and `β : P ⟶ f_*𝒪_Y`,
`(ψ ⊗ 𝟙) ≫ (β ⊗ β) ≫ μ = (𝟙 ⊗ β) ≫ (e ⊗ b ↦ b (ψ ≫ β)(e))`. -/
private theorem pushforwardUnitTensorMulHom_tensor_map_comp {M P : Modules.{u, u} B S hS X.1 X.2}
    (ψ : M ⟶ P) (β : P ⟶ chartBaseChangeStructureModule B S hS f hf) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        ψ).app P ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        β).app P ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        (chartBaseChangeStructureModule B S hS f hf)).map β ≫
      pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf)) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        M).map β ≫ pushforwardUnitTensorMulHom (ψ ≫ β) := by
  rw [pushforwardUnitTensorMulHom_eq_tensor_map_comp (ψ ≫ β), Functor.map_comp,
    NatTrans.comp_app, Category.assoc,
    reassoc_of% (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).map ψ).naturality β),
    reassoc_of% (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).map β).naturality β)]

variable {X' Y' : AlgebraicSpaces B S hS} {f' : Y' ⟶ X'}
    {hf' : yoneda.relativelyRepresentable f'.hom}

/-- **The inverse image of the multiplication `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y` along `g : X' ⟶ X`.**
Let `β : g^*(f_*𝒪_Y) ≅ f'_*𝒪_{Y'}` be an isomorphism of algebras, in the sense of the hypothesis
`hβ`: it carries the inverse image of the multiplication of `f_*𝒪_Y`, read through the comparison
`δ` of Stacks 03EL, to the multiplication of `f'_*𝒪_{Y'}`. Then for every `φ : ℰ ⟶ f_*𝒪_Y`,

`g^*(μ_φ) ≫ β = δ_{ℰ, f_*𝒪_Y} ≫ (𝟙 ⊗ β) ≫ μ_{g^*φ ≫ β}`.

The proof writes `μ_φ = (φ ⊗ 𝟙) ≫ μ_𝟙`, moves `φ ⊗ 𝟙` across `δ` by naturality, applies `hβ`, and
recombines by `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom_comp_left` over `X'`. -/
theorem modulePullback_map_pushforwardUnitTensorMulHom_comp (g : X' ⟶ X)
    (β : (modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS f hf) ≅
      chartBaseChangeStructureModule B S hS f' hf')
    (hβ : (modulePullback B S hS g).map
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf))) ≫ β.hom =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (chartBaseChangeStructureModule B S hS f hf, chartBaseChangeStructureModule B S hS f hf) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).map
          β.hom).app ((modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS f hf)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          (chartBaseChangeStructureModule B S hS f' hf')).map β.hom ≫
          pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f' hf')))
    {E : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ chartBaseChangeStructureModule B S hS f hf) :
    (modulePullback B S hS g).map (pushforwardUnitTensorMulHom φ) ≫ β.hom =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (E, chartBaseChangeStructureModule B S hS f hf) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          ((modulePullback B S hS g).obj E)).map β.hom ≫
          pushforwardUnitTensorMulHom ((modulePullback B S hS g).map φ ≫ β.hom) := by
  have hnat : (modulePullback B S hS g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
          φ).app (chartBaseChangeStructureModule B S hS f hf)) ≫
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (chartBaseChangeStructureModule B S hS f hf, chartBaseChangeStructureModule B S hS f hf) =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (E, chartBaseChangeStructureModule B S hS f hf) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).map
          ((modulePullback B S hS g).map φ)).app
            ((modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS f hf)) :=
    Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst
      (smallEtaleRingedToposModulesHom B S hS g) φ (chartBaseChangeStructureModule B S hS f hf)
  have h0 := pushforwardUnitTensorMulHom_eq_tensor_map_comp (f := f) (hf := hf) φ
  rw [h0, Functor.map_comp, Category.assoc]
  refine (congrArg _ hβ).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) hnat).trans ((Category.assoc _ _ _).trans ?_)
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (pushforwardUnitTensorMulHom_tensor_map_comp ((modulePullback B S hS g).map φ) β.hom))

/-- A composite `a ≫ b ≫ c ≫ d` with `a`, `b` and `d` isomorphisms vanishes exactly when `c`
does. -/
private theorem iso_comp_comp_comp_iso_eq_zero_iff {C : Type*} [Category C] [HasZeroMorphisms C]
    {P Q R P' Q' : C} (a : P ≅ Q) (b : Q ≅ R) (c : R ⟶ P') (d : P' ≅ Q') :
    a.hom ≫ b.hom ≫ c ≫ d.hom = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [show c = b.inv ≫ a.inv ≫ (a.hom ≫ b.hom ≫ c ≫ d.hom) ≫ d.inv by simp, h]
  simp

/-- The inverse image of a cokernel along a morphism of algebraic spaces is the cokernel of the
inverse image, read through an isomorphism `β` of the target: `g^*` is a left adjoint. -/
private theorem exists_cokernel_iso_modulePullback (g : X' ⟶ X)
    {E M : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ M) {M' : Modules.{u, u} B S hS X'.1 X'.2}
    (β : (modulePullback B S hS g).obj M ≅ M') :
    ∃ e : cokernel ((modulePullback B S hS g).map φ ≫ β.hom) ≅
        (modulePullback B S hS g).obj (cokernel φ),
      cokernel.π ((modulePullback B S hS g).map φ ≫ β.hom) ≫ e.hom =
        β.inv ≫ (modulePullback B S hS g).map (cokernel.π φ) := by
  have hadj := modulePullbackAdjunction B S hS g
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    hadj.leftAdjoint_preservesColimits
  have : (modulePullback B S hS g).IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback B S hS g)
  refine ⟨cokernelCompIsIso _ β.hom ≪≫ (PreservesCokernel.iso _ φ).symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, PreservesCokernel.iso_inv, cokernelCompIsIso_hom,
    cokernel.π_desc_assoc, Category.assoc, π_comp_cokernelComparison, IsIso.Iso.inv_hom]

/-- **The vanishing of `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ coker φ` moves along `g : X' ⟶ X`.** For an
isomorphism of algebras `β : g^*(f_*𝒪_Y) ≅ f'_*𝒪_{Y'}` (hypothesis `hβ`, as in
`AlgebraicGeometry.Space.modulePullback_map_pushforwardUnitTensorMulHom_comp`), the inverse image
along `g` of the composite of the multiplication of `φ` with the cokernel map of `φ` is zero if and
only if the composite of the multiplication of `g^*φ ≫ β` with the cokernel map of `g^*φ ≫ β` is
zero.

By `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom_comp_eq_zero_iff` on either side, this
says that the image of `φ` is closed under multiplication by `f_*𝒪_Y` after pullback along `g`
exactly when the image of `g^*φ ≫ β` is closed under multiplication by `f'_*𝒪_{Y'}`. The inverse
image of the cokernel of `φ` is the cokernel of `g^*φ ≫ β`, since `g^*` is a left adjoint
(Stacks 03D7) and `β` is an isomorphism. -/
theorem modulePullback_map_pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_iff (g : X' ⟶ X)
    (β : (modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS f hf) ≅
      chartBaseChangeStructureModule B S hS f' hf')
    (hβ : (modulePullback B S hS g).map
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf))) ≫ β.hom =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (chartBaseChangeStructureModule B S hS f hf, chartBaseChangeStructureModule B S hS f hf) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).map
          β.hom).app ((modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS f hf)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          (chartBaseChangeStructureModule B S hS f' hf')).map β.hom ≫
          pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f' hf')))
    {E : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ chartBaseChangeStructureModule B S hS f hf) :
    (modulePullback B S hS g).map (pushforwardUnitTensorMulHom φ ≫ cokernel.π φ) = 0 ↔
      pushforwardUnitTensorMulHom ((modulePullback B S hS g).map φ ≫ β.hom) ≫
        cokernel.π ((modulePullback B S hS g).map φ ≫ β.hom) = 0 := by
  obtain ⟨e, he⟩ := exists_cokernel_iso_modulePullback g φ β
  have key : (modulePullback B S hS g).map (pushforwardUnitTensorMulHom φ ≫ cokernel.π φ) =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (E, chartBaseChangeStructureModule B S hS f hf) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          ((modulePullback B S hS g).obj E)).map β.hom ≫
        (pushforwardUnitTensorMulHom ((modulePullback B S hS g).map φ ≫ β.hom) ≫
          cokernel.π ((modulePullback B S hS g).map φ ≫ β.hom)) ≫ e.hom := by
    refine Eq.trans (?_ : _ = ((modulePullback B S hS g).map (pushforwardUnitTensorMulHom φ) ≫
      β.hom) ≫ β.inv ≫ (modulePullback B S hS g).map (cokernel.π φ)) ?_
    · rw [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
    · rw [modulePullback_map_pushforwardUnitTensorMulHom_comp g β hβ φ, ← he]
      exact (Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z)
        ((Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _).symm)))
  rw [key]
  exact iso_comp_comp_comp_iso_eq_zero_iff
    ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).app
      (E, chartBaseChangeStructureModule B S hS f hf))
    (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
      ((modulePullback B S hS g).obj E)).mapIso β) _ e

end AlgebraicGeometry.Space

end
