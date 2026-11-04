module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme

/-!
# The sections of a tensor product over an affine open

For a scheme `X`, two quasi-coherent sheaves of modules `F G : X.Modules` and an **affine** open
`U : X.Opens`, the comparison

  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ⟶ Γ(F ⊗ G, U)`

of `Stacks.SectionTensorFormula.tensorSectionLinear` is bijective, and the resulting
`Γ(X, U)`-linear equivalence sends a pure tensor `m ⊗ₜ n` to the product of sections
`Stacks.SectionTensorFormula.tensorSection F G m n`.

In general the comparison is only locally bijective.

## Main definitions

* `Stacks.SectionTensorFormula.tensorSheafUnitAdd`: the sheafification unit of the sectionwise
  tensor product over an open, as an additive map.
* `Stacks.SectionTensorFormula.tmulChange` and
  `Stacks.SectionTensorFormula.restrictTmul`: the two canonical additive maps between tensor
  products of one pair of modules over two different scalar rings, each the identity on pure
  tensors.
* `Stacks.SectionTensorFormula.tensorSectionEquiv`: the section formula over an affine open,
  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ≃ₗ[Γ(X, U)] Γ(F ⊗ G, U)`, and
  `Stacks.SectionTensorFormula.tensorSectionIso` the same as an isomorphism in
  `ModuleCat Γ(X, U)`.

## Main results

* `Stacks.SectionTensorFormula.bijective_tensorSectionLinear_iff`: the comparison is bijective
  over an open exactly when the sheafification unit of the sectionwise tensor product is.
* `Stacks.SectionTensorFormula.bijective_tensorSectionLinear_top`: the comparison is bijective on
  global sections of `Spec R`.
* `Stacks.SectionTensorFormula.bijective_tensorSheafUnit_image`: bijectivity of the
  sheafification unit over `W` for the restrictions of `F` and `G` along an open immersion gives
  bijectivity over the image of `W` for `F` and `G`.
* `Stacks.SectionTensorFormula.bijective_tensorSectionLinear`: the comparison is bijective over
  an affine open.
* `Stacks.SectionTensorFormula.tensorSectionEquiv_tmul`: the equivalence sends `m ⊗ₜ n` to
  `tensorSection F G m n`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open PresheafOfModules Stacks.SheafOfModules.TensorSheafification
open scoped TensorProduct

universe u

namespace Stacks.SectionTensorFormula

/-! ### Bijectivity through a surjection -/

/-- If a composite is bijective and the inner map is surjective, the outer map is bijective. -/
theorem bijective_of_bijective_comp {α β γ : Type*} (f : β → γ) {g : α → β}
    (hg : Function.Surjective g) (h : Function.Bijective (f ∘ g)) :
    Function.Bijective f :=
  ⟨h.1.of_comp_right hg, h.2.of_comp⟩

/-! ### Changing the scalars of a tensor product -/

/-- An additive map into a tensor product whose range contains every pure tensor is surjective. -/
private theorem surjective_of_tmul_mem_range {R M N P : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] (f : P →+ M ⊗[R] N)
    (h : ∀ (m : M) (n : N), ∃ x, f x = m ⊗ₜ[R] n) : Function.Surjective f := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n => exact h m n
  | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add, hx, hy]⟩

section TensorScalars

variable {A B M N : Type*} [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [Module B M] [AddCommGroup N] [Module A N] [Module B N]

/-- The canonical additive map `M ⊗_A N ⟶ M ⊗_B N`, the identity on pure tensors, given that the
`A`-action may be moved across a tensor sign formed over `B`. -/
def tmulChange (h : ∀ (a : A) (m : M) (n : N), (a • m) ⊗ₜ[B] n = m ⊗ₜ[B] (a • n)) :
    M ⊗[A] N →+ M ⊗[B] N :=
  TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk B M N).toAddMonoidHom) h

/-- `tmulChange` sends `m ⊗ₜ[A] n` to `m ⊗ₜ[B] n`. -/
@[simp]
lemma tmulChange_tmul
    (h : ∀ (a : A) (m : M) (n : N), (a • m) ⊗ₜ[B] n = m ⊗ₜ[B] (a • n)) (m : M) (n : N) :
    tmulChange h (m ⊗ₜ[A] n) = m ⊗ₜ[B] n :=
  rfl

/-- `tmulChange` is surjective. -/
lemma surjective_tmulChange
    (h : ∀ (a : A) (m : M) (n : N), (a • m) ⊗ₜ[B] n = m ⊗ₜ[B] (a • n)) :
    Function.Surjective (tmulChange h) :=
  surjective_of_tmul_mem_range _ fun m n => ⟨m ⊗ₜ[A] n, rfl⟩

/-- **Transfer of bijectivity across a change of scalars.**  Two additive maps out of the two
tensor products that agree on pure tensors are bijective together, provided the `A`-action may be
moved across a tensor sign formed over `B`. -/
theorem bijective_of_tmulChange_eq {P : Type*} [AddCommGroup P]
    (f : (M ⊗[B] N) →+ P) (g : (M ⊗[A] N) →+ P)
    (hsmul : ∀ (a : A) (m : M) (n : N), (a • m) ⊗ₜ[B] n = m ⊗ₜ[B] (a • n))
    (h : ∀ (m : M) (n : N), f (m ⊗ₜ[B] n) = g (m ⊗ₜ[A] n))
    (hg : Function.Bijective g) : Function.Bijective f := by
  refine bijective_of_bijective_comp f (surjective_tmulChange hsmul) ?_
  have hfg : ⇑f ∘ ⇑(tmulChange hsmul) = ⇑g := by
    refine funext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => exact h m n
    | add a b ha hb => simp only [Function.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]
  rwa [hfg]

end TensorScalars

/-! ### Sections of an isomorphism of presheaves of modules -/

/-- An isomorphism of presheaves of modules is bijective on sections over every object. -/
theorem bijective_app_of_iso {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {P Q : PresheafOfModules.{u} R} (e : P ≅ Q) (V : Cᵒᵖ) :
    Function.Bijective (Hom.app e.hom V) := by
  have : IsIso (Hom.app e.hom V) :=
    ⟨Hom.app e.inv V, by rw [← comp_app, e.hom_inv_id, id_app],
      by rw [← comp_app, e.inv_hom_id, id_app]⟩
  exact (ConcreteCategory.isIso_iff_bijective (Hom.app e.hom V)).mp this

/-! ### The comparison is the sheafification unit -/

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable {X : Scheme.{u}}

/-- **The sheafification unit of the sectionwise tensor product over an open**, as an additive
map `Γ(F, V) ⊗_{Γ(X, V)} Γ(G, V) ⟶ Γ(F ⊗ G, V)` into the sheafified sectionwise product. -/
def tensorSheafUnitAdd (F G : X.Modules) (V : X.Opens) :
    TensorProduct Γ(X, V) Γ(F, V) Γ(G, V) →+
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj (F, G)).val.obj
          (op V) :=
  (Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
      (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F).val (G).val))
    (op V)).hom.toAddMonoidHom

/-- The comparison is the sheafification unit of the sectionwise tensor product, read in `F ⊗ G`
through `tensorSheafIsoTensorObj`. -/
lemma tensorSectionLinear_apply (F G : X.Modules) (V : X.Opens)
    (t : TensorProduct Γ(X, V) Γ(F, V) Γ(G, V)) :
    tensorSectionLinear F G V t =
      (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val.app (op V)
        (tensorSheafUnitAdd F G V t) :=
  rfl

/-- The comparison is bijective over an open exactly when the sheafification unit of the
sectionwise tensor product is. -/
theorem bijective_tensorSectionLinear_iff (F G : X.Modules) (V : X.Opens) :
    Function.Bijective (tensorSectionLinear F G V) ↔
      Function.Bijective (tensorSheafUnitAdd F G V) := by
  have he : ⇑(tensorSectionLinear F G V) =
      ⇑((tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val.app (op V)) ∘
        ⇑(tensorSheafUnitAdd F G V) :=
    funext (tensorSectionLinear_apply F G V)
  rw [he]
  exact Function.Bijective.of_comp_iff'
    (bijective_app_of_iso
      ((SheafOfModules.forget _).mapIso
        (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G)) (op V)) _

/-! ### Global sections over `Spec R` -/

/-- On `Spec R`, the action of `R` on global sections crosses a tensor sign formed over
`Γ(Spec R, ⊤)`. -/
lemma smul_tmul_Spec {R : CommRingCat.{u}} (F G : (Spec R).Modules) (r : R)
    (m : Γ(F, ⊤)) (n : Γ(G, ⊤)) :
    (r • m) ⊗ₜ[Γ(Spec R, ⊤)] n = m ⊗ₜ[Γ(Spec R, ⊤)] (r • n) :=
  (congrArg (fun x : Γ(F, ⊤) => x ⊗ₜ[Γ(Spec R, ⊤)] n)
      (Scheme.Modules.smul_Spec_def (M := F) r m)).trans
    ((TensorProduct.smul_tmul _ m n).trans
      (congrArg (fun y : Γ(G, ⊤) => m ⊗ₜ[Γ(Spec R, ⊤)] y)
        (Scheme.Modules.smul_Spec_def (M := G) r n).symm))

/-- The sheafification unit of the sectionwise tensor product is bijective on global sections of
`Spec R` for two quasi-coherent modules. -/
theorem bijective_tensorSheafUnit_top (R : CommRingCat.{u}) (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (tensorSheafUnitAdd F G ⊤) :=
  bijective_of_tmulChange_eq (A := R) (B := Γ(Spec R, ⊤)) (M := Γ(F, ⊤)) (N := Γ(G, ⊤))
    (tensorSheafUnitAdd F G ⊤)
    (AlgebraicGeometry.TildeTensor.gammaTensorMap F G).toAddMonoidHom
    (smul_tmul_Spec F G) (fun _ _ => rfl)
    (AlgebraicGeometry.TildeTensor.bijective_gammaTensorMap F G)

/-- The comparison is bijective on global sections of `Spec R` for two quasi-coherent modules. -/
theorem bijective_tensorSectionLinear_top (R : CommRingCat.{u}) (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (tensorSectionLinear F G ⊤) :=
  (bijective_tensorSectionLinear_iff F G ⊤).mpr (bijective_tensorSheafUnit_top R F G)

/-! ### Descent along an open immersion -/

section Restrict

variable {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]

/-- The identification of the sections of a restriction over `W` with the sections over the image
of `W`, as an additive map. -/
def restrictSectionAdd (F : X.Modules) (W : Z.Opens) :
    Γ((Scheme.Modules.restrictFunctor j).obj F, W) →+ Γ(F, j ''ᵁ W) where
  toFun m := m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A scalar of `Γ(Z, W)` acts on the sections of a restriction as its image under `j.appIso`. -/
lemma restrictSectionAdd_smul (F : X.Modules) (W : Z.Opens) (r : Γ(Z, W))
    (m : Γ((Scheme.Modules.restrictFunctor j).obj F, W)) :
    restrictSectionAdd j F W (r • m) = (j.appIso W).inv r • restrictSectionAdd j F W m :=
  rfl

/-- The pure tensor over `Γ(X, j(W))` attached to two sections of restrictions over `W`. -/
def restrictTmulFun (F G : X.Modules) (W : Z.Opens)
    (m : Γ((Scheme.Modules.restrictFunctor j).obj F, W))
    (n : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    TensorProduct Γ(X, j ''ᵁ W) Γ(F, j ''ᵁ W) Γ(G, j ''ᵁ W) :=
  restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n

/-- `restrictTmulFun` is additive in its first argument. -/
lemma restrictTmulFun_add_left (F G : X.Modules) (W : Z.Opens)
    (m m' : Γ((Scheme.Modules.restrictFunctor j).obj F, W))
    (n : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    restrictTmulFun j F G W (m + m') n =
      restrictTmulFun j F G W m n + restrictTmulFun j F G W m' n := by
  show restrictSectionAdd j F W (m + m') ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n =
    restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n +
      restrictSectionAdd j F W m' ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n
  rw [map_add, TensorProduct.add_tmul]

/-- `restrictTmulFun` is additive in its second argument. -/
lemma restrictTmulFun_add_right (F G : X.Modules) (W : Z.Opens)
    (m : Γ((Scheme.Modules.restrictFunctor j).obj F, W))
    (n n' : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    restrictTmulFun j F G W m (n + n') =
      restrictTmulFun j F G W m n + restrictTmulFun j F G W m n' := by
  show restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W (n + n') =
    restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n +
      restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n'
  rw [map_add, TensorProduct.tmul_add]

/-- A scalar of `Γ(Z, W)` may be moved from the first argument of `restrictTmulFun` to the
second. -/
lemma restrictTmulFun_smul (F G : X.Modules) (W : Z.Opens) (r : Γ(Z, W))
    (m : Γ((Scheme.Modules.restrictFunctor j).obj F, W))
    (n : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    restrictTmulFun j F G W (r • m) n = restrictTmulFun j F G W m (r • n) := by
  show restrictSectionAdd j F W (r • m) ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W n =
    restrictSectionAdd j F W m ⊗ₜ[Γ(X, j ''ᵁ W)] restrictSectionAdd j G W (r • n)
  rw [restrictSectionAdd_smul, restrictSectionAdd_smul, TensorProduct.smul_tmul]

/-- The additive map from the sectionwise tensor product of two restrictions over `W` to the
sectionwise tensor product over the image of `W`, the identity on pure tensors. -/
def restrictTmul (F G : X.Modules) (W : Z.Opens) :
    TensorProduct Γ(Z, W) Γ((Scheme.Modules.restrictFunctor j).obj F, W)
        Γ((Scheme.Modules.restrictFunctor j).obj G, W) →+
      TensorProduct Γ(X, j ''ᵁ W) Γ(F, j ''ᵁ W) Γ(G, j ''ᵁ W) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun m => AddMonoidHom.mk' (restrictTmulFun j F G W m)
        (restrictTmulFun_add_right j F G W m))
      (fun m m' => AddMonoidHom.ext (restrictTmulFun_add_left j F G W m m')))
    (restrictTmulFun_smul j F G W)

/-- `restrictTmul` sends `m ⊗ₜ n` to `restrictTmulFun j F G W m n`. -/
@[simp]
lemma restrictTmul_tmul (F G : X.Modules) (W : Z.Opens)
    (m : Γ((Scheme.Modules.restrictFunctor j).obj F, W))
    (n : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    restrictTmul j F G W (m ⊗ₜ[Γ(Z, W)] n) = restrictTmulFun j F G W m n :=
  rfl

/-- `restrictTmul` is surjective. -/
lemma surjective_restrictTmul (F G : X.Modules) (W : Z.Opens) :
    Function.Surjective (restrictTmul j F G W) :=
  surjective_of_tmul_mem_range _ fun m n => ⟨m ⊗ₜ[Γ(Z, W)] n, rfl⟩

/-- The comparison of the two sheafified sectionwise tensor products, as an additive map on
sections over `W`. -/
def restrictTensorAdd (F G : X.Modules) (W : Z.Opens) :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj (F, G)).val.obj
        (op (j ''ᵁ W)) →+
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj
        ((Scheme.Modules.restrictFunctor j).obj F,
          (Scheme.Modules.restrictFunctor j).obj G)).val.obj (op W) :=
  (Hom.app (Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F G).hom.val
    (op W)).hom.toAddMonoidHom

/-- The sheafification unit over `W` for the restrictions is the unit over `j(W)` for `F` and `G`,
followed by the comparison of the two tensor products, precomposed with `restrictTmul`. -/
lemma restrictTensorAdd_comp (F G : X.Modules) (W : Z.Opens) :
    (restrictTensorAdd j F G W).comp
        ((tensorSheafUnitAdd F G (j ''ᵁ W)).comp (restrictTmul j F G W)) =
      tensorSheafUnitAdd ((Scheme.Modules.restrictFunctor j).obj F)
        ((Scheme.Modules.restrictFunctor j).obj G) W := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m n =>
      exact Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul
        j F G W m n
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- If the sheafification unit of the sectionwise tensor product is bijective over `W` for the
restrictions of `F` and `G` along an open immersion `j`, then it is bijective over the image of `W`
for `F` and `G`. -/
theorem bijective_tensorSheafUnit_image (F G : X.Modules) (W : Z.Opens)
    (h : Function.Bijective (tensorSheafUnitAdd ((Scheme.Modules.restrictFunctor j).obj F)
      ((Scheme.Modules.restrictFunctor j).obj G) W)) :
    Function.Bijective (tensorSheafUnitAdd F G (j ''ᵁ W)) := by
  have hΘ : Function.Bijective (restrictTensorAdd j F G W) :=
    bijective_app_of_iso ((SheafOfModules.forget _).mapIso
      (Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F G)) (op W)
  refine (hΘ.of_comp_iff' _).mp ?_
  refine bijective_of_bijective_comp _ (surjective_restrictTmul j F G W) ?_
  rw [← restrictTensorAdd_comp] at h
  exact h

end Restrict

/-! ### The affine open case -/

/-- Bijectivity of the comparison transported along an equality of opens. -/
lemma bijective_tensorSectionLinear_of_eq (F G : X.Modules) {U V : X.Opens} (h : U = V)
    (hb : Function.Bijective (tensorSectionLinear F G U)) :
    Function.Bijective (tensorSectionLinear F G V) :=
  h ▸ hb

/-- For two quasi-coherent modules `F` and `G` on a scheme `X` and an affine open `U`, the
canonical map

  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ⟶ Γ(F ⊗ G, U)`

is bijective. -/
theorem bijective_tensorSectionLinear (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (tensorSectionLinear F G U) := by
  have himg : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  refine bijective_tensorSectionLinear_of_eq F G himg ?_
  refine (bijective_tensorSectionLinear_iff F G _).mpr ?_
  exact bijective_tensorSheafUnit_image hU.fromSpec F G ⊤
    (bijective_tensorSheafUnit_top _ _ _)

/-- The section formula for a tensor product over an affine open, as a `Γ(X, U)`-linear
equivalence

  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ≅ Γ(F ⊗ G, U)`

sending a pure tensor `m ⊗ₜ n` to `tensorSection F G m n`. -/
def tensorSectionEquiv (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    TensorProduct Γ(X, U) Γ(F, U) Γ(G, U) ≃ₗ[Γ(X, U)] Γ(F ⊗ G, U) :=
  LinearEquiv.ofBijective _ (bijective_tensorSectionLinear F G hU)

/-- `tensorSectionEquiv` sends a pure tensor to the product of the two sections. -/
@[simp]
lemma tensorSectionEquiv_tmul (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (m : Γ(F, U)) (n : Γ(G, U)) :
    tensorSectionEquiv F G hU (m ⊗ₜ[Γ(X, U)] n) = tensorSection F G m n :=
  rfl

/-- `tensorSectionEquiv` as an isomorphism in `ModuleCat Γ(X, U)`. -/
def tensorSectionIso (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ModuleCat.of Γ(X, U) (TensorProduct Γ(X, U) Γ(F, U) Γ(G, U)) ≅
      ModuleCat.of Γ(X, U) Γ(F ⊗ G, U) :=
  (tensorSectionEquiv F G hU).toModuleIso

end Stacks.SectionTensorFormula

end
