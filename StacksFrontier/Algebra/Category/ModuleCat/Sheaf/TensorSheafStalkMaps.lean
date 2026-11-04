module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation

/-!
# Stalks of tensor products of morphisms of sheaves of modules

Let `X` be a topological space and `O♯` a sheaf of commutative rings on `X`. For sheaves of
`O♯`-modules the stalk of a tensor product is the tensor product of the stalks
(`PresheafOfModules.tensorSheafStalkEquiv`, [Stacks, Tag 01CB]). This file records how the
basic constructions on tensor products of sheaves are read through that identification:

* the tensor product `f ⊗ g : A ⊗ B ⟶ A' ⊗ B'` of two morphisms is `fₓ ⊗ gₓ` on stalks; in
  particular it is an epimorphism when `f` and `g` are;
* the symmetry `A ⊗ B ⟶ B ⊗ A` is the symmetry `a ⊗ b ↦ b ⊗ a` of the stalks;
* the middle-four interchange `(A ⊗ B) ⊗ (C ⊗ D) ⟶ (A ⊗ C) ⊗ (B ⊗ D)` is the middle-four
  interchange `(a ⊗ b) ⊗ (c ⊗ d) ↦ (a ⊗ c) ⊗ (b ⊗ d)` of the stalks, for the identification of
  the stalk of `(A ⊗ B) ⊗ (C ⊗ D)` with `(Aₓ ⊗ Bₓ) ⊗ (Cₓ ⊗ Dₓ)` obtained by applying Tag 01CB
  twice.

## Main definitions

* `SheafOfModules.TensorStalkMaps.tensorHom`: the tensor product of two morphisms.
* `SheafOfModules.TensorStalkMaps.braid`: the symmetry of the tensor product, the braiding
  `Stacks.SheafOfModules.tensorSheafBraiding` of the monoidal structure of [Stacks, Tag 01CA].
* `SheafOfModules.TensorStalkMaps.tensorTensorStalkEquiv`: the stalk of `(A ⊗ B) ⊗ (C ⊗ D)` is
  `(Aₓ ⊗ Bₓ) ⊗ (Cₓ ⊗ Dₓ)`.
* `SheafOfModules.TensorStalkMaps.leftInterchange`: the interchange
  `B ⊗ (C ⊗ D) ⟶ C ⊗ (B ⊗ D)`.
* `SheafOfModules.TensorStalkMaps.middleFour`: the middle-four interchange.

## Main results

* `SheafOfModules.TensorStalkMaps.tensorSheafStalkEquiv_stalkMapL_tensorHom`: the stalk of
  `f ⊗ g` is `fₓ ⊗ gₓ`.
* `SheafOfModules.TensorStalkMaps.epi_tensorHom`: the tensor product of two epimorphisms is an
  epimorphism.
* `SheafOfModules.TensorStalkMaps.tensorSheafStalkEquiv_stalkMapL_braid`: the stalk of the
  symmetry is the symmetry of the stalks.
* `SheafOfModules.TensorStalkMaps.tensorTensorStalkEquiv_stalkMapL_middleFour`: the stalk of the
  middle-four interchange is the middle-four interchange of the stalks.
* `SheafOfModules.TensorStalkMaps.tensorTensorStalkEquiv_stalkMapL_tensorHom_tensorHom`: the
  stalk of `(f ⊗ g) ⊗ (h ⊗ k)` is `(fₓ ⊗ gₓ) ⊗ (hₓ ⊗ kₓ)`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf MonoidalCategory
open scoped TensorProduct

universe u

namespace SheafOfModules.TensorStalkMaps

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- The tensor product of two sheaves of modules over the section variable `Osharp`. -/
local macro:70 A:term:71 " ⊗ₛ " B:term:71 : term =>
  `(((Stacks.SheafOfModules.Tensor.sheafTensor $(Lean.mkIdent `Osharp)).obj $A).obj $B)

/-! ### Germs and linear maps on stalks -/

section Germs

/-- Two germs of two presheaves at `x` are represented by sections over one open neighbourhood
of `x`, in continuation form. -/
theorem forall_common_germ_pair {p : Prop} (P Q : TopCat.Presheaf AddCommGrpCat.{u} X) (x : ↥X)
    (a : ↑(TopCat.Presheaf.stalk P x)) (b : ↑(TopCat.Presheaf.stalk Q x))
    (H : ∀ (U : Opens ↥X) (hx : x ∈ U) (s : P.obj (op U)) (t : Q.obj (op U)),
      TopCat.Presheaf.germ P U x hx s = a → TopCat.Presheaf.germ Q U x hx t = b → p) : p := by
  obtain ⟨U₁, h₁, s, hs⟩ := TopCat.Presheaf.exists_germ_eq P a
  obtain ⟨U₂, h₂, t, ht⟩ := TopCat.Presheaf.exists_germ_eq Q b
  exact H (U₁ ⊓ U₂) ⟨h₁, h₂⟩ (P.map (homOfLE inf_le_left).op s)
    (Q.map (homOfLE inf_le_right).op t)
    ((TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_left) x ⟨h₁, h₂⟩ s).trans hs)
    ((TopCat.Presheaf.germ_res_apply Q (homOfLE inf_le_right) x ⟨h₁, h₂⟩ t).trans ht)

/-- Four germs of four presheaves at `x` are represented by sections over one open
neighbourhood of `x`, in continuation form. -/
theorem forall_common_germ_four {p : Prop} (P₁ P₂ P₃ P₄ : TopCat.Presheaf AddCommGrpCat.{u} X)
    (x : ↥X) (a₁ : ↑(TopCat.Presheaf.stalk P₁ x)) (a₂ : ↑(TopCat.Presheaf.stalk P₂ x))
    (a₃ : ↑(TopCat.Presheaf.stalk P₃ x)) (a₄ : ↑(TopCat.Presheaf.stalk P₄ x))
    (H : ∀ (U : Opens ↥X) (hx : x ∈ U) (s₁ : P₁.obj (op U)) (s₂ : P₂.obj (op U))
      (s₃ : P₃.obj (op U)) (s₄ : P₄.obj (op U)),
      TopCat.Presheaf.germ P₁ U x hx s₁ = a₁ → TopCat.Presheaf.germ P₂ U x hx s₂ = a₂ →
        TopCat.Presheaf.germ P₃ U x hx s₃ = a₃ → TopCat.Presheaf.germ P₄ U x hx s₄ = a₄ → p) :
    p :=
  forall_common_germ_pair P₁ P₂ x a₁ a₂ fun U hU s₁ s₂ hs₁ hs₂ =>
    forall_common_germ_pair P₃ P₄ x a₃ a₄ fun V hV s₃ s₄ hs₃ hs₄ =>
      H (U ⊓ V) ⟨hU, hV⟩ (P₁.map (homOfLE inf_le_left).op s₁)
        (P₂.map (homOfLE inf_le_left).op s₂) (P₃.map (homOfLE inf_le_right).op s₃)
        (P₄.map (homOfLE inf_le_right).op s₄)
        ((TopCat.Presheaf.germ_res_apply P₁ (homOfLE inf_le_left) x ⟨hU, hV⟩ s₁).trans hs₁)
        ((TopCat.Presheaf.germ_res_apply P₂ (homOfLE inf_le_left) x ⟨hU, hV⟩ s₂).trans hs₂)
        ((TopCat.Presheaf.germ_res_apply P₃ (homOfLE inf_le_right) x ⟨hU, hV⟩ s₃).trans hs₃)
        ((TopCat.Presheaf.germ_res_apply P₄ (homOfLE inf_le_right) x ⟨hU, hV⟩ s₄).trans hs₄)

/-- A linear map conjugated by two linear equivalences is a given linear map as soon as the
conjugate, composed with the inverse of the first equivalence, is that map. -/
theorem linearEquiv_apply_eq_of_comp_symm {R S S' M N : Type*} [CommRing R] [AddCommGroup S]
    [Module R S] [AddCommGroup S'] [Module R S'] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : S ≃ₗ[R] M) (e' : S' ≃ₗ[R] N) (φ : S →ₗ[R] S')
    (T : M →ₗ[R] N) (h : e'.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap = T) (z : S) :
    e' (φ z) = T (e z) :=
  (congrArg (fun w => e' (φ w)) (e.symm_apply_apply z).symm).trans (LinearMap.congr_fun h (e z))

/-- A linear map conjugated by two linear equivalences, the first onto a tensor product, is a
given linear map as soon as the two agree on pure tensors. -/
theorem linearEquiv_apply_eq_of_tmul {R S S' M₁ M₂ N : Type*} [CommRing R] [AddCommGroup S]
    [Module R S] [AddCommGroup S'] [Module R S'] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N] [Module R N] (e : S ≃ₗ[R] M₁ ⊗[R] M₂)
    (e' : S' ≃ₗ[R] N) (φ : S →ₗ[R] S') (T : M₁ ⊗[R] M₂ →ₗ[R] N)
    (h : ∀ m₁ m₂, e' (φ (e.symm (m₁ ⊗ₜ m₂))) = T (m₁ ⊗ₜ m₂)) (z : S) :
    e' (φ z) = T (e z) :=
  linearEquiv_apply_eq_of_comp_symm e e' φ T (TensorProduct.ext' h) z

/-- A linear map conjugated by two linear equivalences, the first onto a tensor product of two
tensor products, is a given linear map as soon as the two agree on pure tensors of pure
tensors. -/
theorem linearEquiv_apply_eq_of_tmul_tmul {R S S' M₁ M₂ M₃ M₄ N : Type*} [CommRing R]
    [AddCommGroup S] [Module R S] [AddCommGroup S'] [Module R S'] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup M₄] [Module R M₄] [AddCommGroup N] [Module R N]
    (e : S ≃ₗ[R] (M₁ ⊗[R] M₂) ⊗[R] (M₃ ⊗[R] M₄)) (e' : S' ≃ₗ[R] N) (φ : S →ₗ[R] S')
    (T : (M₁ ⊗[R] M₂) ⊗[R] (M₃ ⊗[R] M₄) →ₗ[R] N)
    (h : ∀ m₁ m₂ m₃ m₄, e' (φ (e.symm ((m₁ ⊗ₜ m₂) ⊗ₜ (m₃ ⊗ₜ m₄)))) =
      T ((m₁ ⊗ₜ m₂) ⊗ₜ (m₃ ⊗ₜ m₄))) (z : S) :
    e' (φ z) = T (e z) :=
  linearEquiv_apply_eq_of_comp_symm e e' φ T (TensorProduct.ext_fourfold' h) z

/-- Tensor products of linear maps commute with tensor products of linear equivalences as soon
as the factors do. -/
theorem congr_map_apply {R M₁ M₂ N₁ N₂ P₁ P₂ Q₁ Q₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]
    (e₁ : M₁ ≃ₗ[R] P₁) (e₂ : M₂ ≃ₗ[R] P₂) (e₁' : N₁ ≃ₗ[R] Q₁) (e₂' : N₂ ≃ₗ[R] Q₂)
    (φ₁ : M₁ →ₗ[R] N₁) (φ₂ : M₂ →ₗ[R] N₂) (ψ₁ : P₁ →ₗ[R] Q₁) (ψ₂ : P₂ →ₗ[R] Q₂)
    (h₁ : ∀ m, e₁' (φ₁ m) = ψ₁ (e₁ m)) (h₂ : ∀ m, e₂' (φ₂ m) = ψ₂ (e₂ m)) (w : M₁ ⊗[R] M₂) :
    TensorProduct.congr e₁' e₂' (TensorProduct.map φ₁ φ₂ w) =
      TensorProduct.map ψ₁ ψ₂ (TensorProduct.congr e₁ e₂ w) := by
  have key : (TensorProduct.congr e₁' e₂').toLinearMap ∘ₗ TensorProduct.map φ₁ φ₂ =
      TensorProduct.map ψ₁ ψ₂ ∘ₗ (TensorProduct.congr e₁ e₂).toLinearMap :=
    TensorProduct.ext' fun m₁ m₂ => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
        TensorProduct.congr_tmul, h₁, h₂]
  exact LinearMap.congr_fun key w

end Germs

/-! ### Morphisms out of a tensor product on germs of local pure tensors -/

section GermFormula

variable {A B A' B' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The inverse of the stalk identification of Tag 01CB on a pure tensor of germs is the germ of
the image of the pure tensor of sections. -/
theorem tensorSheafStalkEquiv_symm_germ_tmul (x : ↥X) (W : Opens ↥X) (hx : x ∈ W)
    (a : A.val.obj (op W)) (b : B.val.obj (op W)) :
    (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x).symm
        (TopCat.Presheaf.germ A.val.presheaf W x hx a ⊗ₜ
          TopCat.Presheaf.germ B.val.presheaf W x hx b) =
      PresheafOfModules.tensorSheafGerm Osharp A B x W hx a b :=
  (LinearEquiv.symm_apply_eq _).2
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp A B x W hx a b).symm

/-- A morphism of sheaves of modules carrying a section `m` to `n` carries, on stalks, the
preimage of the image of the germ of `m` to the image of the germ of `n`, for any
identifications `e`, `e'` of the stalks. -/
private theorem stalkMapL_symm_apply_of_germ {M N : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} {x : ↥X} {S S' : Type u}
    [AddCommGroup S] [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) S] [AddCommGroup S']
    [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) S'] (φ : M ⟶ N)
    (e : ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] S)
    (e' : ↑(TopCat.Presheaf.stalk N.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] S')
    (W : Opens ↥X) (hx : x ∈ W) (m : M.val.obj (op W)) (n : N.val.obj (op W)) (t : S) (t' : S')
    (ht : e (TopCat.Presheaf.germ M.val.presheaf W x hx m) = t) (h : φ.val.app (op W) m = n)
    (ht' : e' (TopCat.Presheaf.germ N.val.presheaf W x hx n) = t') :
    e' (PresheafOfModules.stalkMapL x φ.val (e.symm t)) = t' := by
  subst ht h ht'
  rw [e.symm_apply_apply, PresheafOfModules.stalkMapL_germ]

/-- A morphism between tensor products of sheaves which carries the image of a local pure tensor
`a ⊗ b` to the image of `a' ⊗ b'` carries, on stalks, `aₓ ⊗ bₓ` to `a'ₓ ⊗ b'ₓ`. -/
theorem tensorSheafStalkEquiv_stalkMapL_symm_germ_tmul (φ : (A ⊗ₛ B) ⟶ (A' ⊗ₛ B'))
    (x : ↥X) (W : Opens ↥X) (hx : x ∈ W) (a : A.val.obj (op W)) (b : B.val.obj (op W))
    (a' : A'.val.obj (op W)) (b' : B'.val.obj (op W))
    (h : φ.val.app (op W) ((PresheafOfModules.tensorSheafUnit A B).app (op W) (a ⊗ₜ b)) =
      (PresheafOfModules.tensorSheafUnit A' B').app (op W) (a' ⊗ₜ b')) :
    PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x
        (PresheafOfModules.stalkMapL x φ.val
          ((PresheafOfModules.tensorSheafStalkEquiv Osharp A B x).symm
            (TopCat.Presheaf.germ A.val.presheaf W x hx a ⊗ₜ
              TopCat.Presheaf.germ B.val.presheaf W x hx b))) =
      TopCat.Presheaf.germ A'.val.presheaf W x hx a' ⊗ₜ
        TopCat.Presheaf.germ B'.val.presheaf W x hx b' := by
  exact stalkMapL_symm_apply_of_germ φ _ _ W hx _ _ _ _
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp A B x W hx a b) h
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp A' B' x W hx a' b')

end GermFormula

/-! ### The tensor product of two morphisms -/

section TensorHom

variable {A B A' B' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The tensor product `f ⊗ g : A ⊗ B ⟶ A' ⊗ B'` of two morphisms of sheaves of modules. -/
def tensorHom (f : A ⟶ A') (g : B ⟶ B') : (A ⊗ₛ B) ⟶ (A' ⊗ₛ B') :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map f).app B ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A').map g

/-- The tensor product of two morphisms on the image of a local pure tensor. -/
theorem tensorHom_unit (f : A ⟶ A') (g : B ⟶ B') (V : (Opens ↥X)ᵒᵖ) (a : A.val.obj V)
    (b : B.val.obj V) :
    (tensorHom f g).val.app V ((PresheafOfModules.tensorSheafUnit A B).app V (a ⊗ₜ b)) =
      (PresheafOfModules.tensorSheafUnit A' B').app V (f.val.app V a ⊗ₜ g.val.app V b) :=
  Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp A B f g V a b

/-- **The stalk of a tensor product of morphisms is the tensor product of the stalk maps**,
under the identification of Tag 01CB. -/
theorem tensorSheafStalkEquiv_stalkMapL_tensorHom (f : A ⟶ A') (g : B ⟶ B') (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp A B).presheaf x)) :
    PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x
        (PresheafOfModules.stalkMapL x (tensorHom f g).val z) =
      TensorProduct.map (PresheafOfModules.stalkMapL x f.val)
        (PresheafOfModules.stalkMapL x g.val)
        (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x z) := by
  refine linearEquiv_apply_eq_of_tmul _ _ _ _ (fun a b => ?_) z
  refine forall_common_germ_pair A.val.presheaf B.val.presheaf x a b
    (fun W hx s t hs ht => ?_)
  subst hs ht
  refine (tensorSheafStalkEquiv_stalkMapL_symm_germ_tmul (tensorHom f g) x W hx s t _ _
    (tensorHom_unit f g (op W) s t)).trans ?_
  exact (congrArg₂ (fun p q => p ⊗ₜ q) (PresheafOfModules.stalkMapL_germ x f.val W hx s)
    (PresheafOfModules.stalkMapL_germ x g.val W hx t)).symm

/-- The tensor product of two epimorphisms of sheaves of modules is an epimorphism. -/
theorem epi_tensorHom (f : A ⟶ A') (g : B ⟶ B') [Epi f] [Epi g] : Epi (tensorHom f g) := by
  have hf := (SheafOfModules.SymPresentation.epi_iff_surjective_stalkMapL f).1 inferInstance
  have hg := (SheafOfModules.SymPresentation.epi_iff_surjective_stalkMapL g).1 inferInstance
  refine (SheafOfModules.SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x t => ?_
  obtain ⟨w, hw⟩ := TensorProduct.map_surjective (hf x) (hg x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x t)
  refine ⟨(PresheafOfModules.tensorSheafStalkEquiv Osharp A B x).symm w,
    (PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x).injective ?_⟩
  exact (tensorSheafStalkEquiv_stalkMapL_tensorHom f g x _).trans
    ((congrArg (TensorProduct.map (PresheafOfModules.stalkMapL x f.val)
      (PresheafOfModules.stalkMapL x g.val))
      ((PresheafOfModules.tensorSheafStalkEquiv Osharp A B x).apply_symm_apply w)).trans hw)

end TensorHom

/-! ### The symmetry -/

section Braid

variable (A B : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- The structure ring presheaf of `O♯` is a sheaf. -/
theorem isSheaf_structureRingPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj) :=
  (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property

/-- The symmetry `A ⊗ B ⟶ B ⊗ A` of the tensor product of sheaves of modules. -/
def braid : (A ⊗ₛ B) ⟶ (B ⊗ₛ A) :=
  (Stacks.SheafOfModules.tensorSheafBraiding Osharp.obj
    (isSheaf_structureRingPresheaf (Osharp := Osharp)) A B).hom

/-- The symmetry on the image of a local pure tensor. -/
theorem braid_unit (V : (Opens ↥X)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) :
    (braid A B).val.app V ((PresheafOfModules.tensorSheafUnit A B).app V (a ⊗ₜ b)) =
      (PresheafOfModules.tensorSheafUnit B A).app V (b ⊗ₜ a) :=
  Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt Osharp.obj
    (isSheaf_structureRingPresheaf (Osharp := Osharp)) V A B a b

/-- **The stalk of the symmetry is the symmetry of the stalks**, under the identification of
Tag 01CB. -/
theorem tensorSheafStalkEquiv_stalkMapL_braid (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp A B).presheaf x)) :
    PresheafOfModules.tensorSheafStalkEquiv Osharp B A x
        (PresheafOfModules.stalkMapL x (braid A B).val z) =
      TensorProduct.comm _ _ _ (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x z) := by
  refine linearEquiv_apply_eq_of_tmul (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp B A x)
    (PresheafOfModules.stalkMapL x (braid A B).val) (TensorProduct.comm _ _ _).toLinearMap
    (fun a b => ?_) z
  refine forall_common_germ_pair A.val.presheaf B.val.presheaf x a b
    (fun W hx s t hs ht => ?_)
  subst hs ht
  exact tensorSheafStalkEquiv_stalkMapL_symm_germ_tmul (braid A B) x W hx s t t s
    (braid_unit A B (op W) s t)

end Braid

/-! ### The middle-four interchange -/

section MiddleFour

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (A B C D : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- **The stalk of `(A ⊗ B) ⊗ (C ⊗ D)` is `(Aₓ ⊗ Bₓ) ⊗ (Cₓ ⊗ Dₓ)`**: the identification of
Tag 01CB, applied to the outer tensor product and then to each of the two inner ones. -/
def tensorTensorStalkEquiv (x : ↥X) :
    ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A ⊗ₛ B) (C ⊗ₛ D)).presheaf x) ≃ₗ[
        ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (↑(TopCat.Presheaf.stalk A.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
          ↑(TopCat.Presheaf.stalk B.val.presheaf x)) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (↑(TopCat.Presheaf.stalk C.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
          ↑(TopCat.Presheaf.stalk D.val.presheaf x)) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp (A ⊗ₛ B) (C ⊗ₛ D) x).trans
    (TensorProduct.congr (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x)
      (PresheafOfModules.tensorSheafStalkEquiv Osharp C D x))

/-- `tensorTensorStalkEquiv` on the germ of the image of a local pure tensor of images of local
pure tensors. -/
theorem tensorTensorStalkEquiv_germ (x : ↥X) (W : Opens ↥X) (hx : x ∈ W)
    (a : A.val.obj (op W)) (b : B.val.obj (op W)) (c : C.val.obj (op W))
    (d : D.val.obj (op W)) :
    tensorTensorStalkEquiv A B C D x
        (TopCat.Presheaf.germ
          (PresheafOfModules.tensorSheafVal Osharp (A ⊗ₛ B) (C ⊗ₛ D)).presheaf W x hx
          ((PresheafOfModules.tensorSheafUnit (A ⊗ₛ B) (C ⊗ₛ D)).app (op W)
            ((PresheafOfModules.tensorSheafUnit A B).app (op W) (a ⊗ₜ b) ⊗ₜ
              (PresheafOfModules.tensorSheafUnit C D).app (op W) (c ⊗ₜ d)))) =
      (TopCat.Presheaf.germ A.val.presheaf W x hx a ⊗ₜ
          TopCat.Presheaf.germ B.val.presheaf W x hx b) ⊗ₜ
        (TopCat.Presheaf.germ C.val.presheaf W x hx c ⊗ₜ
          TopCat.Presheaf.germ D.val.presheaf W x hx d) :=
  (congrArg (TensorProduct.congr (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x)
      (PresheafOfModules.tensorSheafStalkEquiv Osharp C D x))
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp (A ⊗ₛ B) (C ⊗ₛ D) x W hx
      ((PresheafOfModules.tensorSheafUnit A B).app (op W) (a ⊗ₜ b))
      ((PresheafOfModules.tensorSheafUnit C D).app (op W) (c ⊗ₜ d)))).trans
    (congrArg₂ (fun p q => p ⊗ₜ q)
      (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp A B x W hx a b)
      (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp C D x W hx c d))

/-- The associator of Tag 01CA on local pure tensors, at the `sheafTensor` spelling. -/
theorem associator_hom_unit (M N P : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (V : (Opens ↥X)ᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).hom.val.app V
        ((PresheafOfModules.tensorSheafUnit (M ⊗ₛ N) P).app V
          ((PresheafOfModules.tensorSheafUnit M N).app V (m ⊗ₜ n) ⊗ₜ p)) =
      (PresheafOfModules.tensorSheafUnit M (N ⊗ₛ P)).app V
        (m ⊗ₜ (PresheafOfModules.tensorSheafUnit N P).app V (n ⊗ₜ p)) :=
  Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp
    (isSheaf_structureRingPresheaf (Osharp := Osharp)) M N P V m n p

/-- The inverse associator of Tag 01CA on local pure tensors, at the `sheafTensor` spelling. -/
theorem associator_inv_unit (M N P : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (V : (Opens ↥X)ᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).inv.val.app V
        ((PresheafOfModules.tensorSheafUnit M (N ⊗ₛ P)).app V
          (m ⊗ₜ (PresheafOfModules.tensorSheafUnit N P).app V (n ⊗ₜ p))) =
      (PresheafOfModules.tensorSheafUnit (M ⊗ₛ N) P).app V
        ((PresheafOfModules.tensorSheafUnit M N).app V (m ⊗ₜ n) ⊗ₜ p) :=
  Stacks.TensorSheafWorld.associator_inv_val_app_tensorSheafUnit Osharp
    (isSheaf_structureRingPresheaf (Osharp := Osharp)) M N P V m n p

/-- The interchange `B ⊗ (C ⊗ D) ⟶ C ⊗ (B ⊗ D)`, built from the associators and the symmetry
`B ⊗ C ⟶ C ⊗ B`. -/
def leftInterchange : (B ⊗ₛ (C ⊗ₛ D)) ⟶ (C ⊗ₛ (B ⊗ₛ D)) :=
  (α_ B C D).inv ≫ tensorHom (braid B C) (𝟙 D) ≫ (α_ C B D).hom

/-- The middle-four interchange `(A ⊗ B) ⊗ (C ⊗ D) ⟶ (A ⊗ C) ⊗ (B ⊗ D)` of tensor products of
sheaves of modules, built from the associators of Tag 01CA and the symmetry `B ⊗ C ⟶ C ⊗ B`. -/
def middleFour : ((A ⊗ₛ B) ⊗ₛ (C ⊗ₛ D)) ⟶ ((A ⊗ₛ C) ⊗ₛ (B ⊗ₛ D)) :=
  (α_ A B (C ⊗ₛ D)).hom ≫ tensorHom (𝟙 A) (leftInterchange B C D) ≫ (α_ A C (B ⊗ₛ D)).inv

/-- The sections of a composite of morphisms of sheaves of modules. -/
theorem comp_val_app_apply {R : Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u}}
    {M N P : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P)
    (V : (Opens ↥X)ᵒᵖ) (y : M.val.obj V) :
    (f ≫ g).val.app V y = g.val.app V (f.val.app V y) :=
  rfl

/-- The identity morphism of a sheaf of modules on sections. -/
theorem id_val_app_apply {M : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (V : (Opens ↥X)ᵒᵖ) (y : M.val.obj V) :
    (𝟙 M : M ⟶ M).val.app V y = y :=
  rfl

/-- `leftInterchange` on the image of a local pure tensor. -/
theorem leftInterchange_unit (V : (Opens ↥X)ᵒᵖ) (b : B.val.obj V) (c : C.val.obj V)
    (d : D.val.obj V) :
    (leftInterchange B C D).val.app V
        ((PresheafOfModules.tensorSheafUnit B (C ⊗ₛ D)).app V
          (b ⊗ₜ (PresheafOfModules.tensorSheafUnit C D).app V (c ⊗ₜ d))) =
      (PresheafOfModules.tensorSheafUnit C (B ⊗ₛ D)).app V
        (c ⊗ₜ (PresheafOfModules.tensorSheafUnit B D).app V (b ⊗ₜ d)) := by
  have h2b : (tensorHom (braid B C) (𝟙 D)).val.app V
      ((PresheafOfModules.tensorSheafUnit (B ⊗ₛ C) D).app V
        ((PresheafOfModules.tensorSheafUnit B C).app V (b ⊗ₜ c) ⊗ₜ d)) =
      (PresheafOfModules.tensorSheafUnit (C ⊗ₛ B) D).app V
        ((PresheafOfModules.tensorSheafUnit C B).app V (c ⊗ₜ b) ⊗ₜ d) :=
    (tensorHom_unit (braid B C) (𝟙 D) V _ d).trans
      (congrArg (fun t => (PresheafOfModules.tensorSheafUnit (C ⊗ₛ B) D).app V (t ⊗ₜ d))
        (braid_unit B C V b c))
  unfold leftInterchange
  refine (comp_val_app_apply (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) _ _ V _).trans
    ((comp_val_app_apply (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) _ _ V _).trans ?_)
  rw [associator_inv_unit B C D V b c d]
  exact (congrArg (ConcreteCategory.hom ((α_ C B D).hom.val.app V)) h2b).trans
    (associator_hom_unit C B D V c b d)

/-- The middle-four interchange on the image of a local pure tensor of images of local pure
tensors. -/
theorem middleFour_unit (V : (Opens ↥X)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V)
    (c : C.val.obj V) (d : D.val.obj V) :
    (middleFour A B C D).val.app V
        ((PresheafOfModules.tensorSheafUnit (A ⊗ₛ B) (C ⊗ₛ D)).app V
          ((PresheafOfModules.tensorSheafUnit A B).app V (a ⊗ₜ b) ⊗ₜ
            (PresheafOfModules.tensorSheafUnit C D).app V (c ⊗ₜ d))) =
      (PresheafOfModules.tensorSheafUnit (A ⊗ₛ C) (B ⊗ₛ D)).app V
        ((PresheafOfModules.tensorSheafUnit A C).app V (a ⊗ₜ c) ⊗ₜ
          (PresheafOfModules.tensorSheafUnit B D).app V (b ⊗ₜ d)) := by
  unfold middleFour
  refine (comp_val_app_apply (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) _ _ V _).trans
    ((comp_val_app_apply (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
      (M := A ⊗ₛ (B ⊗ₛ (C ⊗ₛ D))) _ _ V _).trans ?_)
  rw [associator_hom_unit A B (C ⊗ₛ D) V a b
      ((PresheafOfModules.tensorSheafUnit C D).app V (c ⊗ₜ d)),
    tensorHom_unit (𝟙 A) (leftInterchange B C D) V a _, id_val_app_apply V a]
  exact (congrArg (fun t => (α_ A C (B ⊗ₛ D)).inv.val.app V
    ((PresheafOfModules.tensorSheafUnit A (C ⊗ₛ (B ⊗ₛ D))).app V (a ⊗ₜ t)))
    (leftInterchange_unit B C D V b c d)).trans
    (associator_inv_unit A C (B ⊗ₛ D) V a c
      ((PresheafOfModules.tensorSheafUnit B D).app V (b ⊗ₜ d)))

/-- **The stalk of the middle-four interchange is the middle-four interchange of the stalks**,
under the identification `tensorTensorStalkEquiv` of the stalk of `(A ⊗ B) ⊗ (C ⊗ D)` with
`(Aₓ ⊗ Bₓ) ⊗ (Cₓ ⊗ Dₓ)`. -/
theorem tensorTensorStalkEquiv_stalkMapL_middleFour (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A ⊗ₛ B) (C ⊗ₛ D)).presheaf x)) :
    tensorTensorStalkEquiv A C B D x
        (PresheafOfModules.stalkMapL x (middleFour A B C D).val z) =
      TensorProduct.tensorTensorTensorComm _ _ _ _ _ (tensorTensorStalkEquiv A B C D x z) := by
  refine linearEquiv_apply_eq_of_tmul_tmul (tensorTensorStalkEquiv A B C D x)
    (tensorTensorStalkEquiv A C B D x) (PresheafOfModules.stalkMapL x (middleFour A B C D).val)
    (TensorProduct.tensorTensorTensorComm _ _ _ _ _).toLinearMap (fun a b c d => ?_) z
  refine forall_common_germ_four A.val.presheaf B.val.presheaf C.val.presheaf D.val.presheaf x
    a b c d (fun W hx s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => ?_)
  subst h₁ h₂ h₃ h₄
  exact stalkMapL_symm_apply_of_germ (middleFour A B C D) _ _ W hx _ _ _ _
    (tensorTensorStalkEquiv_germ A B C D x W hx s₁ s₂ s₃ s₄)
    (middleFour_unit A B C D (op W) s₁ s₂ s₃ s₄)
    (tensorTensorStalkEquiv_germ A C B D x W hx s₁ s₃ s₂ s₄)

end MiddleFour

/-! ### Tensor products of tensor products of morphisms -/

section TensorHomTensorHom

variable {A B C D A' B' C' D' :
  SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The stalk of `(f ⊗ g) ⊗ (h ⊗ k)` is `(fₓ ⊗ gₓ) ⊗ (hₓ ⊗ kₓ)`**, under the identifications
`tensorTensorStalkEquiv`. -/
theorem tensorTensorStalkEquiv_stalkMapL_tensorHom_tensorHom (f : A ⟶ A') (g : B ⟶ B')
    (h : C ⟶ C') (k : D ⟶ D') (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A ⊗ₛ B) (C ⊗ₛ D)).presheaf x)) :
    tensorTensorStalkEquiv A' B' C' D' x
        (PresheafOfModules.stalkMapL x (tensorHom (tensorHom f g) (tensorHom h k)).val z) =
      TensorProduct.map
        (TensorProduct.map (PresheafOfModules.stalkMapL x f.val)
          (PresheafOfModules.stalkMapL x g.val))
        (TensorProduct.map (PresheafOfModules.stalkMapL x h.val)
          (PresheafOfModules.stalkMapL x k.val))
        (tensorTensorStalkEquiv A B C D x z) := by
  refine (congrArg (TensorProduct.congr (PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x)
      (PresheafOfModules.tensorSheafStalkEquiv Osharp C' D' x))
    (tensorSheafStalkEquiv_stalkMapL_tensorHom (tensorHom f g) (tensorHom h k) x z)).trans ?_
  exact congr_map_apply _ _ _ _ _ _ _ _ (tensorSheafStalkEquiv_stalkMapL_tensorHom f g x)
    (tensorSheafStalkEquiv_stalkMapL_tensorHom h k x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp (A ⊗ₛ B) (C ⊗ₛ D) x z)

end TensorHomTensorHom

end SheafOfModules.TensorStalkMaps

end
