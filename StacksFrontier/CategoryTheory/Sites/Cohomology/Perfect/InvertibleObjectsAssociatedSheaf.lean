module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionTensorGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsIdempotentSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedAssociated
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeRetract

/-!
# The functor `N ↦ N ⊗_R O` of Stacks 0FPX on a ringed site

Let `(C, O)` be a ringed site and `R = Γ(C, O)`. The functor `N ↦ N ⊗_R O` from `R`-modules to
`O`-modules (the sheafification of `U ↦ O(U) ⊗_R N`) is left adjoint to global sections. Its unit
is an isomorphism at finite projective `R`-modules and its counit is an isomorphism at direct
summands of finite free `O`-modules, which is the equivalence of Stacks 0FPX read through the
adjunction; and it carries the tensor product of `R`-modules to the tensor product of
`O`-modules, naturally in both variables, hence the total tensor complex of two complexes of
`R`-modules to the total tensor complex of the associated complexes of `O`-modules.

These are the site counterparts of `Stacks.Cohomology.InvertibleDerived.assocGammaIso` and
`Stacks.Cohomology.InvertibleDerived.assocTotIso` on a ringed space, used by the proof of
`(1) ⟹ (2)` of Stacks 0FPY to pass from the sheaves to the global sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.assocF`, `gammaF`, `assocAdj`: the adjunction.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.assocTensorIso`: the tensor comparison.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.assocTotIso`: the total-complex comparison.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.isIso_assocAdj_unit` and
  `isIso_assocAdj_counit`: the unit and counit are isomorphisms where Stacks 0FPX says.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.assocTensorIso_naturality_left` and
  `assocTensorIso_naturality_right`: naturality of the tensor comparison.

## References

* [Stacks Project, Tag 0FPX](https://stacks.math.columbia.edu/tag/0FPX)
* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules MonoidalCategory

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The ring `Γ(C, O)` of global sections of the structure sheaf, as in Stacks 0FPX. -/
abbrev GammaRing : Type u := GlobalFunctionRing X.O

/-- The functor `N ↦ N ⊗_R O` of Stacks 0FPX, from modules over `R = Γ(C, O)` to `O`-modules. -/
abbrev assocF : ModuleCat.{u} (GammaRing X) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  sectionTensorSheafFunctor.{u, u, u, u} X.O

/-- Global sections, as modules over `R = Γ(C, O)`. -/
abbrev gammaF : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
    ModuleCat.{u} (GammaRing X) :=
  globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The adjunction `N ↦ N ⊗_R O ⊣ Γ`. -/
def assocAdj : assocF X ⊣ gammaF X := sectionTensorSheafAdjunction.{u, u, u, u} X.O

/-- Global sections, in the spelling of `gammaF`, are additive. The base instance
`Stacks.Cohomology.SiteModules.globalSectionsFunctor_additive` is stated for the ring
`GlobalSectionRing (ringSheaf X.O)`, which is `GammaRing X` only up to unfolding
`Stacks.SheafOfModules.Tensor.ringSheaf`, a step instance search does not take. -/
instance gammaF_additive : (gammaF X).Additive :=
  globalSectionsFunctor_additive _

/-- The free module on `n` generators over `R = Γ(C, O)`. -/
abbrev freeG (n : ℕ) : ModuleCat.{u} (GammaRing X) :=
  ModuleCat.of (GammaRing X) (ULift.{u} (Fin n) →₀ GammaRing X)

/-- Global sections commute with finite coproducts of copies of the structure sheaf. -/
theorem preservesColimit_gammaF_unit (n : ℕ) :
    PreservesColimit (Discrete.functor (fun _ : ULift.{u} (Fin n) =>
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (gammaF X) := by
  have : PreservesLimitsOfShape (Discrete (ULift.{u} (Fin n))) (gammaF X) :=
    (assocAdj X).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have := preservesBiproductsOfShape_of_preservesProductsOfShape (J := ULift.{u} (Fin n))
    (gammaF X)
  exact preservesCoproduct_of_preservesBiproduct (gammaF X)

/-- **The unit of `assocF ⊣ gammaF` is an isomorphism at a finite free module.** -/
theorem isIso_assocAdj_unit_free (n : ℕ) : IsIso ((assocAdj X).unit.app (freeG X n)) := by
  have h := isIso_sectionTensorSheafUnit_free.{u, u, u} X.O (ULift.{u} (Fin n))
    (preservesColimit_gammaF_unit X n)
  have e := sectionTensorSheafAdjunction_unit_app (J := X.J) (O := X.O)
    (freeGlobalModule X.O (ULift.{u} (Fin n)))
  rwa [← e] at h

/-- **The unit of `assocF ⊣ gammaF` is an isomorphism at a finite projective module.** -/
theorem isIso_assocAdj_unit (N : ModuleCat.{u} (GammaRing X))
    [Module.Finite (GammaRing X) N] [Module.Projective (GammaRing X) N] :
    IsIso ((assocAdj X).unit.app N) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (GammaRing X) N
  let eL : (ULift.{u} (Fin n) →₀ GammaRing X) ≃ₗ[GammaRing X] (Fin n → GammaRing X) :=
    (Finsupp.linearEquivFunOnFinite (GammaRing X) (GammaRing X) (ULift.{u} (Fin n))).trans
      (LinearEquiv.funCongrLeft (GammaRing X) (GammaRing X) Equiv.ulift.symm)
  have := isIso_assocAdj_unit_free X n
  let ρ : Retract N (freeG X n) :=
    ⟨ModuleCat.ofHom (eL.symm.toLinearMap ∘ₗ g), ModuleCat.ofHom (f ∘ₗ eL.toLinearMap), by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      exact (congrArg f (eL.apply_symm_apply (g m))).trans (LinearMap.congr_fun hfg m)⟩
  exact Stacks.Cohomology.InvertibleDerived.isIso_unit_of_retract (assocAdj X) ρ

/-- **The counit of `assocF ⊣ gammaF` is an isomorphism at a finite free sheaf of modules.** -/
theorem isIso_assocAdj_counit_free (n : ℕ) :
    IsIso ((assocAdj X).counit.app (SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (ULift.{u} (Fin n)))) := by
  have := isIso_assocAdj_unit_free X n
  have : IsIso ((assocAdj X).counit.app ((assocF X).obj (freeG X n))) := by
    have : IsIso ((assocF X).map ((assocAdj X).unit.app (freeG X n)) ≫
        (assocAdj X).counit.app ((assocF X).obj (freeG X n))) := by
      rw [(assocAdj X).left_triangle_components (freeG X n)]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((assocF X).map ((assocAdj X).unit.app (freeG X n))) _
  let e : (assocF X).obj (freeG X n) ≅ SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (ULift.{u} (Fin n)) :=
    sectionTensorFreeIso.{u, u, u} X.O (ULift.{u} (Fin n))
  exact Stacks.AssociatedSheaf.isIso_counit_of_retract (assocAdj X) ⟨e.inv, e.hom, e.inv_hom_id⟩

/-- **The counit of `assocF ⊣ gammaF` is an isomorphism at a direct summand of a finite free
module.** -/
theorem isIso_assocAdj_counit (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : _root_.IsDirectSummandOfFiniteFree _ F) :
    IsIso ((assocAdj X).counit.app F) := by
  obtain ⟨n, i, r, h⟩ := (_root_.isDirectSummandOfFiniteFree_iff_free _ F).mp hF
  have := isIso_assocAdj_counit_free X n
  exact Stacks.AssociatedSheaf.isIso_counit_of_retract (assocAdj X) ⟨i, r, h⟩

/-! ### The functor `N ↦ N ⊗_R O` and the tensor product -/

variable {X}

variable (X) in
/-- The presheaf `U ↦ O(U) ⊗_R N` as a functor of `N`. -/
abbrev assocPF : ModuleCat.{u} (GammaRing X) ⥤
    PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  sectionTensorPresheafFunctor.{u, u, u, u} X.O

/-- The presheaf `U ↦ O(U) ⊗_R N`, before sheafification. -/
abbrev assocP (M : ModuleCat.{u} (GammaRing X)) :
    PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (assocPF X).obj M

/-- Base change distributes over the tensor product, over a fixed object:
`O(U) ⊗_R (M ⊗_R N) ≅ (O(U) ⊗_R M) ⊗_{O(U)} (O(U) ⊗_R N)`. -/
def assocPTensorIsoAt (U : X.Cᵒᵖ) (M N : ModuleCat.{u} (GammaRing X)) :
    (assocP (M ⊗ N)).obj U ≅
      (PresheafOfModules.tensorObj (O := X.O.obj) (assocP M) (assocP N)).obj U :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange (GammaRing X) (X.O.obj.obj U)
    M N).toModuleIso

/-- Two additive maps out of `A ⊗ (B ⊗ C)` agree if they agree on pure tensors `a ⊗ (b ⊗ c)`. -/
private theorem eq_of_tmul_tmul {R A B C S F : Type*} [CommSemiring R] [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid S] [Module R A] [Module R B] [Module R C]
    [FunLike F (TensorProduct R A (TensorProduct R B C)) S]
    [AddMonoidHomClass F (TensorProduct R A (TensorProduct R B C)) S] (f g : F)
    (h : ∀ (a : A) (b : B) (c : C), f (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = g (a ⊗ₜ[R] (b ⊗ₜ[R] c))) :
    f = g := by
  refine DFunLike.ext _ _ fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [TensorProduct.tmul_add, hz, hw]
    | tmul b c => exact h a b c

/-- **The presheaf-level comparison of `N ↦ N ⊗_R O` with the tensor product.** -/
def assocPTensorIso (M N : ModuleCat.{u} (GammaRing X)) :
    assocP (M ⊗ N) ≅ PresheafOfModules.tensorObj (O := X.O.obj) (assocP M) (assocP N) := by
  refine PresheafOfModules.isoMk (fun U ↦ assocPTensorIsoAt U M N)
    (fun {U V} i ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg (fun t ↦ t + _) hx).trans
      ((congrArg (fun t ↦ _ + t) hy).trans (map_add _ x y).symm))
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (TensorProduct.tmul_zero _ a)).trans (map_zero _)).trans
        (((congrArg _ (TensorProduct.tmul_zero _ a)).trans (map_zero _)).symm)
    | add z w hz hw =>
      exact ((congrArg _ (TensorProduct.tmul_add a z w)).trans ((map_add _ _ _).trans
        ((congrArg (fun t ↦ t + _) hz).trans ((congrArg (fun t ↦ _ + t) hw).trans
          (map_add _ _ _).symm)))).trans (congrArg _ (TensorProduct.tmul_add a z w)).symm
    | tmul m n =>
      have h : (X.O.obj.map i).hom (1 : X.O.obj.obj U) = 1 := map_one _
      with_unfolding_all exact congrArg (fun b : X.O.obj.obj V =>
        TensorProduct.tmul (X.O.obj.obj V)
          (TensorProduct.tmul (GammaRing X) ((X.O.obj.map i).hom a) m)
          (TensorProduct.tmul (GammaRing X) b n)) h.symm

/-- **`N ↦ N ⊗_R O` carries the tensor product of `R`-modules to the tensor product of sheaves
of modules.** -/
def assocTensorIso (M N : ModuleCat.{u} (GammaRing X)) :
    (assocF X).obj (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj ((assocF X).obj M)).obj
        ((assocF X).obj N) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapIso
      (assocPTensorIso M N) ≪≫
    Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (assocP M) (assocP N)

variable (X) in
/-- Sheafification of presheaves of `O`-modules. -/
abbrev Sh : PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

variable (X) in
/-- The underlying presheaf of a sheafification, as the adjunction spells it. -/
abbrev ShVal : PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
    PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  Sh X ⋙ SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- The sheafification unit of `U ↦ O(U) ⊗_R N`. -/
abbrev assocUnit (M : ModuleCat.{u} (GammaRing X)) : assocP M ⟶ (ShVal X).obj (assocP M) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app (assocP M)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Naturality of `assocPTensorIso` in the first variable. -/
theorem assocPTensorIso_naturality_left {M M' : ModuleCat.{u} (GammaRing X)} (f : M ⟶ M')
    (N : ModuleCat.{u} (GammaRing X)) :
    (assocPF X).map (f ▷ N) ≫ (assocPTensorIso M' N).hom =
      (assocPTensorIso M N).hom ≫
        PresheafOfModules.tensorHom ((assocPF X).map f) (𝟙 (assocP N)) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (eq_of_tmul_tmul _ _ ?_)
  intro a m n
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Naturality of `assocPTensorIso` in the second variable. -/
theorem assocPTensorIso_naturality_right (M : ModuleCat.{u} (GammaRing X))
    {N N' : ModuleCat.{u} (GammaRing X)} (g : N ⟶ N') :
    (assocPF X).map (M ◁ g) ≫ (assocPTensorIso M N').hom =
      (assocPTensorIso M N).hom ≫
        PresheafOfModules.tensorHom (𝟙 (assocP M)) ((assocPF X).map g) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (eq_of_tmul_tmul _ _ ?_)
  intro a m n
  rfl

/-- Naturality of `assocTensorIso` from a presheaf-level square and naturality of the units. -/
private theorem sheafify_assocPTensorIso_square {M M' N N' : ModuleCat.{u} (GammaRing X)}
    (φ : assocP (M ⊗ N) ⟶ assocP (M' ⊗ N')) (α : assocP M ⟶ assocP M') (β : assocP N ⟶ assocP N')
    (α' : (ShVal X).obj (assocP M) ⟶ (ShVal X).obj (assocP M'))
    (β' : (ShVal X).obj (assocP N) ⟶ (ShVal X).obj (assocP N'))
    (H : φ ≫ (assocPTensorIso M' N').hom =
      (assocPTensorIso M N).hom ≫ PresheafOfModules.tensorHom α β)
    (hα : α ≫ assocUnit M' = assocUnit M ≫ α') (hβ : β ≫ assocUnit N' = assocUnit N ≫ β') :
    (Sh X).map φ ≫ (assocTensorIso M' N').hom =
      (assocTensorIso M N).hom ≫ (Sh X).map (PresheafOfModules.tensorHom α' β') := by
  have key : φ ≫ (assocPTensorIso M' N').hom ≫
        PresheafOfModules.tensorHom (assocUnit M') (assocUnit N') =
      (assocPTensorIso M N).hom ≫ PresheafOfModules.tensorHom (assocUnit M) (assocUnit N) ≫
        PresheafOfModules.tensorHom α' β' := by
    rw [← Category.assoc, H, Category.assoc, PresheafOfModules.tensorHom_comp,
      PresheafOfModules.tensorHom_comp, hα, hβ]
  have := congrArg (Sh X).map key
  simp only [Functor.map_comp] at this
  exact this

/-- **Naturality of `assocTensorIso` in the first variable.** -/
theorem assocTensorIso_naturality_left {M M' : ModuleCat.{u} (GammaRing X)} (f : M ⟶ M')
    (N : ModuleCat.{u} (GammaRing X)) :
    (assocF X).map (f ▷ N) ≫ (assocTensorIso M' N).hom =
      (assocTensorIso M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
          ((assocF X).map f)).app ((assocF X).obj N) := by
  refine sheafify_assocPTensorIso_square _ _ (𝟙 _) _ (𝟙 _)
    (assocPTensorIso_naturality_left f N) ?_ (by simp)
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality ((assocPF X).map f)

/-- **Naturality of `assocTensorIso` in the second variable.** -/
theorem assocTensorIso_naturality_right (M : ModuleCat.{u} (GammaRing X))
    {N N' : ModuleCat.{u} (GammaRing X)} (g : N ⟶ N') :
    (assocF X).map (M ◁ g) ≫ (assocTensorIso M N').hom =
      (assocTensorIso M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          ((assocF X).obj M)).map ((assocF X).map g) := by
  refine sheafify_assocPTensorIso_square _ (𝟙 _) _ (𝟙 _) _
    (assocPTensorIso_naturality_right M g) (by simp) ?_
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality ((assocPF X).map g)

/-! ### Total complexes -/

variable (X) in
/-- The functor `N ↦ N ⊗_R O` preserves colimits. -/
instance assocF_preservesColimits : PreservesColimitsOfSize.{0, 0} (assocF X) :=
  (assocAdj X).leftAdjoint_preservesColimits

variable (X) in
/-- The functor `N ↦ N ⊗_R O` is additive. -/
instance assocF_additive : (assocF X).Additive :=
  have : PreservesBinaryBiproducts (assocF X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The tensor product of sheaves of `O`-modules preserves zero morphisms in the first variable. -/
instance sheafTensor_preservesZeroMorphisms' :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).PreservesZeroMorphisms :=
  inferInstance

/-- Tensoring with a fixed sheaf of `O`-modules `A` preserves zero morphisms. -/
instance sheafTensor_obj_preservesZeroMorphisms'
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).PreservesZeroMorphisms :=
  inferInstance

/-- **`N ↦ N ⊗_R O` carries the total tensor complex to the total tensor complex.** -/
def assocTotIso (P P' : CochainComplex (ModuleCat.{u} (GammaRing X)) ℤ) :
    ((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ P') ≅
      HomologicalComplex.mapBifunctor
        (((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P')
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  Functor.mapBifunctorTotalIso (curriedTensor _)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    (assocF X) (assocF X) (assocF X) assocTensorIso
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f b => assocTensorIso_naturality_left f b)
    (fun a _ _ g => assocTensorIso_naturality_right a g) P P'

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
