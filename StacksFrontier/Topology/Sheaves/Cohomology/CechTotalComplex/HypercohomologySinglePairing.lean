module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing

/-!
# Pairings of sheaves placed in degree zero

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and `A = Γ(X, 𝒪_X)`. A
pairing `ℱ × 𝒢 ⟶ ℋ` of `𝒪_X`-modules on sections — a compatible family of `A`-bilinear maps
`ℱ(Z) × 𝒢(Z) ⟶ ℋ(Z)` — is a pairing of the complexes `ℱ[0]`, `𝒢[0]`, `ℋ[0]` in the sense of
`Stacks.Cech.Hypercohomology.Pairing`: the Leibniz rule holds trivially, every differential being
zero.

## Main definitions

* `Stacks.Cech.Hypercohomology.singlePairing`: the pairing of complexes concentrated in degree
  zero attached to a pairing of sheaves on sections.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)

open scoped TensorProduct

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The sections over the opens of `X` of a sheaf of `𝒪_X`-modules, as a presheaf of
`Γ(X, 𝒪_X)`-modules. -/
abbrev sectionsP (F : SheafOfModules.{u} (ringSheaf O)) :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).obj F

/-- Morphisms out of the pointwise tensor product of presheaves of modules agree if they agree on
pure tensors. -/
private theorem tensorPresheafModules_hom_ext_tmul
    {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {P Q T : Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤)}
    {f g : ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj P).obj Q ⟶ T}
    (h : ∀ (Z : (Over (⊤ : Opens X))ᵒᵖ) (x : P.obj Z) (y : Q.obj Z),
      (f.app Z).hom (x ⊗ₜ y) = (g.app Z).hom (x ⊗ₜ y)) : f = g :=
  NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => h Z x y))

/-- The pointwise tensor product of presheaves of modules carries a zero morphism in the first
variable to zero. -/
theorem tensorPresheafModules_map_zero
    {P P' : Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤)}
    (Q : Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤)) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map (0 : P ⟶ P')).app Q = 0 := by
  refine tensorPresheafModules_hom_ext_tmul fun Z x y => ?_
  change (TensorProduct.map _ _) (x ⊗ₜ y) = 0
  rw [TensorProduct.map_tmul]
  change (0 : P'.obj Z) ⊗ₜ _ = 0
  exact TensorProduct.zero_tmul _ _

/-- The pointwise tensor product of presheaves of modules carries a zero morphism in the second
variable to zero. -/
theorem tensorPresheafModules_obj_map_zero
    (P : Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤))
    {Q Q' : Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤)} :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj P).map (0 : Q ⟶ Q') = 0 := by
  refine tensorPresheafModules_hom_ext_tmul fun Z x y => ?_
  change (TensorProduct.map _ _) (x ⊗ₜ y) = 0
  rw [TensorProduct.map_tmul]
  change _ ⊗ₜ (0 : Q'.obj Z) = 0
  exact TensorProduct.tmul_zero _ _

variable {O}

/-- The scalar action of `Γ(X, 𝒪_X)` on the sections of a sheaf of modules over an open `Z` is
the action of the restriction of the scalar to `Z`. -/
theorem sectionsP_smul (F : SheafOfModules.{u} (ringSheaf O)) (Z : (Over (⊤ : Opens X))ᵒᵖ)
    (r : SectionRing (ringSheaf O) ⊤) (x : (sectionsP O F).obj Z) :
    r • x = (show (sectionsP O F).obj Z from
      ((ringSheaf O).obj.map ((homOfLE le_top : (unop Z).left ⟶ ⊤).op) r) •
        (show F.val.obj (op (unop Z).left) from x)) :=
  rfl

/-- A bilinear map of `B`-modules is bilinear over `A` after restricting scalars along
`ψ : A ⟶ B`, and so descends to the tensor product over `A`. -/
def restrictScalarsLift {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)
    (M N P : ModuleCat.{u} B) (b : M →ₗ[B] N →ₗ[B] P) :
    ModuleCat.of A (((ModuleCat.restrictScalars ψ).obj M) ⊗[A]
        ((ModuleCat.restrictScalars ψ).obj N)) ⟶ (ModuleCat.restrictScalars ψ).obj P :=
  ConcreteCategory.ofHom (C := ModuleCat A) (TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => b x y
          map_add' := fun y y' => (b x).map_add y y'
          map_smul' := fun a y => (b x).map_smul (ψ a) y }
      map_add' := fun x x' => LinearMap.ext fun y =>
        LinearMap.congr_fun (b.map_add (show M from x) (show M from x')) (show N from y)
      map_smul' := fun a x => LinearMap.ext fun y =>
        LinearMap.congr_fun (b.map_smul (ψ a) (show M from x)) (show N from y) })

/-- The descended map on a pure tensor. -/
theorem restrictScalarsLift_tmul {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)
    (M N P : ModuleCat.{u} B) (b : M →ₗ[B] N →ₗ[B] P) (x : M) (y : N) :
    ConcreteCategory.hom (restrictScalarsLift ψ M N P b) (x ⊗ₜ[A] y) = b x y :=
  rfl

/-- A biadditive map of `B`-modules which is linear in each variable, as a bilinear map. -/
def bilinearOfApp {B : Type u} [CommRing B] (M N P : ModuleCat.{u} B) (f : M →+ N →+ P)
    (hl : ∀ (r : B) (x : M) (y : N), f (r • x) y = r • f x y)
    (hr : ∀ (r : B) (x : M) (y : N), f x (r • y) = r • f x y) :
    M →ₗ[B] N →ₗ[B] P :=
  LinearMap.mk₂ B (fun x y => f x y)
    (fun x x' y => by rw [map_add, AddMonoidHom.add_apply]) hl
    (fun x y y' => by rw [map_add]) hr

/-- **The pairing on sections attached to a bilinear map of sheaves of modules**: on the opens
of `X`, the `𝒪_X(Z)`-bilinear maps `ℱ(Z) × 𝒢(Z) ⟶ ℋ(Z)` are in particular
`Γ(X, 𝒪_X)`-bilinear, and they descend to the tensor products over `Γ(X, 𝒪_X)`. -/
def bilinearPairing {F G H : SheafOfModules.{u} (ringSheaf O)}
    (β : Stacks.BilinearMap F.val G.val H.val) :
    Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H) where
  app Z := restrictScalarsLift
    (Stacks.Cech.SheafTensorPairing.coeffRestriction O ⊤ Z) (F.val.obj (op (unop Z).left))
    (G.val.obj (op (unop Z).left)) (H.val.obj (op (unop Z).left))
    (bilinearOfApp _ _ _ (β.app (op (unop Z).left)) (β.map_smul_left (op (unop Z).left))
      (β.map_smul_right (op (unop Z).left)))
  naturality Z Z' f := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_)
    exact (β.naturality ((Over.forget (⊤ : Opens X)).op.map f) x y).symm

/-- The pairing of a bilinear map on a pure tensor. -/
theorem bilinearPairing_app_tmul {F G H : SheafOfModules.{u} (ringSheaf O)}
    (β : Stacks.BilinearMap F.val G.val H.val) (Z : (Over (⊤ : Opens X))ᵒᵖ)
    (x : F.val.obj (op (unop Z).left)) (y : G.val.obj (op (unop Z).left)) :
    ((bilinearPairing β).app Z).hom (x ⊗ₜ y) = β.app (op (unop Z).left) x y :=
  rfl

variable (O) in
/-- The term in degree `a = 0` of the sections of a sheaf placed in degree zero. -/
def singleXIso (F : SheafOfModules.{u} (ringSheaf O)) (a : ℤ) (h : a = 0) :
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F 0).obj).X a ≅ sectionsP O F :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).mapIso
    (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F a h)

/-- The differentials of the sections of a sheaf placed in degree zero vanish. -/
theorem sectionsComplex_singlePlus_d (F : SheafOfModules.{u} (ringSheaf O)) (i j : ℤ) :
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F 0).obj).d i j = 0 := by
  change (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
    (((HomologicalComplex.single _ (up ℤ) 0).obj F).d i j) = 0
  rw [HomologicalComplex.single_obj_d, Functor.map_zero]

/-- **The pairing of sheaves placed in degree zero attached to a pairing on sections**: the given
pairing in degree `(0, 0)` and zero in every other bidegree. -/
def singlePairing {F G H : SheafOfModules.{u} (ringSheaf O)}
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    Pairing O (singlePlus O F 0) (singlePlus O G 0) (singlePlus O H 0) where
  μ a b n h := if hab : a = 0 ∧ b = 0 then
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (singleXIso O F a hab.1).hom).app _ ≫
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj (sectionsP O F)).map
          (singleXIso O G b hab.2).hom ≫ μ₀ ≫ (singleXIso O H n (by omega)).inv
    else 0
  μ_d a b n h := by
    rw [sectionsComplex_singlePlus_d, sectionsComplex_singlePlus_d,
      sectionsComplex_singlePlus_d, Limits.comp_zero, tensorPresheafModules_map_zero,
      tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.zero_comp, smul_zero,
      add_zero]

/-- The pairing of sheaves placed in degree zero, in bidegree `(0, 0)`. -/
theorem singlePairing_μ_zero {F G H : SheafOfModules.{u} (ringSheaf O)}
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    (singlePairing μ₀).μ 0 0 0 rfl =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (singleXIso O F 0 rfl).hom).app _ ≫
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj (sectionsP O F)).map
          (singleXIso O G 0 rfl).hom ≫ μ₀ ≫ (singleXIso O H 0 rfl).inv := by
  dsimp only [singlePairing]
  exact dite_eq_left ⟨rfl, rfl⟩

/-- The pairing of sheaves placed in degree zero vanishes outside bidegree `(0, 0)`. -/
theorem singlePairing_μ_of_ne {F G H : SheafOfModules.{u} (ringSheaf O)}
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) (a b n : ℤ) (h : a + b = n) (hab : ¬(a = 0 ∧ b = 0)) :
    (singlePairing μ₀).μ a b n h = 0 := by
  dsimp only [singlePairing]
  exact dite_eq_right hab

variable (O) in
/-- A morphism of sheaves of modules placed in degree zero. -/
def singlePlusMap {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G) :
    singlePlus O F 0 ⟶ singlePlus O G 0 :=
  ObjectProperty.homMk ((HomologicalComplex.single _ (up ℤ) 0).map f)

/-- **Compatible bilinear maps give compatible pairings in degree zero**: if
`β₁(x, v(y)) = β₂(u(x), y)` on sections, the induced pairings of sheaves placed in degree zero
satisfy `μ₁ ∘ (id ⊗ v) = μ₂ ∘ (u ⊗ id)` in every bidegree. -/
theorem singlePairing_compat {F₁ F₂ G₁ G₂ H : SheafOfModules.{u} (ringSheaf O)}
    (u : F₁ ⟶ F₂) (v : G₂ ⟶ G₁) (β₁ : Stacks.BilinearMap F₁.val G₁.val H.val)
    (β₂ : Stacks.BilinearMap F₂.val G₂.val H.val)
    (h : ∀ (Z : (Opens X)ᵒᵖ) (x : F₁.val.obj Z) (y : G₂.val.obj Z),
      β₁.app Z x (v.val.app Z y) = β₂.app Z (u.val.app Z x) y)
    (a b n : ℤ) (hn : a + b = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F₁ 0).obj).X a)).map
        (((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMap O v).hom).f b) ≫
        (singlePairing (bilinearPairing β₁)).μ a b n hn =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMap O u).hom).f a)).app
          (((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O G₂ 0).obj).X b) ≫
        (singlePairing (bilinearPairing β₂)).μ a b n hn := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    obtain rfl : n = 0 := by omega
    rw [singlePairing_μ_zero, singlePairing_μ_zero]
    exact tensorPresheafModules_hom_ext_tmul fun Z x y => h (op (unop Z).left) x y
  · rw [singlePairing_μ_of_ne _ a b n hn hab, singlePairing_μ_of_ne _ a b n hn hab,
      Limits.comp_zero, Limits.comp_zero]

end Stacks.Cech.Hypercohomology
