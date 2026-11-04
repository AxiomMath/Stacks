module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of a bilinear map of presheaves of modules

Let `θ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a category `C` and let
`M`, `N`, `P` be presheaves of `O₁`-modules. Every `O₁`-bilinear map `M × N ⟶ P` extends to an
`O₂`-bilinear map between the change-of-rings presheaves `O₂ ⊗_{O₁} M`, `O₂ ⊗_{O₁} N` and
`O₂ ⊗_{O₁} P`, characterised on pure tensors by `(a ⊗ m, c ⊗ n) ↦ ac ⊗ β(m, n)`.

## Main definitions

* `baseChange₂`: the base change of a bilinear map of modules over a commutative ring along an
  algebra.
* `cofApp`: the sectionwise base change of a bilinear map of presheaves of modules.
* `cofBil`: the base change of a bilinear map of presheaves of modules, as a bilinear map of the
  change-of-rings presheaves.

## Main results

* `baseChange₂_tmul`, `cofApp_tmul`: the base-changed bilinear map on pure tensors.
* `cofApp_naturality`: the base-changed bilinear map commutes with the restriction maps.
* `cofApp_map`: naturality in the bilinear map: a triple of morphisms compatible with two
  bilinear maps base-changes to a triple compatible with their base changes.

## Implementation notes

`baseChange₂` applies the base change of linear maps twice: the base change of `n ↦ b m n` is
`S`-linear, depends `R`-linearly on `m`, and so extends over `S ⊗_R M` by
`TensorProduct.AlgebraTensorModule.lift`.

The algebra structure on the sections of `O₂` over those of `O₁` is the one induced by `θ` at
each object of the site, the same one `Stacks.PresheafOfModules.ChangeOfRings.cofObj` uses; it
depends on `θ` and on the object, so it is introduced by `letI` at each use.

Scalars are written at `O₂.obj X` rather than at
`(Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₂).obj X`; the two agree definitionally,
and the tensor products are formed over the former.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory TensorProduct Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.Sheaves.BilinearChangeOfRings

universe v u w

section Algebra

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The base change along an `R`-algebra `S` of an `R`-bilinear map `M × N ⟶ P`: the
`S`-bilinear map on the base-changed modules sending `a ⊗ m` and `c ⊗ n` to `ac ⊗ b m n`. -/
public noncomputable def baseChange₂ (b : M →ₗ[R] N →ₗ[R] P) :
    S ⊗[R] M →ₗ[S] (S ⊗[R] N) →ₗ[S] (S ⊗[R] P) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton S (M →ₗ[R] ((S ⊗[R] N) →ₗ[S] (S ⊗[R] P)))
      ((LinearMap.baseChangeHom R S N P).comp b))

/-- The base change of a bilinear map on pure tensors. -/
public lemma baseChange₂_tmul (b : M →ₗ[R] N →ₗ[R] P) (a c : S) (m : M) (n : N) :
    baseChange₂ (S := S) b (a ⊗ₜ m) (c ⊗ₜ n) = (a * c) ⊗ₜ b m n := by
  simp [baseChange₂, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    LinearMap.baseChangeHom, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']

end Algebra

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  {M N P : PMod O₁}

/-- The sections of a bilinear map of presheaves of modules over an object of the site, as a
bilinear map of modules over the ring of sections there. -/
public def bilAt (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    M.obj X →ₗ[O₁.obj X] N.obj X →ₗ[O₁.obj X] P.obj X :=
  LinearMap.mk₂ (O₁.obj X) (fun x y => β.app X x y)
    (fun x x' y => β.map_add_left X x x' y)
    (fun r x y => β.map_smul_left X r x y)
    (fun x y y' => map_add (β.app X x) y y')
    (fun r x y => β.map_smul_right X r x y)

/-- The base change of a bilinear map of presheaves of modules over an object of the site, as a
bilinear map over the ring of sections of `O₂` there. -/
public noncomputable def cofLin (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    (cofObj θ M X) →ₗ[O₂.obj X] (cofObj θ N X) →ₗ[O₂.obj X] (cofObj θ P X) := by
  letI := (θ.app X).hom.toAlgebra
  exact baseChange₂ (S := O₂.obj X) (bilAt β X)

/-- The base change of a bilinear map of presheaves of modules over an object of the site, as a
biadditive map on sections. -/
public noncomputable def cofApp (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    cofObj θ M X →+ cofObj θ N X →+ cofObj θ P X :=
  AddMonoidHom.mk' (fun x => (cofLin θ β X x).toAddMonoidHom)
    (fun x x' => by ext y; exact congrArg (fun m => m y) (map_add (cofLin θ β X) x x'))

/-- The base-changed bilinear map on pure tensors. -/
public lemma cofApp_tmul (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    ∀ (a c : O₂.obj X) (m : M.obj X) (n : N.obj X),
      cofApp θ β X (a ⊗ₜ[O₁.obj X] m) (c ⊗ₜ[O₁.obj X] n)
        = (a * c) ⊗ₜ[O₁.obj X] (β.app X m n) := by
  let := (θ.app X).hom.toAlgebra
  intro a c m n
  exact baseChange₂_tmul (S := O₂.obj X) (bilAt β X) a c m n

/-- The base-changed bilinear map is linear in its first variable. -/
public lemma cofApp_smul_left (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    ∀ (r : O₂.obj X) (x : cofObj θ M X) (y : cofObj θ N X),
      cofApp θ β X (r • x) y = r • (cofApp θ β X x y) := by
  let := (θ.app X).hom.toAlgebra
  intro r x y
  exact (LinearMap.congr_fun (map_smul (cofLin θ β X) r x) y).trans
    (LinearMap.smul_apply _ _ _)

/-- The base-changed bilinear map is linear in its second variable. -/
public lemma cofApp_smul_right (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    ∀ (r : O₂.obj X) (x : cofObj θ M X) (y : cofObj θ N X),
      cofApp θ β X x (r • y) = r • (cofApp θ β X x y) := by
  let := (θ.app X).hom.toAlgebra
  intro r x y
  exact map_smul (cofLin θ β X x) r y

/-- The base-changed bilinear map vanishes on a zero first argument. -/
public lemma cofApp_zero_left (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) (y : cofObj θ N X) :
    cofApp θ β X 0 y = 0 :=
  (DFunLike.congr_fun (map_zero (cofApp θ β X)) y).trans (AddMonoidHom.zero_apply _)

/-- The base-changed bilinear map is additive in its first variable. -/
public lemma cofApp_add_left (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ)
    (x x' : cofObj θ M X) (y : cofObj θ N X) :
    cofApp θ β X (x + x') y = cofApp θ β X x y + cofApp θ β X x' y :=
  DFunLike.congr_fun (map_add (cofApp θ β X) x x') y

/-- The base-changed bilinear map vanishes on a zero second argument. -/
public lemma cofApp_zero_right (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) (x : cofObj θ M X) :
    cofApp θ β X x 0 = 0 :=
  map_zero (cofApp θ β X x)

/-- The base-changed bilinear map is additive in its second variable. -/
public lemma cofApp_add_right (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ)
    (x : cofObj θ M X) (y y' : cofObj θ N X) :
    cofApp θ β X x (y + y') = cofApp θ β X x y + cofApp θ β X x y' :=
  map_add (cofApp θ β X x) y y'

/-- The restriction maps of a change-of-rings presheaf preserve zero, in the spelling in which
the sections are those of `Stacks.PresheafOfModules.ChangeOfRings.cofObj`. -/
public lemma cofMap_zero (G : PMod O₁) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (cofMap θ G f).hom (0 : cofObj θ G X) = (0 : cofObj θ G Y) := map_zero _

/-- The restriction maps of a change-of-rings presheaf are additive, in the spelling in which
the sections are those of `Stacks.PresheafOfModules.ChangeOfRings.cofObj`. -/
public lemma cofMap_add (G : PMod O₁) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x x' : cofObj θ G X) :
    (cofMap θ G f).hom (x + x') =
      ((cofMap θ G f).hom x + (cofMap θ G f).hom x' : cofObj θ G Y) := map_add _ _ _

/-- An additive map applied to a biadditive map on two base-changed modules agrees with another
biadditive map after additive maps on the arguments, once it does so on pure tensors. -/
private theorem map_tensor_biadd {R S M N A' B' Q Q' U V W : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup Q] [AddCommGroup Q']
    [FunLike U (S ⊗[R] M) A'] [AddMonoidHomClass U (S ⊗[R] M) A']
    [FunLike V (S ⊗[R] N) B'] [AddMonoidHomClass V (S ⊗[R] N) B']
    [FunLike W Q Q'] [AddMonoidHomClass W Q Q']
    (u : U) (v : V) (w : W) (f : S ⊗[R] M →+ S ⊗[R] N →+ Q) (g : A' →+ B' →+ Q')
    (h : ∀ (a c : S) (m : M) (n : N),
      w (f (a ⊗ₜ m) (c ⊗ₜ n)) = g (u (a ⊗ₜ m)) (v (c ⊗ₜ n)))
    (x : S ⊗[R] M) (y : S ⊗[R] N) : w (f x y) = g (u x) (v y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
    | tmul c n => exact h a c m n

/-- The base-changed bilinear map commutes with the restriction maps. -/
public lemma cofApp_naturality (β : Stacks.BilinearMap M N P) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : cofObj θ M X) (y : cofObj θ N X) :
    (cofMap θ P f).hom (cofApp θ β X x y) =
      cofApp θ β Y ((cofMap θ M f).hom x) ((cofMap θ N f).hom y) := by
  let := (θ.app X).hom.toAlgebra
  let := (θ.app Y).hom.toAlgebra
  refine map_tensor_biadd (cofMap θ M f).hom (cofMap θ N f).hom (cofMap θ P f).hom
    (cofApp θ β X) (cofApp θ β Y) ?_ x y
  intro a c m n
  erw [cofApp_tmul θ β X a c m n, cofMap_tmul, cofMap_tmul, cofMap_tmul, map_mul, β.naturality]
  exact (cofApp_tmul θ β Y _ _ _ _).symm

/-- Base change of a bilinear map of presheaves of modules: an `O₁`-bilinear map
`M × N ⟶ P` induces an `O₂`-bilinear map between the change-of-rings presheaves, given on
pure tensors by `(a ⊗ m, c ⊗ n) ↦ ac ⊗ β(m, n)`. -/
public noncomputable def cofBil (β : Stacks.BilinearMap M N P) :
    Stacks.BilinearMap ((changeOfRings θ).obj M) ((changeOfRings θ).obj N)
      ((changeOfRings θ).obj P) where
  app X := cofApp θ β X
  map_smul_left X r x y := cofApp_smul_left θ β X r x y
  map_smul_right X r x y := cofApp_smul_right θ β X r x y
  naturality f x y := cofApp_naturality θ β f x y

section Map

variable {M' N' P' : PMod O₁}

/-- Base change is natural in the bilinear map: if three morphisms of presheaves of modules
carry one bilinear map to another, their base changes carry the base-changed bilinear map to the
base-changed one. -/
public lemma cofApp_map (β : Stacks.BilinearMap M N P) (β' : Stacks.BilinearMap M' N' P')
    (u : M ⟶ M') (v : N ⟶ N') (w : P ⟶ P')
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X),
      (w.app X).hom (β.app X x y) = β'.app X ((u.app X).hom x) ((v.app X).hom y))
    (X : Cᵒᵖ) (x : cofObj θ M X) (y : cofObj θ N X) :
    (cofHomApp θ w X).hom (cofApp θ β X x y) =
      cofApp θ β' X ((cofHomApp θ u X).hom x) ((cofHomApp θ v X).hom y) := by
  let := (θ.app X).hom.toAlgebra
  refine map_tensor_biadd (cofHomApp θ u X).hom (cofHomApp θ v X).hom (cofHomApp θ w X).hom
    (cofApp θ β X) (cofApp θ β' X) ?_ x y
  intro a c m n
  erw [cofApp_tmul θ β X a c m n, cofHomApp_tmul, cofHomApp_tmul, cofHomApp_tmul, h]
  exact (cofApp_tmul θ β' X a c _ _).symm

end Map

/-- The base-changed multiplication of `cofBil` on pure tensors. -/
public lemma cofBil_app_tmul (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    ∀ (a c : O₂.obj X) (m : M.obj X) (n : N.obj X),
      (cofBil θ β).app X (a ⊗ₜ[O₁.obj X] m) (c ⊗ₜ[O₁.obj X] n)
        = (a * c) ⊗ₜ[O₁.obj X] (β.app X m n) :=
  cofApp_tmul θ β X

end Stacks.Sheaves.BilinearChangeOfRings
