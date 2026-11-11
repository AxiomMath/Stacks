module

public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorCohomology

/-!
# Monoidal natural transformations into graded vector spaces, on elements

Let `θ : G ⟶ G'` be a monoidal natural transformation between lax monoidal functors
`D ⥤ GradedObject ℤ (ModuleCat F)`. On elements, `θ` commutes with the products
`G(X)ⁱ × G(Y)ʲ → G(X ⊗ Y)ᵏ` given by the tensorators (`Functor.gradedMul`) and sends the unit of
`G` to the unit of `G'`; for monoidal functors it also commutes with the counits `G(𝟙)⁰ → F`, the
products of monoid objects and the traces `x ↦ t(x ⊗ e)` of `Functor.gradedTrace`, provided the
element `e` is replaced by its image under `θ`.

## Main results

* `CategoryTheory.NatTrans.app_gradedMul`, `CategoryTheory.NatTrans.app_gradedOne`.
* `CategoryTheory.NatTrans.gradedCounit_app`, `CategoryTheory.NatTrans.app_gradedMonMul`,
  `CategoryTheory.NatTrans.gradedTrace_app`.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open MonoidalCategory GradedObject GradedObject.Monoidal CategoryTheory.Functor
open scoped TensorProduct

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  {G G' : D ⥤ GradedObject ℤ (ModuleCat.{w} F)}

/-- Naturality on elements: `θ(G(f)(x)) = G'(f)(θ(x))`. -/
theorem app_map_apply (θ : G ⟶ G') {X Y : D} (f : X ⟶ Y) (k : ℤ) (x : G.obj X k) :
    θ.app Y k (G.map f k x) = G'.map f k (θ.app X k x) := by
  have h := congr($(θ.naturality f) k)
  simp only [categoryOfGradedObjects_comp] at h
  exact ConcreteCategory.congr_hom h x

section Lax

variable [G.LaxMonoidal] [G'.LaxMonoidal] (θ : G ⟶ G') [θ.IsMonoidal]

/-- A monoidal natural transformation commutes with the products of the tensorators. -/
theorem app_gradedMul (X Y : D) (i j k : ℤ) (h : i + j = k) (x : G.obj X i) (y : G.obj Y j) :
    θ.app (X ⊗ Y) k (G.gradedMul X Y i j k h x y) =
      G'.gradedMul X Y i j k h (θ.app X i x) (θ.app Y j y) := by
  have key : ιTensorObj (G.obj X) (G.obj Y) i j k h ≫ (θ.app X ⊗ₘ θ.app Y) k =
      (θ.app X i ⊗ₘ θ.app Y j) ≫ ιTensorObj (G'.obj X) (G'.obj Y) i j k h :=
    ι_tensorHom _ _ i j k h
  have H := ConcreteCategory.congr_hom
    (ιTensorObj (G.obj X) (G.obj Y) i j k h ≫= congr($(IsMonoidal.tensor (τ := θ) X Y) k))
    (x ⊗ₜ y)
  simp only [categoryOfGradedObjects_comp] at H
  rw [reassoc_of% key] at H
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at H
  exact H

/-- A monoidal natural transformation sends the unit of `G` to the unit of `G'`. -/
theorem app_gradedOne : θ.app (𝟙_ D) 0 (gradedOne G) = gradedOne G' := by
  have h := congr($(IsMonoidal.unit (τ := θ)) 0)
  simp only [categoryOfGradedObjects_comp] at h
  exact ConcreteCategory.congr_hom h _

end Lax

section Monoidal

variable [G.Monoidal] [G'.Monoidal] (θ : G ⟶ G') [θ.IsMonoidal]

/-- A monoidal natural transformation commutes with the inverses `η` of the units. -/
theorem app_unit_comp_η : θ.app (𝟙_ D) ≫ OplaxMonoidal.η G' = OplaxMonoidal.η G := by
  rw [← Category.id_comp (θ.app _), ← Monoidal.η_ε (F := G), Category.assoc, Category.assoc,
    ← Category.assoc (LaxMonoidal.ε G), IsMonoidal.unit, Monoidal.ε_η, Category.comp_id]

/-- A monoidal natural transformation commutes with the counits `G(𝟙)⁰ → F`. -/
theorem gradedCounit_app (x : G.obj (𝟙_ D) 0) :
    G'.gradedCounit (θ.app (𝟙_ D) 0 x) = G.gradedCounit x := by
  have h := congr($(app_unit_comp_η θ) 0)
  simp only [categoryOfGradedObjects_comp] at h
  simp only [gradedCounit, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [← h]
  rfl

/-- A monoidal natural transformation commutes with the products of monoid objects. -/
theorem app_gradedMonMul (M : D) [MonObj M] (p q n : ℤ) (h : p + q = n) (a : G.obj M p)
    (b : G.obj M q) :
    θ.app M n (G.gradedMonMul M p q n h a b) =
      G'.gradedMonMul M p q n h (θ.app M p a) (θ.app M q b) := by
  rw [gradedMonMul_apply, gradedMonMul_apply, app_map_apply, app_gradedMul]

/-- A monoidal natural transformation commutes with the traces `x ↦ t(x ⊗ e)`, the element `e`
being replaced by its image. -/
theorem gradedTrace_app {M T : D} (t : M ⊗ T ⟶ 𝟙_ D) {s : ℤ} (e : G.obj T s) (m : ℤ)
    (h : m + s = 0) (x : G.obj M m) :
    G'.gradedTrace t (θ.app T s e) m h (θ.app M m x) = G.gradedTrace t e m h x := by
  rw [gradedTrace_apply, gradedTrace_apply, ← app_gradedMul, ← app_map_apply, gradedCounit_app]

/-- A monoidal natural transformation sends the unit of the graded algebra `G(M)` of a monoid
object `M` to the unit of `G'(M)`. -/
theorem app_cohomologyAlgebra_one (M : D) [MonObj M] :
    θ.app M 0 (G.cohomologyAlgebra M).one = (G'.cohomologyAlgebra M).one := by
  change θ.app M 0 (G.map MonObj.one 0 (gradedOne G)) = G'.map MonObj.one 0 (gradedOne G')
  rw [app_map_apply, app_gradedOne]

/-- A monoidal natural transformation is multiplicative for the graded algebras of a monoid
object. -/
theorem app_cohomologyAlgebra_mul (M : D) [MonObj M] (i j : ℤ) (a : G.obj M i)
    (b : G.obj M j) :
    θ.app M (i + j) ((G.cohomologyAlgebra M).mul i j a b) =
      (G'.cohomologyAlgebra M).mul i j (θ.app M i a) (θ.app M j b) := by
  rw [Functor.cohomologyAlgebra_mul, Functor.cohomologyAlgebra_mul]
  exact app_gradedMonMul θ M i j (i + j) rfl a b

end Monoidal

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

open MonoidalCategory GradedObject

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  (G : D ⥤ GradedObject ℤ (ModuleCat.{w} F)) [G.Monoidal]

/-- The trace `x ↦ t(x ⊗ e)` is linear in `e`. -/
theorem gradedTrace_smul {M T : D} (t : M ⊗ T ⟶ 𝟙_ D) {s : ℤ} (a : F) (e : G.obj T s) (m : ℤ)
    (h : m + s = 0) (x : G.obj M m) :
    G.gradedTrace t (a • e) m h x = a • G.gradedTrace t e m h x := by
  rw [gradedTrace_apply, gradedTrace_apply, _root_.map_smul, _root_.map_smul, _root_.map_smul]

end CategoryTheory.Functor
