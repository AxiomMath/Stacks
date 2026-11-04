module

public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The algebra obtained by applying a tensor functor to a commutative algebra object

Let `F : Q ⥤ ModuleCat R` be a lax braided monoidal functor out of a braided monoidal category and
let `G` be a commutative monoid object of `Q`.  Then `F G` is a commutative monoid object of
`ModuleCat R`, that is a commutative `R`-algebra, with multiplication `F(μ) ∘ μ_F`.  This is the
first assertion of Stacks 0GRK, in the abstract.

If `κ : G ⟶ G` commutes with the multiplication of `G` — `(κ ⊗ 1) ≫ μ = μ ≫ κ`, the diagram of the
proof of Stacks 0GRK — then `F κ` is multiplication by the element `F κ (1)` of `F G`.

## Main definitions

* `CategoryTheory.Functor.tensorFunctorCommRing`: the commutative ring structure on `F G`, and
  `CategoryTheory.Functor.tensorFunctorAlgebraStr` the `R`-algebra structure.

## Main results

* `CategoryTheory.Functor.tensorFunctor_map_mul`: `F κ (x * y) = F κ x * y`.
* `CategoryTheory.Functor.tensorFunctor_map_eq_mul`: `F κ c = F κ 1 * c`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj

universe v u

namespace CategoryTheory.Functor

open ModuleCat.MonModuleEquivalenceAlgebra

variable {Q : Type*} [Category* Q] [MonoidalCategory Q] {R : Type u} [CommRing R]
  (F : Q ⥤ ModuleCat.{u} R) (G : Q) [MonObj G]

section LaxMonoidal

variable [F.LaxMonoidal]

/-- The ring structure on `F G`: multiplication `F(μ) ∘ μ_F`. -/
@[instance_reducible]
noncomputable def tensorFunctorRing : Ring (F.obj G) :=
  letI := Functor.monObjObj (F := F) (X := G)
  MonObj.toRing (F.obj G)

/-- The `R`-algebra structure on `F G`. -/
@[instance_reducible]
noncomputable def tensorFunctorAlgebraStr :
    letI := tensorFunctorRing F G
    Algebra R (F.obj G) :=
  letI := Functor.monObjObj (F := F) (X := G)
  Algebra_of_Mon_ (F.obj G)

/-- The product of `x y : F G` is `F(μ) (μ_F (x ⊗ y))`. -/
lemma tensorFunctor_mul_def (x y : F.obj G) :
    letI := tensorFunctorRing F G
    x * y = (F.map μ[G]).hom ((LaxMonoidal.μ F G G).hom (x ⊗ₜ y)) := rfl

/-- The unit of `F G` is `F(η) (ε_F 1)`. -/
lemma tensorFunctor_one_def :
    letI := tensorFunctorRing F G
    (1 : F.obj G) = (F.map η[G]).hom ((LaxMonoidal.ε F).hom (1 : R)) := rfl

/-- **An endomorphism commuting with the multiplication is linear over `F G`**: if
`(κ ⊗ 1) ≫ μ = μ ≫ κ` then `F κ (x * y) = F κ x * y`. -/
theorem tensorFunctor_map_mul (κ : G ⟶ G) (hκ : κ ▷ G ≫ μ[G] = μ[G] ≫ κ) (x y : F.obj G) :
    letI := tensorFunctorRing F G
    (F.map κ).hom (x * y) = (F.map κ).hom x * y := by
  let := tensorFunctorRing F G
  rw [tensorFunctor_mul_def, tensorFunctor_mul_def]
  have h1 := congrArg (fun φ => (F.map φ).hom ((LaxMonoidal.μ F G G).hom (x ⊗ₜ y))) hκ
  have h2 := congrArg (fun φ => φ.hom (x ⊗ₜ y)) (LaxMonoidal.μ_natural_left F κ G)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]
  rfl

/-- **An endomorphism commuting with the multiplication is multiplication by an element**:
`F κ c = F κ 1 * c`. -/
theorem tensorFunctor_map_eq_mul (κ : G ⟶ G) (hκ : κ ▷ G ≫ μ[G] = μ[G] ≫ κ) (c : F.obj G) :
    letI := tensorFunctorRing F G
    (F.map κ).hom c = (F.map κ).hom 1 * c := by
  let := tensorFunctorRing F G
  rw [← tensorFunctor_map_mul F G κ hκ, _root_.one_mul]

end LaxMonoidal

section LaxBraided

variable [BraidedCategory Q] [IsCommMonObj G] [F.LaxBraided]

/-- The multiplication of `F G` is commutative when `F` is lax braided and `G` is commutative. -/
lemma tensorFunctor_mul_comm (x y : F.obj G) :
    letI := tensorFunctorRing F G
    x * y = y * x := by
  have hb := congrArg (fun φ : F.obj G ⊗ F.obj G ⟶ F.obj (G ⊗ G) => φ.hom (x ⊗ₜ y))
    (LaxBraided.braided (F := F) G G)
  have hc := congrArg (fun φ => (F.map φ).hom ((LaxMonoidal.μ F G G).hom (x ⊗ₜ y)))
    (IsCommMonObj.mul_comm G)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.map_comp,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at hb hc
  exact hc.symm.trans (congrArg (F.map μ[G]).hom hb)

/-- **`F G` is a commutative ring** when `F` is lax braided and `G` is commutative. -/
@[instance_reducible]
noncomputable def tensorFunctorCommRing : CommRing (F.obj G) :=
  { tensorFunctorRing F G with mul_comm := tensorFunctor_mul_comm F G }

end LaxBraided

end CategoryTheory.Functor
