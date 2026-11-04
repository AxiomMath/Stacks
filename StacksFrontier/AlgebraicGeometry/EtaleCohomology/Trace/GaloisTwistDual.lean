module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientMateComp
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The dual `E^∨` of a representation, as a module over `k₀[G]` and `Λ`

Let `k₀` be a commutative ring, `Λ` a commutative `k₀`-algebra, `G` a group and `E` a `Λ`-module
with a `Λ`-linear action `ρ` of `G`.  The `k₀`-dual `E^∨ = Hom_{k₀}(E, k₀)` is a module over
`k₀[G]` through the contragredient action `(g ξ)(e) = ξ(ρ(g⁻¹) e)`, and over `Λ` through
`(c ξ)(e) = ξ(c e)`; the two actions commute.  The coefficient functor of the twist is
`Ψ = Hom_{k₀[G]}(E^∨, -)`, with `Λ` acting through `E^∨`.

## Main definitions

* `Stacks.EtaleCohomology.TwistDual`: the module `E^∨`.
* `Stacks.EtaleCohomology.twistFunctor`: the coefficient functor `Ψ = Hom_{k₀[G]}(E^∨, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v

namespace Stacks.EtaleCohomology

/-- The `k₀`-dual `E^∨ = Hom_{k₀}(E, k₀)` of a representation `ρ` of `G` on a `Λ`-module `E`. -/
structure TwistDual (k₀ : Type) [CommRing k₀] (G : Type) [Group G] (Λ : Type) [CommRing Λ]
    [Algebra k₀ Λ] (E : Type v) [AddCommGroup E] [Module Λ E] [Module k₀ E]
    [IsScalarTower k₀ Λ E] (ρ : Representation Λ G E) : Type v where
  /-- The underlying linear form. -/
  toDual : E →ₗ[k₀] k₀

namespace TwistDual

variable {k₀ : Type} [CommRing k₀] {G : Type} [Group G] {Λ : Type} [CommRing Λ] [Algebra k₀ Λ]
  {E : Type v} [AddCommGroup E] [Module Λ E] [Module k₀ E] [IsScalarTower k₀ Λ E]
  {ρ : Representation Λ G E}

/-- `E^∨` is `Hom_{k₀}(E, k₀)`. -/
def equiv : TwistDual k₀ G Λ E ρ ≃ (E →ₗ[k₀] k₀) where
  toFun ξ := ξ.toDual
  invFun ξ := ⟨ξ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive group structure on `E^∨` transported from `Hom_{k₀}(E, k₀)`. -/
instance : AddCommGroup (TwistDual k₀ G Λ E ρ) := equiv.addCommGroup

/-- Two elements of `E^∨` are equal if their linear forms agree at every `e : E`. -/
@[ext] lemma ext {ξ η : TwistDual k₀ G Λ E ρ} (h : ∀ e, ξ.toDual e = η.toDual e) : ξ = η := by
  cases ξ; cases η
  exact congrArg _ (LinearMap.ext h)

/-- `k₀` acts on `E^∨` by `(c ξ)(e) = c ξ(e)`. -/
instance : SMul k₀ (TwistDual k₀ G Λ E ρ) where
  smul c ξ := ⟨c • ξ.toDual⟩

/-- `E^∨` is a `k₀`-module. -/
instance : Module k₀ (TwistDual k₀ G Λ E ρ) where
  one_smul ξ := TwistDual.ext fun e => one_smul k₀ (ξ.toDual e)
  mul_smul c c' ξ := TwistDual.ext fun e => mul_smul c c' (ξ.toDual e)
  smul_zero c := TwistDual.ext fun _ => smul_zero c
  smul_add c ξ η := TwistDual.ext fun e => smul_add c (ξ.toDual e) (η.toDual e)
  add_smul c c' ξ := TwistDual.ext fun e => add_smul c c' (ξ.toDual e)
  zero_smul ξ := TwistDual.ext fun e => zero_smul k₀ (ξ.toDual e)

/-- The linear form of `ξ + η` is the sum of the linear forms of `ξ` and `η`. -/
@[simp] lemma add_toDual (ξ η : TwistDual k₀ G Λ E ρ) : (ξ + η).toDual = ξ.toDual + η.toDual :=
  rfl

/-- The linear form of `0 : E^∨` is zero. -/
@[simp] lemma zero_toDual : (0 : TwistDual k₀ G Λ E ρ).toDual = 0 := rfl

/-- The linear form of `c • ξ`, for `c : k₀`, is `c` times the linear form of `ξ`. -/
@[simp] lemma smul_toDual (c : k₀) (ξ : TwistDual k₀ G Λ E ρ) : (c • ξ).toDual = c • ξ.toDual :=
  rfl

/-- The contragredient action of `g`, `ξ ↦ ξ ∘ ρ(g⁻¹)`. -/
def act (g : G) : TwistDual k₀ G Λ E ρ →ₗ[k₀] TwistDual k₀ G Λ E ρ where
  toFun ξ := ⟨ξ.toDual ∘ₗ (ρ g⁻¹).restrictScalars k₀⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `(g ξ)(e) = ξ(ρ(g⁻¹) e)`. -/
@[simp] lemma act_toDual (g : G) (ξ : TwistDual k₀ G Λ E ρ) (e : E) :
    (act g ξ).toDual e = ξ.toDual (ρ g⁻¹ e) := rfl

/-- The contragredient representation of `G` on `E^∨`. -/
def actHom : G →* Module.End k₀ (TwistDual k₀ G Λ E ρ) where
  toFun := act
  map_one' := LinearMap.ext fun ξ => TwistDual.ext fun e => by simp
  map_mul' g h := LinearMap.ext fun ξ => TwistDual.ext fun e => by
    simp [mul_inv_rev, Module.End.mul_apply]

/-- `E^∨` is a `k₀[G]`-module through the contragredient action `actHom`. -/
instance : Module (MonoidAlgebra k₀ G) (TwistDual k₀ G Λ E ρ) :=
  Module.compHom _ (MonoidAlgebra.lift k₀ (Module.End k₀ (TwistDual k₀ G Λ E ρ)) G
    actHom).toRingHom

/-- An element `a : k₀[G]` acts on `E^∨` as the image of `a` under the algebra map
`k₀[G] → End_{k₀}(E^∨)` induced by `actHom`. -/
lemma monoidAlgebra_smul_def (a : MonoidAlgebra k₀ G) (ξ : TwistDual k₀ G Λ E ρ) :
    a • ξ = MonoidAlgebra.lift k₀ (Module.End k₀ (TwistDual k₀ G Λ E ρ)) G actHom a ξ := rfl

/-- The element `c g` of `k₀[G]` acts on `E^∨` as `c • act g`. -/
lemma single_smul (g : G) (c : k₀) (ξ : TwistDual k₀ G Λ E ρ) :
    (MonoidAlgebra.single g c : MonoidAlgebra k₀ G) • ξ = c • act g ξ := by
  rw [monoidAlgebra_smul_def, MonoidAlgebra.lift_single]
  rfl

/-- The `k₀`-action and the `k₀[G]`-action on `E^∨` are compatible. -/
instance : IsScalarTower k₀ (MonoidAlgebra k₀ G) (TwistDual k₀ G Λ E ρ) where
  smul_assoc c a ξ := by
    rw [monoidAlgebra_smul_def, monoidAlgebra_smul_def, map_smul]
    rfl

/-- `Λ` acts on `E^∨` through `E`: `(c ξ)(e) = ξ(c e)`. -/
instance : SMul Λ (TwistDual k₀ G Λ E ρ) where
  smul c ξ := ⟨ξ.toDual ∘ₗ (LinearMap.lsmul Λ E c).restrictScalars k₀⟩

/-- `(c ξ)(e) = ξ(c e)` for `c : Λ`. -/
@[simp] lemma lsmul_toDual (c : Λ) (ξ : TwistDual k₀ G Λ E ρ) (e : E) :
    (c • ξ).toDual e = ξ.toDual (c • e) := rfl

/-- `E^∨` is a `Λ`-module. -/
instance : Module Λ (TwistDual k₀ G Λ E ρ) where
  one_smul ξ := TwistDual.ext fun e => by simp
  mul_smul c c' ξ := TwistDual.ext fun e => by simp [mul_comm c c', mul_smul]
  smul_zero c := TwistDual.ext fun e => by simp
  smul_add c ξ η := TwistDual.ext fun e => by simp
  add_smul c c' ξ := TwistDual.ext fun e => by simp [add_smul]
  zero_smul ξ := TwistDual.ext fun e => by simp

/-- The `k₀`-action and the `Λ`-action on `E^∨` are compatible. -/
instance : IsScalarTower k₀ Λ (TwistDual k₀ G Λ E ρ) where
  smul_assoc c c' ξ := TwistDual.ext fun e => by
    simp only [lsmul_toDual, smul_toDual, LinearMap.smul_apply]
    rw [smul_assoc, _root_.map_smul]

/-- The contragredient action of `g` commutes with the action of `c : Λ`. -/
lemma act_lsmul (g : G) (c : Λ) (ξ : TwistDual k₀ G Λ E ρ) : act g (c • ξ) = c • act g ξ :=
  TwistDual.ext fun e => by simp [_root_.map_smul]

/-- The actions of `Λ` and `k₀[G]` on `E^∨` commute. -/
instance : SMulCommClass Λ (MonoidAlgebra k₀ G) (TwistDual k₀ G Λ E ρ) where
  smul_comm c a ξ := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, add_smul, smul_add, ha, hb]
    | single g c' =>
      rw [single_smul, single_smul, act_lsmul, smul_comm]

end TwistDual

/-- **The coefficient functor of the twist**, `Ψ = Hom_{k₀[G]}(E^∨, -)`, from `k₀[G]`-modules to
`Λ`-modules. -/
abbrev twistFunctor (k₀ : Type) [CommRing k₀] (G : Type) [Group G] (Λ : Type) [CommRing Λ]
    [Algebra k₀ Λ] (E : Type v) [AddCommGroup E] [Module Λ E] [Module k₀ E]
    [IsScalarTower k₀ Λ E] (ρ : Representation Λ G E) :
    ModuleCat.{v} (MonoidAlgebra k₀ G) ⥤ ModuleCat.{v} Λ :=
  sourceHomFunctor (MonoidAlgebra k₀ G) Λ (TwistDual k₀ G Λ E ρ)

end Stacks.EtaleCohomology

end
