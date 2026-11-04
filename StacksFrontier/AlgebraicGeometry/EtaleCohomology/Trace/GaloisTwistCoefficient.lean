module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingCoinduction
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The coefficient functor `Hom_A(D, -)` with coefficients acting through `D`

Let `A` be a ring, `Λ` a commutative ring and `D` an `A`-module carrying a commuting action of
`Λ`.  Consider the functor `Ψ_D : N ↦ Hom_A(D, N)`, from `A`-modules to `Λ`-modules, with `Λ`
acting through `D`.

This file defines `Ψ_D`, shows that it preserves limits (it is representable after forgetting the
`Λ`-action), and identifies its composite with coinduction along `k₀ → k₀[G]`: for `A = k₀[G]`,
`Hom_{k₀[G]}(D, Hom_{k₀}(k₀[G], M)) = Hom_{k₀}(D, M)`.

## Main definitions

* `Stacks.EtaleCohomology.SourceHom`: `Hom_A(D, N)` with `Λ` acting through `D`.
* `Stacks.EtaleCohomology.sourceHomFunctor`: the functor `Ψ_D`.
* `Stacks.EtaleCohomology.sourceHomCoinductionIso`: `Ψ_D ∘ coinduction ≅ Ψ_D` over `k₀`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v

namespace Stacks.EtaleCohomology

section SourceHom

variable {A : Type} [Ring A] (Λ : Type) [CommRing Λ]
  (D : Type v) [AddCommGroup D] [Module A D] [Module Λ D] [SMulCommClass Λ A D]

/-- `Hom_A(D, N)`, on which `Λ` will act through `D`. -/
structure SourceHom (A : Type) [Ring A] (Λ : Type) (D : Type v) [AddCommGroup D] [Module A D]
    (N : Type v) [AddCommGroup N] [Module A N] : Type v where
  /-- The underlying `A`-linear map. -/
  toLinearMap : D →ₗ[A] N

variable {Λ D} {N : Type v} [AddCommGroup N] [Module A N]

/-- An `A`-linear map, as an element of `SourceHom`. -/
abbrev SourceHom.ofLinearMap (φ : D →ₗ[A] N) : SourceHom A Λ D N := ⟨φ⟩

/-- `SourceHom` is `Hom_A(D, N)`. -/
def SourceHom.equiv : SourceHom A Λ D N ≃ (D →ₗ[A] N) where
  toFun φ := φ.toLinearMap
  invFun φ := ⟨φ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive group structure on `SourceHom A Λ D N` transported from `D →ₗ[A] N`. -/
instance : AddCommGroup (SourceHom A Λ D N) := SourceHom.equiv.addCommGroup

omit [CommRing Λ] [Module Λ D] [SMulCommClass Λ A D] in
/-- The underlying linear map of `SourceHom.ofLinearMap φ` is `φ`. -/
@[simp] lemma SourceHom.toLinearMap_ofLinearMap (φ : D →ₗ[A] N) :
    (SourceHom.ofLinearMap (Λ := Λ) φ).toLinearMap = φ := rfl

omit [CommRing Λ] [Module Λ D] [SMulCommClass Λ A D] in
/-- An element of `SourceHom` is `SourceHom.ofLinearMap` of its underlying linear map. -/
@[simp] lemma SourceHom.ofLinearMap_toLinearMap (φ : SourceHom A Λ D N) :
    SourceHom.ofLinearMap φ.toLinearMap = φ := rfl

omit [CommRing Λ] [Module Λ D] [SMulCommClass Λ A D] in
/-- The underlying linear map of a sum is the sum of the underlying linear maps. -/
@[simp] lemma SourceHom.toLinearMap_add (φ ψ : SourceHom A Λ D N) :
    (φ + ψ).toLinearMap = φ.toLinearMap + ψ.toLinearMap := rfl

omit [CommRing Λ] [Module Λ D] [SMulCommClass Λ A D] in
/-- The underlying linear map of `0 : SourceHom A Λ D N` is `0`. -/
@[simp] lemma SourceHom.toLinearMap_zero :
    (0 : SourceHom A Λ D N).toLinearMap = 0 := rfl

omit [CommRing Λ] [Module Λ D] [SMulCommClass Λ A D] in
/-- Two elements of `SourceHom` are equal if their underlying linear maps agree pointwise. -/
@[ext] lemma SourceHom.ext {φ ψ : SourceHom A Λ D N} (h : ∀ d, φ.toLinearMap d = ψ.toLinearMap d) :
    φ = ψ := by
  cases φ; cases ψ
  exact congrArg _ (LinearMap.ext h)

variable (A) in
/-- Multiplication by `c ∈ Λ` on `D`, an `A`-linear map. -/
def smulLinearMap (c : Λ) : D →ₗ[A] D where
  toFun d := c • d
  map_add' := smul_add c
  map_smul' a d := smul_comm c a d

/-- `Λ` acts on `Hom_A(D, N)` through `D`: `(c • φ)(d) = φ(c • d)`. -/
instance : SMul Λ (SourceHom A Λ D N) where
  smul c φ := SourceHom.ofLinearMap (φ.toLinearMap ∘ₗ smulLinearMap A c)

/-- `(c • φ)(d) = φ(c • d)`. -/
@[simp] lemma SourceHom.smul_apply (c : Λ) (φ : SourceHom A Λ D N) (d : D) :
    (c • φ).toLinearMap d = φ.toLinearMap (c • d) := rfl

/-- `Hom_A(D, N)` is a `Λ`-module, with `Λ` acting through `D`. -/
instance : Module Λ (SourceHom A Λ D N) where
  one_smul φ := SourceHom.ext fun d => by simp
  mul_smul c c' φ := SourceHom.ext fun d => by simp [mul_comm c c', mul_smul]
  smul_zero c := SourceHom.ext fun d => by simp
  smul_add c φ ψ := SourceHom.ext fun d => by simp
  add_smul c c' φ := SourceHom.ext fun d => by simp [add_smul]
  zero_smul φ := SourceHom.ext fun d => by simp

variable (A Λ D)

/-- **The coefficient functor `Ψ_D : N ↦ Hom_A(D, N)`**, with `Λ` acting through `D`. -/
def sourceHomFunctor : ModuleCat.{v} A ⥤ ModuleCat.{v} Λ where
  obj N := ModuleCat.of Λ (SourceHom A Λ D N)
  map {N N'} f := ModuleCat.ofHom
    { toFun := fun φ => SourceHom.ofLinearMap (f.hom ∘ₗ φ.toLinearMap)
      map_add' := fun φ ψ => SourceHom.ext fun d => by simp
      map_smul' := fun c φ => SourceHom.ext fun d => by simp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Ψ_D(f)` is postcomposition with `f`: `Ψ_D(f)(φ)(d) = f(φ(d))`. -/
lemma sourceHomFunctor_map_apply {N N' : ModuleCat.{v} A} (f : N ⟶ N')
    (φ : (sourceHomFunctor A Λ D).obj N) (d : D) :
    (((sourceHomFunctor A Λ D).map f).hom φ).toLinearMap d = f.hom (φ.toLinearMap d) := rfl

/-- The functor `Ψ_D` is additive. -/
instance sourceHomFunctor_additive : (sourceHomFunctor A Λ D).Additive where
  map_add := rfl

/-- After forgetting the `Λ`-action, `Ψ_D` is corepresented by `D`. -/
def sourceHomFunctorForgetIso :
    sourceHomFunctor A Λ D ⋙ forget (ModuleCat.{v} Λ) ≅
      coyoneda.obj (op (ModuleCat.of A D)) :=
  NatIso.ofComponents
    (fun N => Equiv.toIso
      { toFun := fun φ => (ModuleCat.ofHom (SourceHom.toLinearMap φ) : ModuleCat.of A D ⟶ N)
        invFun := fun f => SourceHom.ofLinearMap f.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- **`Ψ_D` preserves limits**: a limit cone is reflected by the forgetful functor, after which
`Ψ_D` is corepresentable. -/
instance sourceHomFunctor_preservesLimitsOfSize [UnivLE.{w, v}] :
    PreservesLimitsOfSize.{w', w} (sourceHomFunctor A Λ D) where
  preservesLimitsOfShape {_} _ :=
    { preservesLimit := fun {K} =>
        have : PreservesLimit K (sourceHomFunctor A Λ D ⋙ forget (ModuleCat.{v} Λ)) :=
          preservesLimit_of_natIso K (sourceHomFunctorForgetIso A Λ D).symm
        have : ReflectsLimit (K ⋙ sourceHomFunctor A Λ D) (forget (ModuleCat.{v} Λ)) :=
          reflectsLimit_of_reflectsIsomorphisms _ _
        preservesLimit_of_reflects_of_preserves _ (forget (ModuleCat.{v} Λ)) }

end SourceHom

section Functoriality

variable (A : Type) [Ring A] (Λ : Type) [CommRing Λ]
  {D D' : Type v} [AddCommGroup D] [Module A D] [Module Λ D] [SMulCommClass Λ A D]
  [AddCommGroup D'] [Module A D'] [Module Λ D'] [SMulCommClass Λ A D']

/-- **Functoriality of `Ψ_D` in `D`**: precomposition with a map `D' ⟶ D` compatible with both
actions. -/
def sourceHomFunctorMap (u : D' →ₗ[A] D) (hu : ∀ (c : Λ) (d : D'), u (c • d) = c • u d) :
    sourceHomFunctor A Λ D ⟶ sourceHomFunctor A Λ D' where
  app N := ModuleCat.ofHom
    { toFun := fun φ => SourceHom.ofLinearMap (φ.toLinearMap ∘ₗ u)
      map_add' := fun _ _ => rfl
      map_smul' := fun c φ => SourceHom.ext fun d => by
        change φ.toLinearMap (c • u d) = φ.toLinearMap (u (c • d))
        rw [hu] }
  naturality _ _ _ := rfl

/-- The map `Ψ_D(N) → Ψ_{D'}(N)` induced by `u : D' → D` is precomposition with `u`. -/
lemma sourceHomFunctorMap_app_apply (u : D' →ₗ[A] D) (hu : ∀ (c : Λ) (d : D'), u (c • d) = c • u d)
    (N : ModuleCat.{v} A) (φ : (sourceHomFunctor A Λ D).obj N) (d : D') :
    (((sourceHomFunctorMap A Λ u hu).app N).hom φ).toLinearMap d = φ.toLinearMap (u d) := rfl

end Functoriality

/-! ### `Ψ_D` of a coinduced module -/

section Coinduction

variable (k₀ : Type) [CommRing k₀] (G : Type) [Group G] (Λ : Type) [CommRing Λ]
  (D : Type v) [AddCommGroup D] [Module k₀ D] [Module (MonoidAlgebra k₀ G) D]
  [IsScalarTower k₀ (MonoidAlgebra k₀ G) D] [Module Λ D] [SMulCommClass Λ k₀ D]
  [SMulCommClass Λ (MonoidAlgebra k₀ G) D]

variable {k₀ G Λ D} in
/-- In an `A`-module with compatible `k₀`-structure, `single 1 c` acts as `c`. -/
lemma single_one_smul_eq (c : k₀) (d : D) :
    (MonoidAlgebra.single (1 : G) c : MonoidAlgebra k₀ G) • d = c • d := by
  rw [show (MonoidAlgebra.single (1 : G) c : MonoidAlgebra k₀ G) =
    c • (1 : MonoidAlgebra k₀ G) by
      rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
    smul_assoc, one_smul]

variable [Fintype G]

/-- **`Hom_{k₀[G]}(D, Hom_{k₀}(k₀[G], M)) = Hom_{k₀}(D, M)`**: an element `φ` goes to
`d ↦ φ(d)(1)`, and `ψ` comes from `d ↦ (a ↦ ψ(a • d))`. -/
def sourceHomCoinductionLinearEquiv (M : ModuleCat.{v} k₀) :
    SourceHom (MonoidAlgebra k₀ G) Λ D ((groupRingCoinduction k₀ G).obj M) ≃ₗ[Λ]
      SourceHom k₀ Λ D M where
  toFun φ := SourceHom.ofLinearMap
    { toFun := fun d => coindEval (φ.toLinearMap d) 1
      map_add' := fun d d' => by rw [map_add, coindEval_add_left]
      map_smul' := fun c d => by
        rw [RingHom.id_apply, ← single_one_smul_eq (G := G), map_smul, coindEval_smul, one_mul,
          ← mul_one (MonoidAlgebra.single (1 : G) c), coindEval_single_one_mul] }
  invFun ψ := SourceHom.ofLinearMap
    { toFun := fun d => (ModuleCat.CoextendScalars.equiv _ M).symm
        { toFun := fun a => ψ.toLinearMap (ofGroupRingRes a • d)
          map_add' := fun a b => by
            rw [ofGroupRingRes_add, add_smul, map_add]
          map_smul' := fun c a => by
            rw [ofGroupRingRes_smul, mul_smul, single_one_smul_eq, map_smul, RingHom.id_apply] }
      map_add' := fun d d' => coind_ext fun a => by
        change ψ.toLinearMap (a • (d + d')) = ψ.toLinearMap (a • d) + ψ.toLinearMap (a • d')
        rw [smul_add, map_add]
      map_smul' := fun s d => coind_ext fun a => by
        change ψ.toLinearMap (a • s • d) = ψ.toLinearMap ((a * s) • d)
        rw [mul_smul] }
  map_add' φ φ' := SourceHom.ext fun d => rfl
  map_smul' c φ := SourceHom.ext fun d => rfl
  left_inv φ := SourceHom.ext fun d => coind_ext fun a => by
    change coindEval (φ.toLinearMap (a • d)) 1 = coindEval (φ.toLinearMap d) a
    rw [map_smul, coindEval_smul, one_mul]
  right_inv ψ := SourceHom.ext fun d => by
    change ψ.toLinearMap ((1 : MonoidAlgebra k₀ G) • d) = ψ.toLinearMap d
    rw [one_smul]

/-- **`Ψ_D` of a coinduced module is `Ψ_D` over `k₀`**, naturally. -/
def sourceHomCoinductionIso :
    groupRingCoinduction.{v} k₀ G ⋙ sourceHomFunctor (MonoidAlgebra k₀ G) Λ D ≅
      sourceHomFunctor k₀ Λ D :=
  NatIso.ofComponents
    (fun M => (sourceHomCoinductionLinearEquiv k₀ G Λ D M).toModuleIso)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => SourceHom.ext fun _ => rfl))

end Coinduction

end Stacks.EtaleCohomology

end
