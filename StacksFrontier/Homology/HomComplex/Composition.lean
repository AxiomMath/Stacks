module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import StacksFrontier.Homology.HomComplex.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition morphism for Hom complexes

Let `R` be a commutative ring and let `K`, `L`, `M` be cochain complexes of `R`-modules. There is a
canonical morphism of complexes
$$c : \operatorname{Tot}(\operatorname{Hom}^\bullet(L, M)
  \otimes_R \operatorname{Hom}^\bullet(K, L)) \to \operatorname{Hom}^\bullet(K, M)$$
sending a pure tensor `β ⊗ₜ γ` with `β : Cochain L M p` and `γ : Cochain K L q` to the composite
cochain `γ.comp β = β ∘ γ` of degree `p + q`. The compatibility with differentials is the Leibniz
rule `CochainComplex.HomComplex.δ_comp`.

## Main definitions

* `cochainCompMap`: the `R`-linear map `Cochain L M p ⊗[R] Cochain K L q → Cochain K M n` for
  `p + q = n`, sending `β ⊗ₜ γ` to `γ.comp β`.
* `compFun`: the degree-`n` component of the composition morphism.
* `compMor`: the composition morphism of complexes
  `tensorObj (HomComplexR R L M) (HomComplexR R K L) ⟶ HomComplexR R K M`.

## Main results

* `compFun_comm`: the components `compFun` commute with the differentials.
* `compMor_tmul`: on the `(p, q)`-summand, `compMor` sends `β ⊗ₜ γ` to `γ.comp β`.
* `composition_morphism_exists`: existence of a morphism of complexes with this action on pure
  tensors.

## Implementation notes

The total complex of the tensor product is the monoidal product `HomologicalComplex.tensorObj`,
and the Hom complex is `CochainComplex.HomComplexR`. Composition of cochains carries no sign;
the sign `(-1)^p` appears only in the differential of the tensor product.

## References

* [Stacks, Tag 0A8I](https://stacks.math.columbia.edu/tag/0A8I)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CochainComplex CochainComplex.HomComplex MonoidalCategory TensorProduct

variable {R : Type*} [CommRing R]

variable (K L M : CochainComplex (ModuleCat R) ℤ)

/-- For `p + q = n`, the `R`-linear map `Cochain L M p ⊗[R] Cochain K L q → Cochain K M n` sending
the pure tensor `β ⊗ₜ γ` to the composite cochain `γ.comp β`. -/
noncomputable def cochainCompMap (p q n : ℤ) (h : p + q = n) :
    (ModuleCat.of R (Cochain L M p)) ⊗ (ModuleCat.of R (Cochain K L q)) ⟶
      ModuleCat.of R (Cochain K M n) :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun := fun β =>
        { toFun := fun γ => γ.comp β (by rw [add_comm]; exact h)
          map_add' := fun γ γ' => by rw [Cochain.add_comp]
          map_smul' := fun r γ => by rw [Cochain.smul_comp]; rfl }
      map_add' := fun β β' => by ext γ; simp [Cochain.comp_add]
      map_smul' := fun r β => by ext γ; simp [Cochain.comp_smul] })

/-- The degree-`n` component of the composition morphism, induced on the total complex by the maps
`cochainCompMap` on the summands indexed by `(p, q)` with `p + q = n`. -/
noncomputable def compFun (n : ℤ) :
    (HomologicalComplex.tensorObj (HomComplexR R L M) (HomComplexR R K L)).X n
      ⟶ (HomComplexR R K M).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q (hpq : p + q = n) => cochainCompMap K L M p q n hpq)

/-- The components `compFun` commute with the differentials of
`tensorObj (HomComplexR R L M) (HomComplexR R K L)` and `HomComplexR R K M`. -/
@[sga "4 XVII 1.1.10" "(iii), special case"]
theorem compFun_comm (n n' : ℤ) :
    compFun K L M n ≫ (HomComplexR R K M).d n n'
      = (HomologicalComplex.tensorObj (HomComplexR R L M) (HomComplexR R K L)).d n n'
          ≫ compFun K L M n' := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq' : p + q = n := hpq
  by_cases hn : n + 1 = n'
  · subst hn
    unfold compFun
    rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, Preadditive.add_comp, Preadditive.comp_add,
      ← Category.assoc, ← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.up_mk p (p+1) rfl) q (n+1)
        (show p + 1 + q = n + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (ComplexShape.up_mk q (q+1) rfl) (n+1)
        (show p + (q + 1) = n + 1 by omega),
      Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun β γ => ?_)
    have hw₁ : (ModuleCat.Hom.hom (((curriedTensor (ModuleCat R)).map
        ((HomComplexR R L M).d p (p+1))).app
        ((HomComplexR R K L).X q))) (β ⊗ₜ[R] γ) = δ p (p+1) β ⊗ₜ[R] γ := by
      rw [curriedTensor_map_app]
      exact ModuleCat.MonoidalCategory.whiskerRight_apply ((HomComplexR R L M).d p (p+1)) _ β γ
    have hw₂ : (ModuleCat.Hom.hom (((curriedTensor (ModuleCat R)).obj ((HomComplexR R L M).X p)).map
        ((HomComplexR R K L).d q (q+1)))) (β ⊗ₜ[R] γ) = β ⊗ₜ[R] δ q (q+1) γ := by
      rw [curriedTensor_obj_map]
      exact ModuleCat.MonoidalCategory.whiskerLeft_apply _ ((HomComplexR R K L).d q (q+1)) β γ
    simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, one_smul,
      ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply, cochainCompMap, ModuleCat.hom_ofHom]
    exact δ_comp γ β (show q + p = n by omega) (q+1) (p+1) (n+1) (by omega) rfl rfl
  · rw [(HomComplexR R K M).shape n n' hn,
      (HomologicalComplex.tensorObj (HomComplexR R L M) (HomComplexR R K L)).shape n n' hn]
    simp

/-- The composition morphism of complexes
`tensorObj (HomComplexR R L M) (HomComplexR R K L) ⟶ HomComplexR R K M`, with components
`compFun`. -/
@[sga "4 XVII 1.1.10" "(iii), special case"]
noncomputable def compMor :
    HomologicalComplex.tensorObj (HomComplexR R L M) (HomComplexR R K L) ⟶ HomComplexR R K M where
  f n := compFun K L M n
  comm' n n' _ := compFun_comm K L M n n'

/-- On the `(p, q)`-summand, the composition morphism `compMor` sends `β ⊗ₜ γ` to `γ.comp β`. -/
theorem compMor_tmul (p q n : ℤ) (h : p + q = n) (β : Cochain L M p) (γ : Cochain K L q) :
    (HomologicalComplex.ιTensorObj (HomComplexR R L M) (HomComplexR R K L) p q n h
        ≫ (compMor K L M).f n).hom (β ⊗ₜ[R] γ)
      = γ.comp β (by rw [add_comm]; exact h) := by
  change ((HomologicalComplex.ιTensorObj (HomComplexR R L M) (HomComplexR R K L) p q n h
      ≫ compFun K L M n)).hom (β ⊗ₜ[R] γ) = _
  rw [compFun, HomologicalComplex.ι_mapBifunctorDesc]
  rfl

/-- There is a morphism of complexes of `R`-modules
`c : tensorObj (HomComplexR R L M) (HomComplexR R K L) ⟶ HomComplexR R K M` such that for
`β : Cochain L M p` and `γ : Cochain K L q` with `p + q = n`, the `(p, q)`-component of `c` sends
`β ⊗ₜ γ` to the composite cochain `γ.comp β`. -/
@[stacks 0A8I, sga "4 XVII 1.1.10" "(iii), special case"]
theorem composition_morphism_exists :
    ∃ c : HomologicalComplex.tensorObj (HomComplexR R L M) (HomComplexR R K L) ⟶ HomComplexR R K M,
      ∀ (p q n : ℤ) (h : p + q = n) (β : Cochain L M p) (γ : Cochain K L q),
        (HomologicalComplex.ιTensorObj (HomComplexR R L M) (HomComplexR R K L) p q n h ≫ c.f n).hom
            (β ⊗ₜ[R] γ)
          = γ.comp β (by rw [add_comm]; exact h) :=
  ⟨compMor K L M, fun p q n h β γ => compMor_tmul K L M p q n h β γ⟩
