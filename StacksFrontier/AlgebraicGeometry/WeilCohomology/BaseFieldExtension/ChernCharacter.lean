module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Twist
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.BaseChangeData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp

/-!
# The cohomological Chern character along a field extension

Let `Φ` be comparison data of Tag 0FVT between data `𝔇` for `(k, F)` and `𝔇'` for `(k', F')`,
both satisfying (A1)–(A4). The proof of Tag 0FVT shows that `ch^H(β)` maps to `ch^{H'}(β_{k'})`
under the comparison of twists. Both rules `α ↦ ch^{H'}(α_{k'})` and `α ↦ Φ(ch^H(α))` are
cohomological Chern characters, in the sense of Tag 0FIE, of the data `X ↦ (H')^*(X_{k'})` over
`k` (`Stacks.WeilCohomology.FirstChernClassData.baseChangeData`), which satisfies (A1)–(A4); by
the uniqueness in Tag 0FIE they agree. The source reaches the same conclusion through the splitting
principle and the first Chern classes, which is how the uniqueness in Tag 0FIE is proved.

## Main results

* `Stacks.WeilCohomology.FieldExtensionComparison.chernCharacterOf_baseChange`:
  `ch^{H'}(α_{k'}) = Φ(ch^H(α))`.
* `Stacks.WeilCohomology.FieldExtensionComparison.cycleClassMap_baseChange`: the same for the
  cycle class map on `K₀(Vect(X)) ⊗ 𝐐 ≅ CH^*(X) ⊗ 𝐐` of Tag 0FIF.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F' : Type w'} [Field F'] {𝔇' : FirstChernClassData k' F'}

/-- **`α ↦ ch(α_{k'})` is a cohomological Chern character of the base-changed data**, for any
cohomological Chern character `ch` of `𝔇'`. -/
theorem isCohomologicalChernCharacter_baseChangeData
    {ch : ∀ X : (SmoothProjectiveScheme k').FullSubcategory,
      VectorBundleKZero ((toScheme k').obj X) → ∀ n : ℕ, tateTwist F' 𝔇'.tate (𝔇'.H X) n}
    (h : 𝔇'.IsCohomologicalChernCharacter ch) :
    (𝔇'.baseChangeData k).IsCohomologicalChernCharacter fun X α =>
      ch ((baseChange k k').obj X) (VectorBundleKZero.pullbackRingHom (baseChangeProj X) α) := by
  refine ⟨fun X α n => h.1 _ _ n, fun X α β => ?_, fun X α β => ?_, fun X => ?_,
    fun {X Y} f α n => ?_, fun X L hL => ?_⟩
  · dsimp only
    rw [map_add]
    exact h.2.1 _ _ _
  · dsimp only
    rw [map_mul]
    exact h.2.2.1 _ _ _
  · dsimp only
    rw [map_one]
    exact h.2.2.2.1 _
  · dsimp only
    rw [← VectorBundleKZero.pullbackRingHom_comp_apply, ← baseChangeProj_naturality,
      VectorBundleKZero.pullbackRingHom_comp_apply]
    exact h.2.2.2.2.1 _ _ n
  · dsimp only
    rw [VectorBundleKZero.pullbackRingHom_classOf _ L
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L hL),
      h.2.2.2.2.2 _ _ (isInvertible_pullback_obj _ L hL), baseChangeData_c₁_picardClassOf,
      baseChangeData_expTw]

end FirstChernClassData

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- **`α ↦ Φ(ch^H(α))` is a cohomological Chern character of the base-changed data**, for any
cohomological Chern character `ch` of `𝔇`. -/
theorem isCohomologicalChernCharacter_twist
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) :
    (𝔇'.baseChangeData k).IsCohomologicalChernCharacter fun X α =>
      Φ.twistFamily X (ch X α) := by
  refine ⟨fun X α n => ?_, fun X α β => ?_, fun X α β => ?_, fun X => ?_,
    fun {X Y} f α n => ?_, fun X L hL => ?_⟩
  · rw [(𝔇'.baseChangeData k).mem_range_tateTwistMap_iff]
    show 𝔇'.κ _ n (Φ.twist X n (ch X α n)) ∈ 𝔇'.grade _ (2 * (n : ℤ))
    rw [κ_twist]
    exact Submodule.smul_mem _ _
      (Φ.ρ_mem_grade X _ _ ((𝔇.mem_range_tateTwistMap_iff _ _ _).mp (h.1 X α n)))
  · dsimp only
    rw [h.2.1]
    funext n
    exact Φ.twist_add X n _ _
  · dsimp only
    rw [h.2.2.1]
    exact Φ.twistFamily_cupConv X _ _
  · dsimp only
    rw [h.2.2.2.1]
    exact Φ.twistFamily_oneConv X
  · show Φ.twist X n (ch X _ n) = _
    rw [h.2.2.2.2.1 f α n]
    exact Φ.twist_pullTw f n _
  · dsimp only
    rw [h.2.2.2.2.2 X L hL, Φ.twistFamily_expTw, Φ.twist_one_eq_twistOne,
      FirstChernClassData.baseChangeData_c₁_picardClassOf,
      FirstChernClassData.baseChangeData_expTw]
    exact congrArg (𝔇'.expTw _) (Φ.c₁_comm X L hL)

variable [CharZero F] [CharZero F']

/-- **The cohomological Chern characters correspond**: `ch^{H'}(α_{k'}) = Φ(ch^H(α))` in
`(H')^{2n}(X_{k'})(n)`, for `α ∈ K₀(Vect(X))`. -/
theorem chernCharacterOf_baseChange (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (h'A1 : 𝔇'.CoproductAxiom)
    (h'A2 : 𝔇'.PullbackAxiom) (h'A3 : 𝔇'.ProjectiveBundleAxiom) (h'A4 : 𝔇'.DivisorAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (α : VectorBundleKZero ((toScheme k).obj X))
    (n : ℕ) :
    𝔇'.chernCharacterOf h'A1 h'A2 h'A3 h'A4 ((baseChange k k').obj X)
        (VectorBundleKZero.pullbackRingHom (baseChangeProj X) α) n =
      Φ.twist X n (𝔇.chernCharacterOf hA1 hA2 hA3 hA4 X α n) := by
  have bA1 : (𝔇'.baseChangeData k).CoproductAxiom :=
    FirstChernClassData.coproductAxiom_baseChangeData 𝔇' h'A1
  have bA2 : (𝔇'.baseChangeData k).PullbackAxiom :=
    FirstChernClassData.pullbackAxiom_baseChangeData 𝔇' h'A2
  have bA3 : (𝔇'.baseChangeData k).ProjectiveBundleAxiom :=
    FirstChernClassData.projectiveBundleAxiom_baseChangeData 𝔇' h'A2 h'A3
  have bA4 : (𝔇'.baseChangeData k).DivisorAxiom :=
    FirstChernClassData.divisorAxiom_baseChangeData 𝔇' h'A4
  have e1 := (𝔇'.baseChangeData k).eq_chernCharacterOf bA1 bA2 bA3 bA4
    (FirstChernClassData.isCohomologicalChernCharacter_baseChangeData
      (𝔇'.isCohomologicalChernCharacter_chernCharacterOf h'A1 h'A2 h'A3 h'A4))
  have e2 := (𝔇'.baseChangeData k).eq_chernCharacterOf bA1 bA2 bA3 bA4
    (Φ.isCohomologicalChernCharacter_twist
      (𝔇.isCohomologicalChernCharacter_chernCharacterOf hA1 hA2 hA3 hA4))
  exact congrFun (congrFun (congrFun (e1.trans e2.symm) X) α) n

/-- The cycle class map of Tag 0FIF on `ch(q ⊗ α) ∩ [X]` is `q ch^H(α)`. -/
theorem
  _root_.Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap_tmul
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (q : ℚ) (a : VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    h.cycleClassMap X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
      (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) (q ⊗ₜ[ℤ] a)) n =
      algebraMap ℚ F q • ch X a n := by
  apply (𝔇.κ X n).injective
  rw [FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap, AlgEquiv.symm_apply_apply,
    FirstChernClassData.IsCohomologicalChernCharacter.rationalLift_tmul,
    FirstChernClassData.κ_twistRule, PowerSeries.coeff_smul, FirstChernClassData.rat_smul_A,
    Subalgebra.coe_smul, FirstChernClassData.IsCohomologicalChernCharacter.coeff_lift, map_smul]

/-- **The cycle class maps correspond on `K₀(Vect(X)) ⊗ 𝐐`**: for `β ∈ K₀(Vect(X)) ⊗ 𝐐`,
`γ'(ch(β_{k'}) ∩ [X_{k'}]) = Φ(γ(ch(β) ∩ [X]))`. -/
theorem cycleClassMap_baseChange (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (h'A1 : 𝔇'.CoproductAxiom)
    (h'A2 : 𝔇'.PullbackAxiom) (h'A3 : 𝔇'.ProjectiveBundleAxiom) (h'A4 : 𝔇'.DivisorAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (β : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    (𝔇'.isCohomologicalChernCharacter_chernCharacterOf h'A1 h'A2 h'A3 h'A4).cycleClassMap
        ((baseChange k k').obj X)
        (rationalChernCharacterAlgEquiv
          (isRegular_of_smooth_over_field ((baseChange k k').obj X).obj.hom)
          (exists_bounds_relativeDimension_fieldChowSituation k'
            ((baseChange k k').obj X).obj.hom)
          ((VectorBundleKZero.pullback (baseChangeProj X)).toIntLinearMap.baseChange ℚ β)) n =
      Φ.twist X n ((𝔇.isCohomologicalChernCharacter_chernCharacterOf hA1 hA2 hA3 hA4).cycleClassMap
        X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
          (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) β) n) := by
  have htmul : ∀ (q : ℚ) (a : VectorBundleKZero ((toScheme k).obj X)),
      (𝔇'.isCohomologicalChernCharacter_chernCharacterOf h'A1 h'A2 h'A3 h'A4).cycleClassMap
        ((baseChange k k').obj X)
        (rationalChernCharacterAlgEquiv
          (isRegular_of_smooth_over_field ((baseChange k k').obj X).obj.hom)
          (exists_bounds_relativeDimension_fieldChowSituation k'
            ((baseChange k k').obj X).obj.hom)
          ((VectorBundleKZero.pullback (baseChangeProj X)).toIntLinearMap.baseChange ℚ
            (q ⊗ₜ[ℤ] a))) n =
      Φ.twist X n ((𝔇.isCohomologicalChernCharacter_chernCharacterOf hA1 hA2 hA3 hA4).cycleClassMap
        X (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
          (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom) (q ⊗ₜ[ℤ] a)) n) := by
    intro q a
    rw [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap_tmul,
      FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap_tmul,
      VectorBundleKZero.pullback_eq_pullbackRingHom,
      Φ.chernCharacterOf_baseChange hA1 hA2 hA3 hA4 h'A1 h'A2 h'A3 h'A4, twist_smul,
      (algebraMap F F').map_rat_algebraMap]
  induction β using TensorProduct.induction_on with
  | zero =>
    rw [← TensorProduct.zero_tmul ℚ (0 : VectorBundleKZero ((toScheme k).obj X))]
    exact htmul 0 0
  | tmul q a => exact htmul q a
  | add x y hx hy =>
    rw [map_add, map_add, FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap_add,
      Pi.add_apply, hx, map_add,
      FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap_add, Pi.add_apply,
      Φ.twist_add, hy]

end FieldExtensionComparison

end Stacks.WeilCohomology
