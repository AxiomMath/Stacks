module

public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# A chart of a Čech nerve which is the base change of a flat cover is the cover itself

Let `U → P` be a surjective étale chart of an algebraic space, `V = U ×_P U` and
`W = U ×_P U ×_P U`, with rings of functions `B`, `C`, `D`: two projections `p₁, p₂ : B → C`,
the diagonal `δ : C → B`, and the three partial projections `e₁₂, e₁₃, e₂₃ : C → D`. Let `A` be
a ring of invariant functions, mapping to the equalizer of `p₁` and `p₂`, and let `S` be a flat
`A`-algebra with an `A`-algebra map `β : S → B`. Read geometrically, `Spec S → Spec A` is a flat
cover through which the chart factors, and the two conditions

* `S ⊗[A] B → C`, `s ⊗ b ↦ p₁ (β s) · p₂ b`, is bijective, i.e. `V ≅ Spec S ×_{Spec A} U`, and
* `S ⊗[A] C → D`, `s ⊗ c ↦ e₁₂ (p₁ (β s)) · e₂₃ c`, is injective,

say that `U → P` is the base change of `Spec S → Spec A` along `P → Spec A`. When `A` is the
whole equalizer this forces `β` to be bijective (`Module.Descent.bijective_of_bijective_chartMap`):
`U` is the cover itself and `P = Spec A`.

## The argument

The first condition makes `p₁ : B → C ≅ S ⊗[A] B` a coaction of `S` on the `S`-module `B`
(through `β`); it is counital because the diagonal `δ` splits both projections, and
coassociative because the three partial projections of `W` satisfy the simplicial identities and
the second condition identifies `S ⊗[A] (S ⊗[A] B)` with a submodule of `D`. The descended module
of this descent datum is the equalizer of `p₁` and `p₂`, that is `A`, and effectivity of descent
along the flat `A → S` (`Module.Descent.Datum.equivBaseChange`) identifies `S ⊗[A] A = S` with
`B` through `β`.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

open TensorProduct

namespace Module.Descent

variable {A : Type*} [CommRing A] {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]

/-- The comparison map `S ⊗[A] B → C`, `s ⊗ b ↦ p₁ (β s) · p₂ b`, of a chart `p₁, p₂ : B → C` of
a Čech nerve with a cover `β : S → B`. -/
noncomputable def chartMap {S : Type*} [CommRing S] [Algebra A S] (p₁ p₂ : B →ₐ[A] C)
    (β : S →ₐ[A] B) : S ⊗[A] B →ₐ[A] C :=
  Algebra.TensorProduct.lift (p₁.comp β) p₂ fun _ _ => Commute.all _ _

/-- `chartMap p₁ p₂ β` sends `s ⊗ b` to `p₁ (β s) * p₂ b`. -/
@[simp]
lemma chartMap_tmul {S : Type*} [CommRing S] [Algebra A S] (p₁ p₂ : B →ₐ[A] C)
    (β : S →ₐ[A] B) (s : S) (b : B) :
    chartMap p₁ p₂ β (s ⊗ₜ b) = p₁ (β s) * p₂ b := by
  simp [chartMap]

/-- The comparison map `S ⊗[A] C → D`, `s ⊗ c ↦ e₁₂ (p₁ (β s)) · e₂₃ c`. -/
noncomputable def tripleMap {S : Type*} [CommRing S] [Algebra A S] (p₁ : B →ₐ[A] C)
    (e₁₂ e₂₃ : C →ₐ[A] D) (β : S →ₐ[A] B) : S ⊗[A] C →ₐ[A] D :=
  Algebra.TensorProduct.lift ((e₁₂.comp p₁).comp β) e₂₃ fun _ _ => Commute.all _ _

/-- `tripleMap p₁ e₁₂ e₂₃ β` sends `s ⊗ c` to `e₁₂ (p₁ (β s)) * e₂₃ c`. -/
@[simp]
lemma tripleMap_tmul {S : Type*} [CommRing S] [Algebra A S] (p₁ : B →ₐ[A] C)
    (e₁₂ e₂₃ : C →ₐ[A] D) (β : S →ₐ[A] B) (s : S) (c : C) :
    tripleMap p₁ e₁₂ e₂₃ β (s ⊗ₜ c) = e₁₂ (p₁ (β s)) * e₂₃ c := by
  simp [tripleMap]

/-- **A chart of a Čech nerve which is a base change of a flat cover is that cover.** Let
`p₁, p₂ : B → C`, `δ : C → B` and `e₁₂, e₁₃, e₂₃ : C → D` satisfy the identities of the first
three terms of a Čech nerve, let `A` map injectively onto the equalizer of `p₁` and `p₂`, and let
`β : S → B` be a map from a flat `A`-algebra. If `chartMap p₁ p₂ β` is bijective and
`tripleMap p₁ e₁₂ e₂₃ β` is injective, then `β` is bijective. -/
theorem bijective_of_bijective_chartMap {S : Type*} [CommRing S] [Algebra A S]
    [Module.Flat A S] (p₁ p₂ : B →ₐ[A] C) (δ : C →ₐ[A] B) (e₁₂ e₁₃ e₂₃ : C →ₐ[A] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id A B) (hδ₂ : δ.comp p₂ = AlgHom.id A B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hA : ∀ b : B, p₁ b = p₂ b → b ∈ Set.range (algebraMap A B))
    (hAinj : Function.Injective (algebraMap A B))
    (β : S →ₐ[A] B) (hφ : Function.Bijective (chartMap p₁ p₂ β))
    (hν : Function.Injective (tripleMap p₁ e₁₂ e₂₃ β)) :
    Function.Bijective β := by
  classical
  let : Module S B := Module.compHom B (β : S →+* B)
  have hsmulB : ∀ (s : S) (b : B), s • b = β s * b := fun _ _ => rfl
  have : IsScalarTower A S B := ⟨fun a s b => by
    rw [hsmulB, hsmulB, map_smul, smul_mul_assoc]⟩
  let : Module S C := Module.compHom C ((p₁.comp β : S →ₐ[A] C) : S →+* C)
  have hsmulC : ∀ (s : S) (c : C), s • c = p₁ (β s) * c := fun _ _ => rfl
  have : IsScalarTower A S C := ⟨fun a s c => by
    rw [hsmulC, hsmulC, map_smul, map_smul, smul_mul_assoc]⟩
  let φl : S ⊗[A] B →ₗ[S] C :=
    { toFun := chartMap p₁ p₂ β
      map_add' := map_add _
      map_smul' := fun s x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s' b =>
          rw [TensorProduct.smul_tmul', smul_eq_mul, chartMap_tmul, RingHom.id_apply, hsmulC,
            chartMap_tmul, map_mul, map_mul, mul_assoc]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  let φe : S ⊗[A] B ≃ₗ[S] C := LinearEquiv.ofBijective φl hφ
  have hφe : ∀ x, φe x = chartMap p₁ p₂ β x := fun _ => rfl
  let p₁l : B →ₗ[S] C :=
    { toFun := p₁
      map_add' := map_add _
      map_smul' := fun s b => by rw [hsmulB, map_mul, RingHom.id_apply, hsmulC] }
  have hcounit : ∀ x : S ⊗[A] B, counit A S B x = δ (chartMap p₁ p₂ β x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [counit_tmul, chartMap_tmul, map_mul, ← AlgHom.comp_apply δ p₁,
        ← AlgHom.comp_apply δ p₂, hδ₁, hδ₂, hsmulB]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  let Ψ : S ⊗[A] (S ⊗[A] B) →ₗ[A] D :=
    (tripleMap p₁ e₁₂ e₂₃ β).toLinearMap ∘ₗ
      (LinearMap.lTensor S (φe.toLinearMap.restrictScalars A))
  have hΨinj : Function.Injective Ψ := by
    refine hν.comp ?_
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ φe.injective
  have hΨ₁ : ∀ x : S ⊗[A] B, Ψ (AlgebraTensorModule.lTensor S S
      ((φe.symm.toLinearMap ∘ₗ p₁l).restrictScalars A) x) = e₁₂ (chartMap p₁ p₂ β x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      simp only [Ψ, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply, tripleMap_tmul, chartMap_tmul,
        map_mul]
      congr 1
      exact (AlgHom.congr_fun h₁₂₂₃ b).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hΨ₂ : ∀ x : S ⊗[A] B, Ψ (AlgebraTensorModule.lTensor S S
      (TensorProduct.mk A S B 1) x) = e₁₃ (chartMap p₁ p₂ β x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      simp only [Ψ, AlgebraTensorModule.lTensor_tmul, TensorProduct.mk_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hφe, AlgHom.toLinearMap_apply,
        tripleMap_tmul, chartMap_tmul, map_one, one_mul, map_mul]
      rw [← AlgHom.comp_apply e₁₂ p₁, h₁₂₁₃, ← AlgHom.comp_apply e₂₃ p₂, ← h₁₃₂₃]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  let d : Datum A S B :=
    { coaction := φe.symm.toLinearMap ∘ₗ p₁l
      counit_coaction := fun b => by
        rw [hcounit]
        show δ (chartMap p₁ p₂ β (φe.symm (p₁ b))) = b
        rw [← hφe, LinearEquiv.apply_symm_apply, ← AlgHom.comp_apply, hδ₁]
        rfl
      coassoc := fun b => by
        apply hΨinj
        show Ψ (AlgebraTensorModule.lTensor S S
            ((φe.symm.toLinearMap ∘ₗ p₁l).restrictScalars A) (φe.symm (p₁ b))) =
          Ψ (AlgebraTensorModule.lTensor S S (TensorProduct.mk A S B 1) (φe.symm (p₁ b)))
        rw [hΨ₁, hΨ₂, ← hφe, LinearEquiv.apply_symm_apply, ← AlgHom.comp_apply,
          ← AlgHom.comp_apply, h₁₂₁₃] }
  have hdesc : ∀ b : B, b ∈ d.descended ↔ b ∈ Set.range (algebraMap A B) := by
    intro b
    rw [d.mem_descended_iff]
    show φe.symm (p₁ b) = 1 ⊗ₜ b ↔ _
    rw [LinearEquiv.symm_apply_eq, hφe, chartMap_tmul, map_one, map_one, one_mul]
    constructor
    · exact hA b
    · rintro ⟨a, rfl⟩
      rw [AlgHom.commutes, AlgHom.commutes]
  let ι : A →ₗ[A] d.descended :=
    { toFun := fun a => ⟨algebraMap A B a, (hdesc _).2 ⟨a, rfl⟩⟩
      map_add' := fun a a' => by ext; simp
      map_smul' := fun a a' => by ext; simp [Algebra.smul_def] }
  have hι : Function.Bijective ι := by
    refine ⟨fun a a' h => hAinj (congrArg Subtype.val h), fun m => ?_⟩
    obtain ⟨a, ha⟩ := (hdesc m).1 m.2
    exact ⟨a, Subtype.ext ha⟩
  have key : ∀ s : S, β s = d.equivBaseChange (s ⊗ₜ ι 1) := by
    intro s
    rw [Datum.equivBaseChange_tmul]
    show β s = s • algebraMap A B 1
    rw [map_one, hsmulB, mul_one]
  have hβ : (β : S → B) = (d.equivBaseChange.restrictScalars A) ∘
      (LinearMap.lTensor S ι) ∘ (TensorProduct.rid A S).symm := by
    funext s
    simp only [Function.comp_apply, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul,
      LinearEquiv.restrictScalars_apply]
    exact key s
  rw [hβ]
  refine (d.equivBaseChange.restrictScalars A).bijective.comp
    (Function.Bijective.comp ?_ (TensorProduct.rid A S).symm.bijective)
  exact ((LinearEquiv.ofBijective ι hι).lTensor S).bijective

end Module.Descent
