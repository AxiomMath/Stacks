module

public import StacksFrontier.LinearAlgebra.ExteriorPower.SquareArrowFunctorsComparison
public import StacksFrontier.LinearAlgebra.ExteriorPower.SemilinearDerivedLongExact

/-!
# The second Adams operation on modules of finite length over a regular local ring

Let `R` be a regular local ring of dimension `c` with residue field `κ`, and let `M` be an
`R`-module of finite length. With `T(M) = M ⊗ M`, so that `LₙT(M) = Torₙ(M, M)`, and with the
derived exterior squares `LᵢΛ²(M)` of Dold and Puppe, set

`ψ²(M) = Σₙ (-1)ⁿ length Torₙ(M, M) - 2 Σᵢ (-1)ⁱ length LᵢΛ²(M)`.

All the terms have finite length, and they vanish for `n > c` and `i > 2c` since `M` has
projective dimension at most `c`. This file proves `ψ²(M) = 2^c · length M`.

**The residue field.** For `M = κ` this is the Koszul computation
`Stacks.DerivedSquare.sum_tor_sub_two_mul_sum_length_homology_residueField`.

**Additivity.** A nonzero `M` of finite length has a submodule `M'` with `M / M' ≅ κ`. Let `P`
be a simplicial projective resolution of the monomorphism `g : M' → M`, viewed as an object of
the abelian category of arrows. The four sequences of functors on arrows

`0 → Λ² X₀ → Λ² X₁ → D_Λ(X) → 0`, `0 → X₀ ⊗ coker X → D_Λ(X) → Λ² coker X → 0`,
`0 → T X₀ → T X₁ → D_T(X) → 0`, `0 → (X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀) → D_T(X) → T coker X → 0`

are short exact on projective arrows, so each gives a long exact sequence of derived functors
at `g`. Evaluation at the source, at the target and the degreewise cokernel carry `P` to
resolutions of `M'`, `M` and `κ`, so the outer terms are the derived functors of `Λ²` and `T` at
`M'`, `M` and `κ`. Writing `χ` for alternating sums of lengths, the four sequences give

`χΛ(M) = χΛ(M') + χ(D_Λ)`, `χ(D_Λ) = χ(cross) + χΛ(κ)`,
`χT(M) = χT(M') + χ(D_T)`, `χ(D_T) = 2 χ(cross) + χT(κ)`,

the last because the two cross terms are exchanged by the braiding. The cross terms cancel in
`χT - 2 χΛ`, so `ψ²(M) = ψ²(M') + ψ²(κ)`, and the formula follows by induction on the length.
The same sequences show inductively that all the derived functors have finite length.

## Main results

* `Stacks.ShortExactOnProjectives.sum_range_neg_one_pow_mul_length_derivedHomology`: the Euler
  characteristic of the long exact sequence of derived functors of a sequence of functors to
  modules which is short exact on projective objects.
* `Stacks.DerivedSquare.sum_length_tor_sub_two_mul_sum_length_homology_of_isFiniteLength`:
  `ψ²(M) = 2^c · length M` for `M` of finite length over a regular local ring of dimension `c`.
* The same formula for the derived functors of `T` and `Λ²` at the target of an arrow, in
  `Stacks.SemilinearArrowFunctor`:
  `sum_length_tensor_right_sub_two_mul_sum_length_exteriorPower_right_of_isFiniteLength`.

## Implementation notes

The alternating sums are taken over `n ≤ 2c` for both `T` and `Λ²`; the terms of `Tor` with
`c < n` vanish. Inside the induction the sums are taken over `n ≤ 2c + 1`, where the long exact
sequences of `D_Λ` and `D_T` end: `Lₙ D_Λ(g)` sits between `LₙΛ²(M)` and `Lₙ₋₁Λ²(M')`, and so
vanishes only for `n > 2c + 1`.

## References

* H. Gillet, C. Soulé, *Intersection theory using Adams operations*, Invent. Math. 90 (1987),
  243–277.
* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial IsLocalRing

universe u v

/-! ### Alternating sums of lengths -/

namespace Module

variable {A : Type*} [CommRing A]

/-- An alternating sum of lengths of a sequence of modules vanishing from `N` on does not change
when it is taken over a longer range. -/
theorem sum_range_neg_one_pow_mul_length_eq_of_isZero {f : ℕ → ModuleCat.{v} A} {N : ℕ}
    (hf : ∀ i, N ≤ i → IsZero (f i)) {m : ℕ} (hm : N ≤ m) :
    ∑ i ∈ Finset.range m, (-1 : ℤ) ^ i * ((length A (f i)).toNat : ℤ) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * ((length A (f i)).toNat : ℤ) :=
  Finset.eventually_constant_sum (fun i hi => by
    rw [length_eq_zero_iff.2 (ModuleCat.isZero_iff_subsingleton.1 (hf i hi))]
    simp) hm

end Module

/-- The length of a biproduct of modules is the sum of the lengths. -/
theorem ModuleCat.length_biprod {A : Type*} [CommRing A] (M N : ModuleCat.{v} A) :
    Module.length A ↑(M ⊞ N) = Module.length A M + Module.length A N := by
  rw [(ModuleCat.biprodIsoProd M N).toLinearEquiv.length_eq, Module.length_prod]

/-! ### Long exact sequences of derived functors to modules -/

namespace Stacks.ShortExactOnProjectives

open SimplicialProjectiveResolution

variable {A : Type*} [CommRing A] {C : Type*} [Category C] [Abelian C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{v} A} {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃}
  (h : ShortExactOnProjectives α β) {X : C} (P : SimplicialProjectiveResolution X)

include h

/-- The long exact sequence ends with a surjection `L₀F₂(X) → L₀F₃(X)`: in degree `0` the map of
complexes is the epimorphism `F₂(P₀) → F₃(P₀)`. -/
theorem surjective_derivedHomologyMap_zero :
    Function.Surjective (derivedHomologyMap β P 0).hom := by
  have : Epi (((alternatingFaceMapComplex (ModuleCat.{v} A)).map
      (Functor.whiskerLeft P.obj β)).f 0) := by
    rw [alternatingFaceMapComplex_map_f]
    exact (h.shortExact _ (P.projective 0)).epi_g
  exact (ModuleCat.epi_iff_surjective _).1
    (HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 fun j => by simp)

/-- `LⱼF₂(X)` has finite length if `LⱼF₁(X)` and `LⱼF₃(X)` have. -/
theorem isFiniteLength_derivedHomology₂ {j : ℕ}
    (h₁ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₁ j))
    (h₃ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₃ j)) :
    IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₂ j) :=
  Module.finiteLength_middle_of_exact _ _ (h.function_exact_derivedHomologyMap P j) h₁ h₃

/-- `L₀F₃(X)` has finite length if `L₀F₂(X)` has. -/
theorem isFiniteLength_derivedHomology₃_zero
    (h₂ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₂ 0)) :
    IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₃ 0) :=
  h₂.of_surjective (h.surjective_derivedHomologyMap_zero P)

/-- `Lⱼ₊₁F₃(X)` has finite length if `Lⱼ₊₁F₂(X)` and `LⱼF₁(X)` have. -/
theorem isFiniteLength_derivedHomology₃_succ {j : ℕ}
    (h₂ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₂ (j + 1)))
    (h₁ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₁ j)) :
    IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₃ (j + 1)) :=
  Module.finiteLength_middle_of_exact _ _ (h.function_exact_derivedHomologyMap_derivedδ P j) h₂ h₁

/-- `LⱼF₁(X)` has finite length if `Lⱼ₊₁F₃(X)` and `LⱼF₂(X)` have. -/
theorem isFiniteLength_derivedHomology₁ {j : ℕ}
    (h₃ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₃ (j + 1)))
    (h₂ : IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₂ j)) :
    IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₁ j) :=
  Module.finiteLength_middle_of_exact _ _ (h.function_exact_derivedδ_derivedHomologyMap P j) h₃ h₂

/-- `Lⱼ₊₁F₃(X) = 0` if `Lⱼ₊₁F₂(X) = 0` and `LⱼF₁(X) = 0`. -/
theorem isZero_derivedHomology₃_succ {j : ℕ}
    (h₂ : IsZero (P.derivedHomology (D := ModuleCat.{v} A) F₂ (j + 1)))
    (h₁ : IsZero (P.derivedHomology (D := ModuleCat.{v} A) F₁ j)) :
    IsZero (P.derivedHomology (D := ModuleCat.{v} A) F₃ (j + 1)) :=
  (h.exact_derivedHomologyMap_derivedδ P j).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- **The Euler characteristic of the long exact sequence of derived functors.** For a sequence
`F₁ ⟶ F₂ ⟶ F₃` of functors to modules which is short exact on projective objects, if all the
`LⱼFᵢ(X)` have finite length and `LₙF₃(X) = 0`, then

`Σ_{j < n} (-1)ʲ length LⱼF₂(X) = Σ_{j < n} (-1)ʲ length LⱼF₁(X) + Σ_{j < n} (-1)ʲ length LⱼF₃(X)`.
-/
theorem sum_range_neg_one_pow_mul_length_derivedHomology
    (h₁ : ∀ j, IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₁ j))
    (h₂ : ∀ j, IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₂ j))
    (h₃ : ∀ j, IsFiniteLength A (P.derivedHomology (D := ModuleCat.{v} A) F₃ j)) {n : ℕ}
    (hn : IsZero (P.derivedHomology (D := ModuleCat.{v} A) F₃ n)) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
        ((Module.length A (P.derivedHomology (D := ModuleCat.{v} A) F₂ j)).toNat : ℤ) =
      ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
          ((Module.length A (P.derivedHomology (D := ModuleCat.{v} A) F₁ j)).toNat : ℤ) +
        ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
          ((Module.length A (P.derivedHomology (D := ModuleCat.{v} A) F₃ j)).toNat : ℤ) := by
  have key := Module.sum_range_neg_one_pow_mul_length_eq_sum_index
    (fun j => derivedHomologyMap α P j) (fun j => derivedHomologyMap β P j)
    (fun j => h.derivedδ P j) (fun j => h.function_exact_derivedHomologyMap P j)
    (fun j => h.function_exact_derivedHomologyMap_derivedδ P j)
    (fun j => h.function_exact_derivedδ_derivedHomologyMap P j)
    (h.surjective_derivedHomologyMap_zero P) h₃ (ModuleCat.isZero_iff_subsingleton.1 hn)
  have e := fun j => Module.toNat_length_quotient_range_sub_toNat_length_ker
    (derivedHomologyMap α P j).hom (h₁ j) (h₂ j)
  simp only [e, mul_sub, Finset.sum_sub_distrib] at key
  linarith

end Stacks.ShortExactOnProjectives

/-! ### The inductive step -/

namespace Stacks.SemilinearArrowFunctor

open SimplicialProjectiveResolution ComposableArrows

variable {R : CommRingCat.{u}} [IsRegularLocalRing R] {c : ℕ}

/-- **Additivity of `ψ²` along a simple quotient.** Let `X = (X₀ → X₁)` be a monomorphism with
`X₁` of finite length and simple cokernel, over a regular local ring of dimension `c`, and let
`P` be a resolution of `X`. If `Torⱼ(X₀, X₀)` has finite length for every `j` and
`ψ²(X₀) = 2^c m`, then `Torⱼ(X₁, X₁)` has finite length for every `j` and
`ψ²(X₁) = 2^c (m + 1)`. -/
theorem isFiniteLength_tor_right_and_sum_length_eq_of_left (hc : ringKrullDim R = c)
    {X : ComposableArrows (ModuleCat.{u} R) 1} [Mono X.hom]
    [IsSimpleModule R (Limits.cokernel X.hom : ModuleCat.{u} R)] (hX : IsFiniteLength R X.right)
    (P : SimplicialProjectiveResolution X) {m : ℤ}
    (hT : ∀ j, IsFiniteLength R (((Tor' (ModuleCat.{u} R) j).obj X.left).obj X.left))
    (hψ : ∑ j ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ j *
        ((Module.length R (((Tor' (ModuleCat.{u} R) j).obj X.left).obj X.left)).toNat : ℤ) -
      2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
        ((Module.length R (DerivedSquare.homology P.leftResolution i)).toNat : ℤ) = 2 ^ c * m) :
    (∀ j, IsFiniteLength R (((Tor' (ModuleCat.{u} R) j).obj X.right).obj X.right)) ∧
      ∑ j ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ j *
          ((Module.length R (((Tor' (ModuleCat.{u} R) j).obj X.right).obj X.right)).toNat : ℤ) -
        2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
          ((Module.length R (DerivedSquare.homology P.rightResolution i)).toNat : ℤ) =
        2 ^ c * (m + 1) := by
  have hpd : ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M c := fun M =>
    (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE hc.le).2 M
  have hXl : IsFiniteLength R X.left :=
    hX.of_injective ((ModuleCat.mono_iff_injective X.hom).1 inferInstance)
  have hXc : IsFiniteLength R (Limits.cokernel X.hom : ModuleCat.{u} R) :=
    IsSimpleModule.isFiniteLength R _
  -- the cokernel is the residue field
  have : IsSimpleModule R (ResidueField R) :=
    Module.length_eq_one_iff.1 Stacks.OrderOfVanishing.length_residueField
  obtain ⟨e'⟩ := IsLocalRing.nonempty_linearEquiv_of_isSimpleModule (R := R)
    (Limits.cokernel X.hom : ModuleCat.{u} R) (ResidueField R)
  let e : Limits.cokernel X.hom ≅ ModuleCat.of R (ResidueField R) := e'.toModuleIso
  let Qκ : SimplicialProjectiveResolution (ModuleCat.of R (ResidueField R)) :=
    Classical.arbitrary _
  have hTc : ∀ j, Module.length R (((Tor' (ModuleCat.{u} R) j).obj
      (Limits.cokernel X.hom)).obj (Limits.cokernel X.hom)) =
      Module.length R (((Tor' (ModuleCat.{u} R) j).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R))) := fun j =>
    (((Tor' (ModuleCat.{u} R) j).mapIso e).app _ ≪≫
      ((Tor' (ModuleCat.{u} R) j).obj _).mapIso e).toLinearEquiv.length_eq
  have hΛc : ∀ i, Module.length R (DerivedSquare.homology P.cokernelResolution i) =
      Module.length R (DerivedSquare.homology Qκ i) := fun i =>
    DerivedSquare.length_homology_eq_of_iso e P.cokernelResolution Qκ i
  -- the four short exact sequences
  have h₁ : ShortExactOnProjectives ((exteriorPowerMap 2 leftToRight).app R)
      ((cokernelπ (exteriorPowerMap 2 leftToRight)).app R) :=
    ⟨comp_cokernelπ_app _ R, shortExact_exteriorSquare R⟩
  have h₂ : ShortExactOnProjectives (crossToRelExteriorSquare.app R)
      (relExteriorSquareToCoker.app R) :=
    ⟨crossToRelExteriorSquare_comp_relExteriorSquareToCoker_app R, shortExact_relExteriorSquare R⟩
  have h₃ : ShortExactOnProjectives ((tensorHom leftToRight leftToRight).app R)
      ((cokernelπ (tensorHom leftToRight leftToRight)).app R) :=
    ⟨comp_cokernelπ_app _ R, shortExact_tensorSquare R⟩
  have h₄ : ShortExactOnProjectives (crossSumToRelTensorSquare.app R)
      (relTensorSquareToCoker.app R) :=
    ⟨crossSumToRelTensorSquare_comp_relTensorSquareToCoker_app R, shortExact_relTensorSquare R⟩
  -- finiteness
  have fΛr : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 right).obj R) j) := fun j =>
    DerivedSquare.isFiniteLength_homology hX P.rightResolution j
  have fΛl : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 left).obj R) j) := fun j =>
    DerivedSquare.isFiniteLength_homology hXl P.leftResolution j
  have fΛc : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 coker).obj R) j) := fun j =>
    DerivedSquare.isFiniteLength_homology hXc P.cokernelResolution j
  have fDΛ : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) (relExteriorSquare.obj R) j) := fun j => by
    rcases j with _ | j
    · exact h₁.isFiniteLength_derivedHomology₃_zero P (fΛr 0)
    · exact h₁.isFiniteLength_derivedHomology₃_succ P (fΛr (j + 1)) (fΛl j)
  have fx : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) (cross.obj R) j) := fun j =>
    h₂.isFiniteLength_derivedHomology₁ P (fΛc (j + 1)) (fDΛ j)
  have lxr : ∀ j, Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (crossRev.obj R) j) =
      Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (cross.obj R) j) := fun j =>
    (derivedHomologyCrossIso P j).toLinearEquiv.length_eq.symm
  have ly : ∀ j, Module.length R
      (P.derivedHomology (D := ModuleCat.{u} R) ((biprod cross crossRev).obj R) j) =
      Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (cross.obj R) j) +
        Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (cross.obj R) j) := fun j => by
    rw [(derivedHomologyCrossSumIso P j).toLinearEquiv.length_eq, ModuleCat.length_biprod, lxr]
  have fy : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((biprod cross crossRev).obj R) j) := fun j => by
    have := Module.length_ne_top_iff.2 (fx j)
    rw [← Module.length_ne_top_iff, ly]
    exact WithTop.add_ne_top.2 ⟨this, this⟩
  have fTl : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((tensor left left).obj R) j) := fun j =>
    (derivedHomologyTensorLeftIsoTor P j).symm.toLinearEquiv.isFiniteLength (hT j)
  have fTc : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((tensor coker coker).obj R) j) := fun j => by
    rw [← Module.length_ne_top_iff, (derivedHomologyTensorCokerIsoTor P j).toLinearEquiv.length_eq,
      hTc j, IsRegularLocalRing.length_tor_residueField_residueField hc j]
    exact ENat.natCast_ne_top _
  have fDT : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) (relTensorSquare.obj R) j) := fun j =>
    h₄.isFiniteLength_derivedHomology₂ P (fy j) (fTc j)
  have fTr : ∀ j, IsFiniteLength R
      (P.derivedHomology (D := ModuleCat.{u} R) ((tensor right right).obj R) j) := fun j =>
    h₃.isFiniteLength_derivedHomology₂ P (fTl j) (fDT j)
  -- vanishing
  have zΛr : ∀ j, 2 * c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 right).obj R) j) :=
    fun j hj => isZero_derivedHomology_exteriorSquare_right (hpd _) P hj
  have zΛl : ∀ j, 2 * c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 left).obj R) j) :=
    fun j hj => isZero_derivedHomology_exteriorSquare_left (hpd _) P hj
  have zΛc : ∀ j, 2 * c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 coker).obj R) j) :=
    fun j hj => isZero_derivedHomology_exteriorSquare_coker (hpd _) P hj
  have zTr : ∀ j, c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((tensor right right).obj R) j) :=
    fun j hj => isZero_derivedHomology_tensor_right (hpd _) P hj
  have zTl : ∀ j, c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((tensor left left).obj R) j) :=
    fun j hj => isZero_derivedHomology_tensor_left (hpd _) P hj
  have zTc : ∀ j, c < j →
      IsZero (P.derivedHomology (D := ModuleCat.{u} R) ((tensor coker coker).obj R) j) :=
    fun j hj => isZero_derivedHomology_tensor_coker (hpd _) P hj
  have zDΛ : IsZero (P.derivedHomology (D := ModuleCat.{u} R) (relExteriorSquare.obj R)
      (2 * c + 1 + 1)) :=
    h₁.isZero_derivedHomology₃_succ P (zΛr _ (by omega)) (zΛl _ (by omega))
  have zDT : IsZero (P.derivedHomology (D := ModuleCat.{u} R) (relTensorSquare.obj R)
      (2 * c + 1 + 1)) :=
    h₃.isZero_derivedHomology₃_succ P (zTr _ (by omega)) (zTl _ (by omega))
  -- the Euler characteristics
  let χ : SemilinearArrowFunctor.{u} → ℤ := fun Φ => ∑ j ∈ Finset.range (2 * c + 1 + 1),
    (-1 : ℤ) ^ j *
      ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (Φ.obj R) j)).toNat : ℤ)
  have E₁ : χ (exteriorPower 2 right) = χ (exteriorPower 2 left) + χ relExteriorSquare :=
    h₁.sum_range_neg_one_pow_mul_length_derivedHomology P fΛl fΛr fDΛ zDΛ
  have E₂ : χ relExteriorSquare = χ cross + χ (exteriorPower 2 coker) :=
    h₂.sum_range_neg_one_pow_mul_length_derivedHomology P fx fDΛ fΛc (zΛc _ (by omega))
  have E₃ : χ (tensor right right) = χ (tensor left left) + χ relTensorSquare :=
    h₃.sum_range_neg_one_pow_mul_length_derivedHomology P fTl fTr fDT zDT
  have E₄ : χ relTensorSquare = χ (biprod cross crossRev) + χ (tensor coker coker) :=
    h₄.sum_range_neg_one_pow_mul_length_derivedHomology P fy fDT fTc (zTc _ (by omega))
  have E₅ : χ (biprod cross crossRev) = 2 * χ cross := by
    simp only [χ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ly, ENat.toNat_add (Module.length_ne_top_iff.2 (fx j))
      (Module.length_ne_top_iff.2 (fx j))]
    push_cast
    ring
  -- the Euler characteristics in terms of the Euler characteristics of the derived functors
  have hχ : ∀ (Φ : SemilinearArrowFunctor.{u}) (N : ℕ) (M : ℕ → ModuleCat.{u} R),
      N ≤ 2 * c + 1 + 1 →
      (∀ j, N ≤ j → IsZero (P.derivedHomology (D := ModuleCat.{u} R) (Φ.obj R) j)) →
      (∀ j, Module.length R (P.derivedHomology (D := ModuleCat.{u} R) (Φ.obj R) j) =
        Module.length R (M j)) →
      χ Φ = ∑ j ∈ Finset.range N, (-1 : ℤ) ^ j * ((Module.length R (M j)).toNat : ℤ) :=
    fun Φ N M hN hz hl => by
      simp only [χ]
      rw [Module.sum_range_neg_one_pow_mul_length_eq_of_isZero hz hN]
      exact Finset.sum_congr rfl fun j _ => by rw [hl j]
  have cTl := hχ (tensor left left) (2 * c + 1)
    (fun j => ((Tor' (ModuleCat.{u} R) j).obj X.left).obj X.left) (by omega)
    (fun j hj => zTl j (by omega)) fun j =>
    (derivedHomologyTensorLeftIsoTor P j).toLinearEquiv.length_eq
  have cΛl := hχ (exteriorPower 2 left) (2 * c + 1) (DerivedSquare.homology P.leftResolution)
    (by omega) (fun j hj => zΛl j (by omega)) fun _ => rfl
  have cTr := hχ (tensor right right) (2 * c + 1)
    (fun j => ((Tor' (ModuleCat.{u} R) j).obj X.right).obj X.right) (by omega)
    (fun j hj => zTr j (by omega)) fun j =>
    (derivedHomologyTensorRightIsoTor P j).toLinearEquiv.length_eq
  have cΛr := hχ (exteriorPower 2 right) (2 * c + 1) (DerivedSquare.homology P.rightResolution)
    (by omega) (fun j hj => zΛr j (by omega)) fun _ => rfl
  have cTc := hχ (tensor coker coker) (c + 1) (fun n => ((Tor' (ModuleCat.{u} R) n).obj
    (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R (ResidueField R))) (by omega)
    (fun j hj => zTc j (by omega)) fun j =>
    ((derivedHomologyTensorCokerIsoTor P j).toLinearEquiv.length_eq).trans (hTc j)
  have cΛc := hχ (exteriorPower 2 coker) (2 * c + 1) (fun i => DerivedSquare.homology Qκ i)
    (by omega) (fun j hj => zΛc j (by omega)) fun i => hΛc i
  have hκ := DerivedSquare.sum_tor_sub_two_mul_sum_length_homology_residueField hc Qκ
  refine ⟨fun j => (derivedHomologyTensorRightIsoTor P j).toLinearEquiv.isFiniteLength (fTr j),
    ?_⟩
  rw [← cTr, ← cΛr]
  rw [← cTl, ← cΛl] at hψ
  rw [← cTc, ← cΛc] at hκ
  linear_combination E₃ + E₄ - 2 * E₁ - 2 * E₂ + E₅ + hψ + hκ

end Stacks.SemilinearArrowFunctor

/-! ### Modules of finite length -/

namespace Stacks.DerivedSquare

open SimplicialProjectiveResolution ComposableArrows

variable {R : CommRingCat.{u}} [IsRegularLocalRing R] {c : ℕ}

/-- **`ψ²` of a module of length `n`.** Over a regular local ring of dimension `c`, a module `M`
of length `n` has `Torⱼ(M, M)` of finite length for every `j`, and
`Σ_{j ≤ 2c} (-1)ʲ length Torⱼ(M, M) - 2 Σ_{i ≤ 2c} (-1)ⁱ length LᵢΛ²(M) = 2^c n`. The proof is by
induction on `n`, through
`SemilinearArrowFunctor.isFiniteLength_tor_right_and_sum_length_eq_of_left` at the inclusion of a
maximal submodule. -/
theorem isFiniteLength_tor_and_sum_length_tor_sub_two_mul_sum_length_homology
    (hc : ringKrullDim R = c) (n : ℕ) {M : ModuleCat.{u} R} (hM : Module.length R M = n)
    (Q : SimplicialProjectiveResolution M) :
    (∀ j, IsFiniteLength R (((Tor' (ModuleCat.{u} R) j).obj M).obj M)) ∧
      ∑ j ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ j *
          ((Module.length R (((Tor' (ModuleCat.{u} R) j).obj M).obj M)).toNat : ℤ) -
        2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
          ((Module.length R (homology Q i)).toNat : ℤ) = 2 ^ c * n := by
  induction n generalizing M with
  | zero =>
    have hM₀ : IsZero M := ModuleCat.isZero_iff_subsingleton.2
      (Module.length_eq_zero_iff.1 (by exact_mod_cast hM))
    have hT : ∀ j, IsZero (((Tor' (ModuleCat.{u} R) j).obj M).obj M) := fun j =>
      (((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj M).leftDerived j).map_isZero hM₀
    have hT' : ∀ j, Module.length R (((Tor' (ModuleCat.{u} R) j).obj M).obj M) = 0 := fun j =>
      Module.length_eq_zero_iff.2 (ModuleCat.isZero_iff_subsingleton.1 (hT j))
    have hL : ∀ i, Module.length R (homology Q i) = 0 := fun i =>
      Module.length_eq_zero_iff.2 (ModuleCat.isZero_iff_subsingleton.1 (isZero_homology hM₀ Q i))
    refine ⟨fun j => ?_, by simp [hT', hL]⟩
    have := ModuleCat.isZero_iff_subsingleton.1 (hT j)
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    have hfin : IsFiniteLength R M :=
      Module.length_ne_top_iff.1 (by simp [hM])
    have : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfin).1
    have : Nontrivial M := by
      rw [← not_subsingleton_iff_nontrivial]
      intro h
      rw [Module.length_eq_zero_iff (R := R).2 h] at hM
      exact absurd hM (by exact_mod_cast (Nat.succ_ne_zero n).symm)
    obtain ⟨N', hN', -⟩ :=
      (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
    have : IsSimpleModule R (M ⧸ N') := isSimpleModule_iff_isCoatom.2 hN'
    have hlen : Module.length R M = Module.length R N' + 1 := by
      rw [Module.length_eq_add_of_exact N'.subtype N'.mkQ N'.injective_subtype N'.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N'), Module.length_eq_one R (M ⧸ N')]
    let X : ComposableArrows (ModuleCat.{u} R) 1 := mk₁ (ModuleCat.ofHom N'.subtype)
    have : Mono X.hom := (ModuleCat.mono_iff_injective _).2 N'.injective_subtype
    have : IsSimpleModule R (Limits.cokernel X.hom : ModuleCat.{u} R) :=
      IsSimpleModule.congr ((ModuleCat.cokernelIsoRangeQuotient X.hom).toLinearEquiv ≪≫ₗ
        Submodule.quotEquivOfEq _ _ (Submodule.range_subtype N'))
    let P : SimplicialProjectiveResolution X := Classical.arbitrary _
    have hN'len : Module.length R X.left = n := by
      rw [hM, Nat.cast_succ] at hlen
      exact (WithTop.add_right_cancel ENat.one_ne_top hlen).symm
    obtain ⟨hTl, hψl⟩ := ih hN'len P.leftResolution
    obtain ⟨hTr, hψr⟩ := SemilinearArrowFunctor.isFiniteLength_tor_right_and_sum_length_eq_of_left
      hc hfin P hTl hψl
    refine ⟨hTr, ?_⟩
    have hQ : ∀ i, Module.length R (homology Q i) =
        Module.length R (homology P.rightResolution i) := fun i =>
      length_homology_eq_of_iso (Iso.refl _) Q P.rightResolution i
    simp only [hQ]
    exact hψr.trans (by push_cast; ring)

/-- **`ψ²(M) = 2^c · length M`.** For a module `M` of finite length over a regular local ring of
dimension `c`,

`Σ_{j ≤ 2c} (-1)ʲ length Torⱼ(M, M) - 2 Σ_{i ≤ 2c} (-1)ⁱ length LᵢΛ²(M) = 2^c · length M`. -/
theorem sum_length_tor_sub_two_mul_sum_length_homology_of_isFiniteLength
    (hc : ringKrullDim R = c) {M : ModuleCat.{u} R} (hM : IsFiniteLength R M)
    (Q : SimplicialProjectiveResolution M) :
    ∑ j ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ j *
        ((Module.length R (((Tor' (ModuleCat.{u} R) j).obj M).obj M)).toNat : ℤ) -
      2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
        ((Module.length R (homology Q i)).toNat : ℤ) =
      2 ^ c * ((Module.length R M).toNat : ℤ) :=
  (isFiniteLength_tor_and_sum_length_tor_sub_two_mul_sum_length_homology hc _
    (ENat.natCast_toNat (Module.length_ne_top_iff.2 hM)).symm Q).2

end Stacks.DerivedSquare

/-! ### Arrows -/

namespace Stacks.SemilinearArrowFunctor

open SimplicialProjectiveResolution

/-- **The second Adams operation on finite-length targets.** For a regular local ring `R` of
dimension `c` and an arrow `X` whose target has finite length,
`Σ_{n ≤ 2c} (-1)ⁿ length Lₙ(T ∘ right)(X) - 2 Σ_{i ≤ 2c} (-1)ⁱ length Lᵢ(Λ² ∘ right)(X)` is
`2^c · length X₁`. -/
theorem sum_length_tensor_right_sub_two_mul_sum_length_exteriorPower_right_of_isFiniteLength
    {R : CommRingCat.{u}} [IsRegularLocalRing R] {c : ℕ} (hc : ringKrullDim R = c)
    {X : ComposableArrows (ModuleCat.{u} R) 1} (hX : IsFiniteLength R X.right)
    (P : SimplicialProjectiveResolution X) :
    ∑ n ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ n *
        ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((tensor right right).obj R) n)).toNat : ℤ) -
      2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
        ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((exteriorPower 2 right).obj R) i)).toNat : ℤ) =
      2 ^ c * ((Module.length R X.right).toNat : ℤ) := by
  have e : ∀ n, Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
      ((tensor right right).obj R) n) =
      Module.length R (((Tor' (ModuleCat.{u} R) n).obj X.right).obj X.right) := fun n =>
    (derivedHomologyTensorRightIsoTor P n).toLinearEquiv.length_eq
  simp only [e]
  exact DerivedSquare.sum_length_tor_sub_two_mul_sum_length_homology_of_isFiniteLength hc hX
    P.rightResolution

end Stacks.SemilinearArrowFunctor
