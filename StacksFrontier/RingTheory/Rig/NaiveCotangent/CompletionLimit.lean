module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Completion

/-!
# The completed naive cotangent complex as a degreewise adic limit

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `A → B` be of finite type and let
`α : A[x₁, …, xₙ] → B` be a presentation.  Stacks 0GAF identifies `NL^∧_{B^/A}` with
`lim NL(α) ⊗_B B^`: the two terms of `NL(α)` are finite `B`-modules, `B` is Noetherian, and
adic completion of a finite module over a Noetherian ring is base change to the completion.

## Main definitions

* `Rig.adicLimitTwoTerm` — `lim NL(α)`, the degreewise `I`-adic completion of `NL(α)`.
* `Rig.limitComparison` — the canonical comparison of complexes `NL(α) ⊗_B B^ → lim NL(α)`.
* `Rig.limitCompletionComparison` — the resulting comparison `lim NL(α) → NL^∧_{B^/A}`.

## Main results

* `Rig.bijective_limitComparison` — **Stacks 0GAF, `lim` form**: `lim NL(α) = NL(α) ⊗_B B^`
  as complexes.
* `Rig.bijective_limitCompletionComparison` — **Stacks 0GAF, first clause**:
  `NL^∧_{B^/A} = lim NL(α) ⊗_B B^` as complexes.

## References

* [Stacks Project, Lemma 88.3.2 (Tag 0GAF)](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Lemma 10.97.1 (Tag 00MA)](https://stacks.math.columbia.edu/tag/00MA)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace Rig

/-! ## Inverting a chain map which is bijective in both degrees -/

section Invert

variable {S : Type*} [CommRing S] {X Y : NaiveCotangent.TwoTerm S}

/-- A chain map of two-term complexes which is bijective in both degrees is invertible: the two
inverse maps again commute with the differentials. -/
public def chainMapSymm (f : NaiveCotangent.ChainMap X Y) (h₁ : Function.Bijective f.f₁)
    (h₀ : Function.Bijective f.f₀) : NaiveCotangent.ChainMap Y X where
  f₁ := (LinearEquiv.ofBijective f.f₁ h₁).symm
  f₀ := (LinearEquiv.ofBijective f.f₀ h₀).symm
  comm := by
    refine LinearMap.ext fun y => ?_
    have h := LinearMap.congr_fun f.comm ((LinearEquiv.ofBijective f.f₁ h₁).symm y)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h ⊢
    rw [show f.f₁ ((LinearEquiv.ofBijective f.f₁ h₁).symm y) = y from
      (LinearEquiv.ofBijective f.f₁ h₁).apply_symm_apply y] at h
    exact ((LinearEquiv.ofBijective f.f₀ h₀).symm_apply_eq.mpr h).symm

/-- The degree-`1` component of `chainMapSymm f h₁ h₀` is the inverse of `f.f₁`. -/
@[simp] public theorem chainMapSymm_f₁ (f : NaiveCotangent.ChainMap X Y)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Bijective f.f₀) :
    (chainMapSymm f h₁ h₀).f₁ = (LinearEquiv.ofBijective f.f₁ h₁).symm := rfl

/-- The degree-`0` component of `chainMapSymm f h₁ h₀` is the inverse of `f.f₀`. -/
@[simp] public theorem chainMapSymm_f₀ (f : NaiveCotangent.ChainMap X Y)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Bijective f.f₀) :
    (chainMapSymm f h₁ h₀).f₀ = (LinearEquiv.ofBijective f.f₀ h₀).symm := rfl

/-- The inverse of a chain map bijective in both degrees is bijective in degree `1`. -/
public theorem bijective_chainMapSymm_f₁ (f : NaiveCotangent.ChainMap X Y)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Bijective f.f₀) :
    Function.Bijective (chainMapSymm f h₁ h₀).f₁ :=
  (LinearEquiv.ofBijective f.f₁ h₁).symm.bijective

/-- The inverse of a chain map bijective in both degrees is bijective in degree `0`. -/
public theorem bijective_chainMapSymm_f₀ (f : NaiveCotangent.ChainMap X Y)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Bijective f.f₀) :
    Function.Bijective (chainMapSymm f h₁ h₀).f₀ :=
  (LinearEquiv.ofBijective f.f₀ h₀).symm.bijective

end Invert

/-! ## Transporting the adic-limit comparison along a linear equivalence -/

section Transport

/-- **Bijectivity of `AdicCompletion.ofTensorProduct` only depends on the isomorphism class of
the module.**  Mathlib's criterion for a finite module over a Noetherian ring is stated for a
module in the ring's own universe; this transports it to any isomorphic module, in particular to
a finite module living in a higher universe. -/
public theorem bijective_ofTensorProduct_of_linearEquiv {R : Type*} [CommRing R] (K : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : Function.Bijective (AdicCompletion.ofTensorProduct K M)) :
    Function.Bijective (AdicCompletion.ofTensorProduct K N) := by
  have hnat := AdicCompletion.ofTensorProduct_naturality K (e : M →ₗ[R] N)
  have hbc : ∀ z, AdicCompletion.ofTensorProduct K N
      (LinearEquiv.baseChange R (AdicCompletion K R) M N e z) =
      AdicCompletion.map K (e : M →ₗ[R] N) (AdicCompletion.ofTensorProduct K M z) :=
    fun z => (LinearMap.congr_fun hnat z).symm
  have hcomp : (AdicCompletion.ofTensorProduct K N : _ → _) =
      (AdicCompletion.map K (e : M →ₗ[R] N)) ∘ (AdicCompletion.ofTensorProduct K M) ∘
        (LinearEquiv.baseChange R (AdicCompletion K R) M N e).symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, ← hbc,
      LinearEquiv.apply_symm_apply]
  rw [hcomp]
  exact ((AdicCompletion.congr K e).bijective).comp
    (h.comp (LinearEquiv.baseChange R (AdicCompletion K R) M N e).symm.bijective)

end Transport

/-! ## The degreewise adic limit of the naive cotangent complex of a presentation -/

section Limit

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B] {n : ℕ}
  (G : Algebra.Generators A B (Fin n))

omit [Algebra.FiniteType A B] in
/-- The conormal module `J / J²` of a presentation of an algebra over a Noetherian ring is a
finite `B`-module, `J` being an ideal of the Noetherian ring `A[x₁, …, xₙ]`. -/
private theorem finite_cotangent : Module.Finite B G.toExtension.Cotangent := by
  have : IsNoetherianRing G.toExtension.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin n) A))
  exact Algebra.Extension.Cotangent.finite (IsNoetherian.noetherian _)

include G in
/-- `lim NL(α)`: the degreewise `I`-adic completion of the naive cotangent complex of the
presentation `α`, as a two-term complex of `B^`-modules. -/
public def adicLimitTwoTerm : NaiveCotangent.TwoTerm (adicCompletionObj I (B := B)).carrier :=
  letI : Module (adicCompletionObj I (B := B)).carrier
      (AdicCompletion (I.map (algebraMap A B)) G.toExtension.Cotangent) :=
    inferInstanceAs (Module (adicCompletionAlgebra I (B := B)) _)
  letI : Module (adicCompletionObj I (B := B)).carrier
      (AdicCompletion (I.map (algebraMap A B)) (Fin n → B)) :=
    inferInstanceAs (Module (adicCompletionAlgebra I (B := B)) _)
  { X₁ := AdicCompletion (I.map (algebraMap A B)) G.toExtension.Cotangent
    X₀ := AdicCompletion (I.map (algebraMap A B)) (Fin n → B)
    d := AdicCompletion.map (I.map (algebraMap A B)) (presentationDifferential G) }

/-- The differential of `adicLimitTwoTerm I G` is the `I`-adic completion of the differential of
the naive cotangent complex of the presentation. -/
@[simp] public theorem adicLimitTwoTerm_d :
    (adicLimitTwoTerm I G).d =
      AdicCompletion.map (I.map (algebraMap A B)) (presentationDifferential G) := rfl

/-- The canonical comparison of complexes `NL(α) ⊗_B B^ → lim NL(α)`: in each degree it is the
canonical map from the base change of a module to its `I`-adic completion. -/
public def limitComparison :
    NaiveCotangent.ChainMap
      (baseChangedTwoTerm (adicCompletionObj I (B := B)).carrier (presentationDifferential G))
      (adicLimitTwoTerm I G) where
  f₁ := AdicCompletion.ofTensorProduct (I.map (algebraMap A B)) G.toExtension.Cotangent
  f₀ := AdicCompletion.ofTensorProduct (I.map (algebraMap A B)) (Fin n → B)
  comm :=
    AdicCompletion.ofTensorProduct_naturality (I.map (algebraMap A B))
      (presentationDifferential G)

/-- **Stacks 0GAF.** The comparison `NL(α) ⊗_B B^ → lim NL(α)` is bijective in degree `1`:
`J / J²` is a finite module over the Noetherian ring `B`, so its base change to `B^` is its
`I`-adic completion. -/
public theorem bijective_limitComparison_f₁ : Function.Bijective (limitComparison I G).f₁ := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Module.Finite B G.toExtension.Cotangent := finite_cotangent G
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' B G.toExtension.Cotangent
  let : Module.Finite B ((Fin k → B) ⧸ LinearMap.ker f) :=
    Module.Finite.of_surjective (LinearMap.ker f).mkQ (Submodule.mkQ_surjective _)
  exact bijective_ofTensorProduct_of_linearEquiv (I.map (algebraMap A B))
    (f.quotKerEquivOfSurjective hf)
    (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian
      (I.map (algebraMap A B)) ((Fin k → B) ⧸ LinearMap.ker f))

/-- **Stacks 0GAF.** The comparison `NL(α) ⊗_B B^ → lim NL(α)` is bijective in degree `0`:
`⨁ᵢ B dxᵢ` is a finite free module over the Noetherian ring `B`. -/
public theorem bijective_limitComparison_f₀ : Function.Bijective (limitComparison I G).f₀ := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian
    (I.map (algebraMap A B)) (Fin n → B)

/-- **Stacks 0GAF, the `lim` form of the first clause.** `lim NL(α) = NL(α) ⊗_B B^` as
complexes: the comparison is bijective in both degrees and commutes with the differentials. -/
@[stacks 0GAF "lim NL(α) = NL(α) ⊗_B B^ as complexes"]
public theorem bijective_limitComparison :
    Function.Bijective (limitComparison I G).f₁ ∧
      Function.Bijective (limitComparison I G).f₀ ∧
      (adicLimitTwoTerm I G).d ∘ₗ (limitComparison I G).f₁ =
        (limitComparison I G).f₀ ∘ₗ
          (baseChangedTwoTerm (adicCompletionObj I (B := B)).carrier
            (presentationDifferential G)).d :=
  ⟨bijective_limitComparison_f₁ I G, bijective_limitComparison_f₀ I G,
    (limitComparison I G).comm⟩

/-- The comparison of complexes `lim NL(α) → NL^∧_{B^/A}`: the inverse of
`Rig.limitComparison` followed by the comparison `Rig.completionComparison` of the first
clause of Stacks 0GAF. -/
public def limitCompletionComparison :
    NaiveCotangent.ChainMap (adicLimitTwoTerm I G) (completedComplex I G).twoTerm :=
  (completionComparison I G).comp
    (chainMapSymm (limitComparison I G) (bijective_limitComparison_f₁ I G)
      (bijective_limitComparison_f₀ I G))

/-- **Stacks 0GAF, first clause in its `lim` form.** `NL^∧_{B^/A} = lim NL(α) ⊗_B B^` as
complexes: the comparison from the degreewise `I`-adic completion of `NL(α)` to the completed
naive cotangent complex of the completed presentation is bijective in both degrees and commutes
with the differentials. -/
@[stacks 0GAF "NL^∧_{B^/A} = lim NL(α) ⊗_B B^ as complexes"]
public theorem bijective_limitCompletionComparison :
    Function.Bijective (limitCompletionComparison I G).f₁ ∧
      Function.Bijective (limitCompletionComparison I G).f₀ ∧
      (completedComplex I G).twoTerm.d ∘ₗ (limitCompletionComparison I G).f₁ =
        (limitCompletionComparison I G).f₀ ∘ₗ (adicLimitTwoTerm I G).d :=
  ⟨(bijective_completionComparison_f₁ I G).comp
      (bijective_chainMapSymm_f₁ (limitComparison I G) (bijective_limitComparison_f₁ I G)
        (bijective_limitComparison_f₀ I G)),
    (bijective_completionComparison_f₀ I G).comp
      (bijective_chainMapSymm_f₀ (limitComparison I G) (bijective_limitComparison_f₁ I G)
        (bijective_limitComparison_f₀ I G)),
    (limitCompletionComparison I G).comm⟩

end Limit

end Rig

end
