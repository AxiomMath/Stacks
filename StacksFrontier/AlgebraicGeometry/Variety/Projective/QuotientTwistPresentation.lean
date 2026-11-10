module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GlobalGenerationSpanningFamily
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelHyperplaneChain
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelRegularityInduction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGenerationUnconditional

/-!
# Quotients of `𝒪^{⊕ r}` on `ℙⁿ_k` with a given Hilbert polynomial are cokernels

Let `n ≥ 0`, `r ≥ 1` and let `P ∈ ℚ[t]`. The field step of the proof of Stacks 0DPA: there is an
integer `m ≥ 0`, depending only on `n`, `r` and `P`, such that for every field `k` and every
surjection `q : 𝒪^{⊕ r} ⟶ ℱ` of coherent modules on `ℙⁿ_k` where `ℱ` has Hilbert polynomial
`P`, the twist `q(m) : 𝒪(m)^{⊕ r} ⟶ ℱ(m)` is the cokernel of a map
`𝒪^{⊕ N} ⟶ 𝒪(m)^{⊕ r}`, with `N = χ(𝒪(m)^{⊕ r}) - P(m)`.

The source's proof: the kernel `𝒦` of `q` is `m`-regular for the `m` of Stacks 08AG, so `𝒦(m)` is
globally generated (Stacks 08A8) and has no higher cohomology (Stacks 08A6); hence
`dim_k H⁰(ℙⁿ_k, 𝒦(m)) = χ(𝒦(m)) = χ(𝒪(m)^{⊕ r}) - χ(ℱ(m)) = N`, and a basis of `H⁰(𝒦(m))` gives
a surjection `𝒪^{⊕ N} ⟶ 𝒦(m)`. The source twists this back down by `-m`; the statement here keeps
the twist by `m` on the target, which is the same presentation read after the twist.

## Main results

* `AlgebraicGeometry.exists_twist_presentation_of_hilbertPolynomial`: the field step of the proof
  of Stacks 0DPA.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-- The higher cohomology of `F(m)` vanishes when `F` is `m₀`-regular and `m₀ ≤ m`. -/
private theorem isZero_cohomologyOverField_projectiveTwist_of_isMRegular (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] {m₀ m : ℤ}
    (hF : IsMRegular k n F m₀) (hm : m₀ ≤ m) (i : ℕ) (hi : 0 < i) :
    IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (projectiveTwist n F m) i) := by
  rw [isZero_cohomologyOverField_iff_isZero_hgroup]
  by_cases hin : i ≤ n
  · simpa only [add_sub_cancel_right] using
      isMRegular_of_le k n F hF (show m₀ ≤ m + i by omega) i hi hin
  · have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent _
    exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) _ i (by omega)

/-- **The field step of the proof of Stacks 0DPA.** There is `m ≥ 0`, depending only on `n`, `r`
and `P`, such that for every field `k` and every surjection `q : 𝒪^{⊕ r} ⟶ ℱ` onto a coherent
module on `ℙⁿ_k` with Hilbert polynomial `P`, the twist `q(m)` is the cokernel of a morphism
`𝒪^{⊕ N} ⟶ 𝒪(m)^{⊕ r}` with `N = χ(𝒪(m)^{⊕ r}) - χ(ℱ(m))`. -/
theorem exists_twist_presentation_of_hilbertPolynomial (n r : ℕ)
    (P : Polynomial ℚ) :
    ∃ m : ℕ, ∀ (k : Type u) [Field k]
      (Q : (projectiveSpaceOverRing n (.of k)).Modules) [Q.IsCoherent]
      (q : freeModules k n r ⟶ Q) [Epi q],
      (∀ d : ℤ, (hilbertPolynomial k n Q d : ℚ) = P.eval (d : ℚ)) →
      ∃ (φ : freeModules k n
          (hilbertPolynomial k n (freeModules k n r) m - hilbertPolynomial k n Q m).toNat ⟶
            projectiveTwist n (freeModules k n r) m)
        (w : φ ≫ (twistFunctorModules k n m).map q = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ _ w)) := by
  obtain ⟨m₀, hm₀⟩ := exists_isMRegular_kernel_free_of_hilbertPolynomial.{u} n r P
  refine ⟨m₀.toNat, fun k _ Q _ q _ hP => ?_⟩
  have hm : m₀ ≤ ((m₀.toNat : ℕ) : ℤ) := Int.self_le_toNat m₀
  set m : ℤ := ((m₀.toNat : ℕ) : ℤ)
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  have : (kernel q).IsCoherent := CoherentAbelian.isCoherent_kernel q
  -- The twisted kernel sequence `0 ⟶ 𝒦(m) ⟶ 𝒪(m)^{⊕ r} ⟶ ℱ(m) ⟶ 0`.
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel q) }
  let T := S.map (twistFunctorModules k n m)
  have hT : T.ShortExact := hS.map_of_exact _
  have : T.X₁.IsCoherent := isCoherent_projectiveTwist n (kernel q) m
  have : T.X₂.IsCoherent := isCoherent_projectiveTwist n (freeModules k n r) m
  have : T.X₃.IsCoherent := isCoherent_projectiveTwist n Q m
  -- `N = dim_k H⁰(𝒦(m))`.
  have hadd := eulerCharacteristic_add_of_shortExact_of_finiteDimensional' k f hT
    (fun i _ => finiteDimensional_cohomologyOverField_of_isProper k f _ i)
    (fun i _ => finiteDimensional_cohomologyOverField_of_isProper k f _ i)
  have hK0 := hilbertPolynomial_eq_finrank_cohomologyOverField_zero k n (kernel q) m
    (isZero_cohomologyOverField_projectiveTwist_of_isMRegular k n _ (hm₀ k Q q hP) hm)
  rw [hilbertPolynomial_eq_eulerCharacteristic] at hK0
  have hN : (hilbertPolynomial k n (freeModules k n r) m - hilbertPolynomial k n Q m).toNat =
      Module.finrank k (cohomologyOverField k f (projectiveTwist n (kernel q) m) 0) := by
    rw [hilbertPolynomial_eq_eulerCharacteristic, hilbertPolynomial_eq_eulerCharacteristic]
    change (eulerCharacteristic k f T.X₂ - eulerCharacteristic k f T.X₃).toNat = _
    rw [hadd, add_sub_cancel_right]
    change (eulerCharacteristic k f (projectiveTwist n (kernel q) m)).toNat = _
    rw [hK0, Int.toNat_natCast]
  -- A basis of `Hom(𝒪, 𝒦(m))` gives a surjection `𝒪^{⊕ N} ⟶ 𝒦(m)`.
  let := Scheme.linearOver f
  have := globalSectionsOver_linearOver f
  let e := (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f
      (projectiveTwist n (kernel q) m)).trans
    (unitHomLinearEquivGlobalSections f (projectiveTwist n (kernel q) m)).symm
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (projectiveTwist n (kernel q) m) 0
  have := e.finiteDimensional
  let b := Module.finBasisOfFinrankEq k _ (hN.trans e.finrank_eq).symm
  have hepi : Epi (Sigma.desc (fun i => b i) :
      (∐ fun _ : Fin _ => Stacks.Ample.unitModule (projectiveSpaceOverRing n (.of k))) ⟶
        projectiveTwist n (kernel q) m) :=
    epi_sigmaDesc_of_span_eq_top (k := k)
      (isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_field k n (kernel q) m
        (isMRegular_of_le k n _ (hm₀ k Q q hP) hm)) (fun i => b i) b.span_eq
  let φ := Sigma.desc (fun i => b i) ≫ (twistFunctorModules k n m).map (kernel.ι q)
  have w : φ ≫ (twistFunctorModules k n m).map q = 0 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => (Sigma.desc fun i => b i) ≫ g) T.zero).trans comp_zero)
  exact ⟨φ, w, ⟨isCokernelEpiComp (hg := hepi) hT.gIsCokernel _ rfl⟩⟩

end AlgebraicGeometry
