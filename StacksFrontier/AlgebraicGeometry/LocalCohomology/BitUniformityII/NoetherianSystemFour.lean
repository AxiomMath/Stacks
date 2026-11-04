module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.PolynomialSystemFour
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictSystemTwo
public import StacksFrontier.RingTheory.LocalCohomology.StrictProIsoProIso

/-!
# System (4) of Stacks 0GA5 over an arbitrary Noetherian ring

Let `P` be a Noetherian ring, `φ : P → A` a ring map to a Noetherian ring `A`, `J ⊆ P` an ideal
and `I = JA`. Stacks 0GA5 asserts that the system (4) `M ⊗ᴸ_P P/Jⁿ` in `D(A)` is pro-isomorphic
to the system (1) `M/IⁿM` ("because we can compare with Koszul complexes"). In fact the system
(4) is *strictly* pro-isomorphic to the system (2) `M ⊗ᴸ_A A/Iⁿ`, and hence, for a bounded
complex `M` of finite `A`-modules, to the system (1).

The comparison goes through the standard example of the remark. Choose generators
`g₁, …, g_r` of `J` and let `χ : P[x₁, …, x_r] → P` send `xᵢ` to `gᵢ`; it is surjective, hence
finite, and carries `(x₁, …, x_r)` onto `J`. By the finite case
(`Stacks.LocalCohomology.UniformityII.hasUniformInverses_extensionCounit_quotientSingleSystem`)
the system `P ⊗ᴸ_{P[x]} P[x]/(x)ⁿ` is strictly pro-isomorphic to `P/Jⁿ` in `D(P)`; applying
`M ⊗ᴸ_P -` and the change of rings along the composite `P[x] → P → A` identifies (4) with the
system (4) of the standard example for `P[x] → A`, which is strictly pro-isomorphic to (2)
(`Stacks.LocalCohomology.UniformityII.nonempty_proIso_polynomialSystemFour_systemTwo`).

## Main results

* `Stacks.LocalCohomology.UniformityII.nonempty_strictProIso_systemFour_systemTwo`: (4) is
  strictly pro-isomorphic to (2) for every Noetherian `P`.
* `Stacks.LocalCohomology.UniformityII.nonempty_strictProIso_systemFour_systemOne`: (4) is
  strictly pro-isomorphic to (1) for every Noetherian `P`, if `M` is a bounded complex of finite
  `A`-modules.
* `Stacks.LocalCohomology.UniformityII.nonempty_proIso_systemFour_systemOne`: **(4) is
  pro-isomorphic to (1)**, the statement of the source.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.InverseSequence

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.LocalCohomology.UniformityII

universe u

variable {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A)
  (M : CochainComplex (ModuleCat.{u} A) ℤ)

/-- **For every Noetherian `P`, the system (4) is strictly pro-isomorphic to the system (2).**
Let `φ : P → A` be a ring map of Noetherian rings, `J ⊆ P` an ideal and `I = JA`. Then the
inverse systems `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` and `n ↦ M ⊗ᴸ_A A/Iⁿ⁺¹` in `D(A)` are isomorphic in the strict
pro-category, for every complex `M` of `A`-modules. -/
theorem nonempty_strictProIso_systemFour_systemTwo [IsNoetherianRing P] [IsNoetherianRing A]
    (J : Ideal P) (I : Ideal A) (hI : I = J.map φ) :
    Nonempty (proObj (systemFour φ M J) ≅ proObj (systemTwo φ M I)) := by
  classical
  obtain ⟨r, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  let : Algebra P A := φ.toAlgebra
  let g : Fin r → A := fun i ↦ φ (gens i)
  let χ : MvPolynomial (Fin r) P →+* P := polyEval P gens
  let J₀ := MvPolynomial.idealOfVars (Fin r) P
  have hχ : χ.Finite := RingHom.Finite.of_surjective _ fun p ↦ ⟨MvPolynomial.C p, by simp [χ]⟩
  have hcomp : φ.comp χ = polyEval P g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [χ, g]
      rfl
    · intro i
      simp [χ, g]
  have hJ₀ : J = J₀.map χ := by
    show J = (MvPolynomial.idealOfVars (Fin r) P).map χ
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp, ← hgens]
    congr 2
    funext i
    simp [χ]
  have hIg : Ideal.span (Set.range g) = I := by
    rw [hI, ← hgens]
    show _ = Ideal.map φ (Ideal.span (Set.range gens))
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars χ
  let c : DerivedCategory.Q ⋙ D.functor ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} χ ⋙ DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor c
      (HomologicalComplex.quasiIso (ModuleCat.{u} (MvPolynomial (Fin r) P)) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  let S₀ := quotientSingleSystem J₀
  let T := changeOfRings φ M
  have hU : HasUniformInverses (Functor.whiskerLeft S₀ c ≫
      Functor.whiskerRight (extendQuotientSingleSystemIso χ J₀ J hJ₀).hom DerivedCategory.Q) :=
    (hasUniformInverses_extensionCounit_quotientSingleSystem χ hχ J₀ D.functor c).comp
      (HasUniformInverses.of_isIso _)
  have h₁ := isIso_proHom_of_hasUniformInverses _ (hU.whiskerRight T.F)
  let e : systemFour (polyEval P g) M J₀ ≅ (S₀ ⋙ DerivedCategory.Q ⋙ D.functor) ⋙ T.F :=
    Functor.isoWhiskerLeft (S₀ ⋙ DerivedCategory.Q)
      (changeOfRingsCompIso M χ φ (polyEval P g) hcomp)
  have h₂ := isIso_proHom_of_hasUniformInverses _ (HasUniformInverses.of_isIso e.hom)
  obtain ⟨e₃⟩ := nonempty_proIso_polynomialSystemFour_systemTwo P g M
  let e₄ : systemTwo (polyEval P g) M (Ideal.span (Set.range g)) ≅ systemTwo φ M I := by
    rw [hIg]
    exact Functor.isoWhiskerLeft (quotientSingleSystem I ⋙ DerivedCategory.Q)
      (changeOfRingsTensorIso M (polyEval P g) φ)
  have h₄ := isIso_proHom_of_hasUniformInverses _ (HasUniformInverses.of_isIso e₄.hom)
  exact ⟨(@asIso _ _ _ _ _ h₁).symm ≪≫ (@asIso _ _ _ _ _ h₂).symm ≪≫ e₃ ≪≫
    @asIso _ _ _ _ _ h₄⟩

/-- **If `P` is Noetherian, the system (4) is strictly pro-isomorphic to the system (1).**
Let `φ : P → A` be a ring map of Noetherian rings, `J ⊆ P` an ideal, `I = JA`, and `M` a
bounded complex of finite `A`-modules. Then the inverse system `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` in `D(A)` is
isomorphic, in the strict pro-category of `D(A)`, to the system `n ↦ M/Iⁿ⁺¹M`. An isomorphism
of the strict pro-category is in particular an isomorphism of pro-objects. -/
@[stacks 0GA5 "if `P` is Noetherian, the system (4) is strictly pro-isomorphic to the system (1)"]
theorem nonempty_strictProIso_systemFour_systemOne [IsNoetherianRing P] [IsNoetherianRing A]
    (J : Ideal P) (I : Ideal A) (hI : I = J.map φ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    Nonempty (proObj (systemFour φ M J) ≅
      proObj (Stacks.AdicSystem.DerivedReductionProIso.reductionComplexSystem I M ⋙
        DerivedCategory.Q)) := by
  obtain ⟨e⟩ := nonempty_strictProIso_systemFour_systemTwo φ M J I hI
  have h := isIso_proHom_of_hasUniformInverses _
    (hasUniformInverses_systemTwoToOne φ M I hMbounded hMfinite)
  exact ⟨e ≪≫ @asIso _ _ _ _ _ h⟩

/-- **If `P` is Noetherian, the system (4) is pro-isomorphic to the system (1).**
Let `φ : P → A` be a ring map of Noetherian rings, `J ⊆ P` an ideal, `I = JA`, and `M` a bounded
complex of finite `A`-modules. Then the inverse systems `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` and `n ↦ M/Iⁿ⁺¹M`
in `D(A)` are pro-isomorphic. -/
@[stacks 0GA5 "if `P` is Noetherian, the system (4) is pro-isomorphic to the system (1)"]
theorem nonempty_proIso_systemFour_systemOne [IsNoetherianRing P] [IsNoetherianRing A]
    (J : Ideal P) (I : Ideal A) (hI : I = J.map φ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    Nonempty (_root_.InverseSequence.ProIso (systemFour φ M J)
      (Stacks.AdicSystem.DerivedReductionProIso.reductionComplexSystem I M ⋙
        DerivedCategory.Q)) :=
  nonempty_proIso_of_nonempty_iso_proObj
    (nonempty_strictProIso_systemFour_systemOne φ M J I hI hMbounded hMfinite)

end Stacks.LocalCohomology.UniformityII

end
