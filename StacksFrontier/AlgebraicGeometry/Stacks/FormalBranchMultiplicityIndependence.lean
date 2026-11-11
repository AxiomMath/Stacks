module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FormalBranches
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.ComparisonAndExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingMorphism
public import StacksFrontier.RingTheory.MvPowerSeries.MinimalPrimesLength

/-!
# The multiplicity of a formal branch does not depend on the versal ring (Stacks 0DRC)

In the situation of **Stacks 0DQU**, let `x₀ : Spec k ⟶ 𝒳` be a point with `k` a field of finite
type over `S`. Stacks Definition 0DRC defines the multiplicity of a formal branch of `𝒳` through
`x₀` as the multiplicity of the corresponding irreducible component of `Spec A` for *any* choice
of versal ring `A` to `𝒳` at `x₀`, branches read off two versal rings `A`, `A'` being identified
by the procedure preceding **Stacks 0DRA**: after possibly swapping `A` and `A'` there is a
comparison `φ : A' → A ≅ A'[[t₁, …, t_r]]` compatible with the versal formal objects
(**Stacks 0DQX**, **Stacks 0DR1** part (1)), and a minimal prime `𝔭` of `A'` corresponds to the
minimal prime `φ(𝔭) A` of `A`. The definition makes sense because `Spec A'[[t]] → Spec A'` induces
a bijection on irreducible components preserving multiplicities, the proof the source omits
(`MvPowerSeries.minimalPrimesEquivOfRingEquiv`,
`MvPowerSeries.length_localization_minimalPrimesEquivOfRingEquiv`).

This file proves that well-definedness: the value `AlgebraicGeometry.Stack.formalBranchMultiplicity`
computed on one versal ring agrees with the value on any other along the identification of
branches, so the multiplicity is the source's notion, independent of the versal ring.

## Main definitions

* `AlgebraicGeometry.Stack.formalBranchesEquivOfRingEquiv`: the identification `𝔭 ↦ φ(𝔭) A` of
  the formal branches read off `A'` with those read off `A`, for any isomorphism
  `A ≅ A'[[t₁, …, t_r]]` with `φ : A' → A'[[t]] ≅ A`.

## Main results

* `AlgebraicGeometry.Stack.formalBranchMultiplicity_formalBranchesEquivOfRingEquiv`: the
  identification preserves multiplicities, whatever the isomorphism.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity_independent_of_realization`: **Stacks 0DRC**,
  for the comparison compatible with the versal formal objects used by the source.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity_independent`: **Stacks 0DRC**, for any two
  versal rings at `x₀`, over any presentations of `x₀`.

## References

* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DRA](https://stacks.math.columbia.edu/tag/0DRA)
* [Stacks Project, Tag 0DRC](https://stacks.math.columbia.edu/tag/0DRC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (D : VersalSituation.{u, w})
  {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k] [Algebra Λ k] [Algebra Λ' k]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
  (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
  (x₀ : D.𝒳.val.val.obj)
  (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
  (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite' : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
  (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
  (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
  (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A)
  (hA' : IsVersalRingAt D iΛ' hiΛ' x₀ hx₀' hfinite' A')

/-- **The identification of formal branches along a comparison.** For versal rings `A`, `A'` to
`𝒳` at `x₀` and an isomorphism `e : A ≅ A'[[t₁, …, t_r]]`, with `φ : A' → A'[[t]] ≅ A`, a formal
branch `𝔭` read off `A'` corresponds to the formal branch `φ(𝔭) A` read off `A`; the inverse is
the contraction `𝔮 ↦ φ⁻¹ 𝔮`. -/
def formalBranchesEquivOfRingEquiv {r : ℕ} (e : (A : Type u) ≃+* MvPowerSeries (Fin r) A') :
    formalBranches D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA' ≃
      formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA :=
  MvPowerSeries.minimalPrimesEquivOfRingEquiv e

/-- The identification of formal branches is extension along `φ : A' → A'[[t]] ≅ A`. -/
theorem coe_formalBranchesEquivOfRingEquiv {r : ℕ}
    (e : (A : Type u) ≃+* MvPowerSeries (Fin r) A')
    (P : formalBranches D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA') :
    (formalBranchesEquivOfRingEquiv D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A' hA hA'
        e P : Ideal A) = P.1.map (MvPowerSeries.ofRingEquivC e) :=
  rfl

/-- The inverse identification of formal branches is contraction along
`φ : A' → A'[[t]] ≅ A`. -/
theorem coe_formalBranchesEquivOfRingEquiv_symm {r : ℕ}
    (e : (A : Type u) ≃+* MvPowerSeries (Fin r) A')
    (Q : formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) :
    ((formalBranchesEquivOfRingEquiv D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A' hA hA'
        e).symm Q : Ideal A') = Q.1.comap (MvPowerSeries.ofRingEquivC e) :=
  rfl

/-- **The identification of formal branches preserves multiplicities.** For any isomorphism
`A ≅ A'[[t₁, …, t_r]]` of versal rings to `𝒳` at `x₀`, a formal branch read off `A'` and the
corresponding branch read off `A` have the same multiplicity. -/
theorem formalBranchMultiplicity_formalBranchesEquivOfRingEquiv {r : ℕ}
    (e : (A : Type u) ≃+* MvPowerSeries (Fin r) A')
    (P : formalBranches D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA') :
    formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA
        (formalBranchesEquivOfRingEquiv D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A' hA
          hA' e P).2 =
      formalBranchMultiplicity D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA' P.2 :=
  MvPowerSeries.length_localization_minimalPrimesEquivOfRingEquiv e ⟨P.1, P.2⟩

/-- **Stacks 0DRC, for any two versal rings.** Let `A` and `A'` be versal rings to `𝒳` at `x₀`,
for any two presentations of `x₀` over affine opens of `S`. After possibly swapping them there is
an isomorphism `A ≅ A'[[t₁, …, t_r]]` over `S` (Stacks 0DQX), and along the identification
`𝔭 ↦ φ(𝔭) A` of formal branches it induces, multiplicities agree. Hence the multiplicity of a
formal branch, `AlgebraicGeometry.Stack.formalBranchMultiplicity`, does not depend on the choice
of versal ring. -/
@[stacks 0DRC "the multiplicity is independent of the versal ring: for any two versal rings, \
the identification of branches along the comparison A ≅ A'[[t₁,…,t_r]] preserves it"]
theorem formalBranchMultiplicity_independent :
    (∃ r : ℕ, ∃ e : (A : Type u) ≃+* MvPowerSeries (Fin r) A',
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' (MvPowerSeries (Fin r) A'))) ≫ iΛ' ∧
      ∀ P, formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA
          (formalBranchesEquivOfRingEquiv D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A'
            hA hA' e P).2 =
        formalBranchMultiplicity D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA' P.2) ∨
    (∃ r : ℕ, ∃ e : (A' : Type u) ≃+* MvPowerSeries (Fin r) A,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPowerSeries (Fin r) A))) ≫ iΛ ∧
      ∀ P, formalBranchMultiplicity D iΛ' hiΛ' x₀ hx₀' hfinite' A' hA'
          (formalBranchesEquivOfRingEquiv D iΛ' hiΛ' iΛ hiΛ x₀ hx₀' hx₀ hfinite' hfinite A' A
            hA' hA e P).2 =
        formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA P.2) := by
  rcases versalRing_powerSeries_comparison D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A'
      hA hA' with ⟨r, e, he⟩ | ⟨r, e, he⟩
  · exact Or.inl ⟨r, e, he, formalBranchMultiplicity_formalBranchesEquivOfRingEquiv D iΛ hiΛ
      iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A' hA hA' e⟩
  · exact Or.inr ⟨r, e, he, formalBranchMultiplicity_formalBranchesEquivOfRingEquiv D iΛ' hiΛ'
      iΛ hiΛ x₀ hx₀' hx₀ hfinite' hfinite A' A hA' hA e⟩

/-- **Stacks 0DRC, along the comparison compatible with the versal formal objects.** Let `ξ`, `ξ'`
be versal formal objects at `x₀`, over the versal rings `A = ξ.base`, `A' = ξ'.base` and for any
two presentations of `x₀`, with realizations `y : Spec A ⟶ 𝒳` and `y' : Spec A' ⟶ 𝒳` (the
morphisms of Stacks 0DR1). After possibly swapping them there is an isomorphism
`e : A ≅ A'[[t₁, …, t_r]]` over `S` together with a morphism `y ⟶ y'` lying over
`Spec φ`, `φ : A' → A'[[t]] ≅ A` — the comparison of Stacks 0DR1 part (1) used by the source to
identify the formal branches read off `A` and `A'` — and along that identification multiplicities
agree. -/
@[stacks 0DRC "the multiplicity is independent of the versal ring, along the comparison \
A ≅ A'[[t₁,…,t_r]] compatible with the versal formal objects (0DR1 (1)) identifying the branches"]
theorem formalBranchMultiplicity_independent_of_realization
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered ξ')
    {hB : D.B.Contains (Spec (.of ξ.base))} {hB' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hB}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hB'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hB y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ξ').Realization hB' y' hy') :
    (∃ r : ℕ, ∃ e : (ξ.base : Type u) ≃+* MvPowerSeries (Fin r) ξ'.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' (MvPowerSeries (Fin r) ξ'.base))) ≫ iΛ' ∧
      (∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.ofRingEquivC e))) ∧
      ∀ P, formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩
          (formalBranchesEquivOfRingEquiv D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' ξ.base
            ξ'.base ⟨ξ, rfl, hξ⟩ ⟨ξ', rfl, hξ'⟩ e P).2 =
        formalBranchMultiplicity D iΛ' hiΛ' x₀ hx₀' hfinite' ξ'.base ⟨ξ', rfl, hξ'⟩ P.2) ∨
    (∃ r : ℕ, ∃ e : (ξ'.base : Type u) ≃+* MvPowerSeries (Fin r) ξ.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ'.base)) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPowerSeries (Fin r) ξ.base))) ≫ iΛ ∧
      (∃ m : y' ⟶ y, (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.ofRingEquivC e))) ∧
      ∀ P, formalBranchMultiplicity D iΛ' hiΛ' x₀ hx₀' hfinite' ξ'.base ⟨ξ', rfl, hξ'⟩
          (formalBranchesEquivOfRingEquiv D iΛ' hiΛ' iΛ hiΛ x₀ hx₀' hx₀ hfinite' hfinite ξ'.base
            ξ.base ⟨ξ', rfl, hξ'⟩ ⟨ξ, rfl, hξ⟩ e P).2 =
        formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩ P.2) := by
  rcases exists_powerSeries_comparison_realization D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite
      hfinite' ξ hξ ξ' hξ' Ry Ry' with ⟨r, e, he, hm⟩ | ⟨r, e, he, hm⟩
  · exact Or.inl ⟨r, e, he, hm, formalBranchMultiplicity_formalBranchesEquivOfRingEquiv D iΛ hiΛ
      iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' ξ.base ξ'.base ⟨ξ, rfl, hξ⟩ ⟨ξ', rfl, hξ'⟩ e⟩
  · exact Or.inr ⟨r, e, he, hm, formalBranchMultiplicity_formalBranchesEquivOfRingEquiv D iΛ'
      hiΛ' iΛ hiΛ x₀ hx₀' hx₀ hfinite' hfinite ξ'.base ξ.base ⟨ξ', rfl, hξ'⟩ ⟨ξ, rfl, hξ⟩ e⟩

end AlgebraicGeometry.Stack

end
