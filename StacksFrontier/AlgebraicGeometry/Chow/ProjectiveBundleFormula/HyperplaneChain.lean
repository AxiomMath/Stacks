module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.IntegralModel

/-!
# Chains of coordinate hyperplanes

Let `π : P ⟶ U` be a morphism of schemes and `J₁, …, Jₙ` ideal sheaves on `P`. Cut `P` down by
them from the top: `P_n = P`, and `P_{j}` the closed subscheme of `P_{j+1}` cut out by the
inverse image of `J_{j+1}`. The sequence is a *hyperplane chain* of length `n` when each cut is a
relative effective Cartier divisor over `U` and the last one, `P_0 ⟶ U`, is an isomorphism. This
is the structure of `ℙⁿ ⟶ U` with `J_j` the zero scheme of the coordinate `T_{n-j}`: the zero
scheme of `T₀` is the hyperplane `ℙ^{n-1}`, on which `T_{k+1}` restricts to `T_k`
(`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Hyperplane`), and the
iterated intersection `V(T₀, …, T_{n-1})` is the section `[0 : ⋯ : 0 : 1]`.

Being a hyperplane chain is a statement about ideal sheaves only, so it is stable under every
base change, by inverse images of the ideal sheaves; relative effective Cartier divisors base
change to effective Cartier divisors (Stacks 056Q). It is the input of the computation of the
top Segre class on a projective bundle by a chain of regular sections.

## Main definitions

* `Stacks.Chow.IsHyperplaneChain`: the recursive structure.

## Main results

* `Stacks.Chow.IsHyperplaneChain.of_isPullback`: stability under base change.
* `Stacks.Chow.IsHyperplaneChain.congr`: only the ideals `J_j`, `j ≤ n`, matter.
* `Stacks.Chow.FreeTower.isHyperplaneChain_projectiveSpaceAtUniverse`: **the coordinate
  hyperplanes of `ℙⁿ_ℤ` form a hyperplane chain.**

## References

* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **A hyperplane chain of length `n`.** In length zero the projection is an isomorphism. In
length `n + 1` the ideal sheaf `J_{n+1}` is a relative effective Cartier divisor over the base,
and its closed subscheme, with the inverse images of the other ideal sheaves, is a hyperplane
chain of length `n`. -/
inductive IsHyperplaneChain : (n : ℕ) → {P U : Scheme.{u}} → (π : P ⟶ U) →
    (ℕ → P.IdealSheafData) → Prop
  | zero {P U : Scheme.{u}} (π : P ⟶ U) (J : ℕ → P.IdealSheafData) (h : IsIso π) :
      IsHyperplaneChain 0 π J
  | succ {P U : Scheme.{u}} (n : ℕ) (π : P ⟶ U) (J : ℕ → P.IdealSheafData)
      (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π (J (n + 1)))
      (h : IsHyperplaneChain n ((J (n + 1)).subschemeι ≫ π)
        (fun j => (J j).comap (J (n + 1)).subschemeι)) :
      IsHyperplaneChain (n + 1) π J

/-- Only the ideal sheaves `J_j` with `j ≤ n` enter a hyperplane chain of length `n`. -/
theorem IsHyperplaneChain.congr {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {J J' : ℕ → P.IdealSheafData} (h : IsHyperplaneChain n π J) (hJ : ∀ j ≤ n, J j = J' j) :
    IsHyperplaneChain n π J' := by
  induction h with
  | zero π J hπ => exact .zero π J' hπ
  | succ n π J hD _ ih =>
    rw [hJ (n + 1) le_rfl] at hD ih
    refine .succ n π J' hD (ih fun j hj => ?_)
    change (J j).comap _ = _
    rw [hJ j (by omega)]

/-- **Hyperplane chains are stable under base change.** In a cartesian square `P' = U' ×_U P`, a
hyperplane chain `π : P ⟶ U` base changes, by the inverse images of its ideal sheaves, to a
hyperplane chain `π' : P' ⟶ U'` of the same length. -/
theorem IsHyperplaneChain.of_isPullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {J : ℕ → P.IdealSheafData} (h : IsHyperplaneChain n π J) {P' U' : Scheme.{u}}
    {π' : P' ⟶ U'} {g' : P' ⟶ P} {g : U' ⟶ U} (hsq : IsPullback g' π' π g) :
    IsHyperplaneChain n π' (fun j => (J j).comap g') := by
  induction h generalizing P' U' with
  | zero π J hπ =>
    have := hπ
    exact .zero π' _ hsq.isIso_snd_of_isIso
  | @succ P U n π J hD _ ih =>
    set D := J (n + 1) with hDdef
    have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap g') := by
      have := hD.2
      rw [← hsq.flip.isoPullback_hom_snd, Scheme.IdealSheafData.comap_comp]
      exact Stacks.Divisors.isPullbackDefined_of_flat _ _
        (isEffectiveCartierDivisor_comap_pullback π g D hD.1)
    have hDsq : IsPullback (comapRestrict D g') ((D.comap g').subschemeι ≫ π')
        (D.subschemeι ≫ π) g :=
      (isPullback_comapRestrict D g').flip.paste_vert hsq
    have hrest := ih hDsq
    refine .succ n π' _ ⟨hcart, MorphismProperty.of_isPullback hDsq hD.2⟩ ?_
    convert hrest using 2 with j
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      comapRestrict_subschemeι]

/-- A hyperplane chain stays one after an isomorphism of the base. -/
theorem IsHyperplaneChain.comp_iso {n : ℕ} {P U U' : Scheme.{u}} {π : P ⟶ U}
    {J : ℕ → P.IdealSheafData} (h : IsHyperplaneChain n π J) (e : U ≅ U') :
    IsHyperplaneChain n (π ≫ e.hom) J := by
  have h' := h.of_isPullback (π' := π ≫ e.hom) (g' := 𝟙 P) (g := e.inv)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
  simpa [Scheme.IdealSheafData.comap_id] using h'

namespace FreeTower

open Stacks.ProjectiveSpaceModuli Stacks.ProjectiveFromSections
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.SectionsToProjectiveSpace

/-- The ideal sheaves of the coordinate hyperplane chain of `ℙⁿ_ℤ`: `J_j` is the zero scheme of
the coordinate `T_{n-j}`. -/
abbrev coordHyperplaneIdeal (n : ℕ) (j : ℕ) : (projectiveSpaceAtUniverse.{u} n).IdealSheafData :=
  Stacks.Divisors.zeroScheme _ (twistingSheafAtUniverse.{u} n)
    (coordGlobalSection.{u} n ⟨n - j, by omega⟩)

/-- On the hyperplane `V(T₀) ≅ ℙⁿ_ℤ` of `ℙ^{n+1}_ℤ`, the coordinate hyperplanes of `ℙ^{n+1}_ℤ`
restrict to those of `ℙⁿ_ℤ`. -/
theorem comap_coordHyperplaneIdeal_subschemeι (n j : ℕ) (hj : j ≤ n) :
    (coordHyperplaneIdeal.{u} (n + 1) j).comap (hyperplaneIdeal.{u} n).subschemeι =
      (coordHyperplaneIdeal.{u} n j).comap (hyperplaneZeroSchemeIso.{u} n).hom := by
  obtain ⟨β, hβ⟩ := exists_pullback_subschemeι_iso.{u} n
  have hk : (⟨n + 1 - j, by omega⟩ : Fin (n + 2)) = (⟨n - j, by omega⟩ : Fin (n + 1)).succ :=
    Fin.ext (by simp; omega)
  rw [coordHyperplaneIdeal, coordHyperplaneIdeal, ← Stacks.Divisors.zeroScheme_pullback,
    ← Stacks.Divisors.zeroScheme_pullback, hk]
  exact AlgebraicGeometry.zeroScheme_eq_of_iso β (hβ _)

/-- **The coordinate hyperplanes of `ℙⁿ_ℤ` form a hyperplane chain**: cutting by
`T₀, T₁, …, T_{n-1}` in turn, each cut is the hyperplane `V(T₀)` of a projective space of one
dimension less, a relative effective Cartier divisor over `Spec ℤ`, and what remains is the
point `[0 : ⋯ : 0 : 1]`. -/
theorem isHyperplaneChain_projectiveSpaceAtUniverse : ∀ n : ℕ,
    IsHyperplaneChain n (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (coordHyperplaneIdeal.{u} n)
  | 0 => .zero _ _ Stacks.DeRham.isIso_terminalFrom_projectiveSpaceAtUniverse_of_zero.{u}
  | n + 1 => by
    have ih := isHyperplaneChain_projectiveSpaceAtUniverse n
    set e := hyperplaneZeroSchemeIso.{u} n
    have hD : coordHyperplaneIdeal.{u} (n + 1) (n + 1) = hyperplaneIdeal.{u} n := by
      simp only [coordHyperplaneIdeal, hyperplaneIdeal, Nat.sub_self]
      rfl
    have he : e.hom ≫ terminal.from (projectiveSpaceAtUniverse.{u} n) =
        (hyperplaneIdeal.{u} n).subschemeι ≫
          terminal.from (projectiveSpaceAtUniverse.{u} (n + 1)) := terminal.hom_ext _ _
    have hflat : Flat ((hyperplaneIdeal.{u} n).subschemeι ≫
        terminal.from (projectiveSpaceAtUniverse.{u} (n + 1))) := by
      rw [← he]; infer_instance
    refine .succ n _ _ ?_ ?_
    · rw [hD]
      exact ⟨isEffectiveCartierDivisor_hyperplaneIdeal n, hflat⟩
    · have hsq : IsPullback e.hom ((hyperplaneIdeal.{u} n).subschemeι ≫
          terminal.from (projectiveSpaceAtUniverse.{u} (n + 1)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) (𝟙 _) :=
        IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, he]⟩
      have h' := ih.of_isPullback hsq
      rw [hD]
      exact h'.congr fun j hj => (comap_coordHyperplaneIdeal_subschemeι n j hj).symm

end FreeTower

end Stacks.Chow

end
