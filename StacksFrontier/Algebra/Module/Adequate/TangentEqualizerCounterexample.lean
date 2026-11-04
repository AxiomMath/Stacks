module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.Algebra.Module.Adequate.Tangent

/-!
# The free module-valued functor does not preserve the square-zero equalizer

Fix a ring `A`, an `A`-algebra `B` and a short exact sequence `0 → N₁ → N → N₂ → 0` of
`B`-modules.  Write `h(C) = Mor_A(B[N], C)` and `h₁`, `h₂` for the analogous functors on
`B[N₁]` and `B[N₂]`.  Then `h₂ → h ⇉ h₁` is an equalizer diagram of set-valued functors:
the two maps `p, q : h → h₁` are precomposition with the two maps `B[N₁] → B[N]` induced
by `0 : N₁ → N` and by `N₁ → N`, and `f : B[N] → C` satisfies `p f = q f` exactly when
`f` kills `N₁`, that is, exactly when `f` factors through `B[N₂]`.

The usual argument for right exactness of the tangent functor of an *injective*
module-valued functor asserts that the free module-valued functor
`O_h(C) = ⨁_{h(C)} C` turns this into an equalizer diagram `O_{h₂} → O_h ⇉ O_{h₁}` of
module-valued functors.  The step it uses is the claim that if `ξ = ∑ cᵢ · fᵢ` lies in
`O_h(C)` and `p ξ = q ξ`, then every `fᵢ` kills `N₁`.

**That claim is false, and this file refutes it.**  The free module functor identifies
basis elements, so coefficients can cancel: if `p` and `q` identify two *distinct*
elements `f₁ ≠ f₂` of `h(C)` and also agree on each of them, then `ξ = f₁ - f₂` lies in
the kernel of `p - q` while neither `f₁` nor `f₂` factors through `B[N₂]`.

The witness is as small as possible.  Take `A = B = ℚ`, `N = ℚ × ℚ`, `N₁ = ℚ × 0`,
`N₂ = N / N₁ ≅ ℚ`, and `C = B[N₂] = ℚ[ε]/(ε²)`.  The two maps `B[N] → C` are
`(b, (m, n)) ↦ (b, m)` and `(b, (m, n)) ↦ (b, m + n)`.  They agree on `B[N₁]`, they agree
after `N₁` is killed, they are distinct, and neither of them kills `N₁`.

## Main results

* `AdequateFunctor.TangentEqualizer.hom₁_comp_incl_eq`,
  `AdequateFunctor.TangentEqualizer.hom₁_comp_zero_eq`,
  `AdequateFunctor.TangentEqualizer.hom₁_ne_hom₂`,
  `AdequateFunctor.TangentEqualizer.hom₁_comp_incl_ne_hom₁_comp_zero` and
  `AdequateFunctor.TangentEqualizer.hom₁_notMem_range_comp_quot`: the properties of the
  witness.
* `AdequateFunctor.TangentEqualizer.free_not_equalizer`: an element of `O_h(C)` on which
  the two maps to `O_{h₁}(C)` agree and which is not in the image of `O_{h₂}(C)`.

## References

* [Stacks Project, Tag 06ZA](https://stacks.math.columbia.edu/tag/06ZA)
-/

@[expose] public section

namespace AdequateFunctor.TangentEqualizer

open CategoryTheory

/-- The pair `(B, N) = (ℚ, ℚ × ℚ)`. -/
abbrev pairN : AlgebraModulePair.{0} ℚ := { algebra := ℚ, module := ℚ × ℚ }

/-- The pair `(B, ℚ)`, used for `(B, N₁)`, for `(B, N₂)` and for the target algebra. -/
abbrev pairOne : AlgebraModulePair.{0} ℚ := { algebra := ℚ, module := ℚ }

/-- A `ℚ`-linear map `ℚ × ℚ → ℚ`, read as a morphism of algebra-module pairs over the
identity of `ℚ`. -/
def ofLinearDown (g : (ℚ × ℚ) →ₗ[ℚ] ℚ) : pairN ⟶ pairOne :=
  { base := AlgHom.id ℚ ℚ, linear := g }

/-- A `ℚ`-linear map `ℚ → ℚ × ℚ`, read as a morphism of algebra-module pairs over the
identity of `ℚ`. -/
def ofLinearUp (g : ℚ →ₗ[ℚ] ℚ × ℚ) : pairOne ⟶ pairN :=
  { base := AlgHom.id ℚ ℚ, linear := g }

/-- `B[N₁] → B[N]`, induced by the inclusion `N₁ = ℚ × 0 → N = ℚ × ℚ`. -/
noncomputable def inclHom :
    squareZeroAlgebra ℚ pairOne →ₐ[ℚ] squareZeroAlgebra ℚ pairN :=
  squareZeroMap ℚ (ofLinearUp (LinearMap.inl ℚ ℚ ℚ))

/-- `B[N₁] → B[N]`, induced by the zero map `N₁ → N`. -/
noncomputable def zeroHom :
    squareZeroAlgebra ℚ pairOne →ₐ[ℚ] squareZeroAlgebra ℚ pairN :=
  squareZeroMap ℚ (ofLinearUp 0)

/-- `B[N] → B[N₂]`, induced by the quotient map `N → N / N₁ ≅ ℚ`. -/
noncomputable def quotHom :
    squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne :=
  squareZeroMap ℚ (ofLinearDown (LinearMap.snd ℚ ℚ ℚ))

/-- The first of the two coinciding elements of `h(C)`: `(b, (m, n)) ↦ (b, m)`. -/
noncomputable def hom₁ :
    squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne :=
  squareZeroMap ℚ (ofLinearDown (LinearMap.fst ℚ ℚ ℚ))

/-- The second of the two coinciding elements of `h(C)`: `(b, (m, n)) ↦ (b, m + n)`. -/
noncomputable def hom₂ :
    squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne :=
  squareZeroMap ℚ (ofLinearDown (LinearMap.fst ℚ ℚ ℚ + LinearMap.snd ℚ ℚ ℚ))

/-- `q f₁ = q f₂`: the two maps agree on `B[N₁]`. -/
lemma hom₁_comp_incl_eq : hom₁.comp inclHom = hom₂.comp inclHom := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext rfl ?_
  show x.snd = x.snd + 0
  exact (add_zero _).symm

/-- `p f₁ = p f₂`: the two maps agree after `N₁` is killed. -/
lemma hom₁_comp_zero_eq : hom₁.comp zeroHom = hom₂.comp zeroHom := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext rfl ?_
  show (0 : ℚ) = 0 + 0
  exact (add_zero _).symm

/-- Two maps differ if some function of their values at a point differs. -/
private theorem ne_of_apply_ne {F α β γ : Type*} [FunLike F α β] {f g : F} (s : β → γ) (x : α)
    (h : s (f x) ≠ s (g x)) : f ≠ g :=
  fun e => h (by rw [e])

/-- The two maps are nevertheless distinct. -/
lemma hom₁_ne_hom₂ : hom₁ ≠ hom₂ :=
  ne_of_apply_ne TrivSqZeroExt.snd ((0 : ℚ), ((0 : ℚ), (1 : ℚ))) (by change (0 : ℚ) ≠ 0 + 1; simp)

/-- `f₁` is not in the equalizer: it does not kill `N₁`. -/
lemma hom₁_comp_incl_ne_hom₁_comp_zero : hom₁.comp inclHom ≠ hom₁.comp zeroHom :=
  ne_of_apply_ne TrivSqZeroExt.snd ((0 : ℚ), (1 : ℚ)) (by change (1 : ℚ) ≠ 0; simp)

/-- Equivalently, `f₁` does not factor through `B[N₂]`, so it is not in the image of
`h₂(C) → h(C)`. -/
lemma hom₁_notMem_range_comp_quot :
    hom₁ ∉ Set.range
      (fun g : squareZeroAlgebra ℚ pairOne →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
        g.comp quotHom) := by
  rintro ⟨g, hg⟩
  have h1 : TrivSqZeroExt.snd (g (0 : squareZeroAlgebra ℚ pairOne)) = (1 : ℚ) :=
    congrArg
      (fun k : squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
        TrivSqZeroExt.snd (k ((0 : ℚ), ((1 : ℚ), (0 : ℚ))))) hg
  rw [map_zero] at h1
  exact zero_ne_one (show (0 : ℚ) = 1 from h1)

/-- **The free module-valued functor does not preserve the equalizer `h₂ → h ⇉ h₁`.**
At the algebra `C = ℚ[ε]/(ε²)` there is an element of `O_h(C) = ⨁_{h(C)} C` on which the
two induced maps to `O_{h₁}(C)` agree and which is not in the image of `O_{h₂}(C)`.  So
the step of the Stacks proof of Tag 06ZA that produces a coequalizer
`I(B[N₁]) ⇉ I(B[N]) → I(B[N₂])` out of injectivity of `I` is not available. -/
theorem free_not_equalizer :
    ∃ ξ : (squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne) →₀
        squareZeroAlgebra ℚ pairOne,
      Finsupp.mapDomain
            (fun f : squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
              f.comp inclHom) ξ =
          Finsupp.mapDomain
            (fun f : squareZeroAlgebra ℚ pairN →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
              f.comp zeroHom) ξ ∧
        ξ ∉ Set.range (Finsupp.mapDomain
          (M := squareZeroAlgebra ℚ pairOne)
          (fun g : squareZeroAlgebra ℚ pairOne →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
            g.comp quotHom)) := by
  classical
  refine ⟨Finsupp.single hom₁ 1 - Finsupp.single hom₂ 1, ?_, ?_⟩
  · rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      hom₁_comp_incl_eq, hom₁_comp_zero_eq, sub_self, sub_self]
  · rintro ⟨η, hη⟩
    have hzero : Finsupp.mapDomain
        (fun g : squareZeroAlgebra ℚ pairOne →ₐ[ℚ] squareZeroAlgebra ℚ pairOne =>
          g.comp quotHom) η hom₁ = 0 :=
      Finsupp.mapDomain_of_notMem_range η hom₁ hom₁_notMem_range_comp_quot
    rw [hη, Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hom₁_ne_hom₂, sub_zero] at hzero
    exact one_ne_zero (show (1 : ℚ) = 0 from congrArg TrivSqZeroExt.fst hzero)

end AdequateFunctor.TangentEqualizer
