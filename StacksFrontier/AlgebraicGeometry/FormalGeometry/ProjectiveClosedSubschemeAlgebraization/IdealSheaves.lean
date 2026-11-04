module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# A cartesian system of closed subschemes, read through its ideal sheaves

Let `A` be a ring with an ideal `I`, let `f : X ⟶ Spec A` be a morphism, write
`Xₙ = X ×_{Spec A} Spec (A / I ^ (n + 1))` and `pₙ : Xₙ ⟶ X` for the projection, and let
`jₙ : Zₙ ⟶ Xₙ` be a system of closed immersions with cartesian squares over the transition maps
`Xₙ ⟶ X_{n+1}`. Composing with `pₙ` exhibits each `Zₙ` as a closed subscheme of `X`, cut out by
the ideal sheaf `Jₙ = ker (jₙ ≫ pₙ)`. This file records what the cartesian squares say about these
ideal sheaves, and conversely how a single closed subscheme `W` of `X` whose ideal sheaf `K`
satisfies `K + 𝓘 ^ (n + 1) = Jₙ`, with `𝓘 = I · 𝒪_X`, recovers the whole system by base change.

Everything here is formal: a closed immersion is determined by its ideal sheaf, a morphism into
a closed subscheme exists exactly when the ideal sheaf is killed
(`AlgebraicGeometry.IsClosedImmersion.lift`), and the kernel of `pₙ` is
`𝓘 ^ (n + 1)` (`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst`).

## Main results

* `AlgebraicGeometry.ker_pullback_fst_adicThickeningι` — the kernel of `Xₙ ⟶ X` is
  `𝓘 ^ (n + 1)`.
* `AlgebraicGeometry.ker_le_ker_comp_of_isPullback` — the ideal sheaf of the fibre product of two
  closed subschemes is at most the join of their ideal sheaves.
* `AlgebraicGeometry.ker_adicSystem_eq_sup` — `Jₙ = J_{n+1} ⊔ 𝓘 ^ (n + 1)`.
* `AlgebraicGeometry.isPullback_of_ker_eq_sup` — a closed subscheme of `X` whose ideal sheaf
  `K` satisfies `K ⊔ ker pₙ = ker (jₙ ≫ pₙ)` meets `Xₙ` in `Zₙ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow)

universe u

namespace AlgebraicGeometry

/-- The projection `X ×_{Spec A} Spec (A / I ^ (n + 1)) ⟶ X` is a closed immersion. -/
public instance isClosedImmersion_pullback_fst_adicThickeningι (A : Type u) [CommRing A]
    (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) :
    IsClosedImmersion (pullback.fst f (adicThickeningι A I n)) := by
  have : IsClosedImmersion (adicThickeningι A I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/-- **The ideal sheaf of `Xₙ` in `X` is `𝓘 ^ (n + 1)`**, where `𝓘 = I · 𝒪_X`. -/
public theorem ker_pullback_fst_adicThickeningι (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) :
    (pullback.fst f (adicThickeningι A I n)).ker = baseIdealSheaf A I f ^ (n + 1) := by
  rw [← baseIdealSheaf_pow, Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst]
  rfl

/-- **The ideal sheaf of a fibre product of closed subschemes is at most the join.** If `P` is
the fibre product of two closed immersions `a : Z₁ ⟶ X` and `b : Z₂ ⟶ X`, the ideal sheaf of
`P ⟶ X` is contained in `ker a ⊔ ker b`: the closed subscheme cut out by the join maps to both
factors, hence to `P`. -/
public theorem ker_le_ker_comp_of_isPullback {P Z₁ Z₂ X : Scheme.{u}} {u : P ⟶ Z₁} {v : P ⟶ Z₂}
    {a : Z₁ ⟶ X} {b : Z₂ ⟶ X} [IsClosedImmersion a] [IsClosedImmersion b]
    (h : IsPullback u v a b) : (u ≫ a).ker ≤ a.ker ⊔ b.ker := by
  let T := a.ker ⊔ b.ker
  have hT : T.subschemeι.ker = T := Scheme.IdealSheafData.ker_subschemeι T
  have hTa : a.ker ≤ T.subschemeι.ker := le_sup_left.trans_eq hT.symm
  have hTb : b.ker ≤ T.subschemeι.ker := le_sup_right.trans_eq hT.symm
  let la := IsClosedImmersion.lift a T.subschemeι hTa
  let lb := IsClosedImmersion.lift b T.subschemeι hTb
  have hw : la ≫ a = lb ≫ b := by
    rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac]
  have hm : h.lift la lb hw ≫ u ≫ a = T.subschemeι := by
    rw [← Category.assoc, h.lift_fst, IsClosedImmersion.lift_fac]
  calc (u ≫ a).ker ≤ (h.lift la lb hw ≫ u ≫ a).ker := Scheme.Hom.le_ker_comp _ _
    _ = T := by rw [hm, hT]

/-- **A closed subscheme of `X` cut out by `K` meets a closed subscheme `Y` in `Z`** when the
ideal sheaf of `Z` is `K ⊔ ker (Y ⟶ X)`: given closed immersions `i : Z ⟶ X`, `g : W ⟶ X`,
`p : Y ⟶ X` with `ker i = ker g ⊔ ker p`, and factorizations `k ≫ g = i`, `j ≫ p = i`, the square
formed by `k`, `j`, `g`, `p` is cartesian. -/
public theorem isPullback_of_ker_eq_sup {Z W Y X : Scheme.{u}} (i : Z ⟶ X) (g : W ⟶ X)
    (p : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion g] [IsClosedImmersion p]
    (k : Z ⟶ W) (j : Z ⟶ Y) (hk : k ≫ g = i) (hj : j ≫ p = i)
    (hker : i.ker = g.ker ⊔ p.ker) : IsPullback k j g p := by
  have hcomp : k ≫ g = j ≫ p := hk.trans hj.symm
  have hle (s : PullbackCone g p) : i.ker ≤ (s.snd ≫ p).ker := by
    rw [hker]
    refine sup_le ?_ (Scheme.Hom.le_ker_comp _ _)
    rw [← s.condition]
    exact Scheme.Hom.le_ker_comp _ _
  let lift (s : PullbackCone g p) : s.pt ⟶ Z := IsClosedImmersion.lift i (s.snd ≫ p) (hle s)
  have hfac (s : PullbackCone g p) : lift s ≫ i = s.snd ≫ p := IsClosedImmersion.lift_fac _ _ _
  have hfst (s : PullbackCone g p) : lift s ≫ k = s.fst := by
    apply (cancel_mono g).1
    rw [Category.assoc, hk, hfac, s.condition]
  have hsnd (s : PullbackCone g p) : lift s ≫ j = s.snd := by
    apply (cancel_mono p).1
    rw [Category.assoc, hj, hfac]
  have huniq (s : PullbackCone g p) (m : s.pt ⟶ Z) (_ : m ≫ k = s.fst) (hm₂ : m ≫ j = s.snd) :
      m = lift s := by
    apply (cancel_mono i).1
    rw [hfac, ← hj, ← Category.assoc, hm₂]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomp lift hfst hsnd huniq)

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The ideal sheaves of a cartesian system of closed subschemes.** In a system of closed
immersions `jₙ : Zₙ ⟶ Xₙ` with cartesian squares over the transition maps `Xₙ ⟶ X_{n+1}`, the
ideal sheaf `Jₙ` of `Zₙ` in `X` is `J_{n+1} ⊔ 𝓘 ^ (n + 1)`. -/
public theorem ker_adicSystem_eq_sup {Z : ℕ → Scheme.{u}} (j : ∀ n, Z n ⟶ adicBaseChange A I f n)
    (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n))
    (hclosed : ∀ n, IsClosedImmersion (j n)) (n : ℕ) :
    (j n ≫ pullback.fst f (adicThickeningι A I n)).ker =
      (j (n + 1) ≫ pullback.fst f (adicThickeningι A I (n + 1))).ker ⊔
        baseIdealSheaf A I f ^ (n + 1) := by
  have := hclosed n
  have := hclosed (n + 1)
  set p := pullback.fst f (adicThickeningι A I n)
  set p' := pullback.fst f (adicThickeningι A I (n + 1))
  have ht : t n ≫ j (n + 1) ≫ p' = j n ≫ p := by
    rw [← Category.assoc, (hcart n).w, Category.assoc, adicBaseChangeSucc_fst]
  rw [← ker_pullback_fst_adicThickeningι A I f n]
  refine le_antisymm ?_ (sup_le ?_ (Scheme.Hom.le_ker_comp _ _))
  · -- the square `Zₙ = Z_{n+1} ×_X Xₙ` is cartesian
    have hsq : IsPullback (adicBaseChangeSucc A I f n) (𝟙 _) p' p :=
      IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, adicBaseChangeSucc_fst]⟩
    have hP := (hcart n).paste_vert hsq
    rw [Category.comp_id] at hP
    rw [← ht]
    exact ker_le_ker_comp_of_isPullback hP
  · rw [← ht]
    exact Scheme.Hom.le_ker_comp _ _

end AlgebraicGeometry

end
