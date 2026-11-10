module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ProjectiveClosedSubschemeAlgebraization.Algebraize
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ProjectiveClosedSubschemeAlgebraization.IdealSheaves

/-!
# Algebraization of a formal closed subscheme of a projective scheme

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec (A / I ^ (n + 1))`, let `f : X ⟶ S` be projective and put `Xₙ = X ×_S Sₙ`. Given closed
immersions `jₙ : Zₙ ⟶ Xₙ` and maps `tₙ : Zₙ ⟶ Z_{n+1}` making every square

```
  Zₙ --tₙ--> Z_{n+1}
  |            |
  Xₙ -------> X_{n+1}
```

cartesian, there is a closed subscheme `W ⊆ X` with `Zₙ = W ×_S Sₙ` for every `n`, compatibly with
the maps to `X` and with the `tₙ`. This is [Stacks, Tag 0899] for a projective morphism, proved
here without hypotheses: `AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback`
carries the general statement for a separated morphism of finite type, conditional on two
consequences of Grothendieck's existence theorem, and for a projective `f` the existence theorem
itself is available unconditionally as
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`
([Stacks, Tag 0885]).

## The proof

The proof is the source's, run through ideal sheaves rather than through 09ZT. Write
`𝓘 = I · 𝒪_X`, so that `Xₙ` is the closed subscheme of `X` cut out by `𝓘 ^ (n + 1)`
(`AlgebraicGeometry.ker_pullback_fst_adicThickeningι`). Every `jₙ` is a closed immersion by
Stacks 0896 (`AlgebraicGeometry.isClosedImmersion_of_isPullback_adicBaseChangeSucc`), so `Zₙ` is a
closed subscheme of `X` with ideal sheaf `Jₙ`, and the cartesian squares say exactly that
`Jₙ = 𝓘 ^ (n + 1) + J_{n+1}` (`AlgebraicGeometry.ker_adicSystem_eq_sup`).

The structure sheaves `𝒪_X / Jₙ` then form a coherent adic system along `𝓘`; by Stacks 0885 it is
the completion of a coherent `𝒢`, the projections from the completion of `𝒪_X` come from an
epimorphism `𝒪_X ⟶ 𝒢`, and the scheme-theoretic support `K` of `𝒢` satisfies
`Jₙ = K + 𝓘 ^ (n + 1)` (`Stacks.Algebraization.exists_idealSheaf_sup_eq_of_isEquivalence`). So
the closed subscheme `W` cut out by `K` meets `Xₙ` in `Zₙ`
(`AlgebraicGeometry.isPullback_of_ker_eq_sup`), and pasting with the square `Xₙ = X ×_S Sₙ` gives
`Zₙ = W ×_S Sₙ`. Compatibility with the `tₙ` holds because `W ⟶ X` is a monomorphism.

## Main results

* `AlgebraicGeometry.exists_closedImmersion_algebraization_of_isProjective` — Stacks 0899 for a
  projective morphism.

## Implementation notes

Positive powers `Iⁿ` are indexed by `ℕ` through `n ↦ I ^ (n + 1)`, as in
`StacksFrontier.AlgebraicGeometry.Algebraization`, so the index `n` here is the source's `n + 1`.
Projectivity is clause (1) of Tag 01W8, `AlgebraicGeometry.IsProjective`, the hypothesis of the
existence theorem used; an H-projective morphism, such as projective space over `S`, is
projective by `AlgebraicGeometry.IsProjectiveMorphism.isProjective`. The source's hypothesis that
`Z₀` be proper over `S₀` is automatic here, `X` being proper over `S`.

## References

* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0896](https://stacks.math.columbia.edu/tag/0896)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0899, for a projective morphism.** Let `A` be a Noetherian ring complete
with respect to an ideal `I`, let `f : X ⟶ Spec A` be projective and write
`Xₙ = X ×_{Spec A} Spec (A / I ^ (n + 1))`. Let `jₙ : Zₙ ⟶ Xₙ` be a system of morphisms with
transition maps `tₙ : Zₙ ⟶ Z_{n+1}` making every square over `Xₙ ⟶ X_{n+1}` cartesian, with
`j 0` a closed immersion. Then there is a closed immersion `g : W ⟶ X` which recovers the system
by base change: each `Zₙ` is `W ×_{Spec A} Spec (A / I ^ (n + 1))` through maps `kₙ : Zₙ ⟶ W`,
the composite `Zₙ ⟶ W ⟶ X` is `jₙ` followed by `Xₙ ⟶ X`, and the `kₙ` are compatible with the
`tₙ`.

No hypothesis beyond the source's is made; the existence theorem the source invokes is
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`, and the
properness of `Z₀` over the base, which the source assumes, holds automatically. -/
public theorem exists_closedImmersion_algebraization_of_isProjective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : AlgebraicGeometry.IsProjective f)
    (Z : ℕ → Scheme.{u}) (j : ∀ n, Z n ⟶ adicBaseChange A I f n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n))
    (hclosed : IsClosedImmersion (j 0)) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (k : ∀ n, Z n ⟶ W),
      IsClosedImmersion g ∧
      (∀ n, IsPullback (k n) (j n ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
        (adicThickeningι A I n)) ∧
      (∀ n, k n ≫ g = j n ≫ pullback.fst f (adicThickeningι A I n)) ∧
      ∀ n, t n ≫ k (n + 1) = k n := by
  have hclosed_all : ∀ n, IsClosedImmersion (j n) :=
    isClosedImmersion_of_isPullback_adicBaseChangeSucc A I f j t hcart hclosed
  let : IsProper f := hf.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Stacks.Algebraization.completionFunctor X (baseIdealSheaf A I f)).IsEquivalence :=
    Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing A I f hf
  let p (n : ℕ) := pullback.fst f (adicThickeningι A I n)
  let c (n : ℕ) : Z n ⟶ X := j n ≫ p n
  have hc (n : ℕ) : IsClosedImmersion (c n) := by
    have := hclosed_all n
    infer_instance
  have hJ (n : ℕ) : (c n).ker = baseIdealSheaf A I f ^ (n + 1) ⊔ (c (n + 1)).ker := by
    rw [sup_comm]
    exact ker_adicSystem_eq_sup A I f j t hcart hclosed_all n
  obtain ⟨K, hK⟩ := Stacks.Algebraization.exists_idealSheaf_sup_eq_of_isEquivalence
    (baseIdealSheaf A I f) (fun n => (c n).ker) hJ
  let g := K.subschemeι
  have hKle (n : ℕ) : g.ker ≤ (c n).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hK n]
    exact le_sup_left
  let k (n : ℕ) : Z n ⟶ K.subscheme := IsClosedImmersion.lift g (c n) (hKle n)
  have hkg (n : ℕ) : k n ≫ g = c n := IsClosedImmersion.lift_fac _ _ _
  have hsq (n : ℕ) : IsPullback (k n) (j n) g (p n) := by
    have := hc n
    refine isPullback_of_ker_eq_sup (c n) g (p n) (k n) (j n) (hkg n) rfl ?_
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_pullback_fst_adicThickeningι, ← hK n]
  refine ⟨K.subscheme, g, k, inferInstance,
    fun n => (hsq n).paste_vert (IsPullback.of_hasPullback f (adicThickeningι A I n)), hkg,
    fun n => ?_⟩
  apply (cancel_mono g).1
  rw [Category.assoc, hkg (n + 1), hkg n]
  change t n ≫ j (n + 1) ≫ p (n + 1) = j n ≫ p n
  rw [← Category.assoc, (hcart n).w, Category.assoc, adicBaseChangeSucc_fst]

end AlgebraicGeometry

end
