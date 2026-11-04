module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelFormsNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FormsAlgEquivTensor
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.QuotientForms

/-!
# Three comparisons of tensored divided power differential forms, composed

Let `B̂` be the `p`-adic completion of a divided power envelope `E` over `A`, and let `B` be a
divided power `A`-algebra identified with a finite level `B̂/(p)^c` by an isomorphism `f`. For a
module `M` over `B`, over `B̂/(p)^c` and over `B̂`, the actions of `B` and of `B̂/(p)^c` agreeing
along `f`, this file composes the three comparisons of the proof of [Stacks, Tag 07LF]:

* `Crystalline.tensorFormsEquivOfAlgEquiv` crosses the isomorphism `f` of divided power rings over
  the base;
* `Crystalline.tensorFormsLevelEquiv` passes from the finite level `B̂/(p)^c` to `B̂` itself;
* `Crystalline.tensorFormsCompletionLevelEquivAt` replaces the universal divided power
  differential forms of `B̂` by the exterior power of the `p`-adic completion of the differentials
  of `E`, the shape [Stacks, Tag 07LA] is stated in.

The level `k` of the third comparison is `cmp.quotientSystem.cutoff + e` (the hypothesis `hk`),
and `M` also carries a module structure over `B̂/(p)^k`. The composite is additive and not
linear: the first comparison crosses a ring isomorphism and is only semilinear.

## Main definitions

* `Crystalline.completedLevelDividedPowers`: the quotient divided powers on the finite level
  `B̂/(p)^c` of the completed envelope.
* `Crystalline.tensorFormsLevelComposite`: the composite, an additive isomorphism

  `M ⊗_{B} Ωⁱ_{B/A,δ}  ≃+  M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{E/A,δ_E}`.

## Main results

* `Crystalline.tensorFormsLevelComposite_tmul`: its value on a pure tensor, as the three
  comparisons applied in turn.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

section LevelComposite

variable {A : Type u} {E : Type v} {B : Type w} [CommRing A] [CommRing E] [CommRing B]
  [Algebra A E] [Algebra A B]
variable (Jenv : Ideal E) (deltaenv : DividedPowers Jenv) (p : ℕ)
variable (hpn : IsNilpotent (Ideal.Quotient.mk Jenv (p : E)))
variable (cmp : DifferentialsCompletionComparison (A := A) Jenv deltaenv p hpn)
variable (c : ℕ)
variable (hcontained : DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c ≤
  DividedPowers.completionIdeal Jenv p hpn)
variable (hstable : (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1.IsSubDPIdeal
  (DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (J : Ideal B) (delta : DividedPowers J)

/-- **The finite level `B̂/(p)^c` of the completed envelope, with its quotient divided powers**:
the divided powers on the image of the completion ideal in `B̂/(p)^c`. -/
noncomputable def completedLevelDividedPowers :
    DividedPowers ((DividedPowers.completionIdeal Jenv p hpn).map
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))) :=
  DividedPowers.quotientDividedPowers (DividedPowers.completionIdeal Jenv p hpn)
    (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable

variable (f : B ≃ₐ[A] (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (hf : delta.IsDPMorphism
  (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f.toAlgHom.toRingHom)
variable (hJ : J.map f.toAlgHom.toRingHom =
  (DividedPowers.completionIdeal Jenv p hpn).map
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c)))
variable (e k : ℕ) (hk : cmp.quotientSystem.cutoff + e = k)
variable (M : Type*) [AddCommGroup M] [Module B M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]
variable (hsm : ∀ (b : B) (m : M), b • m = f b • m)

/-- **The three comparisons of the proof of [Stacks, Tag 07LF], composed.**

For a module `M` over the section ring `B`, over the finite level `B̂/(p)^c` and over `B̂`, with
the first two actions agreeing along the identification `f` of `B` with that level,

`M ⊗_B Ωⁱ_{B/A,δ}  ≃+  M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{E/A,δ_E}`.

It is `Crystalline.tensorFormsEquivOfAlgEquiv` at `f`, followed by
`Crystalline.tensorFormsLevelEquiv` at the level `c`, followed by
`Crystalline.tensorFormsCompletionLevelEquivAt` at the level `k`. -/
noncomputable def tensorFormsLevelComposite (i : ℕ) :
    M ⊗[B] dividedPowerDifferentialForms (A := A) delta i ≃+
      M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p)
            (dividedPowerDifferentials (A := A) deltaenv))) :=
  ((tensorFormsEquivOfAlgEquiv delta
          (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ hsm
          i).1.trans
        (tensorFormsLevelEquiv (DividedPowers.completionIdeal Jenv p hpn)
          (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable M
          i).toAddEquiv).trans
    (tensorFormsCompletionLevelEquivAt (A := A) Jenv deltaenv p hpn cmp e k hk M i).toAddEquiv

/-- **The value of the composite on a pure tensor**: the three comparisons applied in turn. -/
theorem tensorFormsLevelComposite_tmul (i : ℕ) (m : M)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    tensorFormsLevelComposite Jenv deltaenv p hpn cmp c hcontained hstable J delta f hf hJ e k
        hk M hsm i (m ⊗ₜ[B] x) =
      tensorFormsCompletionLevelEquivAt (A := A) Jenv deltaenv p hpn cmp e k hk M i
        (tensorFormsLevelEquiv (DividedPowers.completionIdeal Jenv p hpn)
          (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable M i
          (m ⊗ₜ mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
            (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable)
            f.toAlgHom hf i x)) :=
  congrArg
    (fun z ↦ tensorFormsCompletionLevelEquivAt (A := A) Jenv deltaenv p hpn cmp e k hk M i
      (tensorFormsLevelEquiv (DividedPowers.completionIdeal Jenv p hpn)
        (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable M i
        z))
    ((tensorFormsEquivOfAlgEquiv delta
      (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ hsm i).2 m x)

end LevelComposite

end Crystalline

end
