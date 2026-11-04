module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelIndependence
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsCompositeNaturality

/-!
# The naturality square of the degreewise composite, with each side at its own level

`Crystalline.tensorFormsLevelComposite_naturality` of
`ModuleDifferentials/LevelFormsCompositeNaturality.lean` carries **one** finite level `k` for
both of its sides: `hk : cmp.quotientSystem.cutoff + e = k` on the unprimed side and
`hk' : cmp'.quotientSystem.cutoff + e' = k` on the primed one.  That is exactly right for two
fixed rings, and it is what `Crystalline.completedDifferentialsLevelEquivAt` was introduced for.
It is not enough for a *family*: the cutoff of a `Crystalline.DifferentialsCompletionComparison`
is produced by a `Classical.choose`, so in a cosimplicial family it varies with the degree and no
single `k` serves every degree at once.  A degreewise family therefore has each of its terms at
its own level, and the square has to be applicable to two such terms.

This file restates the square with the two sides at **two independent levels** `k` and `k'`.  The
proof reads both sides at one common level `K` — which is what the original square asserts there
— and transports each horizontal back to its own level by
`Crystalline.tensorFormsLevelComposite_level_independent` of
`ModuleDifferentials/CompletionLevelIndependence.lean`.

## What the common level is, and why it is an argument

The common level is a *hypothesis*, not a weakening.  As a number it is free — `max k k'` serves,
both cutoffs being below it — but reading the two tensor products there needs `M` to be a module
over `Ê/(p)^K` and `M'` over `Ê'/(p)^K`, and an instance cannot be produced from the ones at `k`
and `k'`.  So `K` is supplied with its two module structures and scalar towers, which is what the
consumer has: the sections of a sheaf over a level object of [Stacks, Tag 07JN] are a module over
*every* level past `N + e` by restriction of scalars along the surjection, which is
`...SmallSite.levelSectionsModuleAt`.

Nothing else changes.  The two verticals are still arbitrary additive maps given only by what
they do to a pure tensor and to a tensor of a wedge, and no hypothesis relating the two
comparisons of [Stacks, Tag 07KK] is introduced.

## Main results

* `Crystalline.tensorFormsLevelComposite_naturality_of_levels` — **the naturality square of the
  degreewise composite with each side read at its own level.**

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved here.**  This is the square in
the shape the cosimplicial family of [Stacks, Tag 07LA] can consume; the family itself and the
isomorphism `ε` is not assembled.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

section CompositeTwoLevels


variable {A : Type u} [CommRing A]
variable {E B E' B' : Type*} [CommRing E] [CommRing B] [CommRing E'] [CommRing B']
  [Algebra A E] [Algebra A B] [Algebra A E'] [Algebra A B']
variable (Jenv : Ideal E) (deltaenv : DividedPowers Jenv)
  (Jenv' : Ideal E') (deltaenv' : DividedPowers Jenv') (p : ℕ)
variable (hpn : IsNilpotent (Ideal.Quotient.mk Jenv (p : E)))
  (hpn' : IsNilpotent (Ideal.Quotient.mk Jenv' (p : E')))
variable (cmp : DifferentialsCompletionComparison (A := A) Jenv deltaenv p hpn)
  (cmp' : DifferentialsCompletionComparison (A := A) Jenv' deltaenv' p hpn')
variable (c : ℕ)
variable (hcontained : DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c ≤
  DividedPowers.completionIdeal Jenv p hpn)
variable (hstable : (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1.IsSubDPIdeal
  (DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (hcontained' : DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c ≤
  DividedPowers.completionIdeal Jenv' p hpn')
variable (hstable' : (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1.IsSubDPIdeal
  (DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c))
variable (J : Ideal B) (delta : DividedPowers J) (J' : Ideal B') (delta' : DividedPowers J')
variable (f : B ≃ₐ[A] (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (hf : delta.IsDPMorphism
  (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f.toAlgHom.toRingHom)
variable (hJ : J.map f.toAlgHom.toRingHom =
  (DividedPowers.completionIdeal Jenv p hpn).map
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c)))
variable (f' : B' ≃ₐ[A] (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c))
variable (hf' : delta'.IsDPMorphism
  (completedLevelDividedPowers Jenv' deltaenv' p hpn' c hcontained' hstable')
  f'.toAlgHom.toRingHom)
variable (hJ' : J'.map f'.toAlgHom.toRingHom =
  (DividedPowers.completionIdeal Jenv' p hpn').map
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c)))
variable (e k e' k' eK eK' K : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k)
variable (hk' : cmp'.quotientSystem.cutoff + e' = k')
variable (hK : cmp.quotientSystem.cutoff + eK = K)
variable (hK' : cmp'.quotientSystem.cutoff + eK' = K)
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
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ K) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ K) M]
variable (hsm : ∀ (b : B) (m : M), b • m = f b • m)
variable (M' : Type*) [AddCommGroup M'] [Module B' M']
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') M']
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c) M']
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E')
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c) M']
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ k') M']
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E')
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ k') M']
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ K) M']
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E')
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ K) M']
variable (hsm' : ∀ (b : B') (m : M'), b • m = f' b • m)
variable (g : E →ₐ[A] E') (hg : deltaenv.IsDPMorphism deltaenv' g.toRingHom)
variable (u : B →ₐ[A] B') (hu : delta.IsDPMorphism delta' u.toRingHom)
variable (hcomm : f'.toAlgHom.comp u = (completedLevelAlgHom p c g).comp f.toAlgHom)

include hcomm hK hK'

/-- **The naturality square of the degreewise composite, with each side at its own level.**

```
M ⊗_B Ωⁱ_{B/A,δ} ───────▶ M ⊗_{Ê} ⋀ⁱ_{Ê} Ω̂_{E/A,δ_E}
       │ Φ                               │ Ψ
       ▼                                 ▼
M' ⊗_{B'} Ωⁱ_{B'/A,δ'} ──▶ M' ⊗_{Ê'} ⋀ⁱ_{Ê'} Ω̂_{E'/A,δ_{E'}}
```

This is `Crystalline.tensorFormsLevelComposite_naturality` with the single level `k` of that
statement split into two independent levels, `k` for the unprimed horizontal and `k'` for the
primed one, at the cost of a common level `K` carried as an argument together with the two module
structures reading the tensor products there.  The horizontals are
`Crystalline.tensorFormsLevelComposite` at those levels, and the two verticals are the same
arbitrary additive maps as in that statement, given only by their values on a pure tensor and on
a tensor of a wedge.

The proof is the original square at `K` with each horizontal transported to its own level by
`Crystalline.tensorFormsLevelComposite_level_independent`.  **No tag attribute is placed.** -/
theorem tensorFormsLevelComposite_naturality_of_levels (i : ℕ) (phi : M →+ M')
    (Phi : (M ⊗[B] dividedPowerDifferentialForms (A := A) delta i) →+
      (M' ⊗[B'] dividedPowerDifferentialForms (A := A) delta' i))
    (Psi : (M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p)
            (dividedPowerDifferentials (A := A) deltaenv)))) →+
      (M' ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E']
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E']^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p)
            (dividedPowerDifferentials (A := A) deltaenv')))))
    (hPhi : ∀ (m : M) (x : dividedPowerDifferentialForms (A := A) delta i),
      Phi (m ⊗ₜ[B] x) = phi m ⊗ₜ[B'] mapDifferentialFormsOfDPMorphism (A := A) (J := J)
        (delta := delta) delta' u hu i x)
    (hPsi : ∀ (m : M) (w : Fin i → AdicCompletion (DividedPowers.pAdicIdeal (A := E) p)
        (dividedPowerDifferentials (A := A) deltaenv)),
      Psi (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) i w) =
        phi m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') i
          fun j ↦ completionDifferentialsMapₛₗ Jenv deltaenv Jenv' deltaenv' p g hg (w j)) :
    Psi.comp (tensorFormsLevelComposite Jenv deltaenv p hpn cmp c hcontained hstable J delta f hf
        hJ e k hk M hsm i).toAddMonoidHom =
      (tensorFormsLevelComposite Jenv' deltaenv' p hpn' cmp' c hcontained' hstable' J' delta' f'
          hf' hJ' e' k' hk' M' hsm' i).toAddMonoidHom.comp Phi := by
  have hcommon := tensorFormsLevelComposite_naturality Jenv deltaenv Jenv' deltaenv' p hpn hpn'
    cmp cmp' c hcontained hstable hcontained' hstable' J delta J' delta' f hf hJ f' hf' hJ' eK eK'
    K hK hK' M hsm M' hsm' g hg u hu hcomm i phi Phi Psi hPhi hPsi
  have hlvl := tensorFormsLevelComposite_level_independent Jenv deltaenv p hpn cmp c hcontained
    hstable J delta f hf hJ eK K e k hK hk M hsm i
  have hlvl' := tensorFormsLevelComposite_level_independent Jenv' deltaenv' p hpn' cmp' c
    hcontained' hstable' J' delta' f' hf' hJ' eK' K e' k' hK' hk' M' hsm' i
  refine AddMonoidHom.ext fun z ↦ ?_
  exact ((congrArg Psi (DFunLike.congr_fun hlvl z).symm).trans
    (DFunLike.congr_fun hcommon z)).trans (DFunLike.congr_fun hlvl' (Phi z))

end CompositeTwoLevels

end Crystalline

end
