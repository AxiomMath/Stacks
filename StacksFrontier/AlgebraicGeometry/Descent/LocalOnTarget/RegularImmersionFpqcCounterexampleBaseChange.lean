module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexampleMorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# The base change of the counterexample morphism to Stacks tag 0694, identified

`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexampleMorphism`
constructs the morphism `f : ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ` of the counterexample to the unconditional
form of Stacks tag 0694 and proves it is not an immersion. This file identifies its base change
along the one-member fpqc covering `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`.

The identification is that the first projection of the base change is an *isomorphism*: because
`(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`, the `p`-th member of the family is unchanged by the base change, so
the square

```
∐ₚ Spec 𝔽ₚ ------ h ------> Spec (∏ₚ ℤₚ)
    |                            |
   𝟙                             g
    v                            v
∐ₚ Spec 𝔽ₚ ------ f ------> Spec ℤ
```

is cartesian, where `h` is the coproduct of the residue maps `∏ₚ ℤₚ ⟶ 𝔽ₚ`.

## Main results

* `Stacks.Descent.subsingleton_ringHom_padicIntProd`: for a ring `R` in which the prime `p`
  vanishes, there is at most one ring homomorphism `∏ₚ ℤₚ →+* R`. Any such map sends `p` to `0`,
  so it factors through `(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`, and a ring homomorphism out of `ZMod p` is
  unique.
* `Stacks.Descent.hom_eq_of_hom_specZMod`: hence a scheme admitting a morphism to `Spec 𝔽ₚ`
  admits at most one morphism to `Spec (∏ₚ ℤₚ)`.
* `Stacks.Descent.hom_eq_of_hom_sigmaSpecZMod`: the same for a scheme admitting a morphism to
  `∐ₚ Spec 𝔽ₚ`, by gluing over the open cover pulled back from the coproduct inclusions.
* `Stacks.Descent.isPullback_counterexampleBaseChange`: the square above is cartesian. This
  replaces the general van Kampen property of infinite coproducts of schemes, which the
  identification of a base change along a coproduct would otherwise need.
* `Stacks.Descent.counterexampleBaseChangeHom_eq`: `h` factors as the coproduct of the closed
  immersions `Spec 𝔽ₚ ⟶ Spec ℤₚ` followed by the open immersion
  `AlgebraicGeometry.sigmaSpec`, which is the clopen decomposition of `Spec (∏ₚ ℤₚ)` by the
  idempotents of its factors.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Definition 35.22.1 (Tag 02KO)](https://stacks.math.columbia.edu/tag/02KO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Descent

/-! ### Uniqueness of ring maps out of `∏ₚ ℤₚ` in characteristic `p` -/

/-- **There is at most one ring homomorphism `∏ₚ ℤₚ →+* R` when `p` vanishes in `R`.** Such a
homomorphism sends the element `p` to `p = 0`, hence factors through
`(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`, and a ring homomorphism out of `ZMod p` is unique. -/
theorem subsingleton_ringHom_padicIntProd (p : Nat.Primes) {R : Type*} [CommRing R]
    (hp : ((p : ℕ) : R) = 0) :
    Subsingleton ((∀ q : Nat.Primes, ℤ_[q]) →+* R) := by
  refine ⟨fun ψ₁ ψ₂ => ?_⟩
  have hker : ∀ ψ : (∀ q : Nat.Primes, ℤ_[q]) →+* R,
      ∀ a ∈ Ideal.span {((p : ℕ) : ∀ q : Nat.Primes, ℤ_[q])}, ψ a = 0 := by
    intro ψ a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [map_natCast, hp]
  have hq : ∀ χ₁ χ₂ : ((∀ q : Nat.Primes, ℤ_[q]) ⧸
      Ideal.span {((p : ℕ) : ∀ q : Nat.Primes, ℤ_[q])}) →+* R, χ₁ = χ₂ := by
    intro χ₁ χ₂
    have h := RingHom.ext_zmod
      (χ₁.comp (padicIntProdQuotEquiv p).symm.toRingHom)
      (χ₂.comp (padicIntProdQuotEquiv p).symm.toRingHom)
    refine RingHom.ext fun x => ?_
    have h2 := RingHom.congr_fun h (padicIntProdQuotEquiv p x)
    simpa using h2
  have hlift : ∀ ψ : (∀ q : Nat.Primes, ℤ_[q]) →+* R,
      ψ = (Ideal.Quotient.lift _ ψ (hker ψ)).comp (Ideal.Quotient.mk _) := fun ψ => rfl
  exact (hlift ψ₁).trans ((congrArg (·.comp (Ideal.Quotient.mk _)) (hq _ _)).trans (hlift ψ₂).symm)

/-- A scheme admitting a morphism to `Spec 𝔽ₚ` has `p = 0` in its ring of global sections. -/
theorem natCast_eq_zero_of_hom_specZMod (p : Nat.Primes) {T : Scheme.{0}}
    (k : T ⟶ Spec (CommRingCat.of (ZMod p))) : ((p : ℕ) : Γ(T, ⊤)) = 0 := by
  have h := map_natCast
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod (p : ℕ)))).inv ≫ Scheme.Γ.map k.op).hom (p : ℕ)
  rw [ZMod.natCast_self] at h
  exact h.symm.trans (map_zero _)

/-- **A scheme of characteristic `p` admits at most one morphism to `Spec (∏ₚ ℤₚ)`.** -/
theorem hom_eq_of_hom_specZMod (p : Nat.Primes) {T : Scheme.{0}}
    (k : T ⟶ Spec (CommRingCat.of (ZMod p)))
    (a b : T ⟶ Spec (CommRingCat.of (∀ q : Nat.Primes, ℤ_[q]))) : a = b :=
  AlgebraicGeometry.ext_to_Spec (CommRingCat.hom_ext
    ((subsingleton_ringHom_padicIntProd p (natCast_eq_zero_of_hom_specZMod p k)).elim _ _))

/-- **A scheme admitting a morphism to `∐ₚ Spec 𝔽ₚ` admits at most one morphism to
`Spec (∏ₚ ℤₚ)`.** The coproduct inclusions pull back to an open cover of the scheme, and on each
member the previous lemma applies. -/
theorem hom_eq_of_hom_sigmaSpecZMod {T : Scheme.{0}}
    (t : T ⟶ ∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p)))
    (a b : T ⟶ Spec (CommRingCat.of (∀ q : Nat.Primes, ℤ_[q]))) : a = b := by
  refine Scheme.Cover.hom_ext
    ((sigmaOpenCover fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))).pullback₁ t) a b
    fun p => hom_eq_of_hom_specZMod p (Scheme.Cover.pullbackHom _ t p) _ _

/-! ### The base change of the counterexample morphism -/

/-- The one-member fpqc covering of the counterexample: `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`. -/
noncomputable def counterexampleCover :
    Spec (CommRingCat.of (∀ q : Nat.Primes, ℤ_[q])) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (∀ q : Nat.Primes, ℤ_[q])))

/-- The base change of `Stacks.Descent.counterexampleHom` along
`Stacks.Descent.counterexampleCover`: the coproduct over the primes of the closed immersions
`Spec 𝔽ₚ ⟶ Spec (∏ₚ ℤₚ)` cut out by the `p`-th residue map. -/
noncomputable def counterexampleBaseChangeHom :
    (∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))) ⟶
      Spec (CommRingCat.of (∀ q : Nat.Primes, ℤ_[q])) :=
  Sigma.desc fun p => Spec.map (CommRingCat.ofHom (padicIntProdResidue p))

/-- The base change morphism lies over the counterexample morphism: the `p`-th residue map of
`∏ₚ ℤₚ` restricts on `ℤ` to the reduction `ℤ ⟶ 𝔽ₚ`, there being only one ring homomorphism
`ℤ →+* 𝔽ₚ`. -/
theorem counterexampleBaseChangeHom_comp :
    counterexampleBaseChangeHom ≫ counterexampleCover = counterexampleHom := by
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [← Category.assoc, counterexampleBaseChangeHom, Sigma.ι_comp_desc, counterexampleCover,
    ← Spec.map_comp, counterexampleHom, Sigma.ι_comp_desc, primeResidueHom]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_int _ _)

/-- **The base change of the counterexample morphism to Stacks tag 0694 is the morphism itself.**
The square whose left leg is the identity is cartesian: the `p`-th member `Spec 𝔽ₚ ⟶ Spec ℤ` of
the family is unchanged by the base change along `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`, because
`(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`.

The cartesian property is checked directly, by the uniqueness of a morphism to `Spec (∏ₚ ℤₚ)`
out of a scheme over `∐ₚ Spec 𝔽ₚ`; no van Kampen property of infinite coproducts of schemes is
used. -/
theorem isPullback_counterexampleBaseChange :
    IsPullback (𝟙 (∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))))
      counterexampleBaseChangeHom counterexampleHom counterexampleCover := by
  have hcomm : 𝟙 (∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))) ≫ counterexampleHom
      = counterexampleBaseChangeHom ≫ counterexampleCover := by
    rw [Category.id_comp, counterexampleBaseChangeHom_comp]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm (fun s => s.fst)
    (fun s => Category.comp_id _) (fun s => ?_) (fun s m hm₁ _ => ?_))
  · exact hom_eq_of_hom_sigmaSpecZMod s.fst _ _
  · simpa using hm₁

/-! ### The base change factors through the clopen decomposition of `Spec (∏ₚ ℤₚ)` -/

/-- The coproduct over the primes of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤₚ`. -/
noncomputable def padicIntSigmaReduce :
    (∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))) ⟶
      (∐ fun q : Nat.Primes => Spec (CommRingCat.of ℤ_[q])) :=
  Limits.Sigma.map fun p => Spec.map (CommRingCat.ofHom (PadicInt.toZMod (p := (p : ℕ))))

/-- **The base change morphism is a closed immersion into an open subscheme.** It factors as the
coproduct of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤₚ` followed by
`AlgebraicGeometry.sigmaSpec`, which is the open immersion `∐ₚ Spec ℤₚ ⟶ Spec (∏ₚ ℤₚ)` given by
the idempotents of the factors. -/
theorem counterexampleBaseChangeHom_eq :
    counterexampleBaseChangeHom
      = padicIntSigmaReduce ≫ sigmaSpec fun q : Nat.Primes => CommRingCat.of ℤ_[q] := by
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [counterexampleBaseChangeHom, Sigma.ι_comp_desc, ← Category.assoc, padicIntSigmaReduce,
    Sigma.ι_map, Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  congr 1

end Stacks.Descent

end
