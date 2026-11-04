module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelReindex
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelFormsExt

/-!
# The level identification in degree `i` is natural in the divided power ring

`Crystalline.tensorFormsCompletionLevelEquiv` of `ModuleDifferentials/CompletionLevelForms.lean`
is the level identification of [Stacks, Tag 07KK] in degree `i`, after tensoring:

`M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`.

This file proves that it is natural along a divided power morphism `f : (B, J, δ) ⟶ (C, L, ε)`,
which is the cosimplicial-direction naturality the source's proof of [Stacks, Tag 07LF] needs of
its first comparison.  `Crystalline.tensorFormsLevelEquiv_symm_naturality` of
`ModuleDifferentials/QuotientForms.lean` is the corresponding statement for the second one.

## The shape of the statement

The two vertical maps of the square are **hypotheses**, given by what they do to a tensor of a
wedge, and not constructed here.  That is deliberate and is not a weakening: source and target
are modules over the two different rings `B̂` and `Ĉ`, so a vertical map is at best additive, and
the consumer — the cosimplicial module `L_* ⊗_{D(*)} Ωⁱ_{D(*)}` of [Stacks, Tag 07LA] — already
has its structure maps and needs them *recognised*, not rebuilt.  What the square asserts is
exactly that any two additive maps with the stated effect on the tensors of wedges, one upstairs
and one downstairs, commute with the identification; and by
`Crystalline.tensorExteriorPower_addMonoidHom_ext` the tensors of wedges determine an additive
map, so nothing is lost.

The level is a bare `k` with the two proofs `cmp.quotientSystem.cutoff + e = k` and
`cmp'.quotientSystem.cutoff + e' = k`: the comparisons of [Stacks, Tag 07KK] for `B` and for `C`
carry their own cutoffs, so without the re-indexing of
`ModuleDifferentials/CompletionLevelReindex.lean` the square is an equation between types that
are equal only propositionally.

## Why it is true

On a tensor of a wedge both routes are computed.  Going right first,
`Crystalline.tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk` replaces the wedge of
differentials of `B̂` by a wedge of lifts `wⱼ` of their classes under the level identification,
and the lower vertical carries that to the wedge of the `wⱼ` transported along `f`.  Going down
first, the upper vertical carries the wedge of `ωⱼ` to the wedge of their images, and the same
computation replaces those by lifts of *their* classes.  So the two routes agree as soon as the
transported `wⱼ` is such a lift, which is the **degree-one** naturality square
`Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt` of
`ModuleDifferentials/CompletionLevelReindex.lean`.  No property of either comparison beyond that
square is used, and in particular nothing relating the two
`Crystalline.DifferentialsCompletionComparison`s is needed, since
`Crystalline.tensorFormsCompletionLevelEquiv_unique` says the identification is pinned by its
value on the tensors of wedges.

## Main definitions

* `Crystalline.tensorFormsCompletionLevelEquivAt` — the level identification in degree `i`, after
  tensoring, at a bare level `k`.

## Main results

* `Crystalline.tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk` — its value on a tensor of a
  wedge, in the lifted form.
* `Crystalline.tensorFormsCompletionLevelEquivAt_naturality` — **the naturality square of the
  level identification in degree `i`, as one equation of additive maps.**

## Implementation notes

The two reductions `Ω_{B̂/A,γ̂} → Ω_{B̂/A,γ̂}/pᵏ` and `Ω̂_{B/A,δ} → Ω̂_{B/A,δ}/pᵏ` are the quotient
maps, and the two transition maps of `ModuleDifferentials/CompletionLevelTransition.lean` are
`Crystalline.adicQuotientMap` of the corresponding maps upstairs, so each commutes with the
reduction by `rfl`; those two `rfl`s are what carry the degree-one square from the quotients up
to the modules the wedges are taken of.

## What is and is not proved

**No tag attribute is placed, and [Stacks, Tag 07LF] is not proved here.**  What is supplied is
the naturality that the "What `ε` owes" note of
`SmallSite/TensorRestrictionVanishing.lean` records as "still not stated and not proved" for
`Crystalline.tensorFormsCompletionLevelEquiv`.  The isomorphism `ε` itself is not constructed:
that also needs the naturality of the identification of the sections of `Ω^i_{X/S}` at an affine
object and of the sheafification bijection, neither of which is addressed here.

No hypothesis is carried beyond the divided power morphism, the two nilpotence hypotheses and
the two comparisons; no flatness, no finiteness, no hypothesis on `i`, and no hypothesis
relating the two comparisons.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### The level identification in degree `i` at a bare level -/

section Reindex

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k)
variable (M : Type*) [AddCommGroup M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]

/-- **The level identification of [Stacks, Tag 07KK] in degree `i`, after tensoring, at a bare
level `k`.**

`M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`

This is `Crystalline.tensorFormsCompletionLevelEquiv`, whose level is
`cmp.quotientSystem.cutoff + e`, re-indexed along a proof that this is the given `k`, so that
two comparisons for two different rings can be read at one and the same level. -/
public noncomputable def tensorFormsCompletionLevelEquivAt (i : ℕ) :
    M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 i ≃ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
          DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k]
      M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta))) := by
  subst hk
  exact tensorFormsCompletionLevelEquiv (A := A) J delta p hp cmp e M i

/-- **The value of the level identification in degree `i` on a tensor of a wedge.**  If the
differentials `ωⱼ` of `B̂` and the elements `wⱼ` of the completion `Ω̂_{B/A,δ}` have the same
class modulo `pᵏ` under the level identification in every slot, the identification carries
`m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to `m ⊗ w₁ ∧ ⋯ ∧ wᵢ`.  Such `wⱼ` exist for every `ωⱼ`, the reduction being
surjective. -/
public theorem tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk (i : ℕ) (m : M)
    (v : Fin i → dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1)
    (w : Fin i → AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta))
    (h : ∀ j, completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
        (Submodule.Quotient.mk (v j)) = Submodule.Quotient.mk (w j)) :
    tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e k hk M i
        (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
      m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i w := by
  subst hk
  exact tensorFormsCompletionLevelEquiv_tmul_ιMulti_of_mk (A := A) J delta p hp cmp e M i m v w h

end Reindex

/-! ### The naturality square in degree `i` -/

section Naturality

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable (J : Ideal B) (delta : DividedPowers J) (L : Ideal C) (epsilon : DividedPowers L)
variable (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (hq : IsNilpotent (Ideal.Quotient.mk L (p : C)))
variable (f : B →ₐ[A] C)
variable (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
variable (cmp : DifferentialsCompletionComparison (A := A) J delta p hp)
variable (cmp' : DifferentialsCompletionComparison (A := A) L epsilon p hq)
variable (e e' k : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k) (hk' : cmp'.quotientSystem.cutoff + e' = k)
variable (M : Type*) [AddCommGroup M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]
variable (N : Type*) [AddCommGroup N]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) N]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) p ^ k) N]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) p ^ k) N]

include hf

/-- **The naturality square of the level identification of [Stacks, Tag 07KK] in degree `i`,
after tensoring, as one equation of additive maps.**

```
M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ──────▶ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}
        │ Φ                              │ Ψ
        ▼                                ▼
N ⊗_{Ĉ} Ωⁱ_{Ĉ/A,ε̂} ──────▶ N ⊗_{Ĉ} ⋀ⁱ_{Ĉ} Ω̂_{C/A,ε}
```

The two verticals are arbitrary additive maps, given only by what they do to a tensor of a
wedge: `Φ` carries `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to `φ m ⊗ f(ω₁) ∧ ⋯ ∧ f(ωᵢ)` for the transport
`Crystalline.mapDifferentialsOfDPMorphismₛₗ` along the completed divided power morphism, and `Ψ`
carries `m ⊗ w₁ ∧ ⋯ ∧ wᵢ` to `φ m ⊗ f(w₁) ∧ ⋯ ∧ f(wᵢ)` for the transport
`Crystalline.completionDifferentialsMapₛₗ` of the completion of the differentials, with the same
`φ` on the coefficients.  Those values determine an additive map by
`Crystalline.tensorExteriorPower_addMonoidHom_ext`, so this is the square and not a weaker
statement.

The proof is the degree-one square
`Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt` evaluated
on the class of each `ωⱼ`. -/
public theorem tensorFormsCompletionLevelEquivAt_naturality (i : ℕ) (phi : M →+ N)
    (Phi : (M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 i) →+
      (N ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers L epsilon p hq).1 i))
    (Psi : (M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta)))) →+
      (N ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p)
            (dividedPowerDifferentials (A := A) epsilon)))))
    (hPhi : ∀ (m : M) (v : Fin i → dividedPowerDifferentials (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1),
      Phi (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
        phi m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) i
          fun j ↦ mapDifferentialsOfDPMorphismₛₗ (A := A) _
            (DividedPowers.completedDividedPowers J delta p hp).1
            (DividedPowers.completedDividedPowers L epsilon p hq).1 (completedAlgHom p f)
            (isDPMorphism_completedAlgHom J delta L epsilon p hp hq f hf) (v j))
    (hPsi : ∀ (m : M) (w : Fin i → AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
        (dividedPowerDifferentials (A := A) delta)),
      Psi (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i w) =
        phi m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) i
          fun j ↦ completionDifferentialsMapₛₗ J delta L epsilon p f hf (w j)) :
    Psi.comp (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e k hk M
        i).toLinearMap.toAddMonoidHom =
      (tensorFormsCompletionLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk' N
          i).toLinearMap.toAddMonoidHom.comp Phi := by
  have hsquare := completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt
    J delta L epsilon p hp hq f hf cmp cmp' e e' k hk hk'
  refine tensorExteriorPower_addMonoidHom_ext fun m v ↦ ?_
  have hex : ∀ j : Fin i, ∃ y : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta),
      completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
        (Submodule.Quotient.mk (v j)) = Submodule.Quotient.mk y := fun j ↦
    Exists.elim (Submodule.Quotient.mk_surjective _
      (completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
        (Submodule.Quotient.mk (v j)))) fun y hy ↦ ⟨y, hy.symm⟩
  choose w hw using hex
  have hleft : Psi (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e k hk M i
      (m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v)) =
      phi m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) i
        fun j ↦ completionDifferentialsMapₛₗ J delta L epsilon p f hf (w j) :=
    Eq.trans (congrArg Psi (tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk
      (A := A) J delta p hp cmp e k hk M i m v w hw)) (hPsi m w)
  have hslot : ∀ j : Fin i,
      completedDifferentialsLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk'
          (Submodule.Quotient.mk (mapDifferentialsOfDPMorphismₛₗ (A := A) _
            (DividedPowers.completedDividedPowers J delta p hp).1
            (DividedPowers.completedDividedPowers L epsilon p hq).1 (completedAlgHom p f)
            (isDPMorphism_completedAlgHom J delta L epsilon p hp hq f hf) (v j))) =
        Submodule.Quotient.mk
          (completionDifferentialsMapₛₗ J delta L epsilon p f hf (w j)) := fun j ↦
    Eq.trans (DFunLike.congr_fun hsquare (Submodule.Quotient.mk (v j))).symm
      (congrArg (completionDifferentialsModPowMap J delta L epsilon p f hf k) (hw j))
  have hright : tensorFormsCompletionLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk' N i
      (Phi (m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v)) =
      phi m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) i
        fun j ↦ completionDifferentialsMapₛₗ J delta L epsilon p f hf (w j) :=
    Eq.trans
      (congrArg (tensorFormsCompletionLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk' N i)
        (hPhi m v))
      (tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk (A := A) L epsilon p hq cmp' e' k hk'
        N i (phi m) _ _ hslot)
  exact hleft.trans hright.symm

end Naturality

end Crystalline

end
