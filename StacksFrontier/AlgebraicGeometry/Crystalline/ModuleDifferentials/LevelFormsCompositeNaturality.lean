module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FormsAlgEquivNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsComposite

/-!
# Naturality of the three composed comparisons of the source's proof of Stacks 07LF

`Crystalline.tensorFormsLevelComposite` of `ModuleDifferentials/LevelFormsComposite.lean` is the
degreewise value of the isomorphism `ε` that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for.  To assemble those values
into an isomorphism of *cosimplicial* abelian groups, one square has to commute for every
transition map: the composite over the degree-`n` data against the composite over the degree-`m`
data.  **This file is that square.**

```
M ⊗_B Ωⁱ_{B/A,δ} ───────▶ M ⊗_{Ê} ⋀ⁱ_{Ê} Ω̂_{E/A,δ_E}
       │ Φ                               │ Ψ
       ▼                                 ▼
M' ⊗_{B'} Ωⁱ_{B'/A,δ'} ──▶ M' ⊗_{Ê'} ⋀ⁱ_{Ê'} Ω̂_{E'/A,δ_{E'}}
```

Everything is over abstract rings, as in `ModuleDifferentials/LevelFormsComposite.lean` and for
the same reason, and **the two verticals are abstract additive maps given only by their values on
pure tensors** — the shape `Crystalline.tensorFormsCompletionLevelEquivAt_naturality` already
uses.  That is not a convenience: at the level objects of `...SmallSite.wholeSpaceSystem` the
left vertical is the restriction map of a presheaf tensor product and the right one the
transition map of a cosimplicial module, neither of which is `TensorProduct.map` of anything, and
the concrete value of the composite on a pure tensor does not elaborate — the `isDefEq` problem
it poses does not terminate inside the heartbeat budget.  Only the two values on pure tensors are
ever needed, and they are what the statement asks for.

## The three squares

The proof chains the naturality of each comparison, through an intermediate vertical built from
the given `Φ` by conjugating with the first two comparisons, so that
`Crystalline.tensorFormsCompletionLevelEquivAt_naturality` can be applied to it:

* `Crystalline.tensorFormsEquivOfAlgEquiv_naturality` of
  `ModuleDifferentials/FormsAlgEquivNaturality.lean` for the crossing of the ring
  identification — this needs the hypothesis `hcomm` that the two identifications are compatible
  with the two verticals, which is the only genuinely new input;
* `Crystalline.tensorFormsQuotientEquiv_tmul_ιMulti` with
  `Crystalline.differentialsQuotientMap_naturality` for the descent from the finite level, the
  reduction being natural in the divided power ring;
* `Crystalline.tensorFormsCompletionLevelEquivAt_naturality` for the comparison of the two shapes
  of `Ω_{D(n)}`.

## Main definitions

* `Crystalline.tensorFormsLevelCrossing` — the first two comparisons composed, which is
  `Crystalline.tensorFormsLevelComposite` with its third factor removed.
* `Crystalline.completedLevelAlgHom` — the descent of a completed divided power morphism to the
  finite `p`-adic level, with its divided power compatibility
  `Crystalline.isDPMorphism_completedLevelAlgHom`.  This is the map the hypothesis `hcomm` is
  stated against.

## Main results

* `Crystalline.tensorFormsLevelComposite_naturality` — **the square**, as one equation of additive
  maps.
* `Crystalline.tensorFormsLevelEquiv_tmul_ιMulti` — the value of the second comparison on a
  tensor of a wedge of reduced universal differentials, which is
  `Crystalline.tensorFormsQuotientEquiv_tmul_ιMulti` at `K = (p)^c`.
* `Crystalline.tensorFormsLevelComposite_apply` — the composite is its third factor applied to
  `Crystalline.tensorFormsLevelCrossing`, by `rfl`.

## Implementation notes

**The intermediate vertical is built, not assumed.**  Writing `S` for
`Crystalline.tensorFormsLevelCrossing`, the middle vertical is `S' ∘ Φ ∘ S⁻¹`, and its value on a
tensor of a wedge is computed from the three naturality statements above.  That value is all
`Crystalline.tensorFormsCompletionLevelEquivAt_naturality` asks of it, and the conclusion then
follows because `S⁻¹ ∘ S` is the identity.

Computing `S⁻¹` on a tensor of a wedge uses only the *forward* equation that
`Crystalline.tensorFormsEquivOfAlgEquiv` is bundled with: the wedge of the reduced differentials
is in the image of `Crystalline.differentialFormsEquivOfAlgEquiv`, which is an additive
isomorphism, so its preimage is named and the forward equation read backwards.  No `symm` lemma
for either transport is needed, and none exists.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved.**  Nothing here is about
crystalline cohomology: the file proves one commuting square of transports of tensor products of
modules of divided power differentials.  Every hypothesis is passed in, and no hypothesis beyond
those `Crystalline.tensorFormsLevelComposite` itself carries is introduced apart from the two
vertical divided power morphisms and the compatibility `hcomm` of the ring identifications with
them — in particular no flatness, no finiteness and no hypothesis on `i`.

No isomorphism of cosimplicial objects is constructed here either; this is the square such a
construction needs for each transition map.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### The second comparison on a tensor of a wedge -/

section LevelWedge

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (J : Ideal B) (delta : DividedPowers J) (p k : ℕ)
  (hcontained : DividedPowers.pAdicIdeal (A := B) p ^ k ≤ J)
  (hstable : delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ k))

include hcontained hstable

/-- **The second equality of the source's proof of [Stacks, Tag 07LF] on a tensor of a wedge.**
A section tensored with a wedge of *reduced* universal differentials of the level `B/(p)^k` is
the section tensored with the wedge of the universal differentials themselves.  This is
`Crystalline.tensorFormsQuotientEquiv_tmul_ιMulti` at `K = (p)^k`. -/
theorem tensorFormsLevelEquiv_tmul_ιMulti (M : Type*) [AddCommGroup M] [Module B M]
    [Module (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) M]
    [IsScalarTower B (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) M] (i : ℕ) (m : M)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    tensorFormsLevelEquiv J delta p k hcontained hstable M i
        (m ⊗ₜ exteriorPower.ιMulti (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) i
          (fun j ↦ differentialsQuotientMap J delta _ hstable
            (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb) (v j))) =
      m ⊗ₜ exteriorPower.ιMulti B i v :=
  tensorFormsQuotientEquiv_tmul_ιMulti J delta _ hstable
    (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb) M i m v

end LevelWedge

/-! ### The descent of a completed divided power morphism to a finite level -/

section CompletedLevelMap

variable {A : Type u} {E : Type v} {E' : Type w} [CommRing A] [CommRing E] [CommRing E']
  [Algebra A E] [Algebra A E'] (p c : ℕ) (g : E →ₐ[A] E')

/-- **The descent of a completed divided power morphism to a finite `p`-adic level.**  Every ring
map carries `(p)^c` into `(p)^c`, by `Crystalline.pAdicIdeal_pow_le_comap_ringHom`, so the
completion `Crystalline.completedAlgHom` of an algebra map descends to the levels with no further
hypothesis. -/
noncomputable def completedLevelAlgHom :
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
        DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) →ₐ[A]
      (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
        DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c) :=
  Ideal.quotientMapₐ _ (completedAlgHom p g)
    (pAdicIdeal_pow_le_comap_ringHom p c (completedAlgHom p g).toRingHom)

end CompletedLevelMap

section CompletedLevelDPMorphism

variable {A : Type u} {E : Type v} {E' : Type w} [CommRing A] [CommRing E] [CommRing E']
  [Algebra A E] [Algebra A E']
variable (Jenv : Ideal E) (deltaenv : DividedPowers Jenv)
  (Jenv' : Ideal E') (deltaenv' : DividedPowers Jenv') (p c : ℕ)
variable (hpn : IsNilpotent (Ideal.Quotient.mk Jenv (p : E)))
  (hpn' : IsNilpotent (Ideal.Quotient.mk Jenv' (p : E')))
variable (g : E →ₐ[A] E') (hg : deltaenv.IsDPMorphism deltaenv' g.toRingHom)
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

include hg

/-- **The descent to a finite `p`-adic level is a divided power morphism** for the quotient
divided powers of `Crystalline.completedLevelDividedPowers`.  This is
`Crystalline.isDPMorphism_quotientMapₐ` applied to
`Crystalline.isDPMorphism_completedAlgHom`. -/
theorem isDPMorphism_completedLevelAlgHom :
    (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable).IsDPMorphism
      (completedLevelDividedPowers Jenv' deltaenv' p hpn' c hcontained' hstable')
      (completedLevelAlgHom p c g).toRingHom :=
  isDPMorphism_quotientMapₐ (DividedPowers.completionIdeal Jenv p hpn)
    (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 _ hstable
    (DividedPowers.completionIdeal Jenv' p hpn')
    (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 _ hstable'
    (completedAlgHom p g)
    (isDPMorphism_completedAlgHom Jenv deltaenv Jenv' deltaenv' p hpn hpn' g hg)
    (pAdicIdeal_pow_le_comap_ringHom p c (completedAlgHom p g).toRingHom)

end CompletedLevelDPMorphism

/-! ### The first two comparisons composed -/

section Crossing

variable {A : Type u} {E : Type v} {B : Type w} [CommRing A] [CommRing E] [CommRing B]
  [Algebra A E] [Algebra A B]
variable (Jenv : Ideal E) (deltaenv : DividedPowers Jenv) (p : ℕ)
variable (hpn : IsNilpotent (Ideal.Quotient.mk Jenv (p : E)))
variable (c : ℕ)
variable (hcontained : DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c ≤
  DividedPowers.completionIdeal Jenv p hpn)
variable (hstable : (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1.IsSubDPIdeal
  (DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (J : Ideal B) (delta : DividedPowers J)
variable (f : B ≃ₐ[A] (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (hf : delta.IsDPMorphism
  (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f.toAlgHom.toRingHom)
variable (hJ : J.map f.toAlgHom.toRingHom =
  (DividedPowers.completionIdeal Jenv p hpn).map
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c)))
variable (M : Type*) [AddCommGroup M] [Module B M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
variable (hsm : ∀ (b : B) (m : M), b • m = f b • m)

/-- **The first two comparisons of the source's proof of [Stacks, Tag 07LF], composed.**

`M ⊗_B Ωⁱ_{B/A,δ}  ≃+  M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂}`

This is `Crystalline.tensorFormsLevelComposite` with its third factor removed: the crossing of
the ring identification followed by the descent from the finite level.  It is named because the
intermediate vertical of the naturality square of the composite is built by conjugating with
it. -/
noncomputable def tensorFormsLevelCrossing (i : ℕ) :
    M ⊗[B] dividedPowerDifferentialForms (A := A) delta i ≃+
      M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 i :=
  (tensorFormsEquivOfAlgEquiv delta
        (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ hsm
      i).1.trans
    (tensorFormsLevelEquiv (DividedPowers.completionIdeal Jenv p hpn)
      (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable M
      i).toAddEquiv

variable (cmp : DifferentialsCompletionComparison (A := A) Jenv deltaenv p hpn) (e k : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k)
variable [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]

/-- **The composite is its third comparison applied to `Crystalline.tensorFormsLevelCrossing`.**
This holds by `rfl`; it is recorded so that the naturality square of the composite can be
reduced to the naturality of the third comparison. -/
theorem tensorFormsLevelComposite_apply (i : ℕ)
    (z : M ⊗[B] dividedPowerDifferentialForms (A := A) delta i) :
    tensorFormsLevelComposite Jenv deltaenv p hpn cmp c hcontained hstable J delta f hf hJ e k hk
        M hsm i z =
      tensorFormsCompletionLevelEquivAt (A := A) Jenv deltaenv p hpn cmp e k hk M i
        (tensorFormsLevelCrossing Jenv deltaenv p hpn c hcontained hstable J delta f hf hJ M hsm
          i z) :=
  rfl

end Crossing

/-! ### The naturality square of the composite -/

section CompositeNaturality

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
variable (e e' k : ℕ) (hk : cmp.quotientSystem.cutoff + e = k)
  (hk' : cmp'.quotientSystem.cutoff + e' = k)
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
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ k) M']
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E')
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ k) M']
variable (hsm' : ∀ (b : B') (m : M'), b • m = f' b • m)
variable (g : E →ₐ[A] E') (hg : deltaenv.IsDPMorphism deltaenv' g.toRingHom)
variable (u : B →ₐ[A] B') (hu : delta.IsDPMorphism delta' u.toRingHom)
variable (hcomm : f'.toAlgHom.comp u = (completedLevelAlgHom p c g).comp f.toAlgHom)

include hcomm

/-- **The three comparisons of the source's proof of [Stacks, Tag 07LF], composed, are natural in
the divided power data.**

For two instances of the situation of `Crystalline.tensorFormsLevelComposite` — an uncompleted
envelope `E` with a section ring `B` identified with the finite level `Ê/(p)^c`, and the same over
`E'`, `B'` — an algebra map `g : (E, δ_E) ⟶ (E', δ_{E'})` of envelopes which is a divided power
morphism and a divided power morphism `u : (B, J, δ) ⟶ (B', J', δ')` of section rings whose
descent `Crystalline.completedLevelAlgHom` of `g` to the levels is compatible with the two ring
identifications, the square

```
M ⊗_B Ωⁱ_{B/A,δ} ───────▶ M ⊗_{Ê} ⋀ⁱ_{Ê} Ω̂_{E/A,δ_E}
       │ Φ                               │ Ψ
       ▼                                 ▼
M' ⊗_{B'} Ωⁱ_{B'/A,δ'} ──▶ M' ⊗_{Ê'} ⋀ⁱ_{Ê'} Ω̂_{E'/A,δ_{E'}}
```

commutes, the horizontals being `Crystalline.tensorFormsLevelComposite`.

The two verticals are arbitrary additive maps, given only by what they do to a pure tensor: `Φ`
carries `m ⊗ x` to `φ m ⊗ Ωⁱ(u) x` for the transport
`Crystalline.mapDifferentialFormsOfDPMorphism` along `u`, and `Ψ` carries `m ⊗ w₁ ∧ ⋯ ∧ wᵢ` to
`φ m ⊗ ĝ(w₁) ∧ ⋯ ∧ ĝ(wᵢ)` for the transport `Crystalline.completionDifferentialsMapₛₗ` of the
completion of the differentials, with the same `φ` on the coefficients.  Those values determine
the maps — pure tensors span the source of `Φ`, and
`Crystalline.tensorExteriorPower_addMonoidHom_ext` covers `Ψ` — so this is the square and not a
weaker statement.

**No tag attribute is placed.** -/
theorem tensorFormsLevelComposite_naturality (i : ℕ) (phi : M →+ M')
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
          hf' hJ' e' k hk' M' hsm' i).toAddMonoidHom.comp Phi := by
  have hmid : ∀ (m : M) (w : Fin i → dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1),
      tensorFormsLevelCrossing Jenv' deltaenv' p hpn' c hcontained' hstable' J' delta' f' hf' hJ'
          M' hsm' i (Phi ((tensorFormsLevelCrossing Jenv deltaenv p hpn c hcontained hstable J
            delta f hf hJ M hsm i).symm (m ⊗ₜ exteriorPower.ιMulti
              (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) i w))) =
        phi m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') i
          fun j ↦ mapDifferentialsOfDPMorphismₛₗ (A := A) _
            (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1
            (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1
            (completedAlgHom p g)
            (isDPMorphism_completedAlgHom Jenv deltaenv Jenv' deltaenv' p hpn hpn' g hg)
            (w j) := by
    intro m w
    obtain ⟨x, hfx⟩ := mapDifferentialFormsOfDPMorphism_surjective (A := A) delta
      (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ i
      (exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
          DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) i
        (fun j ↦ differentialsQuotientMap (DividedPowers.completionIdeal Jenv p hpn)
          (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 _ hstable
          (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A)
            (DividedPowers.completionIdeal Jenv p hpn)
            (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hb) (w j)))
    have hSx : tensorFormsLevelCrossing Jenv deltaenv p hpn c hcontained hstable J delta f hf hJ
        M hsm i (m ⊗ₜ[B] x) = m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) i w :=
      (congrArg (tensorFormsLevelEquiv _ _ p c hcontained hstable M i)
          (((tensorFormsEquivOfAlgEquiv delta
                (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ hsm
                i).2 m x).trans (congrArg (m ⊗ₜ ·) hfx))).trans
        (tensorFormsLevelEquiv_tmul_ιMulti _ _ p c hcontained hstable M i m w)
    have hSsymm := (AddEquiv.symm_apply_eq _).2 hSx.symm
    have hvbar : mapDifferentialFormsOfDPMorphism (A := A) _
        (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable)
        (completedLevelDividedPowers Jenv' deltaenv' p hpn' c hcontained' hstable')
        (completedLevelAlgHom p c g)
        (isDPMorphism_completedLevelAlgHom Jenv deltaenv Jenv' deltaenv' p c hpn hpn' g hg
          hcontained hstable hcontained' hstable') i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f.toAlgHom hf i
          x) =
      exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E' ⧸
          DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') p ^ c) i
        (fun j ↦ differentialsQuotientMap (DividedPowers.completionIdeal Jenv' p hpn')
          (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 _ hstable'
          (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A)
            (DividedPowers.completionIdeal Jenv' p hpn')
            (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 p c hb)
          (mapDifferentialsOfDPMorphism (A := A) _
            (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1
            (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 (completedAlgHom p g)
            (isDPMorphism_completedAlgHom Jenv deltaenv Jenv' deltaenv' p hpn hpn' g hg)
            (w j))) :=
      (congrArg (mapDifferentialFormsOfDPMorphism (A := A) _
            (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable)
            (completedLevelDividedPowers Jenv' deltaenv' p hpn' c hcontained' hstable')
            (completedLevelAlgHom p c g)
            (isDPMorphism_completedLevelAlgHom Jenv deltaenv Jenv' deltaenv' p c hpn hpn' g hg
              hcontained hstable hcontained' hstable') i)
          hfx).trans
        ((mapDifferentialFormsOfDPMorphism_ιMulti (A := A) _ _ _ _ _ i _).trans
          (congrArg (exteriorPower.ιMulti _ i)
            (funext fun j ↦ differentialsQuotientMap_naturality
              (DividedPowers.completionIdeal Jenv p hpn)
              (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 _ hstable
              (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A)
                (DividedPowers.completionIdeal Jenv p hpn)
                (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hb)
              (DividedPowers.completionIdeal Jenv' p hpn')
              (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 _ hstable'
              (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A)
                (DividedPowers.completionIdeal Jenv' p hpn')
                (DividedPowers.completedDividedPowers Jenv' deltaenv' p hpn').1 p c hb)
              (completedAlgHom p g)
              (isDPMorphism_completedAlgHom Jenv deltaenv Jenv' deltaenv' p hpn hpn' g hg)
              (pAdicIdeal_pow_le_comap_ringHom p c (completedAlgHom p g).toRingHom) (w j))))
    rw [hSsymm, hPhi]
    refine Eq.trans (congrArg (tensorFormsLevelEquiv _ _ p c hcontained' hstable' M' i)
      ((tensorFormsEquivOfAlgEquiv_naturality delta delta'
        (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable)
        (completedLevelDividedPowers Jenv' deltaenv' p hpn' c hcontained' hstable')
        f f' hf hf' hJ' u (completedLevelAlgHom p c g) hu
        (isDPMorphism_completedLevelAlgHom Jenv deltaenv Jenv' deltaenv' p c hpn hpn' g hg
          hcontained hstable hcontained' hstable')
        hcomm hsm' i (phi m) x).trans
        (congrArg (phi m ⊗ₜ ·) hvbar))) ?_
    exact tensorFormsLevelEquiv_tmul_ιMulti _ _ p c hcontained' hstable' M' i (phi m) _
  have hthird := tensorFormsCompletionLevelEquivAt_naturality (A := A) Jenv deltaenv Jenv'
    deltaenv' p hpn hpn' g hg cmp cmp' e e' k hk hk' M M' i phi
    ((tensorFormsLevelCrossing Jenv' deltaenv' p hpn' c hcontained' hstable' J' delta' f' hf' hJ'
        M' hsm' i).toAddMonoidHom.comp (Phi.comp
      (tensorFormsLevelCrossing Jenv deltaenv p hpn c hcontained hstable J delta f hf hJ M hsm
        i).symm.toAddMonoidHom)) Psi hmid hPsi
  refine AddMonoidHom.ext fun z ↦ ?_
  simpa [tensorFormsLevelComposite_apply] using DFunLike.congr_fun hthird
    (tensorFormsLevelCrossing Jenv deltaenv p hpn c hcontained hstable J delta f hf hJ M hsm i z)

end CompositeNaturality

end Crystalline

end
