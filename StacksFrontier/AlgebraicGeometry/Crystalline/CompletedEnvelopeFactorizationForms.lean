module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorization
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedForms

/-!
# The graded comparisons of completed forms along `σ`, `τ`, `ν` and `α`

`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeFactorization.lean` builds the
factorization `ρ = τ ∘ σ` of the source's proof of [Stacks, Lemma 60.21.4, Tag 07LH] at the level
of **rings**: the completed divided power polynomial algebra `D⟨ξ_i⟩^∧`, the structure map
`ν : D → D⟨ξ_i⟩^∧`, the maps `σ`, `τ` and the automorphism `α`, and the identities `τ ∘ σ = ρ`,
`α ∘ σ = ν`, `τ ∘ ν = id_D`.

What the source's argument needs is those maps read on the **completed de Rham complexes**, and
`Crystalline.CompletedDeRham.baseChangeComplexHom` carries a ring map up to the complexes once it
is given a *graded comparison of forms* `ψ_* : Ω̂^*_D → Ω̂^*_{D'}` along it, semilinear over the
ring map, together with three compatibilities: `ψ_1 ∘ d = d' ∘ f` (`hpsi1`), multiplicativity for
the wedge product (`hpsi_wedge`) and commutation with the de Rham differential
(`hpsi_deRham`).  This module supplies `ψ_*` and those three compatibilities for each of the four
maps, and for `α⁻¹` as well.

## Which forms

For a divided power ring `R` over `A` the completed divided power forms of this library are
`Crystalline.completedDividedPowerForms`, the `p`-adic completion of the divided power
differential forms `Ω^i_{R/A,δ}` of [Stacks, Tag 07HZ]; that is the family carrying the whole
exterior calculus — `Crystalline.completedDividedPowerWedge`,
`Crystalline.completedDividedPowerDeRham`, `Crystalline.completedFormsDifferential` and the two
conditions `Crystalline.CompletedDeRham.IsGradedLeibniz`,
`Crystalline.CompletedDeRham.IsGradedExterior` that a completed de Rham complex is built from.
Taken at `R = D` and at `R = D⟨ξ_i⟩^∧` — each of which *is* a divided power ring, the first by
[Stacks, Tag 07KD] and the second by [Stacks, Tag 07H6] followed by [Stacks, Tag 07KD] — it gives
the two families `Crystalline.envelopeCompletionForms` and
`Crystalline.envelopeCompletionVariableForms` compared below.

This is the one choice of the two families for which **all four** comparisons exist, which is why
it is the choice made here.  The alternative on the `D⟨ξ_i⟩^∧` side is
`Crystalline.DividedPowerPolynomial.completedPolynomialForms`, the completion along `(p) ⊆ P` of
the forms of the *uncompleted* algebra `P = D⟨ξ_i⟩`, which is what the completed clause of
[Stacks, Lemma 60.19.2, Tag 07LD] works with.  A comparison into that family exists along `ν`
(it is `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMap`) and one out of it
exists along `τ`, both because the maps in question are induced by ring maps out of or into `P`
itself.  But `σ` and `α` are *not*: `σ(x_i) = x_i + ξ_i` is defined by the universal property of
`D` into the divided power ideal of the **completion** `D⟨ξ_i⟩^∧`, and `α` restricts to `σ⁻` on
the coefficients, so neither factors through `P`.  Since the whole point of the four comparisons
is that they satisfy the factorization identities — which only makes sense when all four have the
same source and target families — the uniform choice is forced.  No identification of the two
families is claimed here; see `Crystalline.DividedPowerPolynomial.completedPolynomialForms` for
what that identification would involve.

## The algebra structures

`Ω^i_{R/A,δ}` needs `R` to be an `A`-algebra, and the comparison along a map needs that map to be
an `A`-algebra homomorphism.  Both rings are given their `A`-algebra structure here: `D` through
its structure map `A → D`, and `D⟨ξ_i⟩^∧` through `ν` after it, which is the structure map of
[Stacks, Tag 07H6].  That each of `σ`, `τ`, `ν`, `α`, `α⁻¹` is an `A`-algebra map for those
structures is the content of `..._comp_structureMap`, `..._comp_nu` and `τ ∘ ν = id_D` of the
factorization module, and is recorded in the `...AlgHom` declarations below.

No `Algebra D (D⟨ξ_i⟩^∧)` instance is declared: `σ` and `ν` are two different ring maps `D →
D⟨ξ_i⟩^∧` and `τ` goes the other way, so there is no canonical one.  Each comparison is therefore
semilinear over its map's `toRingHom`, and a caller applying
`Crystalline.CompletedDeRham.baseChangeComplexHom` installs the algebra structure it wants with
`letI : Algebra _ _ := (envelopeCompletionSigma E p hp).toRingHom.toAlgebra`, for which
`algebraMap` is that `toRingHom`.

## Main definitions

* `Crystalline.envelopeCompletionForms` — `Ω̂^i_D`.
* `Crystalline.envelopeCompletionVariableForms` — `Ω̂^i_{D⟨ξ_i⟩^∧}`.
* `Crystalline.envelopeCompletionFormsDifferential` and
  `Crystalline.envelopeCompletionVariableFormsDifferential` — the universal differentials
  `d : D → Ω̂^1_D` and `d' : D⟨ξ_i⟩^∧ → Ω̂^1_{D⟨ξ_i⟩^∧}`.
* `Crystalline.envelopeCompletionFormsWedge` and
  `Crystalline.envelopeCompletionVariableFormsWedge` — the wedge products of the two families,
  bilinear over `D` and over `D⟨ξ_i⟩^∧` respectively, which is the variance
  `Crystalline.CompletedDeRham.baseChangeComplexHom` asks for.
* `Crystalline.envelopeCompletionNuForms` — **`ψ_*` along `ν`.**
* `Crystalline.envelopeCompletionSigmaForms` — **`ψ_*` along `σ`.**
* `Crystalline.envelopeCompletionTauForms` — **`ψ_*` along `τ`.**
* `Crystalline.envelopeCompletionAlphaForms` — **`ψ_*` along `α`**, with
  `Crystalline.envelopeCompletionAlphaInvForms` along `α⁻¹`.
* `Crystalline.envelopeCompletionRhoForms` — `ψ_*` along `ρ` itself.

## Main results

* `..._differential`, `..._wedge`, `..._deRham` for each of the five maps — **the three
  compatibilities `Crystalline.CompletedDeRham.baseChangeComplexHom` asks of `ψ_*`.**
* `Crystalline.envelopeCompletionTauForms_sigmaForms` — **`ψ_τ ∘ ψ_σ = ψ_ρ`**, the factorization
  on forms.
* `Crystalline.envelopeCompletionAlphaForms_sigmaForms` — **`ψ_α ∘ ψ_σ = ψ_ν`.**
* `Crystalline.envelopeCompletionTauForms_nuForms` — **`ψ_τ ∘ ψ_ν = id`.**
* `Crystalline.envelopeCompletionAlphaForms_alphaInvForms` and
  `Crystalline.envelopeCompletionAlphaInvForms_alphaForms` — `ψ_α` is invertible.
* `Crystalline.isGradedLeibniz_envelopeCompletionForms`,
  `Crystalline.isGradedLeibniz_envelopeCompletionVariableForms` and the four
  `..._FormsDifferential_add`, `..._FormsDifferential_mul` lemmas — the remaining hypotheses
  `Crystalline.CompletedDeRham.baseChangeComplexHom` asks of the two families themselves, as
  opposed to of the comparison between them.  What it then still needs is the module `M`, its
  connection, and the two square-zero hypotheses, none of which is a statement about the forms.

No tag attribute is placed on anything here: these are steps towards the proof of
[Stacks, Tag 07LH] and none of them states that lemma.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u

/-! ### Divided power morphisms over the base as algebra homomorphisms -/

section AlgHomOfDPMorphism

variable {A : Type u} [CommRing A] {R S : Type u} [CommRing R] [CommRing S] [Algebra A R]
  [Algebra A S] {I : Ideal R} {K : Ideal S} {gamma : _root_.DividedPowers I}
  {delta : _root_.DividedPowers K}

/-- **A divided power morphism compatible with the structure maps from `A`, read as an
`A`-algebra homomorphism.**

The comparison of divided power differential forms
`Crystalline.mapDifferentialFormsOfDPMorphism` and its completion
`Crystalline.completedMapDifferentialForms` are indexed by an `A`-algebra homomorphism together
with a proof that it is a divided power morphism, whereas the maps of a divided power
factorization are bundled the other way round, as divided power morphisms which happen to be
compatible with the base.  This turns one into the other; the underlying ring homomorphism is
unchanged, so the comparison is semilinear over the divided power morphism itself. -/
public def dpMorphismAlgHom (f : DPMorphism gamma delta)
    (hf : ∀ a : A, f (algebraMap A R a) = algebraMap A S a) : R →ₐ[A] S where
  toRingHom := f.toRingHom
  commutes' := hf

/-- The underlying ring homomorphism of `Crystalline.dpMorphismAlgHom f hf` is that of `f`. -/
@[simp] public theorem dpMorphismAlgHom_toRingHom (f : DPMorphism gamma delta)
    (hf : ∀ a : A, f (algebraMap A R a) = algebraMap A S a) :
    (dpMorphismAlgHom (A := A) f hf).toRingHom = f.toRingHom := rfl

/-- `Crystalline.dpMorphismAlgHom f hf` acts as `f`. -/
@[simp] public theorem dpMorphismAlgHom_apply (f : DPMorphism gamma delta)
    (hf : ∀ a : A, f (algebraMap A R a) = algebraMap A S a) (x : R) :
    dpMorphismAlgHom (A := A) f hf x = f x := rfl

/-- The comparisons of completed forms along `f` and `g` compose to that along `g ∘ f`. -/
private theorem completedMapDifferentialForms_comp_dpMorphism (p : ℕ) {T : Type u} [CommRing T]
    [Algebra A T] {L : Ideal T} {epsilon : _root_.DividedPowers L} (f : DPMorphism gamma delta)
    (g : DPMorphism delta epsilon) (h : DPMorphism gamma epsilon)
    (hf : ∀ a : A, f (algebraMap A R a) = algebraMap A S a)
    (hg : ∀ a : A, g (algebraMap A S a) = algebraMap A T a)
    (hh : ∀ a : A, h (algebraMap A R a) = algebraMap A T a) (hcomp : g.comp f = h) (i : ℕ)
    (x : completedDividedPowerForms p A gamma i) :
    completedMapDifferentialForms p A delta epsilon (dpMorphismAlgHom (A := A) g hg)
        g.isDPMorphism i
      (completedMapDifferentialForms p A gamma delta (dpMorphismAlgHom (A := A) f hf)
        f.isDPMorphism i x) =
      completedMapDifferentialForms p A gamma epsilon (dpMorphismAlgHom (A := A) h hh)
        h.isDPMorphism i x :=
  (completedMapDifferentialForms_eq_comp p A gamma delta epsilon _ _ _ f.isDPMorphism
    g.isDPMorphism h.isDPMorphism (AlgHom.ext fun y ↦ (congrArg (· y) hcomp).symm) i x).symm

/-- If `g ∘ f` is the identity, the comparisons of completed forms along `f` and `g` compose to
the identity. -/
private theorem completedMapDifferentialForms_comp_dpMorphism_id (p : ℕ)
    (f : DPMorphism gamma delta) (g : DPMorphism delta gamma)
    (hf : ∀ a : A, f (algebraMap A R a) = algebraMap A S a)
    (hg : ∀ a : A, g (algebraMap A S a) = algebraMap A R a)
    (hcomp : g.comp f = DPMorphism.id gamma)
    (i : ℕ) (x : completedDividedPowerForms p A gamma i) :
    completedMapDifferentialForms p A delta gamma (dpMorphismAlgHom (A := A) g hg)
        g.isDPMorphism i
      (completedMapDifferentialForms p A gamma delta (dpMorphismAlgHom (A := A) f hf)
        f.isDPMorphism i x) = x :=
  (completedMapDifferentialForms_comp_dpMorphism p f g _ hf hg (fun _ ↦ rfl) hcomp i x).trans
    (completedMapDifferentialForms_eq_self p A gamma _ (DPMorphism.id gamma).isDPMorphism
      (AlgHom.ext fun _ ↦ rfl) i x)

end AlgHomOfDPMorphism

/-! ### The two families of completed forms -/

section FormComparison

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **The `A`-algebra structure on `D`**, through the structure map `A → D` of the envelope
followed by the `p`-adic completion.  Stated as an instance because
`Crystalline.envelopeCompletion` is not reducible for instance search. -/
@[instance_reducible]
public def algebraBaseEnvelopeCompletion :
    Algebra (A : Type u) (envelopeCompletion E p hp : Type u) :=
  (envelopeCompletionStructureMap E p hp).toRingHom.toAlgebra

attribute [instance] algebraBaseEnvelopeCompletion

/-- **The `A`-algebra structure on `D⟨ξ_i⟩^∧`**, through `ν` after the structure map of `D`.
This is the structure map of the divided power polynomial algebra of [Stacks, Tag 07H6] read
over `A`, and it is the structure for which `σ`, `τ`, `α` and `α⁻¹` are `A`-algebra maps. -/
@[instance_reducible]
public def algebraBaseEnvelopeCompletionVariableRing :
    Algebra (A : Type u) (envelopeCompletionVariableRing E p hp : Type u) :=
  ((envelopeCompletionNu E p hp).comp
    (envelopeCompletionStructureMap E p hp)).toRingHom.toAlgebra

attribute [instance] algebraBaseEnvelopeCompletionVariableRing

/-- **`Ω̂^i_D`**: the `p`-adic completion of the divided power differential forms
`Ω^i_{D/A,γ}` of [Stacks, Tag 07HZ] of the ring `D`. -/
public abbrev envelopeCompletionForms (i : ℕ) : Type u :=
  completedDividedPowerForms p (A : Type u) (envelopeCompletion E p hp).dividedPowers i

/-- **`Ω̂^i_{D⟨ξ_i⟩^∧}`**: the `p`-adic completion of the divided power differential forms
`Ω^i_{D⟨ξ_i⟩^∧/A}` of [Stacks, Tag 07HZ] of the ring `D⟨ξ_i⟩^∧`. -/
public abbrev envelopeCompletionVariableForms (i : ℕ) : Type u :=
  completedDividedPowerForms p (A : Type u) (envelopeCompletionVariableRing E p hp).dividedPowers i

/-- **The universal differential `d : D → Ω̂^1_D`**: the universal divided power differential of
`D` followed by the completion map.  It is the differential a completed de Rham complex over the
ring `D` itself is built from, `Crystalline.completedFormsDifferential` being the one over the
completion of `D`. -/
public abbrev envelopeCompletionFormsDifferential (x : envelopeCompletion E p hp) :
    envelopeCompletionForms E p hp 1 :=
  completedDividedPowerDifferentialOnRing p (A : Type u)
    (envelopeCompletion E p hp).dividedPowers x

/-- **The universal differential `d' : D⟨ξ_i⟩^∧ → Ω̂^1_{D⟨ξ_i⟩^∧}`.** -/
public abbrev envelopeCompletionVariableFormsDifferential
    (x : envelopeCompletionVariableRing E p hp) : envelopeCompletionVariableForms E p hp 1 :=
  completedDividedPowerDifferentialOnRing p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers x

/-- **The wedge product `Ω̂^i_D × Ω̂^1_D → Ω̂^{i+1}_D`**, bilinear over `D`. -/
public abbrev envelopeCompletionFormsWedge (i : ℕ) :
    envelopeCompletionForms E p hp i →ₗ[(envelopeCompletion E p hp : Type u)]
      envelopeCompletionForms E p hp 1 →ₗ[(envelopeCompletion E p hp : Type u)]
        envelopeCompletionForms E p hp (i + 1) :=
  completedDividedPowerWedgeOnRing p (A : Type u) (envelopeCompletion E p hp).dividedPowers i

/-- **The wedge product of the forms of `D⟨ξ_i⟩^∧`**, bilinear over `D⟨ξ_i⟩^∧`. -/
public abbrev envelopeCompletionVariableFormsWedge (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₗ[(envelopeCompletionVariableRing E p hp : Type u)]
      envelopeCompletionVariableForms E p hp 1 →ₗ[(envelopeCompletionVariableRing E p hp :
          Type u)]
        envelopeCompletionVariableForms E p hp (i + 1) :=
  completedDividedPowerWedgeOnRing p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers i

/-- **The Leibniz rule for the forms of `D`**, the hypothesis `hleib` of
`Crystalline.CompletedDeRham.baseChangeComplexHom` for the source complex. -/
public theorem isGradedLeibniz_envelopeCompletionForms :
    CompletedDeRham.IsGradedLeibniz (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
      (completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers)
      (envelopeCompletionFormsDifferential E p hp) :=
  isGradedLeibniz_completedDividedPowerOnRing p (A : Type u)
    (envelopeCompletion E p hp).dividedPowers

/-- **The Leibniz rule for the forms of `D⟨ξ_i⟩^∧`**, the hypothesis `hleib'` of
`Crystalline.CompletedDeRham.baseChangeComplexHom` for the target complex. -/
public theorem isGradedLeibniz_envelopeCompletionVariableForms :
    CompletedDeRham.IsGradedLeibniz (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
      (completedDividedPowerDeRham p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers)
      (envelopeCompletionVariableFormsDifferential E p hp) :=
  isGradedLeibniz_completedDividedPowerOnRing p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers

/-- `d'` is additive, the hypothesis `hd'add` of
`Crystalline.CompletedDeRham.baseChangeComplexHom`. -/
public theorem envelopeCompletionVariableFormsDifferential_add
    (x y : envelopeCompletionVariableRing E p hp) :
    envelopeCompletionVariableFormsDifferential E p hp (x + y) =
      envelopeCompletionVariableFormsDifferential E p hp x +
        envelopeCompletionVariableFormsDifferential E p hp y :=
  completedDividedPowerDifferentialOnRing_add p (A : Type u) _ x y

/-- `d'` obeys the product rule, the hypothesis `hd'leib` of
`Crystalline.CompletedDeRham.baseChangeComplexHom`. -/
public theorem envelopeCompletionVariableFormsDifferential_mul
    (x y : envelopeCompletionVariableRing E p hp) :
    envelopeCompletionVariableFormsDifferential E p hp (x * y) =
      x • envelopeCompletionVariableFormsDifferential E p hp y +
        y • envelopeCompletionVariableFormsDifferential E p hp x :=
  completedDividedPowerDifferentialOnRing_mul p (A : Type u) _ x y

/-- `d` is additive. -/
public theorem envelopeCompletionFormsDifferential_add (x y : envelopeCompletion E p hp) :
    envelopeCompletionFormsDifferential E p hp (x + y) =
      envelopeCompletionFormsDifferential E p hp x +
        envelopeCompletionFormsDifferential E p hp y :=
  completedDividedPowerDifferentialOnRing_add p (A : Type u) _ x y

/-- `d` obeys the product rule. -/
public theorem envelopeCompletionFormsDifferential_mul (x y : envelopeCompletion E p hp) :
    envelopeCompletionFormsDifferential E p hp (x * y) =
      x • envelopeCompletionFormsDifferential E p hp y +
        y • envelopeCompletionFormsDifferential E p hp x :=
  completedDividedPowerDifferentialOnRing_mul p (A : Type u) _ x y

/-! ### `ν` and its comparison of forms -/

/-- **`ν` as an `A`-algebra homomorphism.**  The `A`-algebra structure of `D⟨ξ_i⟩^∧` is `ν` after
that of `D`, so this is a tautology. -/
public def envelopeCompletionNuAlgHom :
    (envelopeCompletion E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionNu E p hp) (fun _ ↦ rfl)

/-- **The graded comparison of completed forms `ψ_* : Ω̂^*_D → Ω̂^*_{D⟨ξ_i⟩^∧}` along `ν`.** -/
public abbrev envelopeCompletionNuForms (i : ℕ) :
    envelopeCompletionForms E p hp i →ₛₗ[(envelopeCompletionNu E p hp).toRingHom]
      envelopeCompletionVariableForms E p hp i :=
  completedMapDifferentialForms p (A : Type u) (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletionVariableRing E p hp).dividedPowers (envelopeCompletionNuAlgHom E p hp)
    (envelopeCompletionNu E p hp).isDPMorphism i

/-- `ψ_1 (d x) = d' (ν x)`: the comparison along `ν` respects the universal differential. -/
public theorem envelopeCompletionNuForms_differential (x : envelopeCompletion E p hp) :
    envelopeCompletionNuForms E p hp 1 (envelopeCompletionFormsDifferential E p hp x) =
      envelopeCompletionVariableFormsDifferential E p hp (envelopeCompletionNu E p hp x) :=
  completedMapDifferentialForms_completedFormsDifferential_of p (A : Type u) _ _ _ _ x

/-- `ψ_{i+1} (ω ∧ η) = ψ_i ω ∧ ψ_1 η`: the comparison along `ν` respects the wedge product. -/
public theorem envelopeCompletionNuForms_wedge (i : ℕ) (omega : envelopeCompletionForms E p hp i)
    (eta : envelopeCompletionForms E p hp 1) :
    envelopeCompletionNuForms E p hp (i + 1)
        (completedDividedPowerWedge p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
          omega eta) =
      completedDividedPowerWedge p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionNuForms E p hp i omega) (envelopeCompletionNuForms E p hp 1 eta) :=
  completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _ i omega eta

/-- `ψ_{i+1} (d ω) = d (ψ_i ω)`: the comparison along `ν` is a map of de Rham complexes. -/
public theorem envelopeCompletionNuForms_deRham (i : ℕ)
    (omega : envelopeCompletionForms E p hp i) :
    envelopeCompletionNuForms E p hp (i + 1)
        (completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
          omega) =
      completedDividedPowerDeRham p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionNuForms E p hp i omega) :=
  completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _ i omega

/-! ### The identity of `D`, as an algebra homomorphism -/

/-- The identity of `D` as an `A`-algebra homomorphism, in the shape
`Crystalline.completedMapDifferentialForms_eq_self` needs. -/
public def envelopeCompletionIdAlgHom :
    (envelopeCompletion E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletion E p hp : Type u) :=
  dpMorphismAlgHom (DPMorphism.id (envelopeCompletion E p hp).dividedPowers) (fun _ ↦ rfl)

/-- The identity algebra homomorphism of `D` is `AlgHom.id`. -/
public theorem envelopeCompletionIdAlgHom_eq :
    envelopeCompletionIdAlgHom E p hp = AlgHom.id (A : Type u) (envelopeCompletion E p hp) :=
  AlgHom.ext fun _ ↦ rfl

/-! ### `σ`, `σ⁻`, `α`, `α⁻¹` and `τ` -/

section Instances

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]

/-- **`σ` as an `A`-algebra homomorphism**, by
`Crystalline.envelopeCompletionSigma_comp_structureMap`. -/
public def envelopeCompletionSigmaAlgHom :
    (envelopeCompletion E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionSigma E p hp) fun a ↦
    congrArg (fun r : DPMorphism A.dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers ↦ r a)
      (envelopeCompletionSigma_comp_structureMap E p hp)

/-- **`σ⁻` as an `A`-algebra homomorphism**, by
`Crystalline.envelopeCompletionSigmaNeg_comp_structureMap`. -/
public def envelopeCompletionSigmaNegAlgHom :
    (envelopeCompletion E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionSigmaNeg E p hp) fun a ↦
    congrArg (fun r : DPMorphism A.dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers ↦ r a)
      (envelopeCompletionSigmaNeg_comp_structureMap E p hp)

/-- **`α` as an `A`-algebra homomorphism**: on the coefficient ring `α` is `σ⁻`, by
`Crystalline.envelopeCompletionAlpha_comp_nu`, and `σ⁻` agrees with `ν` on the base. -/
public def envelopeCompletionAlphaAlgHom :
    (envelopeCompletionVariableRing E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionAlpha E p hp) (by
    have h : ((envelopeCompletionAlpha E p hp).comp (envelopeCompletionNu E p hp)).comp
        (envelopeCompletionStructureMap E p hp) =
          (envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp) := by
      rw [envelopeCompletionAlpha_comp_nu]
      exact envelopeCompletionSigmaNeg_comp_structureMap E p hp
    exact fun a ↦ congrArg (fun r : DPMorphism A.dividedPowers
      (envelopeCompletionVariableRing E p hp).dividedPowers ↦ r a) h)

/-- **`α⁻¹` as an `A`-algebra homomorphism**, by
`Crystalline.envelopeCompletionAlphaInv_comp_nu` and
`Crystalline.envelopeCompletionSigma_comp_structureMap`. -/
public def envelopeCompletionAlphaInvAlgHom :
    (envelopeCompletionVariableRing E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionAlphaInv E p hp) (by
    have h : ((envelopeCompletionAlphaInv E p hp).comp (envelopeCompletionNu E p hp)).comp
        (envelopeCompletionStructureMap E p hp) =
          (envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp) := by
      rw [envelopeCompletionAlphaInv_comp_nu]
      exact envelopeCompletionSigma_comp_structureMap E p hp
    exact fun a ↦ congrArg (fun r : DPMorphism A.dividedPowers
      (envelopeCompletionVariableRing E p hp).dividedPowers ↦ r a) h)

/-- **The graded comparison of completed forms along `σ`.** -/
public abbrev envelopeCompletionSigmaForms (i : ℕ) :
    envelopeCompletionForms E p hp i →ₛₗ[(envelopeCompletionSigma E p hp).toRingHom]
      envelopeCompletionVariableForms E p hp i :=
  completedMapDifferentialForms p (A : Type u) (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletionVariableRing E p hp).dividedPowers (envelopeCompletionSigmaAlgHom E p hp)
    (envelopeCompletionSigma E p hp).isDPMorphism i

/-- **The graded comparison of completed forms along `α`.** -/
public abbrev envelopeCompletionAlphaForms (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[(envelopeCompletionAlpha E p hp).toRingHom]
      envelopeCompletionVariableForms E p hp i :=
  completedMapDifferentialForms p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers
    (envelopeCompletionVariableRing E p hp).dividedPowers (envelopeCompletionAlphaAlgHom E p hp)
    (envelopeCompletionAlpha E p hp).isDPMorphism i

/-- **The graded comparison of completed forms along `α⁻¹`.** -/
public abbrev envelopeCompletionAlphaInvForms (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[(envelopeCompletionAlphaInv E p hp).toRingHom]
      envelopeCompletionVariableForms E p hp i :=
  completedMapDifferentialForms p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers
    (envelopeCompletionVariableRing E p hp).dividedPowers
    (envelopeCompletionAlphaInvAlgHom E p hp)
    (envelopeCompletionAlphaInv E p hp).isDPMorphism i

/-- `ψ_1 (d x) = d' (σ x)`. -/
public theorem envelopeCompletionSigmaForms_differential (x : envelopeCompletion E p hp) :
    envelopeCompletionSigmaForms E p hp 1 (envelopeCompletionFormsDifferential E p hp x) =
      envelopeCompletionVariableFormsDifferential E p hp (envelopeCompletionSigma E p hp x) :=
  completedMapDifferentialForms_completedFormsDifferential_of p (A : Type u) _ _ _ _ x

/-- `ψ_{i+1} (ω ∧ η) = ψ_i ω ∧ ψ_1 η` for the comparison along `σ`. -/
public theorem envelopeCompletionSigmaForms_wedge (i : ℕ)
    (omega : envelopeCompletionForms E p hp i) (eta : envelopeCompletionForms E p hp 1) :
    envelopeCompletionSigmaForms E p hp (i + 1)
        (completedDividedPowerWedge p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
          omega eta) =
      completedDividedPowerWedge p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionSigmaForms E p hp i omega)
        (envelopeCompletionSigmaForms E p hp 1 eta) :=
  completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _ i omega eta

/-- `ψ_{i+1} (d ω) = d (ψ_i ω)` for the comparison along `σ`. -/
public theorem envelopeCompletionSigmaForms_deRham (i : ℕ)
    (omega : envelopeCompletionForms E p hp i) :
    envelopeCompletionSigmaForms E p hp (i + 1)
        (completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
          omega) =
      completedDividedPowerDeRham p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionSigmaForms E p hp i omega) :=
  completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _ i omega

/-- `ψ_1 (d' x) = d' (α x)`. -/
public theorem envelopeCompletionAlphaForms_differential
    (x : envelopeCompletionVariableRing E p hp) :
    envelopeCompletionAlphaForms E p hp 1
        (envelopeCompletionVariableFormsDifferential E p hp x) =
      envelopeCompletionVariableFormsDifferential E p hp (envelopeCompletionAlpha E p hp x) :=
  completedMapDifferentialForms_completedFormsDifferential_of p (A : Type u) _ _ _ _ x

/-- `ψ_{i+1} (ω ∧ η) = ψ_i ω ∧ ψ_1 η` for the comparison along `α`. -/
public theorem envelopeCompletionAlphaForms_wedge (i : ℕ)
    (omega : envelopeCompletionVariableForms E p hp i)
    (eta : envelopeCompletionVariableForms E p hp 1) :
    envelopeCompletionAlphaForms E p hp (i + 1)
        (completedDividedPowerWedge p (A : Type u)
          (envelopeCompletionVariableRing E p hp).dividedPowers i omega eta) =
      completedDividedPowerWedge p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionAlphaForms E p hp i omega)
        (envelopeCompletionAlphaForms E p hp 1 eta) :=
  completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _ i omega eta

/-- `ψ_{i+1} (d ω) = d (ψ_i ω)` for the comparison along `α`. -/
public theorem envelopeCompletionAlphaForms_deRham (i : ℕ)
    (omega : envelopeCompletionVariableForms E p hp i) :
    envelopeCompletionAlphaForms E p hp (i + 1)
        (completedDividedPowerDeRham p (A : Type u)
          (envelopeCompletionVariableRing E p hp).dividedPowers i omega) =
      completedDividedPowerDeRham p (A : Type u)
        (envelopeCompletionVariableRing E p hp).dividedPowers i
        (envelopeCompletionAlphaForms E p hp i omega) :=
  completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _ i omega

/-! ### `τ`, the factorization, and the comparisons along it -/

variable (rho : DPMorphism (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletion E p hp).dividedPowers)
  (hrhoA : rho.comp (envelopeCompletionStructureMap E p hp) =
      envelopeCompletionStructureMap E p hp)
  (hrhoaug : IsAugmentationCompatible rho)

include hrhoaug in
/-- **`τ` as an `A`-algebra homomorphism**: `τ ∘ ν = id_D` and the `A`-algebra structure of
`D⟨ξ_i⟩^∧` is `ν` after that of `D`, so `τ` restricts to the identity on the base. -/
public def envelopeCompletionTauAlgHom :
    (envelopeCompletionVariableRing E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletion E p hp : Type u) :=
  dpMorphismAlgHom (envelopeCompletionTau E p hp rho hrhoaug) fun a ↦
    congrArg (fun r : DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletion E p hp).dividedPowers ↦ r (envelopeCompletionStructureMap E p hp a))
      (envelopeCompletionTau_comp_nu E p hp rho hrhoaug)

include hrhoA in
/-- **`ρ` as an `A`-algebra homomorphism**, which is the hypothesis `hrhoA` on `ρ`. -/
public def envelopeCompletionRhoAlgHom :
    (envelopeCompletion E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletion E p hp : Type u) :=
  dpMorphismAlgHom rho fun a ↦
    congrArg (fun r : DPMorphism A.dividedPowers
      (envelopeCompletion E p hp).dividedPowers ↦ r a) hrhoA

include hrhoaug in
/-- **The graded comparison of completed forms `Ω̂^*_{D⟨ξ_i⟩^∧} → Ω̂^*_D` along `τ`.** -/
public abbrev envelopeCompletionTauForms (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[(envelopeCompletionTau E p hp rho
        hrhoaug).toRingHom] envelopeCompletionForms E p hp i :=
  completedMapDifferentialForms p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers
    (envelopeCompletion E p hp).dividedPowers (envelopeCompletionTauAlgHom E p hp rho hrhoaug)
    (envelopeCompletionTau E p hp rho hrhoaug).isDPMorphism i

include hrhoA in
/-- **The graded comparison of completed forms along `ρ` itself.** -/
public abbrev envelopeCompletionRhoForms (i : ℕ) :
    envelopeCompletionForms E p hp i →ₛₗ[rho.toRingHom] envelopeCompletionForms E p hp i :=
  completedMapDifferentialForms p (A : Type u) (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletion E p hp).dividedPowers (envelopeCompletionRhoAlgHom E p hp rho hrhoA)
    rho.isDPMorphism i

include hrhoaug in
/-- `ψ_1 (d' x) = d (τ x)`. -/
public theorem envelopeCompletionTauForms_differential
    (x : envelopeCompletionVariableRing E p hp) :
    envelopeCompletionTauForms E p hp rho hrhoaug 1
        (envelopeCompletionVariableFormsDifferential E p hp x) =
      envelopeCompletionFormsDifferential E p hp
        (envelopeCompletionTau E p hp rho hrhoaug x) :=
  completedMapDifferentialForms_completedFormsDifferential_of p (A : Type u) _ _ _ _ x

include hrhoaug in
/-- `ψ_{i+1} (ω ∧ η) = ψ_i ω ∧ ψ_1 η` for the comparison along `τ`. -/
public theorem envelopeCompletionTauForms_wedge (i : ℕ)
    (omega : envelopeCompletionVariableForms E p hp i)
    (eta : envelopeCompletionVariableForms E p hp 1) :
    envelopeCompletionTauForms E p hp rho hrhoaug (i + 1)
        (completedDividedPowerWedge p (A : Type u)
          (envelopeCompletionVariableRing E p hp).dividedPowers i omega eta) =
      completedDividedPowerWedge p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
        (envelopeCompletionTauForms E p hp rho hrhoaug i omega)
        (envelopeCompletionTauForms E p hp rho hrhoaug 1 eta) :=
  completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _ i omega eta

include hrhoaug in
/-- `ψ_{i+1} (d ω) = d (ψ_i ω)` for the comparison along `τ`. -/
public theorem envelopeCompletionTauForms_deRham (i : ℕ)
    (omega : envelopeCompletionVariableForms E p hp i) :
    envelopeCompletionTauForms E p hp rho hrhoaug (i + 1)
        (completedDividedPowerDeRham p (A : Type u)
          (envelopeCompletionVariableRing E p hp).dividedPowers i omega) =
      completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers i
        (envelopeCompletionTauForms E p hp rho hrhoaug i omega) :=
  completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _ i omega

/-! ### The factorization identities, read on the forms -/

include hrhoA hrhoaug in
/-- **`ψ_τ ∘ ψ_σ = ψ_ρ`**: the factorization `ρ = τ ∘ σ` read on the completed forms.  The
comparison of completed forms is functorial in the divided power morphism
(`Crystalline.completedMapDifferentialForms_eq_comp`), so this is
`Crystalline.envelopeCompletionTau_comp_sigma`. -/
public theorem envelopeCompletionTauForms_sigmaForms (i : ℕ)
    (x : envelopeCompletionForms E p hp i) :
    envelopeCompletionTauForms E p hp rho hrhoaug i
        (envelopeCompletionSigmaForms E p hp i x) =
      envelopeCompletionRhoForms E p hp rho hrhoA i x :=
  completedMapDifferentialForms_comp_dpMorphism p _ _ _ _ _ _
    (envelopeCompletionTau_comp_sigma E p hp rho hrhoA hrhoaug) i x

/-- **`ψ_α ∘ ψ_σ = ψ_ν`**: the identity `α ∘ σ = ν` read on the completed forms. -/
public theorem envelopeCompletionAlphaForms_sigmaForms (i : ℕ)
    (x : envelopeCompletionForms E p hp i) :
    envelopeCompletionAlphaForms E p hp i (envelopeCompletionSigmaForms E p hp i x) =
      envelopeCompletionNuForms E p hp i x :=
  completedMapDifferentialForms_comp_dpMorphism p _ _ _ _ _ _
    (envelopeCompletionAlpha_comp_sigma E p hp) i x

include hrhoaug in
/-- **`ψ_τ ∘ ψ_ν = id`**: the identity `τ ∘ ν = id_D` read on the completed forms, so that the
comparison along `ν` is a section of the comparison along `τ`. -/
public theorem envelopeCompletionTauForms_nuForms (i : ℕ)
    (x : envelopeCompletionForms E p hp i) :
    envelopeCompletionTauForms E p hp rho hrhoaug i (envelopeCompletionNuForms E p hp i x) = x :=
  completedMapDifferentialForms_comp_dpMorphism_id p _ _ _ _
    (envelopeCompletionTau_comp_nu E p hp rho hrhoaug) i x

/-- The identity of `D⟨ξ_i⟩^∧` as an `A`-algebra homomorphism. -/
public def envelopeCompletionVariableIdAlgHom :
    (envelopeCompletionVariableRing E p hp : Type u) →ₐ[(A : Type u)]
      (envelopeCompletionVariableRing E p hp : Type u) :=
  dpMorphismAlgHom (DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers)
    (fun _ ↦ rfl)

omit [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)] in
/-- The identity algebra homomorphism of `D⟨ξ_i⟩^∧` is `AlgHom.id`. -/
public theorem envelopeCompletionVariableIdAlgHom_eq :
    envelopeCompletionVariableIdAlgHom E p hp =
      AlgHom.id (A : Type u) (envelopeCompletionVariableRing E p hp) :=
  AlgHom.ext fun _ ↦ rfl

/-- **`ψ_α ∘ ψ_{α⁻¹} = id`.** -/
public theorem envelopeCompletionAlphaForms_alphaInvForms (i : ℕ)
    (x : envelopeCompletionVariableForms E p hp i) :
    envelopeCompletionAlphaForms E p hp i (envelopeCompletionAlphaInvForms E p hp i x) = x :=
  completedMapDifferentialForms_comp_dpMorphism_id p _ _ _ _
    (envelopeCompletionAlpha_comp_alphaInv E p hp) i x

/-- **`ψ_{α⁻¹} ∘ ψ_α = id`**, so `ψ_α` is an isomorphism of the graded family of completed
forms of `D⟨ξ_i⟩^∧`. -/
public theorem envelopeCompletionAlphaInvForms_alphaForms (i : ℕ)
    (x : envelopeCompletionVariableForms E p hp i) :
    envelopeCompletionAlphaInvForms E p hp i (envelopeCompletionAlphaForms E p hp i x) = x :=
  completedMapDifferentialForms_comp_dpMorphism_id p _ _ _ _
    (envelopeCompletionAlphaInv_comp_alpha E p hp) i x

end Instances

end FormComparison

end Crystalline

end
