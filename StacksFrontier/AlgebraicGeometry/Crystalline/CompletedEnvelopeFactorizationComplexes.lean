module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeComposite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorizationForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.EndomorphismFactorizationQuasiIso

/-!
# The factorization of [Stacks, Tag 07LH] read on the completed de Rham complexes

`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeFactorization.lean` builds the
factorization `D --σ--> D⟨ξ_i⟩^∧ --τ--> D` of an augmentation-compatible divided power
`A`-algebra endomorphism `ρ` of `D` that the proof of [Stacks, Lemma 60.21.4, Tag 07LH] uses, and
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeFactorizationForms.lean` reads the
four maps `ν`, `σ`, `τ`, `α` on the
completed divided power differential forms.  This module reads them on the **completed de Rham
complexes** of a `D`-module with a completed connection, which is the level at which the source's
argument runs.

## The identification of the carried data with the envelope data

`Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LH` and
`...SmallSite.computes07LH_of_computes07LG_of_factorization` carry the ring `D`, its graded forms,
their wedge product, de Rham differential and universal differential as *parameters*: the library
does not identify the completed divided power forms of a particular `D`, so the statement of
[Stacks, Tag 07LG] and of [Stacks, Tag 07LH] quantifies over them.  Everything in this module is
stated at the concrete data instead —
`Crystalline.envelopeCompletion`, `Crystalline.envelopeCompletionForms`,
`Crystalline.envelopeCompletionFormsWedge`,
`Crystalline.completedDividedPowerDeRham` and
`Crystalline.envelopeCompletionFormsDifferential` — because that is the only place the maps `σ`,
`τ`, `ν` and `α` exist.

## The algebra instances

A base change of completed de Rham complexes along a ring map is indexed by an `Algebra`
instance, and the maps of the factorization are four different ring maps between two rings:
`ν` and `σ` both go `D → D⟨ξ_i⟩^∧`, `τ` goes back, and `α` is an endomorphism of `D⟨ξ_i⟩^∧`.  So
at most one of them can be the instance for a given ordered pair of rings.  The choice made here
is the canonical one: `ν`, the structure map, is installed as the instance
`Crystalline.algebraEnvelopeCompletionNu`, and the other maps are carried as instances by the
consumer, pinned by a hypothesis saying which ring map the instance's structure map is.  That
hypothesis is not a stand-in for a missing proof: it is how a caller says *which* of the four
maps the base change is along.

## Main definitions

* `Crystalline.algebraEnvelopeCompletionNu` — the `D`-algebra structure of `D⟨ξ_i⟩^∧` through the
  structure map `ν`.
* `Crystalline.semilinearCongrRingHom` — a semilinear map read as semilinear over an equal ring
  homomorphism, which is what lets the comparison of forms along `τ` be used at an `Algebra`
  instance whose structure map is `τ` only up to a proof.
* `Crystalline.envelopeDeRhamComplex` — the complex `M ⊗^∧_D Ω̂^*_D`.
* `Crystalline.envelopeCompletionNuComplexHom` — the base change map of completed de Rham
  complexes along `ν`.  This is the map [Stacks, Lemma 60.21.2, Tag 07LD] is about.
* `Crystalline.envelopeCompletionTauComplexHom` — the base change map along `τ` out of the
  complex over `D⟨ξ_i⟩^∧`.
* `Crystalline.envelopeCompletionNuTauConnection`,
  `Crystalline.envelopeCompletionIdConnection` — the connections of the two base changes the
  round trip `τ ∘ ν = id_D` compares.
* `Crystalline.envelopeCompletionSigmaTarget` — `D⟨ξ_i⟩^∧` carrying `σ` as its algebra structure
  over `D`, so that `σ` and `ν` can both be base changed along; `α`, which satisfies
  `α ∘ σ = ν`, is then the algebra structure of `D⟨ξ_i⟩^∧` over that copy.
* `Crystalline.envelopeCompletionSigmaComplexHom`,
  `Crystalline.envelopeCompletionAlphaComplexHom` — the base change maps along `σ` and `α`.
* `Crystalline.envelopeCompletionSigmaAlphaCorrection` — the correction in the composition law
  of those two base changes.
* `Crystalline.envelopeCompletionSigmaNuTransport` — **the transport of the factorization step**:
  the base change along `α` followed by that correction, which carries the base change along `σ`
  to the base change along `ν`.

## Main results

* `Crystalline.isScalarTower_of_algebraMap_eq_tau` — `τ ∘ ν = id_D` as a scalar tower, so the
  instance the composition law of base changes is stated along is available and is not an extra
  assumption.
* `Crystalline.isIso_homologyMap_tauComplexHom` — **the base change map along `τ` out of the
  complex over `D⟨ξ_i⟩^∧` is a quasi-isomorphism as soon as the one along `ν` is.**  The source's
  proof of [Stacks, Tag 07LH] says "the map `τ` has as a left inverse the map
  `D → D⟨x_i⟩^∧`, `x_i ↦ x_i`"; this is that sentence, with the quasi-isomorphism property of the
  left inverse — the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] — as its hypothesis.
* `Crystalline.isScalarTower_envelopeCompletionAlpha_comp_sigma` — `α ∘ σ = ν` as a scalar tower.
* `Crystalline.envelopeCompletionSigmaComplexHom_comp` — **`α ∘ σ = ν` read on the completed de
  Rham complexes**, with
  `Crystalline.isIso_envelopeCompletionSigmaAlphaCorrection` saying that the correction it is
  stated along is an isomorphism.
* `Crystalline.isIso_homologyMap_sigmaComplexHom` — **the base change map along `σ` is a
  quasi-isomorphism as soon as the one along `ν` is and `α` is invertible on homology.**  This is
  the source's "Applying Lemma [Stacks, Tag 07LD] to `α ∘ σ` and using that `α` is an
  isomorphism we conclude that `σ` induces a quasi-isomorphism".
* `Crystalline.isIso_homologyMap_envelopeCompletionSigmaNuTransport` — the transport is
  invertible on homology as soon as `α` is.
* `Crystalline.isIso_homologyMap_of_sigmaFactorization` — **the factorization step of
  [Stacks, Tag 07LH] at this data**: a map out of `M ⊗̂_D Ω̂^*_D` that factors as the base change
  along `σ` followed by some `t` is invertible on homology, given the completed clause of
  [Stacks, Tag 07LD] at `ν`, the invertibility of `α`, and that of `t`.  This is
  `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` filled in with the maps above, and
  `s ≫ transport = incl` is `...envelopeCompletionSigmaComplexHom_comp` on the nose.

## What this route still needs

No tag attribute is placed on anything here.  [Stacks, Tag 07LH] is
`Crystalline.GlobalCrystallineSituation.SmallSite.smoothPresentationPair_computesCohomology` of
`SmallSite/SmoothPresentationCohomology07LH.lean`, proved by a different route: through the
stratification of the crystal and the row coprojections of the double complex of
[Stacks, Tag 07LG].  Along the factorization route of this module, two things stand between it
and the factorization step of [Stacks, Tag 07LH].

The first is the hypothesis `ht` of `Crystalline.isIso_homologyMap_of_sigmaFactorization`: the
base change along `τ` out of the complex over `D⟨ξ_i⟩^∧` base changed along **`σ`**, which is a
different map from the one treated here, is invertible on homology.  Out of the `σ` copy
`τ ∘ σ = ρ` rather than `τ ∘ ν = id_D`, so it has no left inverse coming from a ring map and the
argument of `...isIso_homologyMap_tauComplexHom` does not apply to it; nor does it follow from
the invertibility of the base change along `σ`, since the composite of the two is the map induced
by `ρ`, which is the conclusion.  The source's proof asserts it in one sentence; what that
sentence proves is the statement about `ν` above.

What `ht` does follow from is a **horizontal `D⟨ξ_i⟩^∧`-linear isomorphism between the `ν` copy
and the `σ` copy of `M`** — the stratification attached to an integrable topologically
quasi-nilpotent connection, which is the content of
[Stacks, Proposition 60.17.4, Tag 07JH].  Given such a `Θ`, the base change along `τ` is natural
in the `D⟨ξ_i⟩^∧`-module, so `Θ` read on the complexes carries the base change along `τ` out of
the `σ` copy to the one out of the `ν` copy, and the latter is
`...isIso_homologyMap_tauComplexHom`.  No automorphism of `D⟨ξ_i⟩^∧` can replace `Θ` here: every
rewriting of `τ` out of the `σ` copy by an automorphism of `D⟨ξ_i⟩^∧`, and every factorisation
of `ρ` through `ν` or through the augmentation `ξ_i ↦ 0`, returns a map whose invertibility on
homology is again equivalent to that of the map induced by `ρ`.  This library's Taylor
machinery — `Crystalline.HasTaylorSum` and
`Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` — produces such a comparison only
over a base in which `p` is nilpotent, and `D⟨ξ_i⟩^∧` is not one; the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean` records that as an open debt.

The second is the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD], the hypothesis `hnu` of
both results.  That clause is proved, as clause 2 of
`Crystalline.DividedPowerPolynomial.stacks07LD`, and the library also has it as
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, both in the shape
`M ⊗̂_D Ω̂^*_{D⟨ξ_i⟩^∧}`; what this module does not do is identify that complex with the base
change `(M ⊗̂_D D⟨ξ_i⟩^∧) ⊗̂ Ω̂^*_{D⟨ξ_i⟩^∧}` that `...envelopeCompletionNuComplexHom` is a map
into, so `hnu` stays an argument here.

The hypothesis `halpha`, that `α` is invertible on homology, **is proved**, as
`Crystalline.isIso_homologyMap_envelopeCompletionAlphaComplexHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeAlphaQuasiIso.lean`.  The inputs are
that `α` is an isomorphism of rings
(`Crystalline.envelopeCompletionAlpha_comp_alphaInv`) and that the comparisons of forms along
`α` and `α⁻¹` are mutually inverse
(`Crystalline.envelopeCompletionAlphaInvForms_alphaForms`); the composition law run in both
directions then makes the base change along such a map an isomorphism of complexes, which is
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_of_inverse`.  It stays a hypothesis of
the two results below, and a caller can discharge it with that lemma.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Crystalline

open DividedPowers

universe u

/-! ### Semilinear maps along an equal ring homomorphism -/

/-- **A semilinear map read as semilinear over an equal ring homomorphism.**  The underlying
function is unchanged; only the ring homomorphism the `map_smul'` field is stated along is
replaced by an equal one.

This is what lets a comparison of divided power forms along a map `τ` — which is semilinear over
`τ` itself — be used as the comparison a base change needs, which is semilinear over
`algebraMap`, in a situation where the `Algebra` instance is carried and its structure map is
only *known* to be `τ`. -/
public def semilinearCongrRingHom {R S : Type*} [Semiring R] [Semiring S] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {f g : R →+* S}
    (h : ∀ r, f r = g r) (phi : M →ₛₗ[f] N) : M →ₛₗ[g] N where
  toFun := phi
  map_add' := phi.map_add
  map_smul' r x := by rw [← h r]; exact phi.map_smul' r x

/-- The map `semilinearCongrRingHom h phi` agrees with `phi` at every point. -/
@[simp] public theorem semilinearCongrRingHom_apply {R S : Type*} [Semiring R] [Semiring S]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {f g : R →+* S}
    (h : ∀ r, f r = g r) (phi : M →ₛₗ[f] N) (x : M) :
    semilinearCongrRingHom h phi x = phi x := rfl

/-! ### The complexes over `D` and over `D⟨ξ_i⟩^∧` -/

section Complexes

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **The `D`-algebra structure of `D⟨ξ_i⟩^∧` through the structure map `ν`.**  Of the four maps
of the factorization of [Stacks, Lemma 60.21.4, Tag 07LH] this is the one that is canonical — it
is the structure map of the divided power polynomial algebra — so it is the one installed as an
instance; see the module documentation. -/
@[instance_reducible]
public def algebraEnvelopeCompletionNu :
    Algebra (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) :=
  (envelopeCompletionNu E p hp).toRingHom.toAlgebra

attribute [instance] algebraEnvelopeCompletionNu

/-- The graded de Rham differential of `Ω̂^*_D`. -/
public abbrev envelopeCompletionFormsDeRham (i : ℕ) :
    envelopeCompletionForms E p hp i →+ envelopeCompletionForms E p hp (i + 1) :=
  completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers i

/-- The graded de Rham differential of `Ω̂^*_{D⟨ξ_i⟩^∧}`. -/
public abbrev envelopeCompletionVariableFormsDeRham (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →+ envelopeCompletionVariableForms E p hp (i + 1) :=
  completedDividedPowerDeRham p (A : Type u)
    (envelopeCompletionVariableRing E p hp).dividedPowers i

variable (M : Type u) [AddCommGroup M] [Module (envelopeCompletion E p hp : Type u) M]
  (nabla : CompletedConnection p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp) M)

/-- **The complex `M ⊗^∧_D Ω̂^*_D`** of a `D`-module with a completed connection, with the de Rham
differential `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`. -/
public abbrev envelopeDeRhamComplex
    (hsq : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
      (envelopeCompletionFormsDeRham E p hp) M nabla
      (isGradedLeibniz_envelopeCompletionForms E p hp)) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex p (envelopeCompletion E p hp : Type u) (envelopeCompletionForms E p hp)
    (envelopeCompletionFormsWedge E p hp) (envelopeCompletionFormsDeRham E p hp) M nabla
    (isGradedLeibniz_envelopeCompletionForms E p hp) hsq

/-- **The connection on `M ⊗̂_D D⟨ξ_i⟩^∧` obtained by base change along `ν`.** -/
public abbrev envelopeCompletionNuConnection :
    CompletedConnection p (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionVariableForms E p hp 1)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionVariableRing E p hp : Type u) M) :=
  CompletedConnection.baseChange p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionVariableRing E p hp : Type u) M (envelopeCompletionForms E p hp 1)
    (envelopeCompletionVariableForms E p hp 1)
    (envelopeCompletionVariableFormsDifferential E p hp) (envelopeCompletionNuForms E p hp 1)
    nabla (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionNuForms_differential E p hp)

/-- **The complex `(M ⊗̂_D D⟨ξ_i⟩^∧) ⊗^∧ Ω̂^*_{D⟨ξ_i⟩^∧}`**, the target of the base change along
`ν`. -/
public abbrev envelopeCompletionNuDeRhamComplex
    (hsqNu : CompletedDeRham.IsSquareZero p (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
      (envelopeCompletionVariableFormsDeRham E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionVariableRing E p hp : Type u) M)
      (envelopeCompletionNuConnection E p hp M nabla)
      (isGradedLeibniz_envelopeCompletionVariableForms E p hp)) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex p (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _
    (envelopeCompletionNuConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp) hsqNu

/-- **The base change map of completed de Rham complexes along `ν`**,
`M ⊗^∧_D Ω̂^*_D ⟶ (M ⊗̂_D D⟨ξ_i⟩^∧) ⊗^∧ Ω̂^*_{D⟨ξ_i⟩^∧}`.  This is the map the completed clause of
[Stacks, Lemma 60.21.2, Tag 07LD] asserts to be a quasi-isomorphism. -/
public abbrev envelopeCompletionNuComplexHom
    (hsq : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
      (envelopeCompletionFormsDeRham E p hp) M nabla
      (isGradedLeibniz_envelopeCompletionForms E p hp))
    (hsqNu : CompletedDeRham.IsSquareZero p (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
      (envelopeCompletionVariableFormsDeRham E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionVariableRing E p hp : Type u) M)
      (envelopeCompletionNuConnection E p hp M nabla)
      (isGradedLeibniz_envelopeCompletionVariableForms E p hp)) :
    envelopeDeRhamComplex E p hp M nabla hsq ⟶
      envelopeCompletionNuDeRhamComplex E p hp M nabla hsqNu :=
  CompletedDeRham.baseChangeComplexHom p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionVariableRing E p hp : Type u) M (envelopeCompletionForms E p hp)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionNuForms E p hp)
    (envelopeCompletionFormsWedge E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDifferential E p hp) nabla
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionNuForms_differential E p hp)
    (isGradedLeibniz_envelopeCompletionForms E p hp)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (envelopeCompletionNuForms_wedge E p hp) (envelopeCompletionNuForms_deRham E p hp) hsq hsqNu

end Complexes

/-! ### The base change along `τ`, and the round trip `τ ∘ ν = id_D` -/

section Tau

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))
  [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]
  (rho : DPMorphism (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletion E p hp).dividedPowers)
  (hrhoaug : IsAugmentationCompatible rho)
  [Algebra (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletion E p hp : Type u)]
  (htau : ∀ x : (envelopeCompletionVariableRing E p hp : Type u),
    algebraMap (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletion E p hp : Type u) x = envelopeCompletionTau E p hp rho hrhoaug x)

include htau in
/-- **`τ ∘ ν = id_D` as a scalar tower.**  The `IsScalarTower` instance that the composition law
of base changes of completed de Rham complexes is stated along, for the pair `ν`, `τ`, *is* the
identity `τ ∘ ν = id_D` of `Crystalline.envelopeCompletionTau_comp_nu`: `algebraMap D D` is the
identity, so the tower condition says exactly that the composite of the two structure maps is
it.  So the instance the results below take is not an assumption beyond the factorization. -/
public theorem isScalarTower_of_algebraMap_eq_tau :
    @IsScalarTower (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletion E p hp : Type u)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    have h : envelopeCompletionTau E p hp rho hrhoaug (envelopeCompletionNu E p hp x) = x :=
      congrArg (fun r : DPMorphism (envelopeCompletion E p hp).dividedPowers
          (envelopeCompletion E p hp).dividedPowers ↦ r x)
        (envelopeCompletionTau_comp_nu E p hp rho hrhoaug)
    rw [htau]
    exact h.symm

/-- **The comparison of completed forms along `τ`, read over the carried algebra instance.**  The
underlying function is `Crystalline.envelopeCompletionTauForms` and nothing else; only the ring
homomorphism it is semilinear over is replaced by the structure map of the instance, which `htau`
says is `τ`. -/
public abbrev envelopeCompletionTauFormsOfAlgebra (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[algebraMap
        (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletion E p hp : Type u)]
      envelopeCompletionForms E p hp i :=
  semilinearCongrRingHom (fun x ↦ (htau x).symm)
    (envelopeCompletionTauForms E p hp rho hrhoaug i)

include htau in
/-- `ψ_τ (d' x) = d (x mod D)`, the compatibility a base change along `τ` needs. -/
public theorem envelopeCompletionTauFormsOfAlgebra_differential
    (x : (envelopeCompletionVariableRing E p hp : Type u)) :
    envelopeCompletionTauFormsOfAlgebra E p hp rho hrhoaug htau 1
        (envelopeCompletionVariableFormsDifferential E p hp x) =
      envelopeCompletionFormsDifferential E p hp
        (algebraMap (envelopeCompletionVariableRing E p hp : Type u)
          (envelopeCompletion E p hp : Type u) x) :=
  (envelopeCompletionTauForms_differential E p hp rho hrhoaug x).trans
    (congrArg (envelopeCompletionFormsDifferential E p hp) (htau x).symm)

variable (M : Type u) [AddCommGroup M] [Module (envelopeCompletion E p hp : Type u) M]
  (nabla : CompletedConnection p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp) M)

/-- **The connection on `(M ⊗̂_D D⟨ξ_i⟩^∧) ⊗̂ D` obtained by base changing along `τ`** the
connection of the base change along `ν`. -/
public abbrev envelopeCompletionNuTauConnection :
    CompletedConnection p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp)
      (CompletedConnection.baseChangeCarrier p
        (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletion E p hp : Type u)
        (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
          (envelopeCompletionVariableRing E p hp : Type u) M)) :=
  CompletedConnection.baseChange p (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletion E p hp : Type u)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) M)
    (envelopeCompletionVariableForms E p hp 1) (envelopeCompletionForms E p hp 1)
    (envelopeCompletionFormsDifferential E p hp)
    (envelopeCompletionTauFormsOfAlgebra E p hp rho hrhoaug htau 1)
    (envelopeCompletionNuConnection E p hp M nabla)
    (envelopeCompletionFormsDifferential_add E p hp)
    (envelopeCompletionFormsDifferential_mul E p hp)
    (envelopeCompletionTauFormsOfAlgebra_differential E p hp rho hrhoaug htau)

/-- **The connection on `M ⊗̂_D D` obtained by base changing along the identity of `D`.** -/
public abbrev envelopeCompletionIdConnection :
    CompletedConnection p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
        (envelopeCompletion E p hp : Type u) M) :=
  CompletedConnection.baseChange p (envelopeCompletion E p hp : Type u)
    (envelopeCompletion E p hp : Type u) M (envelopeCompletionForms E p hp 1)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp)
    LinearMap.id nabla (envelopeCompletionFormsDifferential_add E p hp)
    (envelopeCompletionFormsDifferential_mul E p hp) (fun _ ↦ rfl)

variable (hsq : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) M nabla
    (isGradedLeibniz_envelopeCompletionForms E p hp))
  (hsqNu : CompletedDeRham.IsSquareZero p (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) M)
    (envelopeCompletionNuConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp))
  (hsqNuTau : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) _
    (envelopeCompletionNuTauConnection E p hp rho hrhoaug htau M nabla)
    (isGradedLeibniz_envelopeCompletionForms E p hp))
  (hsqId : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) _
    (envelopeCompletionIdConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionForms E p hp))

/-- **The base change map of completed de Rham complexes along `τ`**, out of the complex over
`D⟨ξ_i⟩^∧` of the base change of `(M, ∇)` along `ν`. -/
public abbrev envelopeCompletionTauComplexHom :
    envelopeCompletionNuDeRhamComplex E p hp M nabla hsqNu ⟶
      CompletedDeRham.complex p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
        (envelopeCompletionFormsDeRham E p hp) _
        (envelopeCompletionNuTauConnection E p hp rho hrhoaug htau M nabla)
        (isGradedLeibniz_envelopeCompletionForms E p hp) hsqNuTau :=
  CompletedDeRham.baseChangeComplexHom p (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletion E p hp : Type u)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) M)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionForms E p hp)
    (envelopeCompletionTauFormsOfAlgebra E p hp rho hrhoaug htau)
    (envelopeCompletionVariableFormsWedge E p hp) (envelopeCompletionFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) (envelopeCompletionFormsDeRham E p hp)
    (envelopeCompletionFormsDifferential E p hp)
    (envelopeCompletionNuConnection E p hp M nabla)
    (envelopeCompletionFormsDifferential_add E p hp)
    (envelopeCompletionFormsDifferential_mul E p hp)
    (envelopeCompletionTauFormsOfAlgebra_differential E p hp rho hrhoaug htau)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (isGradedLeibniz_envelopeCompletionForms E p hp)
    (envelopeCompletionTauForms_wedge E p hp rho hrhoaug)
    (envelopeCompletionTauForms_deRham E p hp rho hrhoaug) hsqNu hsqNuTau

/-- A morphism of complexes of abelian groups that is an isomorphism is an isomorphism on
homology in every degree. -/
private theorem isIso_homologyMap_of_isIso {X Y : CochainComplex AddCommGrpCat.{u} ℕ} (f : X ⟶ Y)
    [IsIso f] (j : ℕ) : IsIso (HomologicalComplex.homologyMap f j) :=
  ⟨⟨HomologicalComplex.homologyMap (inv f) j, by
      rw [← HomologicalComplex.homologyMap_comp, IsIso.hom_inv_id,
        HomologicalComplex.homologyMap_id], by
      rw [← HomologicalComplex.homologyMap_comp, IsIso.inv_hom_id,
        HomologicalComplex.homologyMap_id]⟩⟩

/-- A morphism that is invertible on homology in degree `j`, followed by an isomorphism of
complexes, is invertible on homology in degree `j`. -/
private theorem isIso_homologyMap_comp_of_isIso {X Y Z : CochainComplex AddCommGrpCat.{u} ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsIso g) {j : ℕ}
    (hf : IsIso (HomologicalComplex.homologyMap f j)) :
    IsIso (HomologicalComplex.homologyMap (f ≫ g) j) := by
  rw [HomologicalComplex.homologyMap_comp]
  have := isIso_homologyMap_of_isIso g j
  infer_instance

/-- The middle factor of a threefold composite is invertible on homology in a degree when the
composite and the two outer factors are. -/
private theorem isIso_homologyMap_middle {X Y Z W : CochainComplex AddCommGrpCat.{u} ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (j : ℕ)
    (hfgh : IsIso (HomologicalComplex.homologyMap (f ≫ g ≫ h) j))
    (hf : IsIso (HomologicalComplex.homologyMap f j))
    (hh : IsIso (HomologicalComplex.homologyMap h j)) :
    IsIso (HomologicalComplex.homologyMap g j) := by
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hfgh
  have := hf
  have := hh
  have := hfgh
  have : IsIso (HomologicalComplex.homologyMap g j ≫ HomologicalComplex.homologyMap h j) :=
    IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap f j)
      (HomologicalComplex.homologyMap g j ≫ HomologicalComplex.homologyMap h j)
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap g j)
    (HomologicalComplex.homologyMap h j)

include htau hsqId in
/-- **The base change map along `τ` out of the complex over `D⟨ξ_i⟩^∧` is a quasi-isomorphism as
soon as the base change map along `ν` is.**

This is the sentence "the map `τ` has as a left inverse the map `D → D⟨x_i⟩^∧`, `x_i ↦ x_i`, and
we conclude (using Lemma [Stacks, Tag 07LD] once more)" of the source's proof of
[Stacks, Lemma 60.21.4, Tag 07LH], read on the complexes.  The left inverse is `ν`, and the
hypothesis `hnu` — that the base change along `ν` is invertible on homology — is the **completed
clause of [Stacks, Lemma 60.21.2, Tag 07LD]**.  That clause is proved, as clause 2 of
`Crystalline.DividedPowerPolynomial.stacks07LD`
(`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`); this lemma keeps it as
the argument `hnu` so that it is stated for the complexes of this file.

The argument is: `τ ∘ ν = id_D`, so by
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract` the round trip
`α_{ψ_ν} ≫ α_{ψ_τ} ≫ ρ` is an isomorphism of complexes, where `ρ` is the comparison of the twice
base-changed module with the once base-changed one, itself an isomorphism by
`Crystalline.CompletedDeRham.isIso_horizontalComplexHom_baseChangeComposite`.  Cancelling the two
known invertible factors on homology leaves the one along `τ`.

The hypothesis `hM` is the `p`-adic completeness of `M`, which is [Stacks, Tag 07JB] and one of
the four clauses a `Crystalline.Pair` carries; the four `IsSquareZero` hypotheses are what makes
the four complexes complexes at all. -/
public theorem isIso_homologyMap_tauComplexHom
    (hM : IsPAdicallyComplete p (envelopeCompletion E p hp : Type u) M)
    (hnu : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionNuComplexHom E p hp M nabla hsq hsqNu) j))
    (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionTauComplexHom E p hp rho hrhoaug htau M nabla hsqNu hsqNuTau) j) := by
  have := isScalarTower_of_algebraMap_eq_tau E p hp rho hrhoaug htau
  have hcorr := CompletedDeRham.isIso_horizontalComplexHom_baseChangeComposite p
    (envelopeCompletion E p hp : Type u) (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletion E p hp : Type u) M (envelopeCompletionForms E p hp)
    (envelopeCompletionFormsWedge E p hp) (envelopeCompletionFormsDeRham E p hp)
    (envelopeCompletionNuTauConnection E p hp rho hrhoaug htau M nabla)
    (envelopeCompletionIdConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionForms E p hp)
    (CompletedConnection.baseChange_baseChangeComposite p
      (envelopeCompletion E p hp : Type u) (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletion E p hp : Type u) M (envelopeCompletionForms E p hp 1)
      (envelopeCompletionVariableForms E p hp 1) (envelopeCompletionForms E p hp 1)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (envelopeCompletionFormsDifferential E p hp) (envelopeCompletionNuForms E p hp 1)
      (envelopeCompletionTauFormsOfAlgebra E p hp rho hrhoaug htau 1) LinearMap.id nabla
      (envelopeCompletionVariableFormsDifferential_add E p hp)
      (envelopeCompletionVariableFormsDifferential_mul E p hp)
      (envelopeCompletionNuForms_differential E p hp)
      (envelopeCompletionFormsDifferential_add E p hp)
      (envelopeCompletionFormsDifferential_mul E p hp)
      (envelopeCompletionTauFormsOfAlgebra_differential E p hp rho hrhoaug htau)
      (fun omega ↦ (envelopeCompletionTauForms_nuForms E p hp rho hrhoaug 1 omega).symm)
      (fun _ ↦ rfl))
    hsqNuTau hsqId
  have hround := CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract p
    (envelopeCompletion E p hp : Type u) (envelopeCompletionVariableRing E p hp : Type u) M
    (envelopeCompletionForms E p hp) (envelopeCompletionVariableForms E p hp)
    (envelopeCompletionNuForms E p hp)
    (envelopeCompletionTauFormsOfAlgebra E p hp rho hrhoaug htau)
    (envelopeCompletionFormsWedge E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDifferential E p hp) nabla
    (envelopeCompletionFormsDifferential_add E p hp)
    (envelopeCompletionFormsDifferential_mul E p hp)
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionNuForms_differential E p hp)
    (envelopeCompletionTauFormsOfAlgebra_differential E p hp rho hrhoaug htau)
    (isGradedLeibniz_envelopeCompletionForms E p hp)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (envelopeCompletionNuForms_wedge E p hp) (envelopeCompletionNuForms_deRham E p hp)
    (envelopeCompletionTauForms_wedge E p hp rho hrhoaug)
    (envelopeCompletionTauForms_deRham E p hp rho hrhoaug)
    (envelopeCompletionTauForms_nuForms E p hp rho hrhoaug) hM hsq hsqNu hsqNuTau hsqId
  exact isIso_homologyMap_middle _ _ _ j (@isIso_homologyMap_of_isIso _ _ _ hround j) (hnu j)
    (@isIso_homologyMap_of_isIso _ _ _ hcorr j)

end Tau

/-! ### `D⟨ξ_i⟩^∧` as the target of `σ`, and the triangle `α ∘ σ = ν` -/

section SigmaTarget

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))
  [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]

/-- **`D⟨ξ_i⟩^∧` carrying `σ` as its algebra structure over `D`.**

The ring is `Crystalline.envelopeCompletionVariableRing` and nothing else.  The copy exists
because `σ` and `ν` are two different ring maps `D → D⟨ξ_i⟩^∧` and only one of them can be the
`Algebra` instance for that ordered pair: `ν` is, as the canonical structure map, so `σ` is
carried by this copy.  The automorphism `α`, which satisfies `α ∘ σ = ν`, then becomes the
algebra structure of `D⟨ξ_i⟩^∧` over the copy, and `α ∘ σ = ν` becomes a scalar tower. -/
public def envelopeCompletionSigmaTarget : Type u :=
  (envelopeCompletionVariableRing E p hp : Type u)

/-- The copy is the same commutative ring. -/
@[instance_reducible]
public def commRingEnvelopeCompletionSigmaTarget :
    CommRing (envelopeCompletionSigmaTarget E p hp) :=
  inferInstanceAs (CommRing (envelopeCompletionVariableRing E p hp : Type u))

attribute [instance] commRingEnvelopeCompletionSigmaTarget

/-- The forms of `D⟨ξ_i⟩^∧` as modules over the copy. -/
@[instance_reducible]
public def moduleEnvelopeCompletionSigmaTargetForms (i : ℕ) :
    Module (envelopeCompletionSigmaTarget E p hp) (envelopeCompletionVariableForms E p hp i) :=
  inferInstanceAs (Module (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletionVariableForms E p hp i))

attribute [instance] moduleEnvelopeCompletionSigmaTargetForms

/-- The wedge product of the forms of `D⟨ξ_i⟩^∧`, read over the copy. -/
public abbrev envelopeCompletionSigmaTargetFormsWedge (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₗ[envelopeCompletionSigmaTarget E p hp]
      envelopeCompletionVariableForms E p hp 1 →ₗ[envelopeCompletionSigmaTarget E p hp]
        envelopeCompletionVariableForms E p hp (i + 1) :=
  envelopeCompletionVariableFormsWedge E p hp i

omit [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)] in
/-- The Leibniz rule for the forms of `D⟨ξ_i⟩^∧`, read over the copy. -/
public theorem isGradedLeibniz_envelopeCompletionSigmaTargetForms :
    CompletedDeRham.IsGradedLeibniz (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableForms E p hp)
      (envelopeCompletionSigmaTargetFormsWedge E p hp)
      (envelopeCompletionVariableFormsDeRham E p hp)
      (envelopeCompletionVariableFormsDifferential E p hp) :=
  isGradedLeibniz_envelopeCompletionVariableForms E p hp

/-- **`σ` as the algebra structure of the copy over `D`.** -/
@[instance_reducible]
public def algebraEnvelopeCompletionSigma :
    Algebra (envelopeCompletion E p hp : Type u) (envelopeCompletionSigmaTarget E p hp) :=
  (envelopeCompletionSigma E p hp).toRingHom.toAlgebra

attribute [instance] algebraEnvelopeCompletionSigma

/-- **`α` as the algebra structure of `D⟨ξ_i⟩^∧` over the copy.** -/
@[instance_reducible]
public def algebraEnvelopeCompletionAlpha :
    Algebra (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableRing E p hp : Type u) :=
  (envelopeCompletionAlpha E p hp).toRingHom.toAlgebra

attribute [instance] algebraEnvelopeCompletionAlpha

/-- **The comparison of completed forms along `σ`, read over the copy's algebra structure.**  The
map is `Crystalline.envelopeCompletionSigmaForms` and nothing else; the type is restated so that
the identification of the copy's structure map with `σ` is checked once, here, rather than at
every use. -/
public abbrev envelopeCompletionSigmaFormsOfAlgebra (i : ℕ) :
    envelopeCompletionForms E p hp i →ₛₗ[algebraMap (envelopeCompletion E p hp : Type u)
        (envelopeCompletionSigmaTarget E p hp)] envelopeCompletionVariableForms E p hp i :=
  envelopeCompletionSigmaForms E p hp i

/-- **The comparison of completed forms along `α`, read over the copy's algebra structure.** -/
public abbrev envelopeCompletionAlphaFormsOfAlgebra (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[algebraMap
        (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableRing E p hp : Type u)]
      envelopeCompletionVariableForms E p hp i :=
  envelopeCompletionAlphaForms E p hp i

/-- **`α ∘ σ = ν` as a scalar tower.**  This is
`Crystalline.envelopeCompletionAlpha_comp_sigma`, the identity the source's proof of
[Stacks, Lemma 60.21.4, Tag 07LH] records as "`α ∘ σ` maps `x_i` to `x_i`". -/
public theorem isScalarTower_envelopeCompletionAlpha_comp_sigma :
    @IsScalarTower (envelopeCompletion E p hp : Type u) (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableRing E p hp : Type u)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (congrArg (fun r : DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers ↦ r x)
      (envelopeCompletionAlpha_comp_sigma E p hp)).symm

variable (M : Type u) [AddCommGroup M] [Module (envelopeCompletion E p hp : Type u) M]
  (nabla : CompletedConnection p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp) M)

/-- **The connection on `M ⊗̂_{D, σ} D⟨ξ_i⟩^∧` obtained by base change along `σ`.** -/
public abbrev envelopeCompletionSigmaConnection :
    CompletedConnection p (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableForms E p hp 1)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionSigmaTarget E p hp) M) :=
  CompletedConnection.baseChange p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionSigmaTarget E p hp) M (envelopeCompletionForms E p hp 1)
    (envelopeCompletionVariableForms E p hp 1)
    (envelopeCompletionVariableFormsDifferential E p hp)
    (envelopeCompletionSigmaFormsOfAlgebra E p hp 1)
    nabla (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionSigmaForms_differential E p hp)

/-- **The connection on `(M ⊗̂_{D, σ} D⟨ξ_i⟩^∧) ⊗̂_α D⟨ξ_i⟩^∧` obtained by base change along
`α`.** -/
public abbrev envelopeCompletionSigmaAlphaConnection :
    CompletedConnection p (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionVariableForms E p hp 1)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (CompletedConnection.baseChangeCarrier p (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableRing E p hp : Type u)
        (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
          (envelopeCompletionSigmaTarget E p hp) M)) :=
  CompletedConnection.baseChange p (envelopeCompletionSigmaTarget E p hp)
    (envelopeCompletionVariableRing E p hp : Type u)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp) M)
    (envelopeCompletionVariableForms E p hp 1) (envelopeCompletionVariableForms E p hp 1)
    (envelopeCompletionVariableFormsDifferential E p hp)
    (envelopeCompletionAlphaFormsOfAlgebra E p hp 1)
    (envelopeCompletionSigmaConnection E p hp M nabla)
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionAlphaForms_differential E p hp)

variable (hsq : CompletedDeRham.IsSquareZero p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) M nabla
    (isGradedLeibniz_envelopeCompletionForms E p hp))
  (hsqSigma : CompletedDeRham.IsSquareZero p (envelopeCompletionSigmaTarget E p hp)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionSigmaTargetFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _
    (envelopeCompletionSigmaConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp))
  (hsqSigmaAlpha : CompletedDeRham.IsSquareZero p
    (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletionVariableForms E p hp)
    (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _
    (envelopeCompletionSigmaAlphaConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp))

/-- **The base change map of completed de Rham complexes along `σ`.**  This is the map the
source's proof of [Stacks, Lemma 60.21.4, Tag 07LH] shows to be a quasi-isomorphism by
transporting it along `α`. -/
public abbrev envelopeCompletionSigmaComplexHom :
    envelopeDeRhamComplex E p hp M nabla hsq ⟶
      CompletedDeRham.complex p (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionSigmaTargetFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp) hsqSigma :=
  CompletedDeRham.baseChangeComplexHom p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionSigmaTarget E p hp) M (envelopeCompletionForms E p hp)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionSigmaFormsOfAlgebra E p hp)
    (envelopeCompletionFormsWedge E p hp) (envelopeCompletionSigmaTargetFormsWedge E p hp)
    (envelopeCompletionFormsDeRham E p hp) (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDifferential E p hp) nabla
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionSigmaForms_differential E p hp)
    (isGradedLeibniz_envelopeCompletionForms E p hp)
    (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp)
    (envelopeCompletionSigmaForms_wedge E p hp) (envelopeCompletionSigmaForms_deRham E p hp)
    hsq hsqSigma

/-- **The base change map of completed de Rham complexes along the automorphism `α`.** -/
public abbrev envelopeCompletionAlphaComplexHom :
    CompletedDeRham.complex p (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionSigmaTargetFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp) hsqSigma ⟶
      CompletedDeRham.complex p (envelopeCompletionVariableRing E p hp : Type u)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionVariableFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaAlphaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionVariableForms E p hp) hsqSigmaAlpha :=
  CompletedDeRham.baseChangeComplexHom p (envelopeCompletionSigmaTarget E p hp)
    (envelopeCompletionVariableRing E p hp : Type u)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp) M)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableForms E p hp)
    (envelopeCompletionAlphaFormsOfAlgebra E p hp)
    (envelopeCompletionSigmaTargetFormsWedge E p hp)
    (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDifferential E p hp)
    (envelopeCompletionSigmaConnection E p hp M nabla)
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionAlphaForms_differential E p hp)
    (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (envelopeCompletionAlphaForms_wedge E p hp) (envelopeCompletionAlphaForms_deRham E p hp)
    hsqSigma hsqSigmaAlpha

/-- A left factor of a composite that is invertible on homology is itself invertible on homology
when the right factor is. -/
private theorem isIso_homologyMap_left {X Y Z : CochainComplex AddCommGrpCat.{u} ℕ} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : X ⟶ Z) (habc : a ≫ b = c) (j : ℕ)
    (hb : IsIso (HomologicalComplex.homologyMap b j))
    (hc : IsIso (HomologicalComplex.homologyMap c j)) :
    IsIso (HomologicalComplex.homologyMap a j) := by
  have := hb
  have : IsIso (HomologicalComplex.homologyMap a j ≫ HomologicalComplex.homologyMap b j) := by
    rw [← HomologicalComplex.homologyMap_comp, habc]
    exact hc
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap a j)
    (HomologicalComplex.homologyMap b j)

variable (hsqNu : CompletedDeRham.IsSquareZero p
    (envelopeCompletionVariableRing E p hp : Type u)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionVariableRing E p hp : Type u) M)
    (envelopeCompletionNuConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp))

attribute [local instance] isScalarTower_envelopeCompletionAlpha_comp_sigma

/-- **The correction in the composition law of the base changes along `σ` and `α`**: the
comparison `Crystalline.CompletedConnection.baseChangeComposite` of the twice base-changed module
with the module base changed along `ν` directly, read on the complexes.  Its horizontality is
`Crystalline.CompletedConnection.baseChange_baseChangeComposite` at `α ∘ σ = ν`. -/
public abbrev envelopeCompletionSigmaAlphaCorrection :
    CompletedDeRham.complex p (envelopeCompletionVariableRing E p hp : Type u)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionVariableFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaAlphaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionVariableForms E p hp) hsqSigmaAlpha ⟶
      envelopeCompletionNuDeRhamComplex E p hp M nabla hsqNu :=
  CompletedDeRham.horizontalComplexHom p (envelopeCompletionVariableRing E p hp : Type u) _ _
    (envelopeCompletionVariableForms E p hp)
    (CompletedConnection.baseChangeComposite p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableRing E p hp : Type u) M)
    (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionSigmaAlphaConnection E p hp M nabla)
    (envelopeCompletionNuConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (CompletedConnection.baseChange_baseChangeComposite p
      (envelopeCompletion E p hp : Type u) (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableRing E p hp : Type u) M
      (envelopeCompletionForms E p hp 1) (envelopeCompletionVariableForms E p hp 1)
      (envelopeCompletionVariableForms E p hp 1)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (envelopeCompletionVariableFormsDifferential E p hp)
      (envelopeCompletionSigmaFormsOfAlgebra E p hp 1)
      (envelopeCompletionAlphaFormsOfAlgebra E p hp 1)
      (envelopeCompletionNuForms E p hp 1) nabla
      (envelopeCompletionVariableFormsDifferential_add E p hp)
      (envelopeCompletionVariableFormsDifferential_mul E p hp)
      (envelopeCompletionSigmaForms_differential E p hp)
      (envelopeCompletionVariableFormsDifferential_add E p hp)
      (envelopeCompletionVariableFormsDifferential_mul E p hp)
      (envelopeCompletionAlphaForms_differential E p hp)
      (fun omega ↦ (envelopeCompletionAlphaForms_sigmaForms E p hp 1 omega).symm)
      (envelopeCompletionNuForms_differential E p hp))
    hsqSigmaAlpha hsqNu

/-- **The correction is an isomorphism of complexes**, by
`Crystalline.CompletedDeRham.isIso_horizontalComplexHom_baseChangeComposite`: the comparison it
is built from is bijective and horizontal. -/
public theorem isIso_envelopeCompletionSigmaAlphaCorrection :
    IsIso (envelopeCompletionSigmaAlphaCorrection E p hp M nabla hsqSigmaAlpha hsqNu) :=
  CompletedDeRham.isIso_horizontalComplexHom_baseChangeComposite p
    (envelopeCompletion E p hp : Type u) (envelopeCompletionSigmaTarget E p hp)
    (envelopeCompletionVariableRing E p hp : Type u) M
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _ _
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp) _ hsqSigmaAlpha hsqNu

include hsq in
/-- **`α ∘ σ = ν` read on the completed de Rham complexes**: the base change map along `σ`
followed by the one along `α` and the correction is the base change map along `ν`.

This is `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` at the scalar tower
`Crystalline.isScalarTower_envelopeCompletionAlpha_comp_sigma`, which is `α ∘ σ = ν` between the
rings, with the identity of graded comparisons of forms
`Crystalline.envelopeCompletionAlphaForms_sigmaForms`. -/
public theorem envelopeCompletionSigmaComplexHom_comp :
    envelopeCompletionSigmaComplexHom E p hp M nabla hsq hsqSigma ≫
        (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha ≫
          envelopeCompletionSigmaAlphaCorrection E p hp M nabla hsqSigmaAlpha hsqNu) =
      envelopeCompletionNuComplexHom E p hp M nabla hsq hsqNu :=
  CompletedDeRham.baseChangeComplexHom_comp
    (p := p) (D := (envelopeCompletion E p hp : Type u))
    (D' := envelopeCompletionSigmaTarget E p hp)
    (D'' := (envelopeCompletionVariableRing E p hp : Type u)) (M := M)
    (Om := envelopeCompletionForms E p hp) (Om' := envelopeCompletionVariableForms E p hp)
    (Om'' := envelopeCompletionVariableForms E p hp)
    (psi := envelopeCompletionSigmaFormsOfAlgebra E p hp)
    (psi' := envelopeCompletionAlphaFormsOfAlgebra E p hp)
    (psiComp := envelopeCompletionNuForms E p hp)
    (wedge := envelopeCompletionFormsWedge E p hp)
    (wedge' := envelopeCompletionSigmaTargetFormsWedge E p hp)
    (wedge'' := envelopeCompletionVariableFormsWedge E p hp)
    (deRham := envelopeCompletionFormsDeRham E p hp)
    (deRham' := envelopeCompletionVariableFormsDeRham E p hp)
    (deRham'' := envelopeCompletionVariableFormsDeRham E p hp)
    (hpsiComp := fun i omega ↦ (envelopeCompletionAlphaForms_sigmaForms E p hp i omega).symm)
    (d' := envelopeCompletionVariableFormsDifferential E p hp)
    (d'' := envelopeCompletionVariableFormsDifferential E p hp) (nabla := nabla)
    (hd'add := envelopeCompletionVariableFormsDifferential_add E p hp)
    (hd'leib := envelopeCompletionVariableFormsDifferential_mul E p hp)
    (hpsi1 := envelopeCompletionSigmaForms_differential E p hp)
    (hd''add := envelopeCompletionVariableFormsDifferential_add E p hp)
    (hd''leib := envelopeCompletionVariableFormsDifferential_mul E p hp)
    (hpsi'1 := envelopeCompletionAlphaForms_differential E p hp)
    (hpsiComp1 := envelopeCompletionNuForms_differential E p hp)
    (hleib := isGradedLeibniz_envelopeCompletionForms E p hp)
    (hleib' := isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp)
    (hleib'' := isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (hpsi_wedge := envelopeCompletionSigmaForms_wedge E p hp)
    (hpsi_deRham := envelopeCompletionSigmaForms_deRham E p hp)
    (hpsi'_wedge := envelopeCompletionAlphaForms_wedge E p hp)
    (hpsi'_deRham := envelopeCompletionAlphaForms_deRham E p hp)
    (hpsiComp_wedge := envelopeCompletionNuForms_wedge E p hp)
    (hpsiComp_deRham := envelopeCompletionNuForms_deRham E p hp)
    (hsq := hsq) (hsq' := hsqSigma) (hsq'' := hsqSigmaAlpha) (hsqBar := hsqNu)

include hsq in
/-- **The base change map along `σ` is a quasi-isomorphism as soon as the one along `ν` is and
`α` is invertible on the complexes.**

This is the sentence "Applying Lemma [Stacks, Tag 07LD] to `α ∘ σ` (which maps `x_i` to `x_i`)
and using that `α` is an isomorphism we conclude that `σ` induces a quasi-isomorphism" of the
source's proof of [Stacks, Lemma 60.21.4, Tag 07LH], read on the complexes.  Its content is
`Crystalline.envelopeCompletionSigmaComplexHom_comp`; the two hypotheses are the completed clause
of [Stacks, Lemma 60.21.2, Tag 07LD] at `ν` (`hnu`) — proved as clause 2 of
`Crystalline.DividedPowerPolynomial.stacks07LD` and kept here as an argument — and the
invertibility of `α` on homology (`halpha`), which is
`Crystalline.isIso_homologyMap_envelopeCompletionAlphaComplexHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeAlphaQuasiIso.lean`. -/
public theorem isIso_homologyMap_sigmaComplexHom
    (hnu : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionNuComplexHom E p hp M nabla hsq hsqNu) j))
    (halpha : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) j))
    (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionSigmaComplexHom E p hp M nabla hsq hsqSigma) j) := by
  refine isIso_homologyMap_left _ _ _
    (envelopeCompletionSigmaComplexHom_comp E p hp M nabla hsq hsqSigma hsqSigmaAlpha hsqNu) j
    ?_ (hnu j)
  exact isIso_homologyMap_comp_of_isIso _ _
    (isIso_envelopeCompletionSigmaAlphaCorrection E p hp M nabla hsqSigmaAlpha hsqNu) (halpha j)

/-! ### The factorization step at the envelope data -/

/-- **The transport of the factorization step of [Stacks, Lemma 60.21.4, Tag 07LH], at the
envelope data**: the base change along `α` followed by the correction, which is what carries the
base change along `σ` to the base change along `ν`.

It is not an isomorphism of complexes as far as this library knows — only the correction is,
by `Crystalline.isIso_envelopeCompletionSigmaAlphaCorrection` — which is why
`Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` asks only for invertibility on
homology. -/
public abbrev envelopeCompletionSigmaNuTransport :
    CompletedDeRham.complex p (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionSigmaTargetFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp) hsqSigma ⟶
      envelopeCompletionNuDeRhamComplex E p hp M nabla hsqNu :=
  envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha ≫
    envelopeCompletionSigmaAlphaCorrection E p hp M nabla hsqSigmaAlpha hsqNu

/-- **The transport is invertible on homology as soon as `α` is**, the correction being an
isomorphism of complexes. -/
public theorem isIso_homologyMap_envelopeCompletionSigmaNuTransport
    (halpha : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) j))
    (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionSigmaNuTransport E p hp M nabla hsqSigma hsqSigmaAlpha hsqNu) j) := by
  exact isIso_homologyMap_comp_of_isIso _ _
    (isIso_envelopeCompletionSigmaAlphaCorrection E p hp M nabla hsqSigmaAlpha hsqNu) (halpha j)

include hsq in
/-- **The factorization step of [Stacks, Lemma 60.21.4, Tag 07LH] at the envelope data.**

Let `rho` be a map out of `M ⊗̂_D Ω̂^*_D` which factors through the complex over the `σ` copy as
the base change along `σ` followed by some `t`.  If the base change along `ν` is invertible on
homology — the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] — and `α` is invertible on
homology, and `t` is invertible on homology, then `rho` is invertible on homology.

This is `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` instantiated at the maps
this module constructs: `s` is `Crystalline.envelopeCompletionSigmaComplexHom`, `incl` is
`Crystalline.envelopeCompletionNuComplexHom`, the transport is
`Crystalline.envelopeCompletionSigmaNuTransport`, and `s ≫ transport = incl` is exactly
`Crystalline.envelopeCompletionSigmaComplexHom_comp`, which is `α ∘ σ = ν` on the complexes.
The target of `rho` is left general because the base change along `ρ = τ ∘ σ` lands in the
complex of `M ⊗̂_{D, ρ} Ω̂^*_D` and not in `M ⊗̂_D Ω̂^*_D`.

**`ht` is not proved anywhere in this library, and is not a consequence of the other
hypotheses.**  In the source `t` is the base change along `τ` out of the `σ` copy.  The sentence
of the source's proof about the left inverse of `τ` concerns the base change along `τ` out of the
`ν` copy, which is `Crystalline.isIso_homologyMap_tauComplexHom`: there `τ ∘ ν = id_D`, whereas
out of the `σ` copy `τ ∘ σ = ρ` and no section comes from a ring map.  Nor can `ht` be read off
`hfac`, since `H(s) ≫ H(t) = H(rho)` and `H(rho)` is the conclusion.  So this theorem is the
factorization step reduced to that one input, and no tag attribute is placed; [Stacks, Tag 07LH]
is `...SmallSite.smoothPresentationPair_computesCohomology`, by a route that does not need
`ht`. -/
public theorem isIso_homologyMap_of_sigmaFactorization
    (hnu : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionNuComplexHom E p hp M nabla hsq hsqNu) j))
    (halpha : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) j))
    (Z : CochainComplex AddCommGrpCat.{u} ℕ)
    (rho : envelopeDeRhamComplex E p hp M nabla hsq ⟶ Z)
    (t : CompletedDeRham.complex p (envelopeCompletionSigmaTarget E p hp)
        (envelopeCompletionVariableForms E p hp)
        (envelopeCompletionSigmaTargetFormsWedge E p hp)
        (envelopeCompletionVariableFormsDeRham E p hp) _
        (envelopeCompletionSigmaConnection E p hp M nabla)
        (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp) hsqSigma ⟶ Z)
    (hfac : envelopeCompletionSigmaComplexHom E p hp M nabla hsq hsqSigma ≫ t = rho)
    (ht : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap t j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap rho j) :=
  CompletedDeRham.isIso_homologyMap_of_transport rho
    (envelopeCompletionSigmaComplexHom E p hp M nabla hsq hsqSigma)
    (envelopeCompletionSigmaNuTransport E p hp M nabla hsqSigma hsqSigmaAlpha hsqNu)
    (envelopeCompletionNuComplexHom E p hp M nabla hsq hsqNu) t hfac
    (envelopeCompletionSigmaComplexHom_comp E p hp M nabla hsq hsqSigma hsqSigmaAlpha hsqNu)
    (isIso_homologyMap_envelopeCompletionSigmaNuTransport E p hp M nabla hsqSigma hsqSigmaAlpha
      hsqNu halpha)
    hnu ht j

end SigmaTarget

end Crystalline

end
