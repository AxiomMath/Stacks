module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.CyclicSummands
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.InvariantFactorCount
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.UniformExponent
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Triviality of a vector bundle from the generic and one infinitesimal fibre

Let `f : X ⟶ Spec A` be proper with geometrically connected fibres over a discrete valuation
ring `A`, let `η` be the generic point of `Spec A` and let `X_n ⊆ X` be the closed subscheme cut
out by the `n`-th power of a uniformizer. There is an integer `n`, depending only on `X`, such
that every finite locally free `𝒪_X`-module which is free on `X_η` and on `X_n` is free.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `cohomologyOver`, `genericFibre`, `thickening`: the three objects the statement names, namely
  `Hⁱ(X, ℱ)` as an `A`-module, the generic fibre `X_η` and the thickening `X_n`.
* `TrivialityInput`: the inputs of the source's section-based proof — the finiteness of
  cohomology of a proper morphism ([Stacks, Tag 02O6], proved in this library as
  `moduleFinite_cohomologyOver`) and the comparison of `𝓔` with a free module after derived
  reduction modulo `π^m`.
* `TorsionExponentTransfer` and `torsionExponentTransfer`: the summand-counting step, as a
  statement of pure algebra over a discrete valuation ring, and its proof.
* `pow_smul_torsionBy_eq_bot_iff`, `pow_smul_torsionBy_pi_eq_bot`,
  `pow_smul_torsionBy_eq_bot_of_le`: annihilation of `π^m`-torsion read elementwise, and its
  stability under finite products and under raising the annihilating power.
* `exists_thickening_exponent_free_of_free_generic_and_thickening`: the conclusion of the lemma,
  derived from such an input. The integer produced is `k + e + 1` in the source's notation.
  [Stacks, Tag 0EXF] itself, with no input, is `exists_thickening_exponent_free`
  (`StacksFrontier.AlgebraicGeometry.FreenessOverDVR.FreenessCriterion`), whose proof avoids the
  reduction to a section.

## Implementation notes

`X_n` is formed as the base change of `f` along `Spec (A ⧸ 𝔪^n) ⟶ Spec A`, which over a discrete
valuation ring is the closed subscheme cut out by the `n`-th power of any uniformizer, since
`𝔪 = (π)` for every uniformizer `π`. Freeness of a module is `∃ r, 𝓔 ≅ 𝒪^{⊕r}`, with the rank
chosen separately in each premise and in the conclusion.

**What is proved and what is carried.** The source's proof has two halves. The first reduces to
the case of a section, using Krull-Akizuki, the valuative criterion of properness, flat base
change and a determinant which is invertible because the fibres are proper and connected — the
last step with details omitted in the source. The second half is the computation: `RΓ(X, 𝓔)` and
`RΓ(X, 𝒪_X^{⊕r})` have isomorphic derived reductions modulo `π^m` once `n ≥ m + k`, and over a
discrete valuation ring those reductions split into the cohomology modules, which are direct
sums of cyclic modules; counting the summands `A ⧸ π^m` forces `Hⁱ(X, 𝓔)` to have no cyclic
summand of exponent larger than `e`, and then Nakayama upgrades surjectivity modulo `π^{e + 1}`
to surjectivity.

`TrivialityInput` carries the first half and the derived comparison of the second. Of the
objects that comparison speaks about, this library carries all but one: the subsheaf of
sections supported on the special fibre, which is the source's `𝓔_tors`, is
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` of [Stacks, Tag 084L]; the
quotients `𝓔 ⧸ π^j 𝓔` and the subsheaves `𝓔[π^j]` are
`Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.powQuotient` and `torsionSub`; the
exponent `k` is an instance of Artin-Rees, [Stacks, Tag 01YA]; the two-term complex
`(𝓔 --π^m--> 𝓔)` as an object of `D(𝒪_X)`, with its distinguished triangle, is
`Stacks.Cohomology.DerivedSectionsOverBase.principalKoszulTower`; and
`RΓ(X, -) : D(𝒪_X) ⥤ D(A)` is `AlgebraicGeometry.derivedGlobalSectionsOver`. What is genuinely
absent is the reduction formula `Hⁱ(K ⊗^L A ⧸ π^m) = Hⁱ(K) ⧸ π^m ⊕ Hⁱ⁺¹(K)[π^m]`, an unlabelled
step of the source's proof and not a tag of its own: the library has the Dedekind-domain
splitting `K ≅ ⨁ Hⁱ(K)[-i]` of [Stacks, Tag 0EX0] and the Kunneth short exact sequence over a
Dedekind domain, [Stacks, Tag 0H80], but not the identification `Tor₁(M, A ⧸ π^m) ≅ M[π^m]`
that joins the two.

The summand counting, by contrast, is *not* carried: it is isolated as
`TorsionExponentTransfer`, which mentions no geometry at all, and discharged over every
discrete valuation ring by `torsionExponentTransfer`. What is proved here is the construction
of both exponents and hence of the integer `n`, the transfer of the exponent bound from `𝒪_X`
to `𝓔`, and the two Nakayama steps which turn surjectivity modulo `π^{e + 1}` into freeness.
The construction of `n` is the reason the existential quantifier of the source's statement is
outermost: `k` and `e` depend only on `X`, never on `𝓔`.

No field of `TrivialityInput` asserts the conclusion. Freeness of `𝓔` is only ever offered in
exchange for surjectivity of the evaluation `φ` along the section, and whether `φ` is surjective
is exactly what is proved below; the derived quantities `k`, `r`, `φ` and `ψ` are existentially
bound and pinned by the conjuncts that mention them, and `e` and `n` are constructed, not
supplied.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 0ASP](https://stacks.math.columbia.edu/tag/0ASP)
* [Stacks Project, Tag 0EX0](https://stacks.math.columbia.edu/tag/0EX0)
* [Stacks Project, Tag 0H80](https://stacks.math.columbia.edu/tag/0H80)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `Hⁱ(X, ℱ)` as an `A`-module, the action being restriction of scalars along
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`. This is the module [Stacks, Tag 02O6] asserts to be finite. -/
abbrev cohomologyOver (i : ℕ) (F : X.Modules) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
    (((moduleGlobalSections X).rightDerived i).obj F)

/-- The generic fibre `X_η` of `f`, the fibre over the generic point of `Spec A`. -/
abbrev genericFibre [IsDomain A] : Scheme.{u} := f.fiber (genericPoint (Spec (.of A)))

/-- The restriction `ℱ|_{X_η}` of a sheaf of modules to the generic fibre. -/
abbrev genericFibreRestrict [IsDomain A] (F : X.Modules) : (genericFibre A f).Modules :=
  (Scheme.Modules.pullback (f.fiberι (genericPoint (Spec (.of A))))).obj F

/-- The thickening `X_n`, the closed subscheme of `X` cut out by the `n`-th power of a
uniformizer, formed as the base change of `f` along `Spec (A ⧸ 𝔪^n) ⟶ Spec A`. -/
abbrev thickening [IsLocalRing A] (n : ℕ) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n))))

/-- The restriction `ℱ|_{X_n}` of a sheaf of modules to the thickening `X_n`. -/
abbrev thickeningRestrict [IsLocalRing A] (n : ℕ) (F : X.Modules) :
    (thickening A f n).Modules :=
  (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)))))).obj F

/-- A sheaf of modules is **free of finite rank** if it is isomorphic to `𝒪^{⊕r}` for some
natural number `r`. -/
def IsFreeOfFiniteRank {Y : Scheme.{u}} (F : Y.Modules) : Prop :=
  ∃ r : ℕ, Nonempty (F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r)))

/-- The free rank of an `A`-module, the rank of its quotient by the torsion submodule. Over a
discrete valuation ring this is the number of free summands in a cyclic decomposition. -/
abbrev freeRank (M : Type u) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank A (M ⧸ Submodule.torsion A M)

/-- The reduction of `Hⁱ(X, ℱ)` modulo `π^m`. -/
abbrev cohomologyModPow (π : A) (m i : ℕ) (F : X.Modules) : Type u :=
  cohomologyOver A f i F ⧸
    (Ideal.span {π} ^ m • (⊤ : Submodule A (cohomologyOver A f i F)))

/-- The `π^m`-torsion of `Hⁱ(X, ℱ)`. -/
abbrev cohomologyTorsion (π : A) (m i : ℕ) (F : X.Modules) :
    Submodule A (cohomologyOver A f i F) :=
  Submodule.torsionBy A (cohomologyOver A f i F) (π ^ m)

variable [IsDomain A] [IsLocalRing A]

/-- The inputs of the source's section-based proof of [Stacks, Tag 0EXF].

`moduleFinite` and `moduleFiniteUnit` are the conclusion of [Stacks, Tag 02O6] for `f`, which
the library proves (`moduleFinite_cohomologyOver`).
`comparison` is the source's first half — the reduction to the case of a section, whose final
step (invertibility of a determinant which is invertible at one point of each fibre) the source
itself leaves to the reader — together with the derived comparison of its second half, read on
cohomology: for `n ≥ m + k` the two-term complexes `(𝓔 --π^m--> 𝓔)` and `(𝒪_X^{⊕r} --π^m-->
𝒪_X^{⊕r})` are isomorphic in `D(𝒪_X)`, so `RΓ(X, 𝓔) ⊗^L A ⧸ π^m` and `RΓ(X, 𝒪_X^{⊕r}) ⊗^L
A ⧸ π^m` are isomorphic in `D(A)`, compatibly with the section.

No field asserts the conclusion: freeness of `𝓔` is only ever offered in exchange for
surjectivity of the evaluation `φ`, and whether `φ` is surjective is what the theorem proves. -/
structure TrivialityInput (π : A) : Prop where
  /-- [Stacks, Tag 02O6]: `Hⁱ(X, 𝓔)` is a finite `A`-module for `𝓔` finite locally free. -/
  moduleFinite : ∀ E : X.Modules, E.IsFiniteLocallyFree → ∀ i : ℕ,
    Module.Finite A (cohomologyOver A f i E)
  /-- [Stacks, Tag 02O6] for the structure sheaf. -/
  moduleFiniteUnit : ∀ i : ℕ,
    Module.Finite A (cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf))
  /-- The reduction to a section and the derived comparison modulo `π^m`, for a thickening
  exponent `m + k` with `k` depending only on `X`. The data produced is the rank `r`, the
  evaluation `φ` of global sections along the section, and the contribution `ψ` of the
  `π^m`-torsion in degree one to the reduction of that evaluation. -/
  comparison : ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ∀ E : X.Modules, E.IsFiniteLocallyFree →
    IsFreeOfFiniteRank (genericFibreRestrict A f E) →
    IsFreeOfFiniteRank (thickeningRestrict A f (m + k) E) →
    ∃ (r : ℕ) (φ : cohomologyOver A f 0 E →ₗ[A] (Fin r → A))
      (ψ : cohomologyTorsion A f π m 1 E →ₗ[A] (Fin r → A ⧸ Ideal.span {π} ^ m)),
      (Function.Surjective φ → IsFreeOfFiniteRank E) ∧
      (∀ i : ℕ, freeRank A (cohomologyOver A f i E) =
        freeRank A (Fin r → cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf))) ∧
      (∀ i : ℕ, Nonempty
        ((cohomologyModPow A f π m i E × cohomologyTorsion A f π m (i + 1) E) ≃ₗ[A]
          (((Fin r → cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf)) ⧸
              (Ideal.span {π} ^ m • (⊤ : Submodule A
                (Fin r → cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf))))) ×
            Submodule.torsionBy A
              (Fin r → cohomologyOver A f (i + 1) (SheafOfModules.unit X.ringCatSheaf))
              (π ^ m)))) ∧
      LinearMap.range ((Ideal.span {π} ^ m).mkQ.compLeft (Fin r) ∘ₗ φ) ⊔
        LinearMap.range ψ = ⊤

end Stacks.AlgebraicGeometry.FreenessOverDVR

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

/-- **The summand-counting transfer over a discrete valuation ring.** Two finite modules whose
reductions modulo `π^m`, paired with the `π^m`-torsion in the next degree, are isomorphic and
whose free ranks agree have the same number of cyclic summands of exponent at least `m`; so if
one pair has all its cyclic summands of exponent at most `m - 1`, so has the other.

This is pure commutative algebra, and it is the step of [Stacks, Tag 0EXF] that turns the
derived comparison into the exponent bound used by the final Nakayama argument. -/
def TorsionExponentTransfer (A : Type u) [CommRing A] (π : A) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ (H H' G G' : Type u)
    [AddCommGroup H] [Module A H] [Module.Finite A H]
    [AddCommGroup H'] [Module A H'] [Module.Finite A H']
    [AddCommGroup G] [Module A G] [Module.Finite A G]
    [AddCommGroup G'] [Module A G'] [Module.Finite A G'],
    Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A G (π ^ m) = ⊥ →
    Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A G' (π ^ m) = ⊥ →
    freeRank A H = freeRank A G →
    Nonempty (((H ⧸ (Ideal.span {π} ^ m • (⊤ : Submodule A H))) ×
        Submodule.torsionBy A H' (π ^ m)) ≃ₗ[A]
      ((G ⧸ (Ideal.span {π} ^ m • (⊤ : Submodule A G))) ×
        Submodule.torsionBy A G' (π ^ m))) →
    Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A H' (π ^ m) = ⊥

variable {A : Type u} [CommRing A] {π : A}

/-- Annihilation of a submodule by `π^e`, read elementwise. -/
private theorem pow_smul_eq_bot_iff {M : Type*} [AddCommGroup M] [Module A M] {e : ℕ}
    {N : Submodule A M} : Ideal.span {π} ^ e • N = ⊥ ↔ ∀ x ∈ N, π ^ e • x = 0 := by
  constructor
  · intro h x hx
    have hmem : π ^ e • x ∈ Ideal.span {π} ^ e • N := by
      refine Submodule.smul_mem_smul ?_ hx
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [h] at hmem
    exact (Submodule.mem_bot _).1 hmem
  · intro h
    rw [eq_bot_iff]
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_smul, h x hx, smul_zero]
    exact Submodule.zero_mem _

/-- Annihilation of the `π^m`-torsion by `π^e`, read elementwise. -/
theorem pow_smul_torsionBy_eq_bot_iff {M : Type*} [AddCommGroup M] [Module A M] {e m : ℕ} :
    Ideal.span {π} ^ e • Submodule.torsionBy A M (π ^ m) = ⊥ ↔
      ∀ x : M, π ^ m • x = 0 → π ^ e • x = 0 := by
  simp only [pow_smul_eq_bot_iff, Submodule.mem_torsionBy_iff]

/-- The `π^m`-torsion of a finite product is annihilated by whatever annihilates that of the
factor. -/
theorem pow_smul_torsionBy_pi_eq_bot {M : Type*} [AddCommGroup M] [Module A M] {e m : ℕ}
    (ι : Type*) (h : Ideal.span {π} ^ e • Submodule.torsionBy A M (π ^ m) = ⊥) :
    Ideal.span {π} ^ e • Submodule.torsionBy A (ι → M) (π ^ m) = ⊥ := by
  rw [pow_smul_torsionBy_eq_bot_iff] at h ⊢
  intro x hx
  funext j
  exact h (x j) (congrFun hx j)

/-- Raising the annihilating power preserves annihilation of the `π^m`-torsion. -/
theorem pow_smul_torsionBy_eq_bot_of_le {M : Type*} [AddCommGroup M] [Module A M] {e e' m : ℕ}
    (hle : e' ≤ e) (h : Ideal.span {π} ^ e' • Submodule.torsionBy A M (π ^ m) = ⊥) :
    Ideal.span {π} ^ e • Submodule.torsionBy A M (π ^ m) = ⊥ := by
  rw [pow_smul_torsionBy_eq_bot_iff] at h ⊢
  intro x hx
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, h x hx, smul_zero]

/-- The summand-counting transfer holds over every discrete valuation ring: it is
`pow_smul_torsionBy_eq_bot_of_linearEquiv_mod_pow`, read at the universe of the cohomology
modules. -/
theorem torsionExponentTransfer [IsDomain A] [IsDiscreteValuationRing A] (hπ : Irreducible π) :
    TorsionExponentTransfer A π := by
  intro m hm H H' G G' _ _ _ _ _ _ _ _ _ _ _ _ hG hG' hrank hiso
  exact (pow_smul_torsionBy_eq_bot_of_linearEquiv_mod_pow hπ hm hG hG' hrank hiso).2

end Stacks.AlgebraicGeometry.FreenessOverDVR

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The conclusion of [Stacks, Tag 0EXF] from the section-based inputs.** Let
`f : X ⟶ Spec A` be a morphism to the spectrum of a discrete valuation ring `A`, let `η` be the
generic point of `Spec A` and let `X_n ⊆ X` be the closed subscheme cut out by the `n`-th power
of a uniformizer `π`. Given `TrivialityInput A f π`, there is an integer `n`, independent of the
module, such that every finite locally free `𝒪_X`-module which is free on `X_η` and on `X_n` is
free.

The integer produced is `e + 1 + k`, which is the source's `k + e + 1`: `k` is the Artin-Rees
exponent carried by `TrivialityInput.comparison`, and `e` is an exponent annihilating the
`π`-power torsion of `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, both of which depend only on `X`.

[Stacks, Tag 0EXF] itself, with no input, is `exists_thickening_exponent_free`. This declaration
stays conditional: the fields `moduleFinite` and `moduleFiniteUnit` follow from
`moduleFinite_cohomologyOver`, but `comparison` (the reduction to a section and the derived
comparison modulo `π^m`) is not proved in the library, and the statement assumes no properness of
`f`, so it cannot be read off from `exists_thickening_exponent_free`, which needs `IsProper f`. -/
theorem exists_thickening_exponent_free_of_free_generic_and_thickening
    {π : A} (hπ : Irreducible π) (h : TrivialityInput A f π) :
    ∃ n : ℕ, 0 < n ∧ ∀ E : X.Modules, E.IsFiniteLocallyFree →
      IsFreeOfFiniteRank (genericFibreRestrict A f E) →
      IsFreeOfFiniteRank (thickeningRestrict A f n E) →
      IsFreeOfFiniteRank E := by
  classical
  have hcount : TorsionExponentTransfer A π := torsionExponentTransfer hπ
  obtain ⟨k, hk⟩ := h.comparison
  have hfin0 := h.moduleFiniteUnit 0
  have hfin1 := h.moduleFiniteUnit 1
  obtain ⟨e0, he0⟩ := exists_forall_pow_smul_torsionBy_eq_bot
    (A := A) (H := cohomologyOver A f 0 (SheafOfModules.unit X.ringCatSheaf)) π
  obtain ⟨e1, he1⟩ := exists_forall_pow_smul_torsionBy_eq_bot
    (A := A) (H := cohomologyOver A f 1 (SheafOfModules.unit X.ringCatSheaf)) π
  refine ⟨max e0 e1 + 1 + k, by omega, fun E hE hgen hthick => ?_⟩
  obtain ⟨r, φ, ψ, hfree, hrank, hiso, hsurj⟩ :=
    hk (max e0 e1 + 1) (by omega) E hE hgen hthick
  have hfinE0 := h.moduleFinite E hE 0
  have hfinE1 := h.moduleFinite E hE 1
  have htors : Ideal.span {π} ^ max e0 e1 • cohomologyTorsion A f π (max e0 e1 + 1) 1 E = ⊥ := by
    have hG : ∀ (i e : ℕ), e ≤ max e0 e1 →
        (∀ m, Ideal.span {π} ^ e • Submodule.torsionBy A
          (cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf)) (π ^ m) = ⊥) →
        Ideal.span {π} ^ max e0 e1 • Submodule.torsionBy A
          (Fin r → cohomologyOver A f i (SheafOfModules.unit X.ringCatSheaf))
          (π ^ (max e0 e1 + 1)) = ⊥ :=
      fun i e hle he => pow_smul_torsionBy_pi_eq_bot (Fin r)
        (pow_smul_torsionBy_eq_bot_of_le hle (he _))
    simpa using hcount (max e0 e1 + 1) (by omega) (cohomologyOver A f 0 E)
      (cohomologyOver A f 1 E)
      (Fin r → cohomologyOver A f 0 (SheafOfModules.unit X.ringCatSheaf))
      (Fin r → cohomologyOver A f 1 (SheafOfModules.unit X.ringCatSheaf))
      (by simpa using hG 0 e0 (le_max_left _ _) he0)
      (by simpa using hG 1 e1 (le_max_right _ _) he1) (hrank 0) (hiso 0)
  have hT : Ideal.span {π} ^ max e0 e1 • LinearMap.range ψ = ⊥ := by
    rw [pow_smul_eq_bot_iff]
    rintro _ ⟨y, rfl⟩
    have hzero : π ^ max e0 e1 • y = 0 := Subtype.ext (pow_smul_eq_bot_iff.1 htors y y.2)
    rw [← map_smul, hzero, map_zero]
  exact hfree (LinearMap.range_eq_top.mp
    (range_eq_top_of_sup_range_mkQ_comp_eq_top hπ φ (LinearMap.range ψ) hT hsurj))

end Stacks.AlgebraicGeometry.FreenessOverDVR
