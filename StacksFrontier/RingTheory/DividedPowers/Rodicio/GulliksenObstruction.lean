module

public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.RingTheory.DividedPowers.Rodicio.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.InfiniteTorDimension
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.LiftedRelation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ResolutionOfAnyAlgebra
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroLift
public import StacksCore.Tactic.StacksAttribute

/-! # Gulliksen's obstruction, Stacks Tag 09PU

Tag 09PU asserts that a relation `∑ rⱼ Fⱼ = 0` among the equations of a finite presentation
`S = R[x₁,…,x_n]/(F₁,…,F_m)`, whose coefficients lie in the image `I` of the annihilator of the
square-zero generator `f` of a surjection `q : R' → R`, and which lifts to `∑ r'ⱼ F'ⱼ = g f` with
`g` non-nilpotent in `S/IS`, forces `S` to have infinite Tor dimension over `R`. The statement is
recorded in `StacksDraft.Rodicio.GulliksenObstruction`.

This file assembles that statement from the four results it is built out of, all of which are
proved:

* `DividedPowers.TateResolution.exists_tateResolution` — a Tate resolution of `S` over `R`,
  along the tautological polynomial presentation of `S` (Tag 09PN);
* `DividedPowers.TateResolution.liftIsDividedPowerSquareZeroLift` — the divided-power square-zero
  lift of a graded divided power polynomial algebra across `q` (Tag 09PS);
* `DividedPowers.TateResolution.exists_mem_grade_two_derivation_eq_lift` — the degree-two class
  `ξ` produced by the relation, and the value of the derivation on it (Tag 09PT);
* `DividedPowers.TateResolution.not_exists_tor_vanishing_bound_of_derivation_class` — the
  Gulliksen engine, which turns such a class into infinite Tor dimension (the engine of Tag
  09PU).

Nothing beyond those is assumed, so Tag 09PU is proved outright here, and with it Rodicio's
theorem (Tag 09PV), whose own argument is complete in
`StacksFrontier.RingTheory.DividedPowers.Rodicio.Basic` apart from this single input.

## Main definitions

* `StacksDraft.Rodicio.ExistsTateResolution` — the component of Tag 09PN asserting that a
  finite-type algebra over a Noetherian ring has a Tate resolution.

## Main results

* `StacksDraft.Rodicio.existsTateResolution` — that component of Tag 09PN, discharged.
* `StacksDraft.Rodicio.not_exists_tor_vanishing_of_lifted_relation` — the content of Tag 09PU,
  for an arbitrary algebra with a finite presentation.
* `StacksDraft.Rodicio.gulliksenObstruction` — Tag 09PU.
* `StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_finite_torDimension` — Rodicio's theorem,
  Tag 09PV.
* `StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_finite_projectiveDimension` — the same
  under the formally stronger hypothesis of finite projective dimension.

## Implementation notes

`ExistsTateResolution` is kept as a named proposition even though it is now proved: it is the
exact interface the Gulliksen argument below consumes, and naming it keeps that interface visible
and separate from the construction that supplies it. It is stated as the existence of *some*
polynomial presentation carrying a resolution, rather than of a resolution extending a prescribed
one, and it is restricted to a finite-type algebra over a Noetherian ring. Both choices make it
the weakest assumption that suffices here, so that it is implied by either half of Tag 09PN — the
resolution of an arbitrary presentation, or the finite resolution of a finite-type algebra. It is
discharged from the first half, which is the one that is proved.

Finite Tor dimension of the `A/I`-module `A/J` in Tag 09PV is spelled as in Stacks Tag 0652: a
degree beyond which `Tor_i^{A/I}(A/J, N)` vanishes for every `A/I`-module `N`. That is precisely
the form in which Gulliksen's obstruction refutes it, so no comparison with another measure of
Tor dimension is needed. The formally stronger hypothesis of finite projective dimension is kept
as the separate corollary
`StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_finite_projectiveDimension`, obtained from
the vanishing of `Tor` above the projective dimension, which is proved here from the balancing
isomorphism in `exists_tor_vanishing_bound_of_finite_projectiveDimension`.

The resolution's own variable set `σ` and the presentation `R[x₁,…,x_n] → S` of the statement are
independent: the relation lives in the latter, while the differential graded algebra resolves `S`
over the former. That is why Tag 09PT takes both, and it is why the content is proved first for
an arbitrary presented algebra `S` and only then specialized to the statement's quotient — with `S`
abstract, no step has to be transported along the definitional unfolding of that quotient.

The instances of the resolution and of its lift are introduced with `let` from the corresponding
*fields*: they are fields of `DividedPowers.TateResolution.Resolution` and of
`DividedPowers.TateResolution.GradedDPAlgebra` rather than instances, and for the lift this is
also what keeps instance search away from the carrier, a reducible abbreviation ending in a
direct limit.

## References

* [Stacks Project, Tag 09PU](https://stacks.math.columbia.edu/tag/09PU)
* [Stacks Project, Tag 09PV](https://stacks.math.columbia.edu/tag/09PV)
-/

@[expose] public noncomputable section

namespace StacksDraft.Rodicio

open CategoryTheory DividedPowers.TateResolution

universe u

/-- **The component of Stacks Tag 09PN asserting existence**: every finite-type algebra over a
Noetherian ring admits a polynomial presentation carrying a Tate resolution — a divided-power
differential graded algebra, free in every degree, resolving the algebra over that presentation.

This is the one input of `StacksDraft.Rodicio.gulliksenObstruction` beyond Tags 09PS and 09PT.
It is implied by both halves of Tag 09PN: by the resolution of an arbitrary polynomial
presentation, and by the finite resolution of a finite-type algebra. -/
public def ExistsTateResolution : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S],
    ∃ (σ : Type u) (φ : MvPolynomial σ R →ₐ[R] S),
      Function.Surjective φ ∧ Nonempty (Resolution R S σ φ)

/-- **The component of Tag 09PN asserting existence, discharged.** The resolution of an arbitrary
polynomial presentation, `DividedPowers.TateResolution.exists_tateResolution`, gives this
outright: it needs neither the Noetherian hypothesis on `R` nor finite type of `S`, because Tate's
tower adjoins a variable for *every* cycle of each degree rather than for a finite generating
family of them. -/
public theorem existsTateResolution : ExistsTateResolution.{u} :=
  fun R S _ _ _ _ _ => exists_tateResolution R S

/-- **The content of Stacks Tag 09PU, for an arbitrary finitely presented algebra.** Let
`q : R' → R` be a surjection whose kernel is generated by `f`, let `S` be presented as
`R[x₁,…,x_n]/(F₁,…,F_m)`, and let `∑ rⱼ Fⱼ = 0` be a relation all of whose coefficients lie in
the image `I` of the annihilator of `f`. If the relation lifts to `∑ r'ⱼ F'ⱼ = g f` over `R'`
with the image of `g` not nilpotent in `S/IS`, then `S` has infinite Tor dimension over `R`.

The proof is the Gulliksen engine fed by the square-zero lift of Tag 09PS and the degree-two
class of Tag 09PT, both taken at a Tate resolution of `S` over `R` (Tag 09PN).

It carries no `@[stacks]` attribute: the tag for Tag 09PU goes on
`StacksDraft.Rodicio.gulliksenObstruction`, which is this statement at the source's own
presented algebra. -/
public theorem not_exists_tor_vanishing_of_lifted_relation
    {R' R S : Type u} [CommRing R'] [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    {q : R' →+* R} (hq : Function.Surjective q) {f : R'}
    (hker : RingHom.ker q = Ideal.span {f})
    (n m : ℕ) (φ₀ : MvPolynomial (Fin n) R →ₐ[R] S)
    (F r : Fin m → MvPolynomial (Fin n) R)
    (hkerφ₀ : RingHom.ker φ₀.toRingHom = Ideal.span (Set.range F))
    (hrel : ∑ j, r j * F j = 0)
    (hcoeff : ∀ (j : Fin m) (e : Fin n →₀ ℕ),
      MvPolynomial.coeff e (r j) ∈ squareZeroAnnihilator q f)
    (F' r' : Fin m → MvPolynomial (Fin n) R')
    (g : MvPolynomial (Fin n) R')
    (hF : ∀ j, MvPolynomial.map q (F' j) = F j)
    (hr : ∀ j, MvPolynomial.map q (r' j) = r j)
    (hlift : ∑ j, r' j * F' j = g * MvPolynomial.C f)
    (hnil : ¬ IsNilpotent (Ideal.Quotient.mk
      (Ideal.map (algebraMap R S) (squareZeroAnnihilator q f))
      (φ₀ (MvPolynomial.map q g)))) :
    ¬ ∃ b : ℕ, ∀ (M : ModuleCat.{u} R) (i : ℕ), b < i →
      Limits.IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj M) := by
  classical
  -- A Tate resolution of `S` over `R`, which is the one thing assumed.
  obtain ⟨σ, φT, hφT, ⟨T⟩⟩ := existsTateResolution R S
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsStrictlyGradedComm T.grade := T.strict
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let : IsCompatibleWithDifferential T.gamma T.differential := T.compatible
  -- The divided-power square-zero lift of the resolution across `q`, which is Tag 09PS.
  let : Ring (liftAlgebra (R' := R') T.polynomial).carrier :=
    (liftAlgebra (R' := R') T.polynomial).ring
  let : Algebra R' (liftAlgebra (R' := R') T.polynomial).carrier :=
    (liftAlgebra (R' := R') T.polynomial).algebra
  let : GradedAlgebra (liftAlgebra (R' := R') T.polynomial).grade :=
    (liftAlgebra (R' := R') T.polynomial).graded
  let : IsStrictlyGradedComm (liftAlgebra (R' := R') T.polynomial).grade :=
    (liftAlgebra (R' := R') T.polynomial).strict
  have h : IsDividedPowerSquareZeroLift q f T.grade T.gamma T.differential
      (liftAlgebra (R' := R') T.polynomial).grade
      (liftAlgebra (R' := R') T.polynomial).gamma
      (liftRingHom q T.polynomial) (liftDerivation q T.polynomial T.differential hq)
      (liftComparisonMap q T.polynomial hker) :=
    liftIsDividedPowerSquareZeroLift q T.polynomial T.differential hq hker
  -- Every element of `S` is the augmentation of a degree-zero element.
  have hε₀ : ∀ s : S, ∃ a : T.A, a ∈ T.grade 0 ∧ T.augmentation a = s := by
    intro s
    obtain ⟨p, rfl⟩ := hφT s
    exact ⟨T.coefficient p, (T.degree_zero _).2 ⟨p, rfl⟩,
      DFunLike.congr_fun T.augmentation_coefficient p⟩
  -- The degree-two class of the relation and the value of the derivation on it, Tag 09PT.
  obtain ⟨ξ, y, hξ, hdξ, hy, hθξ, hεy⟩ :=
    exists_mem_grade_two_derivation_eq_lift h.toIsSquareZeroLift hker T.coefficient
      (liftCoefficientAlgHom (R' := R') T.polynomial)
      (fun a ha => (T.degree_zero a).1 ha)
      (liftCoefficientAlgHom_mem_grade_zero T.polynomial)
      (liftRingHom_coefficient q T.polynomial)
      T.augmentation hε₀ T.augmentation_differential T.exact_zero
      (fun a ha hda => T.exact_positive 1 a Nat.one_pos ha hda)
      n m φ₀ F r hkerφ₀ hrel hcoeff F' r' g hF hr hlift
  -- The Gulliksen engine, which is the engine of Tag 09PU.
  exact not_exists_tor_vanishing_bound_of_derivation_class T hφT q f
    (liftAlgebra (R' := R') T.polynomial).grade
    (liftAlgebra (R' := R') T.polynomial).gamma
    (liftRingHom q T.polynomial) (liftDerivation q T.polynomial T.differential hq)
    (liftComparisonMap q T.polynomial hker) h ξ y hξ hdξ hy hθξ (by rwa [hεy])

/-- **Gulliksen's obstruction, Stacks Tag 09PU.** A relation among the equations of a finite-type
presentation whose coefficients annihilate the square-zero generator, and which lifts to a
non-nilpotent multiple of that generator, forces the presented algebra to have infinite Tor
dimension over the base.

This is `StacksDraft.Rodicio.not_exists_tor_vanishing_of_lifted_relation` at the source's own
presented algebra `R[x₁,…,x_n]/(F₁,…,F_m)`, which is a finite-type `R`-algebra because it is a
quotient of a polynomial ring in finitely many variables. -/
@[stacks 09PU]
public theorem gulliksenObstruction : GulliksenObstruction.{u} := by
  intro R' R _ _ _ _ q hq f hker _hsq n m F r hrel hcoeff F' r' g hF hr hlift hnil
  exact not_exists_tor_vanishing_of_lifted_relation hq hker n m
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range F))) F r
    (by ext p; simp)
    hrel hcoeff F' r' g hF hr hlift hnil

/-- **Rodicio's theorem, Stacks Tag 09PV.** For proper ideals `I ⊆ J` of a Noetherian local ring
`A` with `A/J` of finite Tor dimension over `A/I`, the canonical map `I/𝔪I → J/𝔪J` is injective.

Finite Tor dimension is spelled as in Stacks Tag 0652: a degree beyond which
`Tor_i^{A/I}(A/J, N)` vanishes for every `A/I`-module `N`.

This is `StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_gulliksenObstruction` with its Tag
09PU hypothesis discharged by `StacksDraft.Rodicio.gulliksenObstruction`. -/
@[stacks 09PV]
public theorem injective_mapQ_maximalIdeal_of_finite_torDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J ≠ ⊤) (hIJ : I ≤ J)
    (hTor : ∃ b : ℕ,
      letI : Algebra (A ⧸ I) (A ⧸ J) := (Ideal.Quotient.factor hIJ).toAlgebra
      ∀ (N : ModuleCat.{u} (A ⧸ I)) (i : ℕ), b < i →
        Limits.IsZero (((Tor (ModuleCat.{u} (A ⧸ I)) i).obj
          (ModuleCat.of (A ⧸ I) (A ⧸ J))).obj N)) :
    let f : I →ₗ[A] J := Submodule.inclusion hIJ
    Function.Injective
      ((IsLocalRing.maximalIdeal A • (⊤ : Submodule A I)).mapQ
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A J)) f
        (Submodule.smul_top_le_comap_smul_top _ f)) :=
  injective_mapQ_maximalIdeal_of_gulliksenObstruction gulliksenObstruction I J hI hJ hIJ hTor

/-- A module of projective dimension at most `n` has vanishing `Tor` in every degree above `n`.
The induction is on `n`, replacing a module by the syzygy of a projective presentation. -/
private theorem tor_vanishes_of_projectiveDimensionLE
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ)
    (h : HasProjectiveDimensionLE M n) :
    ∀ (N : ModuleCat.{u} R) (p : ℕ), n < p →
      Limits.IsZero (((Tor (ModuleCat.{u} R) p).obj M).obj N) := by
  induction n generalizing M with
  | zero =>
      intro N p hp
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr h
      exact Limits.IsZero.of_iso
        (isZero_Tor'_succ_of_projective (ModuleCat.{u} R) M N p)
        (((Tor_iso_Tor' R (p + 1)).app M).app N)
  | succ n ih =>
      have hP : Projective (Tor_iso_Tor'.syzygySC R M).X₂ := by
        show Projective (Projective.over M)
        infer_instance
      have hK : HasProjectiveDimensionLE (Tor_iso_Tor'.syzygy R M) n :=
        ((Tor_iso_Tor'.syzygySC_shortExact R M).hasProjectiveDimensionLT_X₃_iff
          n hP).mp h
      intro N p hp
      obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
      have hz : Limits.IsZero
          (((Tor' (ModuleCat.{u} R) (j + 1)).obj
            (Tor_iso_Tor'.syzygy R M)).obj N) :=
        Limits.IsZero.of_iso
          (ih (Tor_iso_Tor'.syzygy R M) hK N (j + 1) (by omega))
          (((Tor_iso_Tor' R (j + 1)).app (Tor_iso_Tor'.syzygy R M)).app N).symm
      exact Limits.IsZero.of_iso hz ((((Tor_iso_Tor' R (j + 2)).app M).app N).trans
        ((Tor_iso_Tor'.tor'Shift R j M).app N))

/-- A module of finite projective dimension has eventually vanishing `Tor`.

This is `StacksDraft.ProjectiveDimension.exists_isZero_Tor_of_finite_projectiveDimension`,
re-derived here from the balancing isomorphism alone. The library proof goes through
`StacksFrontier.Homology.TorAmplitude.GlobalDimension`, whose import closure contains the whole of
`Stacks`; the result is needed on the light side of the Tag 09PW chain, which must stay off that
closure. -/
private theorem exists_tor_vanishing_bound_of_finite_projectiveDimension
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (h : ∃ n : ℕ, HasProjectiveDimensionLT M n) :
    ∃ b : ℕ, ∀ (N : ModuleCat.{u} R) (i : ℕ), b < i →
      Limits.IsZero (((Tor (ModuleCat.{u} R) i).obj M).obj N) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, tor_vanishes_of_projectiveDimensionLE M n
    (hasProjectiveDimensionLT_of_ge M n (n + 1) (by omega))⟩

/-- **Rodicio's theorem under finite projective dimension.** For proper ideals `I ⊆ J` of a
Noetherian local ring `A` with `A/J` of finite projective dimension over `A/I`, the canonical map
`I/𝔪I → J/𝔪J` is injective.

This is `StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_finite_torDimension` under a formally
stronger hypothesis, finite projective dimension forcing uniform vanishing of `Tor` by
`exists_tor_vanishing_bound_of_finite_projectiveDimension`. -/
public theorem injective_mapQ_maximalIdeal_of_finite_projectiveDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J ≠ ⊤) (hIJ : I ≤ J)
    (hpd : ∃ n : ℕ,
      letI : Algebra (A ⧸ I) (A ⧸ J) := (Ideal.Quotient.factor hIJ).toAlgebra
      HasProjectiveDimensionLT (ModuleCat.of (A ⧸ I) (A ⧸ J)) n) :
    let f : I →ₗ[A] J := Submodule.inclusion hIJ
    Function.Injective
      ((IsLocalRing.maximalIdeal A • (⊤ : Submodule A I)).mapQ
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A J)) f
        (Submodule.smul_top_le_comap_smul_top _ f)) := by
  let : Algebra (A ⧸ I) (A ⧸ J) := (Ideal.Quotient.factor hIJ).toAlgebra
  exact injective_mapQ_maximalIdeal_of_finite_torDimension I J hI hJ hIJ
    (exists_tor_vanishing_bound_of_finite_projectiveDimension
      (ModuleCat.of (A ⧸ I) (A ⧸ J)) hpd)

end StacksDraft.Rodicio

end
