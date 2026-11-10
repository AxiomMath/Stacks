module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Completion
public import StacksFrontier.Deformation.Examples.Geometric.Henselization
public import StacksFrontier.Deformation.Examples.Geometric.CompletionSmooth
public import StacksFrontier.Deformation.Examples.Geometric.Localization
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationTransport
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection
public import StacksFrontier.Deformation.Smooth.Pi
public import StacksFrontier.RingTheory.AdicCompletion.IntersectionOfMaximalIdeals
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Henselian.Pair.HenselizationAtMaximalIdeals

/-!
# Isolated singularities: the chain of deformation categories at the singular points

**Stacks 0DZF** considers a finite type algebra `P` over a field `k` which is smooth over `k`
away from finitely many maximal ideals `𝔪 1, …, 𝔪 n`, and the chain of deformation categories
`Def_P → ∏ Def_{P_{𝔪 i}} → ∏ Def_{P^h_{𝔪 i}} → ∏ Def_{P^∧_{𝔪 i}}`. It asserts that each of the
three maps is smooth and induces an isomorphism on tangent spaces, and that those tangent spaces
are finite dimensional.

This file supplies the ring-theoretic input of the source's proof and its completion leg.

The last term of the chain is written in the source with the *completion of the local ring*
`P_{𝔪 i}`, while the functor landing in it is the completion of the *henselization* `P^h_{𝔪 i}`;
the two agree, which the source records in the parenthetical "the completion of the henselization
is the completion". That identification is the first group of results below: the canonical map
`R^∧_I → (R^h)^∧_{I R^h}` on `I`-adic completions induced by the structural map of the
henselization of the pair `(R, I)` is bijective.

The source's proof does not treat the three maps one at a time. It works with `J = 𝔪 1 ∩ … ∩ 𝔪 n`
and applies **Stacks 0DZ5** and **Stacks 0DZD** to `P` *itself* — where the finite type
hypothesis holds — obtaining the composite `Def_P → Def_{P^∧_J}`, respectively
`Def_P → Def_{P^h}`, and then transports along the decompositions `P^∧_J ≅ ∏ P^∧_{𝔪 i}` and
`P^h ≅ ∏ P^h_{𝔪 i}`. Those two decompositions are the second and third groups of results below,
and the transport of a deformation category along a ring isomorphism is
`Deformation.Examples.ringDeformationTransport`. The completion leg is assembled here, in the
form of the composite of all three maps of the chain; the individual maps of the chain are
recovered in `StacksFrontier/Deformation/Examples/Geometric/IsolatedSingularitiesChain.lean`.

## Main results

* `Deformation.Examples.bijective_adicCompletionMap_henselization`: the canonical map from the
  `I`-adic completion of `R` to the `I R^h`-adic completion of the henselization of the pair
  `(R, I)` is bijective.
* `Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing`: the same for the local
  ring of `P` at a prime and its henselization along the maximal ideal, which is the
  identification of the final ring of the chain of **Stacks 0DZF**.
* `Deformation.Examples.bijective_adicCompletion_iInf_to_pi_completedLocalRing` and
  `Deformation.Examples.adicCompletionIInfPiEquiv`: the decomposition `P^∧_J ≅ ∏ P^∧_{𝔪 i}`.
* `Deformation.Examples.exists_ringEquiv_henselization_iInf_pi_henselizedLocalRing`: the
  decomposition `P^h ≅ ∏ P^h_{𝔪 i}`.
* `Deformation.Examples.isSmooth_piCompletedLocalRingFunctor` and
  `Deformation.Examples.bijective_differential_piCompletedLocalRingFunctor`: **the completion leg
  of Stacks 0DZF**, that is the composite `Def_P → ∏ Def_{P^∧_{𝔪 i}}` of all three maps of the
  chain, is smooth and induces an isomorphism on tangent spaces.

## Implementation notes

No Noetherian hypothesis is needed for the identification of the completion of the henselization.
Stacks 0AGV gives it for a Noetherian pair along with Noetherianness of the henselization, but the
identification itself only uses that the henselization is ind-étale, hence flat, and an
isomorphism modulo `I`; the passage to all powers of `I` is
`Stacks.quotientMap_pow_bijective_of_flat`, and the passage from all powers to the completions is
`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective`. So the statement
below is the one the source uses, with no hypothesis beyond a ring and an ideal.

The local ring of `P` at a prime `𝔮` is `Localization 𝔮.primeCompl` and its henselization is the
henselization of the pair consisting of that local ring and its maximal ideal, which is the
source's `P^h_𝔮`.

The completion leg lands in the deformation category of the *product ring* `∏ P^∧_{𝔪 i}`, which
forces its index type into the universe of `P`: the product of a family indexed by `ι : Type uι`
lives in `Type (max uι w)`. The source's own target is the *product of the deformation categories*
of the factors; identifying the two is a step the source leaves implicit, and it is
`Deformation.Examples.piDeformationFunctor` together with
`Deformation.Examples.piDeformationFunctor_full` and
`Deformation.Examples.piDeformationFunctor_faithful`, in
`StacksFrontier/Deformation/Examples/Geometric/RingDeformationPiFullyFaithful.lean`. The chain of
the tag itself, map by map, is assembled from this file in
`StacksFrontier/Deformation/Examples/Geometric/IsolatedSingularitiesChain.lean`.

The smoothness hypothesis of the completion leg is written as 0DZ5 wants it at `J`, namely
smoothness at every prime not containing `J`. That is implied by, and not stronger than, the
tag's own hypothesis: a prime containing none of the `𝔪 i` is in particular not equal to any of
them, and conversely a prime equal to some `𝔪 i` does contain `J`.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DZ5](https://stacks.math.columbia.edu/tag/0DZ5)
* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0AGV](https://stacks.math.columbia.edu/tag/0AGV)
-/

@[expose] public section

open CategoryTheory

universe uι u w

namespace Deformation.Examples

/-- **The completion of a henselization is the completion.** For a ring `R` and an ideal `I`,
the structural map `R → R^h` to the henselization of the pair `(R, I)` induces a bijection from
the `I`-adic completion of `R` onto the `I R^h`-adic completion of `R^h`.

The map `R → R^h` is ind-étale, hence flat, and is an isomorphism modulo `I`; therefore it is an
isomorphism modulo every power of `I`, and so an isomorphism on the completions. -/
@[ega "IV 18.6.6" "more general"]
public theorem bijective_adicCompletionMap_henselization
    (R : Type w) [CommRing R] (I : Ideal R) :
    Function.Bijective
      (adicCompletionMap (algebraMap R (henselization R I : Type w)) I
        (I.map (algebraMap R (henselization R I : Type w))) le_rfl) :=
  Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective _ _
    (flat_and_bijective_quotientMap_pow_of_ind_etale R I (henselization R I : Type w)
      (ind_henselization R I) (bijective_quotientMap_henselization R I)).2

/-- The local ring of `P` at the prime `𝔮`, the source's `P_𝔮`. -/
public abbrev localRingAt {P : Type w} [CommRing P] (q : PrimeSpectrum P) : Type w :=
  Localization q.asIdeal.primeCompl

/-- The henselization of the local ring of `P` at `𝔮`, along its maximal ideal: the source's
`P^h_𝔮`. -/
public noncomputable abbrev henselizedLocalRingAt {P : Type w} [CommRing P]
    (q : PrimeSpectrum P) : Type w :=
  (henselization (localRingAt q) (IsLocalRing.maximalIdeal (localRingAt q)) : Type w)

/-- The image in `P^h_𝔮` of the maximal ideal of `P_𝔮`: the distinguished ideal of the
henselian pair `P^h_𝔮`. -/
public noncomputable abbrev henselizedMaximalIdealAt {P : Type w} [CommRing P]
    (q : PrimeSpectrum P) : Ideal (henselizedLocalRingAt q) :=
  (IsLocalRing.maximalIdeal (localRingAt q)).map
    (algebraMap (localRingAt q) (henselizedLocalRingAt q))

/-- **Stacks 0DZF.** The completion of the local ring `P_𝔪` is the completion of its
henselization `P^h_𝔪`: the canonical map induced by `P_𝔪 → P^h_𝔪` on adic completions is
bijective.

This is the identification of the final term `∏ Def_{P^∧_{𝔪 i}}` of the chain of Stacks 0DZF,
whose functor out of `∏ Def_{P^h_{𝔪 i}}` is completion of the henselization; the source records
it as the parenthetical remark that "the completion of the henselization is the completion". -/
@[stacks 0DZF "the identification of the last term of the chain: the completion of the \
henselization of the local ring is the completion of the local ring, which the source records \
as the parenthetical `the completion of the henselization is the completion`. Stated with no \
hypothesis at all beyond a commutative ring and a prime of it, so in particular without the \
tag's finite type and smooth-away-from-the-maximal-ideals hypotheses, which this step of the \
proof does not use"]
public theorem bijective_adicCompletionMap_henselizedLocalRing
    {P : Type w} [CommRing P] (q : PrimeSpectrum P) :
    Function.Bijective
      (adicCompletionMap (algebraMap (localRingAt q) (henselizedLocalRingAt q))
        (IsLocalRing.maximalIdeal (localRingAt q)) (henselizedMaximalIdealAt q) le_rfl) :=
  bijective_adicCompletionMap_henselization (localRingAt q)
    (IsLocalRing.maximalIdeal (localRingAt q))

/-- The canonical isomorphism from the completion of the local ring `P_𝔪` onto the completion of
its henselization `P^h_𝔪`, which is
`Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing` read as an isomorphism. -/
public noncomputable def adicCompletionHenselizedLocalRingEquiv
    {P : Type w} [CommRing P] (q : PrimeSpectrum P) :
    AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q) ≃+*
      AdicCompletion (henselizedMaximalIdealAt q) (henselizedLocalRingAt q) :=
  RingEquiv.ofBijective _ (bijective_adicCompletionMap_henselizedLocalRing q)


/-! ### The decomposition of the completion along the singular points -/

/-- The image of `⨅ j, 𝔪 j` in the local ring `P_{𝔪 i}` lies in its maximal ideal. -/
private theorem map_iInf_le_maximalIdeal {P : Type w} [CommRing P] {ι : Type*}
    (m : ι → PrimeSpectrum P) (i : ι) :
    (⨅ j, (m j).asIdeal).map (algebraMap P (localRingAt (m i))) ≤
      IsLocalRing.maximalIdeal (localRingAt (m i)) :=
  (Ideal.map_mono (iInf_le (fun j => (m j).asIdeal) i)).trans_eq
    (IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal (localRingAt (m i)))

/-- **Stacks 0DZF.** The completion of `P` along `J = 𝔪 1 ∩ … ∩ 𝔪 n` is the product of the
completions of the local rings `P_{𝔪 i}`. This is the step the source states as "`P^∧` is
`∏ P^∧_{𝔪 i}`", and it is what carries the completion leg of the chain from the finite type
algebra `P` to the family of its local rings.

The map is the product of the canonical maps `P^∧_J → (P_{𝔪 i})^∧`; the proof is the Chinese
remainder theorem on the levels `P / Jⁿ ≅ ∏ P / 𝔪 iⁿ`, by
`Stacks.AdicCompletion.bijective_adicCompletion_iInf_to_pi`, followed by the identification of
each `𝔪 i`-adic completion of `P` with the completion of `P_{𝔪 i}`, by
`Stacks.AdicCompletion.bijective_adicCompletionMap_localization_atPrime`. -/
@[stacks 0DZF "the decomposition of the completion used by the proof: the completion of `P` \
along the intersection of the maximal ideals `𝔪 1, ..., 𝔪 n` is the product of the completions \
of the local rings `P_{𝔪 i}`, which the source states as `P^ = ∏ P_{𝔪 i}^`. Under the tag's own \
hypotheses on the family: the `𝔪 i` are maximal and distinct. Finite type of `P` and \
smoothness away from the `𝔪 i` are not used by this step and are not assumed",
  ega "IV 18.6.7" "more general"]
public theorem bijective_adicCompletion_iInf_to_pi_completedLocalRing
    {P : Type w} [CommRing P] {ι : Type uι} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m) :
    Function.Bijective (RingHom.pi fun i =>
      adicCompletionMap (algebraMap P (localRingAt (m i))) (⨅ j, (m j).asIdeal)
        (IsLocalRing.maximalIdeal (localRingAt (m i)))
        ((Ideal.map_mono (iInf_le (fun j => (m j).asIdeal) i)).trans_eq
          (IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal (localRingAt (m i))))) := by
  classical
  let I := fun i => (m i).asIdeal
  let J := ⨅ i, I i
  have hI : Pairwise (Function.onFun IsCoprime I) := fun i j hij => by
    have := hmax i
    have := hmax j
    exact Ideal.isCoprime_of_isMaximal fun he => hij (hinj (PrimeSpectrum.ext he))
  have hloc (i : ι) : Function.Bijective
      (adicCompletionMap (algebraMap P (localRingAt (m i))) (I i)
        (IsLocalRing.maximalIdeal (localRingAt (m i)))
        (IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal
          (localRingAt (m i))).le) := by
    have := hmax i
    have he : (I i).map (algebraMap P (localRingAt (m i))) =
        IsLocalRing.maximalIdeal (localRingAt (m i)) :=
      IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal (localRingAt (m i))
    exact Stacks.AdicCompletion.adicCompletionMap_bijective_of_map_eq _ _ _ he
      (Stacks.AdicCompletion.bijective_adicCompletionMap_localization_atPrime
        (I i) (localRingAt (m i)))
  let e i := RingEquiv.ofBijective _ (hloc i)
  have hpi := (Equiv.piCongrRight fun i => (e i).toEquiv).bijective.comp
    (Stacks.AdicCompletion.bijective_adicCompletion_iInf_to_pi I hI)
  convert hpi using 1
  funext x i
  have hc := Rig.adicCompletionMap_comp (RingHom.id P) (algebraMap P (localRingAt (m i)))
    J (I i) (IsLocalRing.maximalIdeal (localRingAt (m i)))
    (by simpa [J] using iInf_le I i)
    (IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal (localRingAt (m i))).le
    (map_iInf_le_maximalIdeal m i)
  simpa [e, RingEquiv.ofBijective_apply] using (DFunLike.congr_fun hc x).symm

/-- The decomposition of the completion of `P` along `J = 𝔪 1 ∩ … ∩ 𝔪 n` as the product of the
completions of the local rings, read as a ring isomorphism. This is
`Deformation.Examples.bijective_adicCompletion_iInf_to_pi_completedLocalRing` bundled. -/
public noncomputable def adicCompletionIInfPiEquiv
    {P : Type w} [CommRing P] {ι : Type uι} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m) :
    AdicCompletion (⨅ j, (m j).asIdeal) P ≃+*
      (∀ i, AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))) :=
  RingEquiv.ofBijective _
    (bijective_adicCompletion_iInf_to_pi_completedLocalRing m hmax hinj)

/-! ### The decomposition of the henselization along the singular points -/

/-- **Stacks 0DZF.** The henselization of the pair `(P, J)` for `J = 𝔪 1 ∩ … ∩ 𝔪 n` is the
product of the henselizations `P^h_{𝔪 i}` of the local rings. This is the step the source
states as "`P^h = ∏ P^h_{𝔪 i}`", proved there by looking at idempotents together with More on
Algebra, Lemma 15.11.6; it is what carries the henselization leg of the chain from the finite
type algebra `P` to the family of its local rings. -/
@[stacks 0DZF "the decomposition of the henselization used by the proof: the henselization of \
the pair `(P, J)` for `J` the intersection of the maximal ideals `𝔪 1, ..., 𝔪 n` is the product \
of the henselizations `P^h_{𝔪 i}` of the local rings, which the source states as \
`P^h = ∏ P^h_{𝔪 i}`. Under the tag's own hypotheses on the family: the `𝔪 i` are maximal and \
distinct. Finite type of `P` and smoothness away from the `𝔪 i` are not used by this step and \
are not assumed"]
public theorem exists_ringEquiv_henselization_iInf_pi_henselizedLocalRing
    {P : Type w} [CommRing P] {ι : Type uι} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m) :
    ∃ e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
        (∀ i, henselizedLocalRingAt (m i)),
      ∀ (r : P) (i : ι),
        e (algebraMap P (henselization P (⨅ j, (m j).asIdeal) : Type w) r) i =
          algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i))
            (algebraMap P (localRingAt (m i)) r) :=
  exists_ringEquiv_henselization_iInf_pi_localization (fun i => (m i).asIdeal) hmax
    fun _ _ h => hinj (PrimeSpectrum.ext h)

/-! ### The chain of deformation categories at the singular points -/

section Chain

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P]

attribute [local instance 100] henselizationAlgebra

/-- **The henselization of the local ring of a finite type algebra over a field is
Noetherian.** This is Stacks 0AGV applied to the Noetherian pair consisting of the local ring
and its maximal ideal, transported to the chosen henselization. -/
@[sga "4 VIII 4.1" "special case"]
public theorem isNoetherianRing_henselizedLocalRingAt [Algebra.FiniteType k P]
    (q : PrimeSpectrum P) : IsNoetherianRing (henselizedLocalRingAt q) := by
  classical
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  set A := localRingAt q
  obtain ⟨H, hH, j, hh, hj⟩ := exists_henselization A (IsLocalRing.maximalIdeal A)
  let : CommRing H := hH
  let : Algebra A H := j.toAlgebra
  have hj' : ∀ (B : Type w) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J → ∀ f : A →+* B,
        IsLocalRing.maximalIdeal A ≤ J.comap f →
          ∃! g : H →+* B,
            g.comp (algebraMap A H) = f ∧
              (IsLocalRing.maximalIdeal A).map (algebraMap A H) ≤ J.comap g := by
    intro B hB J hJ f hf
    simpa only [RingHom.algebraMap_toAlgebra] using hj B hB J hJ f hf
  have : IsNoetherianRing H :=
    (henselization_isNoetherian_and_completion_equiv A
      (IsLocalRing.maximalIdeal A) H hh hj').2.1
  obtain ⟨e⟩ := nonempty_algEquiv_henselization A (IsLocalRing.maximalIdeal A) H hh hj'
  exact isNoetherianRing_of_ringEquiv H e.toRingEquiv.symm

/-- **The first map of the chain of Stacks 0DZF**: localize a deformation of `P` at each of the
primes `𝔪 i` at once. -/
public noncomputable def localizationFunctors {ι : Type uι} (m : ι → PrimeSpectrum P) :
    BasedFunctor (ringDeformationBasedCategory Λ k P)
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (localRingAt (m i))) :=
  piLift fun i =>
    (localizationFunctor (Λ := Λ) (k := k) (m i).asIdeal.primeCompl).functor

/-- **The second map of the chain of Stacks 0DZF**: henselize each local ring of the family
along its maximal ideal. -/
public noncomputable def henselizationFunctors {ι : Type uι} (m : ι → PrimeSpectrum P) :
    BasedFunctor
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (localRingAt (m i)))
      (piBasedCategory fun i =>
        ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i))) :=
  piMap fun i =>
    (henselizationFunctor (Λ := Λ) (k := k)
      (IsLocalRing.maximalIdeal (localRingAt (m i)))).functor

/-- **The third map of the chain of Stacks 0DZF**: complete each henselized local ring along its
distinguished ideal. Its target is the completion of the henselization, which is the completion
`P^∧_{𝔪 i}` of the local ring itself by
`Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing`. -/
public noncomputable def completionFunctors {ι : Type uι} (m : ι → PrimeSpectrum P)
    [Algebra.FiniteType k P] :
    BasedFunctor
      (piBasedCategory fun i =>
        ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))) :=
  piMap fun i => by
    letI := isNoetherianRing_henselizedLocalRingAt (k := k) (m i)
    exact (adicCompletionFunctor (Λ := Λ) (k := k)
      (henselizedLocalRingAt (m i)) (henselizedMaximalIdealAt (m i))).functor

/-- A finite product of ring deformation categories is cofibered in groupoids, which is what
makes its tangent space available. -/
public theorem isCofiberedInGroupoids_pi_ringDeformation {ι : Type uι} (R : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    IsCofiberedInGroupoids
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i)).p :=
  piBasedCategory_isCofiberedInGroupoids _
    fun _ => isCofiberedInGroupoids_ringDeformationProjection

/-! ### The completion leg of the chain -/

section CompletionLeg

variable {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
  (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)

/-- The decomposition isomorphism `P^∧_J ≅ ∏ P^∧_{𝔪 i}` is `k`-linear: both sides are
`k`-algebras through `P`, and the isomorphism is induced by the `P`-algebra maps
`P → P_{𝔪 i}`. -/
public theorem algebraMap_adicCompletionIInfPiEquiv (a : k) :
    adicCompletionIInfPiEquiv m hmax hinj
        (algebraMap k (AdicCompletion (⨅ j, (m j).asIdeal) P) a) =
      algebraMap k (∀ i, AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
        (localRingAt (m i))) a := by
  funext i
  have hcomp := DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap (algebraMap P (localRingAt (m i)))
      (⨅ j, (m j).asIdeal) (IsLocalRing.maximalIdeal (localRingAt (m i)))
      (map_iInf_le_maximalIdeal m i))
    (algebraMap k P a)
  simp only [RingHom.coe_comp, Function.comp_apply] at hcomp
  change adicCompletionMap (algebraMap P (localRingAt (m i))) (⨅ j, (m j).asIdeal)
      (IsLocalRing.maximalIdeal (localRingAt (m i))) (map_iInf_le_maximalIdeal m i)
      (algebraMap k (AdicCompletion (⨅ j, (m j).asIdeal) P) a) = _
  rw [IsScalarTower.algebraMap_apply k P (AdicCompletion (⨅ j, (m j).asIdeal) P), hcomp,
    Pi.algebraMap_apply,
    IsScalarTower.algebraMap_apply k (localRingAt (m i))
      (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))),
    IsScalarTower.algebraMap_apply k P (localRingAt (m i))]

/-- **The completion leg of the chain of Stacks 0DZF**, as the source's proof builds it: the
completion functor of **Stacks 0DYV** at `P` and the ideal `J = 𝔪 1 ∩ … ∩ 𝔪 n`, followed by the
transport along the decomposition `P^∧_J ≅ ∏ P^∧_{𝔪 i}`. This is the composite
`𝓓_P → ∏ 𝓓_{P^∧_{𝔪 i}}` of all three maps of the chain, with the product of deformation
categories read as the deformation category of the product ring. -/
public noncomputable def piCompletedLocalRingFunctor [Algebra.FiniteType k P] :
    BasedFunctor (ringDeformationBasedCategory Λ k P)
      (ringDeformationBasedCategory Λ k
        (∀ i, AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
          (localRingAt (m i)))) :=
  letI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  BasedFunctor.comp (adicCompletionFunctor (Λ := Λ) (k := k) P (⨅ j, (m j).asIdeal)).functor
    (ringDeformationTransport (adicCompletionIInfPiEquiv m hmax hinj)
      (algebraMap_adicCompletionIInfPiEquiv m hmax hinj))

/-- **Stacks 0DZF, smoothness of the composite of the chain.** The map
`𝓓_P → ∏ 𝓓_{P^∧_{𝔪 i}}` is smooth.

This is the source's second step, in its own order: **Stacks 0DZ5** applied to `P` itself with
`J = 𝔪 1 ∩ … ∩ 𝔪 n` — for which `P` really is of finite type over `k` — gives smoothness of
`𝓓_P → 𝓓_{P^∧_J}`, and the transport of
`Deformation.Examples.isSmooth_ringDeformationTransport` along
`Deformation.Examples.adicCompletionIInfPiEquiv` carries it to the decomposed target. -/
@[stacks 0DZF "the smoothness half of the source's second step: the composite \
`Def_P -> ∏ Def_{P^∧_{𝔪 i}}` of all three maps of the chain is smooth, which the source obtains \
from Stacks 0DZ5 at `P` with `J = 𝔪 1 ∩ ... ∩ 𝔪 n` followed by the decomposition \
`P^∧ = ∏ P^∧_{𝔪 i}`. The product of deformation categories is read here as the deformation \
category of the product ring `∏ P^∧_{𝔪 i}`; the identification of that with the product of the \
deformation categories of the factors is \
`Deformation.Examples.piDeformationFunctor_full` and \
`Deformation.Examples.piDeformationFunctor_faithful`, and the clause of the tag for the third \
map of the chain itself is `Deformation.Examples.isSmooth_completedLocalRingFunctors`. \
Hypotheses: the tag's own, namely `P` of finite type over `k`, the `𝔪 i` maximal \
and distinct, and `hsm`, smoothness away from `V(J)` -- which the tag's `smooth except at \
𝔪 1, ..., 𝔪 n` supplies, since every prime not containing `J` is none of the `𝔪 i`"]
public theorem isSmooth_piCompletedLocalRingFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ (⨅ j, (m j).asIdeal) ≤ q.asIdeal →
      Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth (piCompletedLocalRingFunctor (Λ := Λ) (k := k) m hmax hinj) :=
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  isSmooth_comp_ringDeformationTransport _ _ _
    (isSmooth_adicCompletionFunctor P (⨅ j, (m j).asIdeal) hsm)

/-- **Stacks 0DZF, the tangent-space conclusion for the composite of the chain.** The map
`𝓓_P → ∏ 𝓓_{P^∧_{𝔪 i}}` induces an isomorphism on tangent spaces.

Same route as `Deformation.Examples.isSmooth_piCompletedLocalRingFunctor`: the tangent-space
half of **Stacks 0DZ5** at `(P, J)`, carried along the decomposition by
`Deformation.Examples.bijective_differential_ringDeformationTransport`. -/
@[stacks 0DZF "the tangent-space half of the source's second step: the composite \
`Def_P -> ∏ Def_{P^∧_{𝔪 i}}` of all three maps of the chain induces an isomorphism on tangent \
spaces, which the source obtains from Stacks 0DZ5 at `P` with `J = 𝔪 1 ∩ ... ∩ 𝔪 n` followed by \
the decomposition `P^∧ = ∏ P^∧_{𝔪 i}`. As for smoothness, the product of deformation categories \
is read as the deformation category of the product ring, the identification of the two being \
`Deformation.Examples.piDeformationFunctor_full` and \
`Deformation.Examples.piDeformationFunctor_faithful`; the clause of the tag for the third map \
of the chain itself is \
`Deformation.Examples.bijective_differential_completedLocalRingFunctors`. Hypotheses: the \
tag's own"]
public theorem bijective_differential_piCompletedLocalRingFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ (⨅ j, (m j).asIdeal) ≤ q.asIdeal →
      Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := ∀ i, AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
          (localRingAt (m i))))
      (piCompletedLocalRingFunctor (Λ := Λ) (k := k) m hmax hinj)) :=
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  bijective_differential_comp_ringDeformationTransport _ _ _ _
    (bijective_differential_adicCompletionFunctor P (⨅ j, (m j).asIdeal) hsm)

end CompletionLeg

end Chain

/-! ### Finite-dimensionality of the tangent space of the source -/

/-! **Stacks 0DZF**, the finite-dimensionality clause for the source of the chain, is Stacks
0DY4: for `P` of finite type over `k` and smooth over `k` outside a finite set of primes, the
group `Ext¹_P(NL_{P/k}, P)` — which is the tangent space of `𝓓_P` by Stacks 0DY3 — is
finite-dimensional over `k`. -/

add_to_stacks 0DZF "the finite-dimensionality of the tangent space of the source `Def_P` of \
the chain, which the source's proof obtains from Stacks 0DY4 and which this declaration \
carries. The tangent space is the group `Ext¹_P(NL_{P/k}, P)` of Stacks 0DY3. No extra \
hypothesis: `hfinite` asks only that the non-smooth locus be finite, which 0DZF's own \
hypothesis -- smooth except at the maximal ideals `𝔪 1, ..., 𝔪 n` -- gives. \
Finite-dimensionality for all four terms of the chain, which is the tag's own \
`finite dimensional tangent spaces`, is \
`Deformation.Examples.finiteDimensional_artinianTangentSpace_chain`"
  finiteDimensional_naiveCotangentExtOne


end Deformation.Examples
