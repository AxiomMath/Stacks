module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedAwaySquare
public import StacksFrontier.RingTheory.Rig.ClosedPoint.Regular
public import StacksFrontier.RingTheory.Rig.ClosedPoint.Transport
public import StacksFrontier.RingTheory.Rig.FlatJacobson

/-!
# The fourth paragraph of Stacks 0GGR: removing the hypothesis on `q ∩ A`

Flatness of `A{σ} → B{σ}` at a rig-closed prime `q` is available from the fifth paragraph of the
proof of Stacks 0GGR under the extra assumption that `q ∩ A` is rig-closed as well; that is
`Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint_of_comap`.  The fourth paragraph removes
that assumption: Stacks 0GGG, applied to the composite `A → B{σ}`, produces an `f : A` such that
the prime induced on the completed principal localization `A_{\{f\}}` *is* rig-closed, and
flatness descends from the square

```
A{σ} ⟶ B{σ}
 ↓        ↓
A{σ}_{\{f\}} ⟶ B{σ}_{\{φ f\}}
```

whose horizontal arrows are flat.  Through the identifications of Stacks 0GGG the lower arrow is
the coefficientwise reduction `A_{\{f\}}{σ} → B_{\{φ f\}}{σ}`, to which the fifth paragraph does
apply, and the transport across those identifications is
`Rig.restrictedPowerSeriesCompletedAwayEquiv_naturality`.

## Main results

* `Rig.completedAwayHom_unique`: a map of completed principal localizations commuting with the
  structure maps is unique.
* `Rig.exists_isClosedPointAwayFrom_completedAway_comap_of_map_eq`: Stacks 0GGG delivered at a
  caller-chosen presentation of the ideal of definition of the target.
* `Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint`: flatness of `A{σ} → B{σ}` at a
  rig-closed prime, with no hypothesis on its contraction to `A`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGG](https://stacks.math.columbia.edu/tag/0GGG)
-/

@[expose] public section

namespace Rig

section Structure

universe u

open RestrictedPowerSeries TopologicalRing

variable {A : Type u} [CommRing A]

/-- **A completed principal localization is adically complete for its ideal of definition.**  In
the two-step spelling of that ideal, the one in which Stacks 0GGG and `RingHom.IsRigFlat` deliver
it. -/
public theorem isAdicComplete_completedAwayCoefficientIdeal [IsNoetherianRing A] (I : Ideal A)
    (hI : I.FG) (f : A) :
    IsAdicComplete (completedAwayCoefficientIdeal I f) (CompletedAway I f) :=
  (completion_noetherian (Localization.Away f)
    (I.map (algebraMap A (Localization.Away f))) inferInstance
    (hI.map (algebraMap A (Localization.Away f)))).2

/-- **A completed principal localization is weakly admissible for its ideal of definition.**
`Rig.completedAway_weaklyAdmissible` with the ideal of definition in the two-step spelling. -/
public theorem isWeaklyAdmissible_completedAway [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (f : A) :
    letI : TopologicalSpace (CompletedAway I f) :=
      (completedAwayCoefficientIdeal I f).adicTopology
    letI : IsTopologicalRing (CompletedAway I f) :=
      (completedAwayCoefficientIdeal I f).nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (CompletedAway I f) (CompletedAway I f) :=
      (completedAwayCoefficientIdeal I f).isLinearTopology
    TopologicalRing.IsWeaklyAdmissible (CompletedAway I f) := by
  let : TopologicalSpace (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).adicTopology
  let : IsTopologicalRing (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (CompletedAway I f) (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).isLinearTopology
  let := isAdicComplete_completedAwayCoefficientIdeal I hI f
  exact isWeaklyAdmissible_of_isAdicComplete (completedAwayCoefficientIdeal I f) rfl
    ((isIdealOfDefinition_iff_isAdic ⟨_, rfl⟩ _).2 rfl)

/-- **Rig-closedness with respect to an ideal of definition is rig-closedness with respect to
the topological nilradical.**  The two ideals have the same vanishing locus, because the
topological nilradical is the radical of any ideal defining the topology. -/
public theorem isClosedPointAwayFrom_topologicalNilradical_of_isAdic
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (L : Ideal A) (hL : IsAdic L) (q : Ideal A) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom L q) :
    Ideal.IsClosedPointAwayFrom (topologicalNilradical A) q := by
  have hzero : PrimeSpectrum.zeroLocus (L : Set A) =
      PrimeSpectrum.zeroLocus (topologicalNilradical A : Set A) :=
    PrimeSpectrum.zeroLocus_eq_iff.mpr (by
      rw [radical_eq_topologicalNilradical_of_isAdic L hL,
        (TopologicalRing.topologicalNilradical_isRadical (B := A)).radical])
  unfold Ideal.IsClosedPointAwayFrom at hq ⊢
  rwa [hzero] at hq

/-- **Rig-closedness only depends on the prime, not on how it is written.**  A transport that
`Ideal.IsClosedPointAwayFrom` does not admit directly: it carries a primality instance on its
second argument, so rewriting the prime inside it is not type correct.  The detour is through
`Rig.Ideal.IsMaximalAmongPrimesAvoiding`, which carries no instance. -/
public theorem isClosedPointAwayFrom_congr_prime (K p p' : Ideal A) [p.IsPrime] [p'.IsPrime]
    (h : p = p') (hp : Ideal.IsClosedPointAwayFrom K p) :
    Ideal.IsClosedPointAwayFrom K p' := by
  rw [isClosedPointAway_iff_isMaximalAmongPrimesAvoiding] at hp ⊢
  rwa [h] at hp

/-- **Rig-closedness transports along a bijective ring homomorphism, at a caller's
presentation of the contracted data.**  `Rig.isClosedPointAwayFrom_comap_of_bijective` with the
contracted ideal and prime taken as arguments, equated to the contractions by hypothesis, so
that no rewriting happens inside `Ideal.IsClosedPointAwayFrom`. -/
public theorem isClosedPointAwayFrom_of_comap_of_bijective {B : Type u} [CommRing B]
    (e : A →+* B) (he : Function.Bijective e) (K P : Ideal B) [P.IsPrime] (L p : Ideal A)
    [p.IsPrime] (hP : p = P.comap e) (hK : L = K.comap e)
    (h : Ideal.IsClosedPointAwayFrom L p) :
    Ideal.IsClosedPointAwayFrom K P := by
  have : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  subst hK
  exact (isClosedPointAwayFrom_comap_of_bijective e he K P).mp
    (isClosedPointAwayFrom_congr_prime (K.comap e) p (P.comap e) hP h)

/-- **Rig-closedness transports along a bijective ring homomorphism, from the ideal mapped
forward.**  `Rig.isClosedPointAwayFrom_of_comap_of_bijective` with the ideal downstairs given by
its image rather than by a contraction. -/
public theorem isClosedPointAwayFrom_of_map_of_bijective {B : Type u} [CommRing B]
    (e : A →+* B) (he : Function.Bijective e) (K P : Ideal B) [P.IsPrime] (L p : Ideal A)
    [p.IsPrime] (hP : p = P.comap e) (hK : L.map e = K)
    (h : Ideal.IsClosedPointAwayFrom L p) :
    Ideal.IsClosedPointAwayFrom K P :=
  isClosedPointAwayFrom_of_comap_of_bijective e he K P L p hP
    (by rw [← hK, Ideal.comap_map_of_bijective e he]) h

/-- **The comparison isomorphisms of two presentations of one coefficient ideal are mutually
inverse.** -/
public theorem congrEquiv_symm_apply_apply {I J : Ideal A} (h : I = J) (σ : Type u)
    (x : RestrictedPowerSeries I σ) : congrEquiv h.symm σ (congrEquiv h σ x) = x := by
  refine RestrictedPowerSeries.idealSystem_ext fun n => ?_
  rw [coefficientProjection_congrEquiv, coefficientProjection_congrEquiv, congrLevelEquiv,
    congrLevelEquiv, MvPolynomial.mapEquiv_apply, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_map,
    show ((Ideal.quotEquivOfEq (congrArg (· ^ n) h.symm) : A ⧸ J ^ n →+* A ⧸ I ^ n).comp
          (Ideal.quotEquivOfEq (congrArg (· ^ n) h) : A ⧸ I ^ n →+* A ⧸ J ^ n)) =
        RingHom.id (A ⧸ I ^ n) from
      Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.coe_coe,
          Ideal.quotEquivOfEq_mk, RingHom.id_apply]),
    MvPolynomial.map_id]

/-- **The comparison isomorphism of two presentations of a coefficient ideal carries the
extended coefficient ideal onto the extended coefficient ideal.** -/
public theorem map_coefficientIdeal_congrEquiv {I J : Ideal A} (h : I = J) (σ : Type u) :
    (coefficientIdeal I σ).map (congrEquiv h σ).toRingHom = coefficientIdeal J σ := by
  calc (coefficientIdeal I σ).map (congrEquiv h σ).toRingHom
      = I.map ((congrEquiv h σ).toRingHom.comp (coefficientRingHom I σ)) := Ideal.map_map _ _
    _ = I.map (coefficientRingHom J σ) := by
        refine congrArg (fun k => I.map k) (RingHom.ext fun a => ?_)
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact congrEquiv_coefficientRingHom h σ a
    _ = J.map (coefficientRingHom J σ) := congrArg (Ideal.map (coefficientRingHom J σ)) h

/-- **Stacks 0GGG's identification carries the ideal of definition of `A{σ}_{\{f\}}` onto the
coefficient ideal of `A_{\{f\}}{σ}`.**  Both are extended from `A`, so the computation is the
behaviour of the identification on constants. -/
public theorem map_completedAwayCoefficientIdeal_completedAwayEquiv [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (σ : Type u) (f : A) :
    (completedAwayCoefficientIdeal (coefficientIdeal I σ) (coefficientRingHom I σ f)).map
        (restrictedPowerSeriesCompletedAwayEquiv I hI σ f) =
      coefficientIdeal (completedAwayCoefficientIdeal I f) σ := by
  calc (completedAwayCoefficientIdeal (coefficientIdeal I σ)
          (coefficientRingHom I σ f)).map (restrictedPowerSeriesCompletedAwayEquiv I hI σ f)
      = ((coefficientIdeal I σ).map (algebraMap (RestrictedPowerSeries I σ)
            (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)))).map
          (restrictedPowerSeriesCompletedAwayEquiv I hI σ f) :=
        congrArg (Ideal.map (restrictedPowerSeriesCompletedAwayEquiv I hI σ f))
          (completedAwayCoefficientIdeal_eq (coefficientIdeal I σ) (coefficientRingHom I σ f))
    _ = (coefficientIdeal I σ).map
          ((restrictedPowerSeriesCompletedAwayEquiv I hI σ f).comp
            (algebraMap (RestrictedPowerSeries I σ)
              (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)))) :=
        Ideal.map_map _ _
    _ = I.map (((restrictedPowerSeriesCompletedAwayEquiv I hI σ f).comp
          (algebraMap (RestrictedPowerSeries I σ)
            (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)))).comp
          (coefficientRingHom I σ)) := Ideal.map_map _ _
    _ = I.map ((coefficientRingHom (completedAwayCoefficientIdeal I f) σ).comp
          (algebraMap A (CompletedAway I f))) := by
        refine congrArg (fun k => I.map k) (RingHom.ext fun a => ?_)
        simp only [RingHom.comp_apply]
        exact completedAwayEquiv_coefficientRingHom I hI σ f a
    _ = (I.map (algebraMap A (CompletedAway I f))).map
          (coefficientRingHom (completedAwayCoefficientIdeal I f) σ) := (Ideal.map_map _ _).symm
    _ = (completedAwayCoefficientIdeal I f).map
          (coefficientRingHom (completedAwayCoefficientIdeal I f) σ) :=
        congrArg (Ideal.map (coefficientRingHom (completedAwayCoefficientIdeal I f) σ))
          (completedAwayCoefficientIdeal_eq I f).symm

/-- Contracting a prime back along an isomorphism after contracting it along the inverse. -/
private theorem comap_symm_comap {R S : Type u} [CommRing R] [CommRing S] (E : R ≃+* S)
    (p : Ideal R) : (p.comap E.symm.toRingHom).comap E.toRingHom = p := by
  rw [Ideal.comap_comap, show E.symm.toRingHom.comp E.toRingHom = RingHom.id R from
    RingHom.ext E.symm_apply_apply, Ideal.comap_id]

/-- An ideal carried forward by two bijections is the contraction of its image along the
composite. -/
private theorem comap_eq_of_bijective_comp {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (first : R →+* S) (hfirst : Function.Bijective first) (second : S →+* T)
    (hsecond : Function.Bijective second) (E : R ≃+* T)
    (hE : E.toRingHom = second.comp first) (X : Ideal R) (Y : Ideal S) (Z : Ideal T)
    (hXY : X.map first = Y) (hYZ : Y.map second = Z) : X = Z.comap E.toRingHom := by
  rw [hE, ← Ideal.comap_comap, ← hYZ, Ideal.comap_map_of_bijective second hsecond, ← hXY,
    Ideal.comap_map_of_bijective first hfirst]

/-- Cancelling the second half of a factored isomorphism out of a commuting square. -/
private theorem comp_eq_of_comp_eq {R S S' T : Type u} [CommRing R] [CommRing S] [CommRing S']
    [CommRing T] (first : R →+* S) (side : T →+* R) (forward : S' →+* S) (back : S →+* S')
    (hinv : back.comp forward = RingHom.id S') (rest : T →+* S')
    (hnat : first.comp side = forward.comp rest) :
    (back.comp first).comp side = rest := by
  rw [RingHom.comp_assoc, hnat, ← RingHom.comp_assoc, hinv, RingHom.id_comp]

/-- Contracting along a composite, presented as an isomorphism factored in two steps. -/
private theorem comap_eq_of_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (first : R →+* S) (second : S →+* T) (E : R ≃+* T)
    (hE : E.toRingHom = second.comp first) (Q : Ideal T) (middle : Ideal S) (target : Ideal R)
    (hsecond : Q.comap second = middle) (hfirst : middle.comap first = target) :
    Q.comap E.toRingHom = target := by
  rw [hE, ← Ideal.comap_comap, hsecond, hfirst]

/-- Two contractions of one prime agree once the two routes to it agree. -/
private theorem comap_comap_eq_of_comp_eq {R S S' T : Type u} [CommRing R] [CommRing S]
    [CommRing S'] [CommRing T] (upper : R →+* S') (lower : T →+* R) (E : S ≃+* S')
    (side : T →+* S) (hcomm : upper.comp lower = E.toRingHom.comp side) (Q : Ideal S')
    (target : Ideal S) (hQ : Q.comap E.toRingHom = target) :
    (Q.comap upper).comap lower = target.comap side := by
  rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap, hQ]

/-- **Flatness at a prime transported across a commuting square whose right vertical arrow is
an isomorphism.**  `Rig.flat_atPrime_comap_of_ringEquiv` with the left vertical arrow allowed to
be any bijection and the square given as an equation of ring homomorphisms. -/
private theorem flat_atPrime_comap_of_naturality {R S R' S' : Type u} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] (E : S ≃+* S') (Ψ : R →+* S) (left : R →+* R')
    (hleft : Function.Bijective left) (upper : R' →+* S')
    (hnat : E.toRingHom.comp Ψ = upper.comp left) (Q : Ideal S') [Q.IsPrime]
    (hflat : _root_.RingHom.Flat ((algebraMap S' (Localization.AtPrime Q)).comp upper)) :
    letI : (Q.comap E.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    _root_.RingHom.Flat
      ((algebraMap S (Localization.AtPrime (Q.comap E.toRingHom))).comp Ψ) := by
  refine flat_atPrime_comap_of_ringEquiv E Ψ Q ?_
  rw [hnat, ← RingHom.comp_assoc]
  exact (_root_.RingHom.Flat.of_bijective hleft).comp hflat

end Structure

section Unique

universe u

open RestrictedPowerSeries TopologicalRing

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **Coefficient reduction along a bare ring homomorphism is the identity on constants.** -/
public theorem restrictedPowerSeriesMapOfRingHom_coefficientRingHom (φ : A →+* B) (I : Ideal A)
    (σ : Type u) (a : A) :
    restrictedPowerSeriesMapOfRingHom φ I σ (coefficientRingHom I σ a) =
      coefficientRingHom (I.map φ) σ (φ a) := by
  let : Algebra A B := φ.toAlgebra
  exact restrictedPowerSeriesMap_coefficientRingHom I σ a

/-- **A map of completed principal localizations commuting with the structure maps is unique.**
Two ring homomorphisms `A_{\{f\}} → B_{\{g\}}` whose restrictions to `A` are both the structure
map of `B_{\{g\}}` composed with `φ` are equal: they are continuous, because the ideal of
definition of `A_{\{f\}}` is extended from `A` and `I · B = J`, and `A[1/f]` has dense image in
`A_{\{f\}}`.

This is what identifies the arrow Stacks 0GGG hands out with an arrow a consumer has built for
itself, which is needed because `Rig.RingHom.completedAwayMap` has the extension of the ideal
built into its type and so cannot be restated at another presentation of it. -/
public theorem completedAwayHom_unique {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (I : Ideal A) (hI : I.FG) (f : A) (J : Ideal B) (hJ : I.map φ = J) (g : B)
    (ψ₁ ψ₂ : CompletedAway I f →+* CompletedAway J g)
    (h₁ : ψ₁.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap B (CompletedAway J g)).comp φ)
    (h₂ : ψ₂.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap B (CompletedAway J g)).comp φ) :
    ψ₁ = ψ₂ := by
  have hJfg : J.FG := hJ ▸ hI.map φ
  let : TopologicalSpace (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).adicTopology
  let : TopologicalSpace (CompletedAway J g) :=
    (completedAwayCoefficientIdeal J g).adicTopology
  let : IsTopologicalRing (CompletedAway J g) :=
    (completedAwayCoefficientIdeal J g).nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (CompletedAway J g) (CompletedAway J g) :=
    (completedAwayCoefficientIdeal J g).isLinearTopology
  have : T2Space (CompletedAway J g) := (isWeaklyAdmissible_completedAway J hJfg g).2.2
  have hmap : ∀ ψ : CompletedAway I f →+* CompletedAway J g,
      ψ.comp (algebraMap A (CompletedAway I f)) =
          (algebraMap B (CompletedAway J g)).comp φ →
        (completedAwayCoefficientIdeal I f).map ψ = completedAwayCoefficientIdeal J g := by
    intro ψ hψ
    rw [completedAwayCoefficientIdeal_eq I f, completedAwayCoefficientIdeal_eq J g,
      Ideal.map_map, hψ, ← Ideal.map_map, hJ]
  have hdense : DenseRange (algebraMap (Localization.Away f) (CompletedAway I f)) :=
    denseRange_algebraMap_adicCompletion _
      (hI.map (algebraMap A (Localization.Away f)))
  exact completedHom_ext f hdense ψ₁ ψ₂
    (continuous_adic_of_map_le _ _ ψ₁ (le_of_eq (hmap ψ₁ h₁)))
    (continuous_adic_of_map_le _ _ ψ₂ (le_of_eq (hmap ψ₂ h₂)))
    (h₁.trans h₂.symm)

/-- **Stacks 0GGG at a caller-chosen presentation of the ideal of definition of the target.**
`Rig.exists_isClosedPointAwayFrom_completedAway_comap_of_isAdic` with the ideal `J` of `B` taken
as an argument, equated to `I · B` by hypothesis, and with the induced arrow
`A_{\{f\}} → B_{\{J, φ f\}}` existentially quantified rather than named — which is what lets a
consumer receive the arrow at an equal but differently written ideal, the type of
`Rig.RingHom.completedAwayMap` being fixed by `I.map φ`. -/
public theorem exists_isClosedPointAwayFrom_completedAway_comap_of_map_eq
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (I : Ideal A) (hIadic : _root_.IsAdic I) (J : Ideal B) (hJ : I.map φ = J)
    (hJadic : _root_.IsAdic J)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical B) q) :
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ∃ ψ : CompletedAway I f →+* CompletedAway J (φ f),
        ψ.comp (algebraMap A (CompletedAway I f)) =
            (algebraMap B (CompletedAway J (φ f))).comp φ ∧
          ∃ _ : (extendedIdeal J q (φ f)).IsPrime,
            ∃ _ : ((extendedIdeal J q (φ f)).comap ψ).IsPrime,
              Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal J (φ f))
                  (extendedIdeal J q (φ f)) ∧
                Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
                  ((extendedIdeal J q (φ f)).comap ψ) := by
  subst hJ
  obtain ⟨f, hunit, hcomm, hqprime, hpprime, hJq, hIp⟩ :=
    exists_isClosedPointAwayFrom_completedAway_comap_of_isAdic hA hB φ hφ I hIadic hJadic hft
      q hq
  exact ⟨f, hunit, RingHom.completedAwayMap φ I f, hcomm, hqprime, hpprime, hJq, hIp⟩

end Unique

section Main

universe u

open RestrictedPowerSeries TopologicalRing

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The fifth paragraph of Stacks 0GGR applied to the completed principal localizations.**
For `f : A`, the coefficientwise reduction `A_{\{f\}}{σ} → B_{\{φ f\}}{σ}` along the induced map
of completed principal localizations is flat at a rig-closed prime whose contraction to
`A_{\{f\}}` is rig-closed.  The `WAdm^Noeth` structure of the two completed principal
localizations, and the naive rig-flatness of the map between them, come from the third clause of
`RingHom.IsRigFlat`. -/
private theorem flat_atPrime_restrictedPowerSeriesMap_completedAway
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (I : Ideal A) (hI : _root_.IsAdic I) (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (σ : Type u) [Finite σ] (hflat : RingHom.IsRigFlat (algebraMap A B)) (f : A)
    (Q : Ideal (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
      (RingHom.completedAwayMap (algebraMap A B) I f)) σ)) [Q.IsPrime]
    (hα : Ideal.IsClosedPointAwayFrom
      (coefficientIdeal ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ) Q)
    (hβ : Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
      ((Q.comap (restrictedPowerSeriesMapOfRingHom
          (RingHom.completedAwayMap (algebraMap A B) I f)
          (completedAwayCoefficientIdeal I f) σ)).comap
        (coefficientRingHom (completedAwayCoefficientIdeal I f) σ))) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
          (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
        (Localization.AtPrime Q)).comp
        (restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
          (completedAwayCoefficientIdeal I f) σ)) := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJfg : (I.map (algebraMap A B)).FG := hIfg.map (algebraMap A B)
  let : TopologicalSpace (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).adicTopology
  let : IsTopologicalRing (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (CompletedAway I f) (CompletedAway I f) :=
    (completedAwayCoefficientIdeal I f).isLinearTopology
  let : TopologicalSpace (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)) :=
    (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)).adicTopology
  let : IsTopologicalRing (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)) :=
    (completedAwayCoefficientIdeal (I.map (algebraMap A B))
      (algebraMap A B f)).nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f))
      (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)) :=
    (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)).isLinearTopology
  let := isAdicComplete_completedAwayCoefficientIdeal I hIfg f
  let := isAdicComplete_completedAwayCoefficientIdeal (I.map (algebraMap A B)) hJfg
    (algebraMap A B f)
  have hIhatmap := map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f
  have hrig := hflat.2.2 I hI hJ f
  have hJ5 : _root_.IsAdic ((completedAwayCoefficientIdeal I f).map
      (RingHom.completedAwayMap (algebraMap A B) I f)) := by rw [hIhatmap]; exact rfl
  let : IsAdicComplete ((completedAwayCoefficientIdeal I f).map
      (RingHom.completedAwayMap (algebraMap A B) I f))
      (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)) := by
    rw [hIhatmap]; infer_instance
  exact flat_atPrime_restrictedPowerSeriesMapOfRingHom_of_rigPoint_of_comap
    (RingHom.completedAwayMap (algebraMap A B) I f) (completedAwayCoefficientIdeal I f) rfl hJ5 σ
    (RingHom.continuous_of_isAdic _ hrig.1) hrig.2.1
    (isWeaklyAdmissible_completedAway I hIfg f)
    (isWeaklyAdmissible_completedAway (I.map (algebraMap A B)) hJfg (algebraMap A B f))
    hrig.1 hrig Q hα hβ

/-- **`ψ₀` is the composite of the two induced maps of completed principal localizations.**
The arrow `A_{\{f\}} → B{σ}_{\{φ f\}}` that Stacks 0GGG hands out for the composite
`A → B{σ}` is the completed localization of `A → B` followed by that of `B → B{σ}`: both commute
with the structure maps over the composite, and `Rig.completedAwayHom_unique` applies. -/
private theorem eq_completedAwayMap_comp [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (hI : I.FG) (σ : Type u) [Finite σ] (f : A)
    (ψ₀ : CompletedAway I f →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hcomm₀ : ψ₀.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
        ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B))) :
    ψ₀ = (RingHom.completedAwayMap (coefficientRingHom (I.map (algebraMap A B)) σ)
      (I.map (algebraMap A B)) (algebraMap A B f)).comp
        (RingHom.completedAwayMap (algebraMap A B) I f) := by
  let : IsNoetherianRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isNoetherianRing_restrictedPowerSeries (I.map (algebraMap A B)) σ
  exact completedAwayHom_unique ((coefficientRingHom (I.map (algebraMap A B)) σ).comp
        (algebraMap A B)) I hI f (coefficientIdeal (I.map (algebraMap A B)) σ)
      (Ideal.map_map _ _).symm
    (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ψ₀ _ hcomm₀
    ((RingHom.comp_assoc (algebraMap A (CompletedAway I f))
          (RingHom.completedAwayMap (algebraMap A B) I f) _).trans
      (((congrArg (fun k => (RingHom.completedAwayMap
                (coefficientRingHom (I.map (algebraMap A B)) σ)
                (I.map (algebraMap A B)) (algebraMap A B f)).comp k)
            (RingHom.completedAwayMap_comp_base (algebraMap A B) I f)).trans
          (RingHom.comp_assoc (algebraMap A B) _ _).symm).trans
        (congrArg (fun k => k.comp (algebraMap A B))
          (RingHom.completedAwayMap_comp_base
            (coefficientRingHom (I.map (algebraMap A B)) σ) (I.map (algebraMap A B))
            (algebraMap A B f)))))

/-- **The coefficient inclusion of `A_{\{f\}}`, pushed into `B_{\{φ f\}}{σ}`, is the
composite of the two completed localizations followed by Stacks 0GGG's identification.**  Both
sides send a constant to the constant of the image of that element in `B_{\{φ f\}}`. -/
private theorem restrictedPowerSeriesMapOfRingHom_comp_coefficientRingHom
    [IsNoetherianRing A] [IsNoetherianRing B] (I : Ideal A) (hI : I.FG) (σ : Type u) (f : A) :
    (restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
          (completedAwayCoefficientIdeal I f) σ).comp
        (coefficientRingHom (completedAwayCoefficientIdeal I f) σ) =
      ((congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
              (algebraMap A B) I f).symm σ).toRingHom.comp
          (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
            (hI.map (algebraMap A B)) σ (algebraMap A B f))).comp
        ((RingHom.completedAwayMap (coefficientRingHom (I.map (algebraMap A B)) σ)
            (I.map (algebraMap A B)) (algebraMap A B f)).comp
          (RingHom.completedAwayMap (algebraMap A B) I f)) := by
  have hIhatmap := map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f
  have h2 : ∀ y : CompletedAway (I.map (algebraMap A B)) (algebraMap A B f),
      restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          (hI.map (algebraMap A B)) σ (algebraMap A B f)
          (RingHom.completedAwayMap (coefficientRingHom (I.map (algebraMap A B)) σ)
            (I.map (algebraMap A B)) (algebraMap A B f) y) =
        coefficientRingHom (completedAwayCoefficientIdeal (I.map (algebraMap A B))
          (algebraMap A B f)) σ y :=
    fun y => DFunLike.congr_fun (restrictedPowerSeriesCompletedAwayEquiv_comp_completedAwayMap
      (I.map (algebraMap A B)) (hI.map (algebraMap A B)) σ (algebraMap A B f)) y
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, restrictedPowerSeriesMapOfRingHom_coefficientRingHom,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h2]
  exact (congrEquiv_coefficientRingHom hIhatmap.symm σ
    (RingHom.completedAwayMap (algebraMap A B) I f x)).symm

/-- The prime that Stacks 0GGG's identification carries the given one to. -/
private theorem exists_comap_eq_extendedIdeal [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (σ : Type u) (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ))
    (f : A)
    (E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
    (hq'prime : (extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).IsPrime) :
    ∃ Q : Ideal (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
      (RingHom.completedAwayMap (algebraMap A B) I f)) σ),
      Q.IsPrime ∧ Q.comap E.toRingHom =
        extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
          (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) := by
  have := hq'prime
  exact ⟨_, Ideal.comap_isPrime _ _, comap_symm_comap E _⟩

/-- The ideal of definition of `B{σ}_{\{φ f\}}` is the contraction of the coefficient ideal of
`B_{\{φ f\}}{σ}` along Stacks 0GGG's identification, respelled. -/
private theorem completedAwayCoefficientIdeal_eq_comap [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (σ : Type u) [Finite σ] (f : A)
    (E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
    (hE :
      E.toRingHom = (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
            (algebraMap A B) I f).symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B)) σ (algebraMap A B f))) :
    completedAwayCoefficientIdeal (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) =
      (coefficientIdeal ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ).comap E.toRingHom := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJfg : (I.map (algebraMap A B)).FG := hIfg.map (algebraMap A B)
  let : IsNoetherianRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isNoetherianRing_restrictedPowerSeries (I.map (algebraMap A B)) σ
  have hIhatmap := map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f
  exact comap_eq_of_bijective_comp _
    (bijective_restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B)) hJfg σ
      (algebraMap A B f))
    _ (congrEquiv hIhatmap.symm σ).bijective E hE _ _ _
    (map_completedAwayCoefficientIdeal_completedAwayEquiv (I.map (algebraMap A B)) hJfg σ
      (algebraMap A B f))
    (map_coefficientIdeal_congrEquiv hIhatmap.symm σ)

/-- **The two routes from `A_{\{f\}}` into `B_{\{φ f\}}{σ}` agree.**  The coefficient
inclusion of `A_{\{f\}}` followed by the coefficientwise reduction is `ψ₀` followed by Stacks
0GGG's identification. -/
private theorem comp_coefficientRingHom_eq_comp [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (σ : Type u) [Finite σ] (f : A)
    (ψ₀ : CompletedAway I f →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hcomm₀ : ψ₀.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
        ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)))
    (E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
    (hE : E.toRingHom = (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
          (algebraMap A B) I f).symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B)) σ (algebraMap A B f))) :
    (restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
          (completedAwayCoefficientIdeal I f) σ).comp
        (coefficientRingHom (completedAwayCoefficientIdeal I f) σ) =
      E.toRingHom.comp ψ₀ := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hψ₀ := eq_completedAwayMap_comp I hIfg σ f ψ₀ hcomm₀
  have hbeta0 := restrictedPowerSeriesMapOfRingHom_comp_coefficientRingHom (B := B) I hIfg σ f
  exact hbeta0.trans ((congrArg (fun k => k.comp
        ((RingHom.completedAwayMap (coefficientRingHom (I.map (algebraMap A B)) σ)
            (I.map (algebraMap A B)) (algebraMap A B f)).comp
          (RingHom.completedAwayMap (algebraMap A B) I f))) hE.symm).trans
    (congrArg (fun k => E.toRingHom.comp k) hψ₀.symm))

/-- **The contraction to `A_{\{f\}}` along the coefficient inclusion is Stacks 0GGG's.**  So
the prime that the fifth paragraph upstairs needs to be rig-closed is the one Stacks 0GGG
produces rig-closed. -/
private theorem isClosedPointAwayFrom_comap_coefficientRingHom [IsNoetherianRing A]
    [IsNoetherianRing B]
    (I : Ideal A) (σ : Type u) [Finite σ]
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) (f : A)
    (ψ₀ : CompletedAway I f →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hcomm₀ : ψ₀.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
        ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)))
    (E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
    (hE : E.toRingHom = (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
          (algebraMap A B) I f).symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B)) σ (algebraMap A B f)))
    (Q : Ideal (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
      (RingHom.completedAwayMap (algebraMap A B) I f)) σ)) [Q.IsPrime]
    (hQ : Q.comap E.toRingHom = extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hp'prime : ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀).IsPrime)
    (hp'closed : Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
      ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀)) :
    Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
      ((Q.comap (restrictedPowerSeriesMapOfRingHom
            (RingHom.completedAwayMap (algebraMap A B) I f)
            (completedAwayCoefficientIdeal I f) σ)).comap
        (coefficientRingHom (completedAwayCoefficientIdeal I f) σ)) := by
  have := hp'prime
  have hβideal := comap_comap_eq_of_comp_eq _ _ E ψ₀
    (comp_coefficientRingHom_eq_comp I σ f ψ₀ hcomm₀ E hE) Q _ hQ
  have : ((Q.comap (restrictedPowerSeriesMapOfRingHom
        (RingHom.completedAwayMap (algebraMap A B) I f)
        (completedAwayCoefficientIdeal I f) σ)).comap
      (coefficientRingHom (completedAwayCoefficientIdeal I f) σ)).IsPrime :=
    Ideal.comap_isPrime _ _
  exact isClosedPointAwayFrom_congr_prime (completedAwayCoefficientIdeal I f) _ _
    hβideal.symm hp'closed

/-- **The prime and its rig-closedness, transported onto `B_{\{φ f\}}{σ}`.**  Stacks 0GGG's
identification of `B{σ}_{\{φ f\}}` with `B_{\{φ f\}}{σ}`, respelled by
`RestrictedPowerSeries.congrEquiv` so that the coefficient ideal is the one extended from
`A_{\{f\}}`, carries the prime produced by Stacks 0GGG to a rig-closed prime whose contraction
to `A_{\{f\}}` along the coefficient inclusion is the rig-closed prime that Stacks 0GGG cuts
out there.  These are exactly the two hypotheses of the fifth paragraph upstairs. -/
private theorem exists_rigPoint_completedAwayEquiv [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (σ : Type u) [Finite σ]
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (f : A)
    (ψ₀ : CompletedAway I f →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hcomm₀ : ψ₀.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
        ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)))
    (hq'prime : (extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).IsPrime)
    (hp'prime : ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀).IsPrime)
    (hq'closed : Ideal.IsClosedPointAwayFrom
      (completedAwayCoefficientIdeal (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
      (extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))
    (hp'closed : Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
      ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀))
    (E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ)
    (hE :
      E.toRingHom = (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
            (algebraMap A B) I f).symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B)) σ (algebraMap A B f))) :
    ∃ Q : Ideal (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ),
      ∃ _ : Q.IsPrime,
        Q.comap E.toRingHom = extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ∧
          Ideal.IsClosedPointAwayFrom
              (coefficientIdeal ((completedAwayCoefficientIdeal I f).map
                (RingHom.completedAwayMap (algebraMap A B) I f)) σ) Q ∧
            Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
              ((Q.comap (restrictedPowerSeriesMapOfRingHom
                  (RingHom.completedAwayMap (algebraMap A B) I f)
                  (completedAwayCoefficientIdeal I f) σ)).comap
                (coefficientRingHom (completedAwayCoefficientIdeal I f) σ)) := by
  have := hq'prime
  have h := exists_comap_eq_extendedIdeal (B := B) I σ q f E hq'prime
  obtain ⟨Q, hQprime, hQ⟩ := h
  have := hQprime
  refine ⟨Q, hQprime, hQ, ?_, ?_⟩
  · exact isClosedPointAwayFrom_of_comap_of_bijective E.toRingHom E.bijective _ _ _ _
      hQ.symm (completedAwayCoefficientIdeal_eq_comap I σ f E hE) hq'closed
  · exact isClosedPointAwayFrom_comap_coefficientRingHom I σ q f ψ₀ hcomm₀ E hE _
      hQ hp'prime hp'closed


/-- **The descent of the fourth paragraph of Stacks 0GGR, for data supplied by Stacks 0GGG.**
Given the element `f : A`, the induced arrow `A_{\{f\}} → B{σ}_{\{φ f\}}` and the two
rig-closedness statements that `Rig.exists_isClosedPointAwayFrom_completedAway_comap_of_map_eq`
produces for the composite `A → B{σ}`, flatness of `B{σ}_q` over `A{σ}` follows: the prime and
its rig-closedness transport across the two identifications of Stacks 0GGG onto
`B_{\{φ f\}}{σ}`, the fifth paragraph applies there, and
`Rig.restrictedPowerSeriesCompletedAwayEquiv_naturality` carries the resulting flatness back to
`A{σ}_{\{f\}} → B{σ}_{\{φ f\}}`, from which `Rig.flat_atPrime_of_flat_atPrime_comap`
descends it. -/
private theorem flat_atPrime_restrictedPowerSeriesMap_descent
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (I : Ideal A) (hI : _root_.IsAdic I) (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (σ : Type u) [Finite σ] [IsNoetherianRing (RestrictedPowerSeries I σ)]
    [IsLinearTopology (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ)]
    [IsNoetherianRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ)]
    [IsAdicComplete (coefficientIdeal (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ)]
    (hLadic : _root_.IsAdic (coefficientIdeal (I.map (algebraMap A B)) σ))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hflat : RingHom.IsRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (f : A)
    (hunit : IsUnit (Ideal.Quotient.mk q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))
    (ψ₀ : CompletedAway I f →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hcomm₀ : ψ₀.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
        ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)))
    (hq'prime : (extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).IsPrime)
    (hp'prime : ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀).IsPrime)
    (hq'closed : Ideal.IsClosedPointAwayFrom
      (completedAwayCoefficientIdeal (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
      (extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))
    (hp'closed : Ideal.IsClosedPointAwayFrom (completedAwayCoefficientIdeal I f)
      ((extendedIdeal (coefficientIdeal (I.map (algebraMap A B)) σ) q
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))).comap ψ₀)) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.AtPrime q)).comp
          (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJfg : (I.map (algebraMap A B)).FG := hIfg.map (algebraMap A B)
  have hIhatmap := map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f
  have hbijA := bijective_restrictedPowerSeriesCompletedAwayEquiv I hIfg σ f
  have hbijB := bijective_restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B)) hJfg σ
    (algebraMap A B f)
  obtain ⟨E, hE⟩ : ∃ E : CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) ≃+*
      RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ,
      E.toRingHom = (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
            (algebraMap A B) I f).symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B)) σ (algebraMap A B f)) :=
    ⟨RingEquiv.ofBijective ((congrEquiv hIhatmap.symm σ).toRingHom.comp
        (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B)) hJfg σ
          (algebraMap A B f)))
      ((congrEquiv hIhatmap.symm σ).bijective.comp hbijB), rfl⟩
  obtain ⟨Q, hQprime, hQ, hα, hβ⟩ := exists_rigPoint_completedAwayEquiv I σ q f ψ₀ hcomm₀
    hq'prime hp'prime hq'closed hp'closed E hE
  have := hQprime
  -- the arrow `A{σ}_{\{f\}} → B{σ}_{\{φ f\}}` at the presentation of 0GGG's identifications
  obtain ⟨Ψ, hΨcomm, -, -, -, -⟩ :=
    exists_completedAwayMap_properties (restrictedPowerSeriesMap (B := B) I σ)
      (coefficientIdeal I σ) (coefficientIdeal (I.map (algebraMap A B)) σ)
      (coefficientRingHom I σ f)
      (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))
      ((Ideal.map_map _ _).trans ((congrArg (fun k => I.map k) (RingHom.ext fun a =>
          restrictedPowerSeriesMap_coefficientRingHom (B := B) I σ a)).trans
        (Ideal.map_map _ _).symm))
      (restrictedPowerSeriesMap_coefficientRingHom (B := B) I σ f)
      (isTopologicallyOfFiniteType_restrictedPowerSeriesMap I hIfg σ hJ hft) hLadic
  -- transport the flatness across the identifications and descend
  have hinv : (congrEquiv hIhatmap.symm σ).toRingHom.comp (congrEquiv hIhatmap σ).toRingHom =
      RingHom.id (RestrictedPowerSeries ((completedAwayCoefficientIdeal I f).map
        (RingHom.completedAwayMap (algebraMap A B) I f)) σ) :=
    RingHom.ext (congrEquiv_symm_apply_apply hIhatmap σ)
  have hEΨ0 := comp_eq_of_comp_eq
    (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B)) hJfg σ (algebraMap A B f))
    Ψ (congrEquiv hIhatmap σ).toRingHom (congrEquiv hIhatmap.symm σ).toRingHom hinv _
    (restrictedPowerSeriesCompletedAwayEquiv_naturality I hIfg σ f Ψ hΨcomm)
  have hEΨ : E.toRingHom.comp Ψ =
      (restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
          (completedAwayCoefficientIdeal I f) σ).comp
        (restrictedPowerSeriesCompletedAwayEquiv I hIfg σ f) :=
    (congrArg (fun k => k.comp Ψ) hE).trans hEΨ0
  have : (Q.comap E.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  exact flat_atPrime_of_flat_atPrime_comap (restrictedPowerSeriesMap (B := B) I σ)
    (coefficientIdeal I σ) (coefficientRingHom I σ f)
    (coefficientIdeal (I.map (algebraMap A B)) σ)
    (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) Ψ hΨcomm q
    (Q.comap E.toRingHom)
    ((comap_extendedIdeal_eq (coefficientIdeal (I.map (algebraMap A B)) σ) q
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)) hunit).symm.trans
      (congrArg (Ideal.comap (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
          (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))) hQ.symm))
    (flat_atPrime_comap_of_naturality E Ψ (restrictedPowerSeriesCompletedAwayEquiv I hIfg σ f)
      hbijA _ hEΨ Q
      (flat_atPrime_restrictedPowerSeriesMap_completedAway I hI hJ σ hflat f Q hα hβ))

/-- **Flatness of `A{σ} → B{σ}` at a rig-closed prime.**  The fourth and fifth paragraphs of
the proof of Stacks 0GGR together: for a continuous, rig-flat homomorphism `A → B` of
topologically finite type between Noetherian weakly admissible rings, complete along an ideal of
definition `I` of `A` and its extension, and a rig-closed prime `q` of `B{σ}`, the localization
of `B{σ}` at `q` is flat over `A{σ}`.

No hypothesis on the contraction of `q` to `A` is needed: that is what the fourth paragraph
removes, by replacing `A` with a completed principal localization `A_{\{f\}}` at an element `f`
produced by Stacks 0GGG. -/
public theorem flat_atPrime_restrictedPowerSeriesMap_of_rigPoint
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hflat : RingHom.IsRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.AtPrime q)).comp
          (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJfg : (I.map (algebraMap A B)).FG := hIfg.map (algebraMap A B)
  let : IsNoetherianRing (RestrictedPowerSeries I σ) := isNoetherianRing_restrictedPowerSeries I σ
  let : IsLinearTopology (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isLinearTopology_restrictedPowerSeries (I.map (algebraMap A B)) hJfg σ
  let : IsNoetherianRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isNoetherianRing_restrictedPowerSeries (I.map (algebraMap A B)) σ
  let : IsAdicComplete (coefficientIdeal (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isAdicComplete_restrictedPowerSeries (I.map (algebraMap A B)) σ
  have hLadic : _root_.IsAdic (coefficientIdeal (I.map (algebraMap A B)) σ) :=
    isAdic_coefficientIdeal (I.map (algebraMap A B)) hJfg σ
  have hD : TopologicalRing.IsWeaklyAdmissible
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isWeaklyAdmissible_restrictedPowerSeries (I.map (algebraMap A B)) hJfg σ
  have hcB : Continuous (coefficientRingHom (I.map (algebraMap A B)) σ) :=
    continuous_coefficientRingHom (I.map (algebraMap A B)) hJ hJfg σ
  have hcBft : TopologicalRing.IsTopologicallyOfFiniteType
      (coefficientRingHom (I.map (algebraMap A B)) σ) := by
    rw [hLadic]
    exact isTopologicallyOfFiniteType_coefficientRingHom (I.map (algebraMap A B)) σ
  have hmapφ₀ : I.map ((coefficientRingHom (I.map (algebraMap A B)) σ).comp
      (algebraMap A B)) = coefficientIdeal (I.map (algebraMap A B)) σ :=
    (Ideal.map_map _ _).symm
  obtain ⟨f, hunit, ψ₀, hcomm₀, hq'prime, hp'prime, hq'closed, hp'closed⟩ :=
    exists_isClosedPointAwayFrom_completedAway_comap_of_map_eq hA hD
      ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)) (hcB.comp hcont)
      I hI (coefficientIdeal (I.map (algebraMap A B)) σ) hmapφ₀ hLadic
      (isTopologicallyOfFiniteType_comp (coefficientRingHom (I.map (algebraMap A B)) σ)
        (algebraMap A B) hcB hcBft hft)
      q (isClosedPointAwayFrom_topologicalNilradical_of_isAdic
        (coefficientIdeal (I.map (algebraMap A B)) σ) hLadic q hq)
  exact flat_atPrime_restrictedPowerSeriesMap_descent I hI hJ σ hLadic hft hflat q f hunit ψ₀ hcomm₀
    hq'prime hp'prime hq'closed hp'closed

open scoped TensorProduct

/-- **Flatness of `A{σ} → B ⊗̂[A] A{σ}` at a rig-closed point, with no hypothesis on the
contraction to `A`.**  `Rig.flat_atPrime_completedTensorProduct_restrictedPowerSeries` with the
hypothesis that `q ∩ A` be rig-closed removed, which is what the fourth paragraph of the proof of
Stacks 0GGR contributes, and with naive rig-flatness of `A → B` strengthened to the rig-flatness
that Stacks 0GGR assumes. -/
public theorem flat_atPrime_completedTensorProduct_restrictedPowerSeries_of_rigPoint
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hflat : RingHom.IsRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q) :
    letI : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
      RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I
        (Ideal.fg_of_isNoetherianRing I) σ
    letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
    letI : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    let e := completedTensorProductRestrictedEquiv I (Ideal.fg_of_isNoetherianRing I) σ hJ
    let ι : RestrictedPowerSeries I σ →+*
        CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ) :=
      (UniformSpace.Completion.coeRingHom).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := RestrictedPowerSeries I σ)).toRingHom
    letI : (q.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    _root_.RingHom.Flat
      ((algebraMap (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ))
        (Localization.AtPrime (q.comap e.toRingHom))).comp ι) := by
  let : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I
      (Ideal.fg_of_isNoetherianRing I) σ
  let : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
  let : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  have hIdef : TopologicalRing.IsIdealOfDefinition I :=
    (isIdealOfDefinition_iff_isAdic ⟨I, hI⟩ I).2 hI
  refine flat_atPrime_comap_of_ringEquiv
    (completedTensorProductRestrictedEquiv I (Ideal.fg_of_isNoetherianRing I) σ hJ)
    ((UniformSpace.Completion.coeRingHom).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := RestrictedPowerSeries I σ)).toRingHom) q ?_
  rw [show (completedTensorProductRestrictedEquiv I
        (Ideal.fg_of_isNoetherianRing I) σ hJ).toRingHom.comp
        ((UniformSpace.Completion.coeRingHom).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := B)
            (B := RestrictedPowerSeries I σ)).toRingHom) =
      restrictedPowerSeriesMap (B := B) I σ from
    RingHom.ext fun x => completedTensorProductRestrictedEquiv_tmul_one I
      (Ideal.fg_of_isNoetherianRing I) σ hJ x]
  exact flat_atPrime_restrictedPowerSeriesMap_of_rigPoint I hI hJ σ hcont hflat.2.1
    (isWeaklyAdmissible_of_isAdicComplete I hI hIdef) hflat q hq

end Main

end Rig

end
