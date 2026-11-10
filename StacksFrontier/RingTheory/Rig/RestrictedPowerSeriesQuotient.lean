module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.Flat
public import StacksFrontier.RingTheory.Rig.FlatBaseChangeReduction
public import StacksFrontier.RingTheory.RestrictedPowerSeries.CoefficientIdeal

/-!
# An adic algebra of topological finite type is a quotient of a restricted power series ring

Let `A → C` be an adic homomorphism of topological finite type between adic topological rings
with finitely generated ideals of definition.  Then there is an ideal of definition `I` of `A`
and an `n` with `C` a quotient of the restricted power series ring `A{x₁, …, xₙ}` taken with
respect to `I`.  In particular `C` is finite as a module over that ring.

This is the factorisation `A → A{x₁, …, xₙ} → C` of the third paragraph of the proof of
Tag 0GGR.  The content is already in condition (8) of Tag 0GBW
(`Rig.adicFiniteType_tfae`), which presents `C` as a closed quotient of the adic completion of
a polynomial ring; what is added here is the translation into the restricted power series ring
`RestrictedPowerSeries I (Fin n)` of this development, through
`RestrictedPowerSeries.adicCompletionEquiv`.  That translation matters because the two notions
of restricted power series ring in the library are different objects: the one indexed by the
topology of the coefficient ring (`TopologicalRing.RestrictedPowerSeries`, used by Tag 0ANU and
by condition (7)) and the one indexed by an ideal (`RestrictedPowerSeries`, used by the
rig-flatness arguments), and the fourth paragraph of Tag 0GGR is written with the latter.

## Main results

* `Rig.exists_restrictedPowerSeriesSurjection`: the factorisation `A → A{x₁, …, xₙ} ↠ C`.
* `Rig.exists_restrictedPowerSeriesReindex`: reindexing the variables of a restricted power
  series ring along a bijection of index sets.
* `Rig.isOpenMap_of_surjective_of_isAdic`: a surjective adic homomorphism of adic rings is open.
* `Rig.exists_restrictedPowerSeriesQuotientMap`: the same factorisation with the surjection
  continuous and open, so that `C` is the topological quotient, and with the variables in the
  universe of `A`.
* `Rig.module_finite_of_restrictedPowerSeriesSurjection`: `C` is a finite module over the
  restricted power series ring it is a quotient of.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
-/

@[expose] public section

namespace Rig

universe u

/-- **An adic algebra of topological finite type is a quotient of a restricted power series
ring.**  There is an ideal of definition `I` of `A`, a number `n` of variables, and a surjection
from `RestrictedPowerSeries I (Fin n)` onto `C` which restricts to the structure map on
constants. -/
public theorem exists_restrictedPowerSeriesSurjection {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (hCfg : ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧ J.FG)
    (hadic : _root_.RingHom.IsAdic (algebraMap A C))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C)) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ ∃ n : ℕ,
      ∃ π : RestrictedPowerSeries I (Fin n) →+* C, Function.Surjective π ∧
        π.comp (RestrictedPowerSeries.coefficientRingHom I (Fin n)) = algebraMap A C := by
  have h1 : _root_.RingHom.IsAdic (algebraMap A C) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C) := ⟨hadic, hft⟩
  have h8 : HasCompletedPolynomialPresentation (algebraMap A C) :=
    ((adicFiniteType_tfae (algebraMap A C) hA hC hAfg hCfg).out 1 8).mp h1
  obtain ⟨I, hIdef, n, hpres⟩ := h8
  obtain ⟨K, hKclosed, e, hecont, hecont', hecomp⟩ := hpres
  refine ⟨I, hIdef, n, (e.toRingHom.comp (Ideal.Quotient.mk K)).comp
    (RestrictedPowerSeries.adicCompletionEquiv I (Fin n)).toRingHom, ?_, ?_⟩
  · exact e.surjective.comp (Ideal.Quotient.mk_surjective.comp
      (RestrictedPowerSeries.adicCompletionEquiv I (Fin n)).surjective)
  · refine RingHom.ext fun a => ?_
    have hpoly : (RestrictedPowerSeries.adicCompletionEquiv I (Fin n))
        (RestrictedPowerSeries.coefficientRingHom I (Fin n) a) =
        algebraMap (MvPolynomial (Fin n) A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
            (MvPolynomial (Fin n) A)) (MvPolynomial.C a) :=
      RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom I (Fin n) (MvPolynomial.C a)
    change e (Ideal.Quotient.mk K
      ((RestrictedPowerSeries.adicCompletionEquiv I (Fin n))
        (RestrictedPowerSeries.coefficientRingHom I (Fin n) a))) = algebraMap A C a
    rw [hpoly]
    exact DFunLike.congr_fun hecomp a

/-- **Reindexing the variables of a restricted power series ring.**  A bijection of index sets
induces an isomorphism of restricted power series rings over the same coefficient ideal,
compatible with the coefficient maps.  It is needed because condition (8) of Tag 0GBW presents
`C` over the variables `Fin n`, which live in `Type 0`, while the rig-flatness results of this
development take their variables in the universe of the coefficient ring. -/
public theorem exists_restrictedPowerSeriesReindex {A : Type*} [CommRing A] (I : Ideal A)
    {σ τ : Type*} (e : σ ≃ τ) :
    ∃ E : RestrictedPowerSeries I σ ≃+* RestrictedPowerSeries I τ,
      ∀ a : A, E (_root_.RestrictedPowerSeries.coefficientRingHom I σ a) =
        _root_.RestrictedPowerSeries.coefficientRingHom I τ a := by
  have hmap : (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)).map
      (MvPolynomial.renameEquiv A e).toRingEquiv.toRingHom =
      I.map (MvPolynomial.C : A →+* MvPolynomial τ A) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun x => by simp
  refine ⟨(_root_.RestrictedPowerSeries.adicCompletionEquiv I σ).trans
    ((adicCompletionCongr (MvPolynomial.renameEquiv A e).toRingEquiv _ _ hmap).trans
      (_root_.RestrictedPowerSeries.adicCompletionEquiv I τ).symm), fun a => ?_⟩
  have h1 : _root_.RestrictedPowerSeries.adicCompletionEquiv I σ
      (_root_.RestrictedPowerSeries.coefficientRingHom I σ a) =
      AdicCompletion.of (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)
        (MvPolynomial.C a) :=
    _root_.RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom I σ (MvPolynomial.C a)
  have h2 : _root_.RestrictedPowerSeries.adicCompletionEquiv I τ
      (_root_.RestrictedPowerSeries.coefficientRingHom I τ a) =
      AdicCompletion.of (I.map (MvPolynomial.C : A →+* MvPolynomial τ A)) (MvPolynomial τ A)
        (MvPolynomial.C a) :=
    _root_.RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom I τ (MvPolynomial.C a)
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h1, adicCompletionCongr_of,
    RingEquiv.symm_apply_eq, h2]
  simp

/-- **A surjective adic homomorphism of adic topological rings is open.**  A power of an ideal
of definition of the source is carried *onto* the corresponding power of its extension, because
the map is surjective, and that extension is an ideal of definition of the target; translating
by a point, the image of any neighbourhood is a neighbourhood of the image of the point. -/
public theorem isOpenMap_of_surjective_of_isAdic {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hsurj : Function.Surjective φ) {𝔦 : Ideal R} (h𝔦 : _root_.IsAdic 𝔦)
    (h𝔧 : _root_.IsAdic (𝔦.map φ)) : IsOpenMap φ := by
  refine IsOpenMap.of_nhds_le fun x => fun V hV => ?_
  rw [Filter.mem_map] at hV
  have h0 : (fun t : R => t + x) ⁻¹' (φ ⁻¹' V) ∈ nhds (0 : R) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨m, -, hm⟩ := h𝔦.hasBasis_nhds_zero.mem_iff.mp h0
  refine Filter.mem_of_superset
    (((Homeomorph.addRight (φ x)).isOpenMap _ ((isAdic_iff.mp h𝔧).1 m)).mem_nhds
      ⟨0, Submodule.zero_mem _, zero_add _⟩) ?_
  rintro y ⟨c, hc, rfl⟩
  have hc' : c ∈ (𝔦 ^ m).map φ := by rw [Ideal.map_pow]; exact hc
  obtain ⟨r, hr, hrc⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).mp hc'
  have hmem : φ (r + x) ∈ V := hm (show r ∈ ((𝔦 ^ m : Ideal R) : Set R) from hr)
  rw [map_add, hrc] at hmem
  exact hmem

/-- **An adic algebra of topological finite type is a *topological* quotient of a restricted
power series ring, on variables in its own universe.**
`Rig.exists_restrictedPowerSeriesSurjection` with two things added.

First, the topological content: the surjection is continuous and open, so `C` carries the
quotient topology.  That is what right exactness of the completed tensor product
(`TopologicalRing.exists_completedTensorProductQuotientRingEquiv`) asks of the factorisation
`A → A{x₁, …, xₙ} ↠ C` of the third paragraph of Tag 0GGR: the bare ring-theoretic surjection
is not enough, because the topology of `C` has to be the quotient topology for `B ⊗̂_A C` to be
a quotient of `B ⊗̂_A A{x₁, …, xₙ}`.  Continuity and openness are not read off the presentation
of Tag 0GBW — doing that would need the inverse limit topology of the polynomial completion,
which carries no topological ring instance.  They come instead from adicness of
`A{x₁, …, xₙ} → C`, which the surjection has because the coefficient ideal extends to the
extension of `I`.

Second, the variables are produced in the universe of `A` rather than as `Fin n`, by
`Rig.exists_restrictedPowerSeriesReindex`.  The rig-flatness results for restricted power
series rings take their variables there, all the rings in sight having to share one universe. -/
public theorem exists_restrictedPowerSeriesQuotientMap {A C : Type u} [CommRing A] [CommRing C]
    [IsNoetherianRing A] [Algebra A C] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (hCfg : ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧ J.FG)
    (hadic : _root_.RingHom.IsAdic (algebraMap A C))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C)) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ ∃ σ : Type u, ∃ _ : Finite σ,
      ∃ π : RestrictedPowerSeries I σ →+* C, Function.Surjective π ∧
        Continuous π ∧ IsOpenMap π ∧
        π.comp (_root_.RestrictedPowerSeries.coefficientRingHom I σ) = algebraMap A C := by
  obtain ⟨I, hIdef, n, π₀, hsurj₀, hπcomp₀⟩ :=
    exists_restrictedPowerSeriesSurjection hA hC hAfg hCfg hadic hft
  obtain ⟨I₀, hI₀def, hI₀adic⟩ := hA.1
  have hIadic : _root_.IsAdic I := (isIdealOfDefinition_iff_isAdic ⟨I₀, hI₀adic⟩ I).1 hIdef
  obtain ⟨E, hE⟩ := exists_restrictedPowerSeriesReindex I
    (Equiv.ulift.{u, 0} (α := Fin n)).symm
  refine ⟨I, hIdef, ULift.{u, 0} (Fin n), inferInstance, π₀.comp E.symm.toRingHom,
    hsurj₀.comp E.symm.surjective, ?_⟩
  have hπcomp : (π₀.comp E.symm.toRingHom).comp
      (_root_.RestrictedPowerSeries.coefficientRingHom I (ULift.{u, 0} (Fin n))) =
      algebraMap A C := by
    refine RingHom.ext fun a => ?_
    change π₀ (E.symm (_root_.RestrictedPowerSeries.coefficientRingHom I _ a)) = algebraMap A C a
    rw [show E.symm (_root_.RestrictedPowerSeries.coefficientRingHom I _ a) =
        _root_.RestrictedPowerSeries.coefficientRingHom I (Fin n) a from
      E.injective ((E.apply_symm_apply _).trans (hE a).symm)]
    exact DFunLike.congr_fun hπcomp₀ a
  have hcoef : _root_.IsAdic
      (_root_.RestrictedPowerSeries.coefficientIdeal I (ULift.{u, 0} (Fin n))) :=
    _root_.RestrictedPowerSeries.isAdic_coefficientIdeal I (Ideal.fg_of_isNoetherianRing I) _
  have hJadic : _root_.IsAdic (I.map (algebraMap A C)) :=
    _root_.RingHom.isAdic_map_of_isAdic (algebraMap A C) hadic hIadic
  have hmap : (_root_.RestrictedPowerSeries.coefficientIdeal I
        (ULift.{u, 0} (Fin n))).map (π₀.comp E.symm.toRingHom) =
      I.map (algebraMap A C) := by
    rw [show _root_.RestrictedPowerSeries.coefficientIdeal I (ULift.{u, 0} (Fin n)) =
        I.map (_root_.RestrictedPowerSeries.coefficientRingHom I
          (ULift.{u, 0} (Fin n))) from rfl, Ideal.map_map, hπcomp]
  exact ⟨continuous_of_isAdic_of_map_le hcoef hJadic _ (le_of_eq hmap),
    isOpenMap_of_surjective_of_isAdic _ (hsurj₀.comp E.symm.surjective) hcoef (hmap ▸ hJadic),
    hπcomp⟩

/-- **A quotient of a restricted power series ring is finite over it.** -/
public theorem module_finite_of_restrictedPowerSeriesSurjection {A C : Type u} [CommRing A]
    [CommRing C] (I : Ideal A) (n : ℕ) (π : RestrictedPowerSeries I (Fin n) →+* C)
    (hπ : Function.Surjective π) :
    letI : Algebra (RestrictedPowerSeries I (Fin n)) C := π.toAlgebra
    Module.Finite (RestrictedPowerSeries I (Fin n)) C := by
  let : Algebra (RestrictedPowerSeries I (Fin n)) C := π.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap (RestrictedPowerSeries I (Fin n)) C)
    (fun c => by
      obtain ⟨x, rfl⟩ := hπ c
      exact ⟨x, rfl⟩)

end Rig

end
