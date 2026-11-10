module

public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.NaiveCotangent.BaseIsoInvariance
public import StacksFrontier.RingTheory.Rig.RigEtaleTFAE
public import StacksFrontier.RingTheory.Rig.RigSmooth

/-!
# Rig-étaleness over the completion of the base

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `Â` the `I`-adic completion of `A`. An
`IÂ`-adically complete `Â`-algebra `B` with `B / IB` of finite type over `Â / IÂ` is, through
`A → Â`, an `I`-adically complete `A`-algebra with `B / IB` of finite type over `A / I`; and if
`B` is rig-étale over `(Â, IÂ)` then it is rig-étale over `(A, I)`.

This is the identification `NL^∧_{B/A} = NL^∧_{B/Â}` which the source uses tacitly whenever it
reads an arrow `Â → B` of `WAdm^{Noeth}` presenting a chart of the completion `Spec(A)_{/V(I)}` as
an object of the category of Stacks 0AL4 over `(A, I)`: for instance in the proof of Stacks 0AR4,
where the existence of the algebraization "is a restatement of Lemma 0AKG".

## Main results

* `Rig.isRigEtaleOver_of_isRigEtale_adicCompletion`: the statement above, in the form of
  `Rig.IsRigEtaleOver` for the composite `A → Â → B`.

## Implementation notes

Rig-étaleness is compared through condition (4) of Stacks 0AJU
(`Rig.IsReductionCohomologyAnnihilated`), which is presentation free: it concerns the naive
cotangent complexes of `Bₙ = B / IⁿB` over `Aₙ = A / Iⁿ`. For `I` finitely generated the
quotient `Â / IⁿÂ` is `A / Iⁿ` (`AdicCompletion.ker_evalₐ_eq_map_pow`), and `IⁿB` is the same
ideal whether `B` is regarded over `A` or over `Â`, so the two conditions are about isomorphic
squares of rings, between which
`NaiveCotangent.mem_annihilator_homology_of_ringEquiv` moves annihilation statements.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
-/

@[expose] public noncomputable section

universe u v

namespace Rig

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- The quotient of `A` by `Iⁿ` is the quotient of its `I`-adic completion by the extension of
`Iⁿ`, compatibly with the maps from `A`. -/
theorem exists_ringEquiv_quotient_adicCompletion (n : ℕ) :
    ∃ β : A ⧸ I ^ n ≃+* AdicCompletion I A ⧸ (I ^ n).map (algebraMap A (AdicCompletion I A)),
      ∀ a : A, β (Ideal.Quotient.mk _ a) =
        Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a) := by
  let e : (AdicCompletion I A ⧸ (I ^ n).map (algebraMap A (AdicCompletion I A))) ≃ₐ[A]
      (A ⧸ I ^ n) :=
    (Ideal.quotientEquivAlgOfEq A
        (AdicCompletion.ker_evalₐ_eq_map_pow I I.fg_of_isNoetherianRing n).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ I n))
  refine ⟨e.symm.toRingEquiv, fun a ↦ ?_⟩
  have h := e.symm.commutes a
  simpa [Ideal.Quotient.algebraMap_eq] using h

/-- The `I`-adic completion of `A` maps onto `A / I`'s counterpart: every class modulo `IÂ` is the
class of an element of `A`. -/
theorem surjective_quotientMk_comp_algebraMap_adicCompletion :
    Function.Surjective ((Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))).comp
      (algebraMap A (AdicCompletion I A))) := by
  obtain ⟨β, hβ⟩ := exists_ringEquiv_quotient_adicCompletion I 1
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : (I ^ 1).map (algebraMap A (AdicCompletion I A)) =
      I.map (algebraMap A (AdicCompletion I A)) := by rw [pow_one]
  obtain ⟨z, hz⟩ := β.surjective ((Ideal.quotEquivOfEq h1).symm (Ideal.Quotient.mk _ x))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨a, ?_⟩
  rw [hβ, RingEquiv.eq_symm_apply] at hz
  change (Ideal.quotEquivOfEq h1) (Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a)) =
    _ at hz
  rwa [Ideal.quotEquivOfEq_mk] at hz

variable {I}

/-- **Rig-étaleness over the completion of the base descends to the base.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal, `Â` the `I`-adic completion of `A` and `φ : Â → B` a ring map
making `B` rig-étale over `(Â, IÂ)`, with the completeness and finite type data that requires.
Then `B`, regarded as an `A`-algebra through `A → Â → B`, is rig-étale over `(A, I)`, with the
same completeness and finite type data. -/
theorem isRigEtaleOver_of_isRigEtale_adicCompletion {R : Type v} [CommRing R]
    (φ : AdicCompletion I A →+* R)
    (h : IsRigEtaleOver φ (I.map (algebraMap A (AdicCompletion I A)))) :
    IsRigEtaleOver (φ.comp (algebraMap A (AdicCompletion I A))) I := by
  classical
  set α := algebraMap A (AdicCompletion I A) with hα
  set I' := I.map α with hI'
  set ψ := φ.comp α with hψ
  obtain ⟨hc', hf', hrig⟩ := h
  let : Algebra (AdicCompletion I A) R := φ.toAlgebra
  let : Algebra A R := ψ.toAlgebra
  have hIn : ∀ n : ℕ, (I ^ n).map α = I' ^ n := fun n ↦ by rw [hI', Ideal.map_pow]
  have hmap : ∀ n : ℕ, (I ^ n).map (algebraMap A R) = (I' ^ n).map (algebraMap _ R) := by
    intro n
    change (I ^ n).map ψ = (I' ^ n).map φ
    rw [← hIn n, Ideal.map_map]
  have hmap1 : I.map (algebraMap A R) = I'.map (algebraMap _ R) := by
    simpa only [pow_one] using hmap 1
  have hc : IsAdicComplete (I.map (algebraMap A R)) R := by
    rwa [hmap1]
  have hf : Algebra.FiniteType (A ⧸ I) (R ⧸ I.map (algebraMap A R)) := by
    let : Algebra.FiniteType (AdicCompletion I A ⧸ I') (R ⧸ I'.map (algebraMap _ R)) := hf'
    rw [← RingHom.finiteType_algebraMap]
    let g : A ⧸ I →+* AdicCompletion I A ⧸ I' := Ideal.quotientMap I' α Ideal.le_comap_map
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨a, ha⟩ := surjective_quotientMk_comp_algebraMap_adicCompletion I y
      exact ⟨Ideal.Quotient.mk I a, ha⟩
    let e := Ideal.quotEquivOfEq hmap1
    have heq : algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R)) =
        (e.symm : _ →+* _).comp
          ((algebraMap (AdicCompletion I A ⧸ I') (R ⧸ I'.map (algebraMap _ R))).comp g) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    rw [heq]
    exact (RingHom.FiniteType.of_surjective _ e.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr inferInstance).comp
        (RingHom.FiniteType.of_surjective g hg))
  refine ⟨hc, hf, ?_⟩
  let : Algebra.FiniteType (A ⧸ I) (R ⧸ I.map (algebraMap A R)) := hf
  let : Algebra.FiniteType (AdicCompletion I A ⧸ I') (R ⧸ I'.map (algebraMap _ R)) := hf'
  set B := AdicFiniteTypeAlgebra.of (I := I) R hc
  set B' := AdicFiniteTypeAlgebra.of (I := I') R hc'
  have hred' : IsReductionCohomologyAnnihilated B' :=
    ((tfae_isRigEtale B' (completedPolynomialPresentation I' (Ideal.fg_of_isNoetherianRing I')
      B')).out 1 4).mp hrig
  refine ((tfae_isRigEtale B (completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I)
    B)).out 1 4).mpr ?_
  obtain ⟨c, hcn⟩ := hred'
  refine ⟨c, fun n hn a ha ↦ ?_⟩
  obtain ⟨β, hβ⟩ := exists_ringEquiv_quotient_adicCompletion I n
  have ha' : α a ∈ I' ^ c := hIn c ▸ Ideal.mem_map_of_mem α ha
  obtain ⟨h₁, h₀⟩ := hcn n hn (α a) ha'
  let e : (R ⧸ (I ^ n).map (algebraMap A R)) ≃+* (R ⧸ (I' ^ n).map (algebraMap _ R)) :=
    Ideal.quotEquivOfEq (hmap n)
  let β' : A ⧸ I ^ n ≃+* AdicCompletion I A ⧸ I' ^ n := β.trans (Ideal.quotEquivOfEq (hIn n))
  have hβ' : ∀ x : A, β' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (α x) := fun x ↦ by
    change Ideal.quotEquivOfEq (hIn n) (β (Ideal.Quotient.mk _ x)) = _
    rw [hβ, Ideal.quotEquivOfEq_mk]
  have he : ∀ r : A ⧸ I ^ n, e (algebraMap (A ⧸ I ^ n) (R ⧸ (I ^ n).map (algebraMap A R)) r) =
      algebraMap (AdicCompletion I A ⧸ I' ^ n) (R ⧸ (I' ^ n).map (algebraMap _ R)) (β' r) := by
    intro r
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hβ']
    rfl
  have key : ∀ k : ℕ, k ≤ 1 →
      Ideal.Quotient.mk ((I' ^ n).map (algebraMap _ R)) (algebraMap _ R (α a)) ∈
        Module.annihilator (R ⧸ (I' ^ n).map (algebraMap _ R))
          ((Algebra.naiveCotangentComplex (AdicCompletion I A ⧸ I' ^ n)
            (R ⧸ (I' ^ n).map (algebraMap _ R))).homology k) →
      Ideal.Quotient.mk ((I ^ n).map (algebraMap A R)) (algebraMap A R a) ∈
        Module.annihilator (R ⧸ (I ^ n).map (algebraMap A R))
          ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
            (R ⧸ (I ^ n).map (algebraMap A R))).homology k) := by
    intro k hk hr
    refine NaiveCotangent.mem_annihilator_homology_of_ringEquiv
      (R₀ := A ⧸ I ^ n) (R₁ := AdicCompletion I A ⧸ I' ^ n)
      (T := R ⧸ (I ^ n).map (algebraMap A R)) (T' := R ⧸ (I' ^ n).map (algebraMap _ R))
      β' e he (Ideal.Quotient.mk _ a) hk ?_
    rw [← he]
    exact hr
  exact ⟨key 1 le_rfl h₁, key 0 zero_le_one h₀⟩

end Rig

end
