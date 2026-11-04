module

public import StacksFrontier.RingTheory.Rig.RigEtaleAdicCompletionBase

/-!
# Rig-étaleness ascends to the completion of the base

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `Â` the `I`-adic completion of `A`. For a ring
map `φ : Â → B`, rig-étaleness of `B` over `(A, I)`, through `A → Â → B`, implies rig-étaleness
of `B` over `(Â, IÂ)`. This is the converse of
`Rig.isRigEtaleOver_of_isRigEtale_adicCompletion`, and it is proved the same way: both are read
through condition (4) of **Stacks 0AJU** (`Rig.IsReductionCohomologyAnnihilated`), which concerns
the naive cotangent complexes of `B / IⁿB` over `A / Iⁿ = Â / IⁿÂ`.

## Main results

* `Rig.isRigEtaleOver_adicCompletion_of_isRigEtaleOver`: rig-étaleness over `(A, I)` of an
  algebra over `Â` gives rig-étaleness over `(Â, IÂ)`.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
-/

@[expose] public noncomputable section

universe u v

namespace Rig

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

omit [IsNoetherianRing A] in
/-- **The data of Stacks 0AL4 ascend to the completion of the base.** Let `A` be a Noetherian
ring, `I ⊆ A` an ideal, `Â` the `I`-adic completion of `A` and `φ : Â → R` a ring map. If `R`,
regarded as an `A`-algebra through `A → Â → R`, is `I`-adically complete with `R / IR` of finite
type over `A / I`, then `R` is `IÂ`-adically complete with `R / IR` of finite type over
`Â / IÂ`: the ideal `IR` is the same either way, and `A / I → Â / IÂ` is onto. -/
theorem adicFiniteType_adicCompletion_of_adicFiniteType {R : Type v} [CommRing R]
    (φ : AdicCompletion I A →+* R)
    (hc : letI : Algebra A R := (φ.comp (algebraMap A (AdicCompletion I A))).toAlgebra
      IsAdicComplete (I.map (algebraMap A R)) R)
    (hf : letI : Algebra A R := (φ.comp (algebraMap A (AdicCompletion I A))).toAlgebra
      Algebra.FiniteType (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :
    letI : Algebra (AdicCompletion I A) R := φ.toAlgebra
    IsAdicComplete ((I.map (algebraMap A (AdicCompletion I A))).map
        (algebraMap (AdicCompletion I A) R)) R ∧
      Algebra.FiniteType (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)))
        (R ⧸ (I.map (algebraMap A (AdicCompletion I A))).map
          (algebraMap (AdicCompletion I A) R)) := by
  classical
  set α := algebraMap A (AdicCompletion I A)
  set I' := I.map α with hI'
  set ψ := φ.comp α
  let : Algebra (AdicCompletion I A) R := φ.toAlgebra
  let : Algebra A R := ψ.toAlgebra
  have hmap1 : I.map (algebraMap A R) = I'.map (algebraMap _ R) := by
    show I.map ψ = I'.map φ
    rw [hI', Ideal.map_map]
  refine ⟨by rwa [← hmap1], ?_⟩
  rw [← RingHom.finiteType_algebraMap]
  let g : A ⧸ I →+* AdicCompletion I A ⧸ I' := Ideal.quotientMap I' α Ideal.le_comap_map
  let e := Ideal.quotEquivOfEq hmap1
  have heq : (algebraMap (AdicCompletion I A ⧸ I') (R ⧸ I'.map (algebraMap _ R))).comp g =
      (e : _ →+* _).comp (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  refine RingHom.FiniteType.of_comp_finiteType (f := g) ?_
  rw [heq]
  exact (RingHom.FiniteType.of_surjective _ e.surjective).comp
    (RingHom.finiteType_algebraMap.mpr hf)

/-- **Rig-étaleness over the base ascends to the completion of the base.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal, `Â` the `I`-adic completion of `A` and `φ : Â → B` a ring map.
If `B`, regarded as an `A`-algebra through `A → Â → B`, is rig-étale over `(A, I)`, then `B` is
rig-étale over `(Â, IÂ)`, with the same completeness and finite type data. -/
theorem isRigEtaleOver_adicCompletion_of_isRigEtaleOver {R : Type v} [CommRing R]
    (φ : AdicCompletion I A →+* R)
    (h : IsRigEtaleOver (φ.comp (algebraMap A (AdicCompletion I A))) I) :
    IsRigEtaleOver φ (I.map (algebraMap A (AdicCompletion I A))) := by
  classical
  set α := algebraMap A (AdicCompletion I A) with hα
  set I' := I.map α with hI'
  set ψ := φ.comp α with hψ
  obtain ⟨hc, hf, hrig⟩ := h
  let : Algebra (AdicCompletion I A) R := φ.toAlgebra
  let : Algebra A R := ψ.toAlgebra
  have hmap : ∀ n : ℕ, (I ^ n).map (algebraMap A R) = (I' ^ n).map (algebraMap _ R) := by
    intro n
    show (I ^ n).map ψ = (I' ^ n).map φ
    rw [hI', ← Ideal.map_pow, Ideal.map_map]
  obtain ⟨hc', hf'⟩ := adicFiniteType_adicCompletion_of_adicFiniteType φ hc hf
  refine ⟨hc', hf', ?_⟩
  have : Algebra.FiniteType (A ⧸ I) (R ⧸ I.map (algebraMap A R)) := hf
  have : Algebra.FiniteType (AdicCompletion I A ⧸ I') (R ⧸ I'.map (algebraMap _ R)) := hf'
  set B := AdicFiniteTypeAlgebra.of (I := I) R hc
  set B' := AdicFiniteTypeAlgebra.of (I := I') R hc'
  have hred : IsReductionCohomologyAnnihilated B :=
    ((tfae_isRigEtale B (completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I)
      B)).out 1 4).mp hrig
  refine ((tfae_isRigEtale B' (completedPolynomialPresentation I'
    (Ideal.fg_of_isNoetherianRing I') B')).out 1 4).mpr ?_
  obtain ⟨c, hcn⟩ := hred
  refine ⟨c, fun n hn a' ha' ↦ ?_⟩
  obtain ⟨β, hβ⟩ := exists_ringEquiv_quotient_adicCompletion I n
  let e : (R ⧸ (I ^ n).map (algebraMap A R)) ≃+* (R ⧸ (I' ^ n).map (algebraMap _ R)) :=
    Ideal.quotEquivOfEq (hmap n)
  have hIn : (I ^ n).map α = I' ^ n := by rw [hI', Ideal.map_pow]
  let β' : A ⧸ I ^ n ≃+* AdicCompletion I A ⧸ I' ^ n := β.trans (Ideal.quotEquivOfEq hIn)
  have hβ' : ∀ x : A, β' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (α x) := fun x ↦ by
    show Ideal.quotEquivOfEq hIn (β (Ideal.Quotient.mk _ x)) = _
    rw [hβ, Ideal.quotEquivOfEq_mk]
  have he : ∀ r : AdicCompletion I A ⧸ I' ^ n,
      e.symm (algebraMap (AdicCompletion I A ⧸ I' ^ n) (R ⧸ (I' ^ n).map (algebraMap _ R)) r) =
        algebraMap (A ⧸ I ^ n) (R ⧸ (I ^ n).map (algebraMap A R)) (β'.symm r) := by
    intro r
    obtain ⟨x, rfl⟩ := β'.surjective r
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingEquiv.symm_apply_apply, hβ', RingEquiv.symm_apply_eq]
    rfl
  have key : ∀ k : ℕ, k ≤ 1 →
      I' ^ c ≤ Ideal.comap
        ((Ideal.Quotient.mk ((I' ^ n).map (algebraMap _ R))).comp
          (algebraMap (AdicCompletion I A) R))
        (Module.annihilator (R ⧸ (I' ^ n).map (algebraMap _ R))
          ((Algebra.naiveCotangentComplex (AdicCompletion I A ⧸ I' ^ n)
            (R ⧸ (I' ^ n).map (algebraMap _ R))).homology k)) := by
    intro k hk
    rw [hI', ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    have hA : Ideal.Quotient.mk ((I ^ n).map (algebraMap A R)) (algebraMap A R a) ∈
        Module.annihilator (R ⧸ (I ^ n).map (algebraMap A R))
          ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
            (R ⧸ (I ^ n).map (algebraMap A R))).homology k) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
      exacts [(hcn n hn a ha).2, (hcn n hn a ha).1]
    have hmk : algebraMap (A ⧸ I ^ n) (R ⧸ (I ^ n).map (algebraMap A R))
        (β'.symm (Ideal.Quotient.mk _ (α a))) =
          Ideal.Quotient.mk ((I ^ n).map (algebraMap A R)) (algebraMap A R a) := by
      rw [← hβ', RingEquiv.symm_apply_apply]
      rfl
    rw [← hmk] at hA
    exact NaiveCotangent.mem_annihilator_homology_of_ringEquiv
      (R₀ := AdicCompletion I A ⧸ I' ^ n) (R₁ := A ⧸ I ^ n)
      (T := R ⧸ (I' ^ n).map (algebraMap _ R)) (T' := R ⧸ (I ^ n).map (algebraMap A R))
      β'.symm e.symm he (Ideal.Quotient.mk _ (α a)) hk hA
  exact ⟨key 1 le_rfl ha', key 0 zero_le_one ha'⟩

end Rig

end
