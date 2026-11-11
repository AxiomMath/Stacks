module

public import StacksFrontier.RingTheory.AdicCompletion.MaximalIdealLocalization
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.AdicCompletion.Units
public import StacksFrontier.RingTheory.PowerSeries.RegularRing

/-!
# Maximal ideals and local rings of an adic completion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `Â` the `I`-adic completion. Since `IÂ` lies
in the Jacobson radical of `Â` (Stacks 05GI) and `Â ⧸ IÂ = A ⧸ I`, the maximal ideals of `Â` are
the ideals `𝔪Â` for the maximal ideals `𝔪 ⊇ I` of `A`, with `Â ⧸ 𝔪Â = A ⧸ 𝔪`. The flat map
`A → Â` is then an isomorphism modulo `𝔪`, so the `𝔪`-adic completion of `A` is the `𝔪Â`-adic
completion of `Â`; completing at a maximal ideal computes the completion of the local ring there,
so the completions of the local rings `A_𝔪` and `Â_{𝔪Â}` are isomorphic.

Together with Stacks 07NY and 07NV this transfers regularity and dimension of the local rings of
`A` at the maximal ideals containing `I` to `Â`. Idempotents of `Â` are detected in `A ⧸ I`,
because the kernel of `Â → A ⧸ I` lies in the Jacobson radical.

## Main results

* `AdicCompletion.map_isMaximal`: `𝔪Â` is maximal for a maximal ideal `𝔪 ⊇ I`.
* `AdicCompletion.exists_isMaximal_map_eq`: every maximal ideal of `Â` is of this form.
* `AdicCompletion.nonempty_ringEquiv_adicCompletion_localization`: the completions of `A_𝔪`
  and `Â_{𝔪Â}` are isomorphic.
* `AdicCompletion.isRegularRing_of_isRegularLocalRing`: `Â` is regular when every `A_𝔪`, for
  `𝔪 ⊇ I` maximal, is a regular local ring.
* `AdicCompletion.ringKrullDim_eq_of_ringKrullDim_localization`: `Â` has dimension `d` when
  every `A_𝔪`, for `𝔪 ⊇ I` maximal, has dimension `d`.
* `AdicCompletion.eq_zero_or_eq_one_of_isIdempotentElem`: `Â` has no nontrivial idempotents
  when `A ⧸ I` has none.
-/

@[expose] public section

universe u

open IsLocalRing

namespace AdicCompletion

section General

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- An idempotent of the completion whose image in `A ⧸ I` is zero is zero: it lies in the
Jacobson radical, so `1 - e` is a unit, and `e (1 - e) = 0`. -/
theorem eq_zero_of_isIdempotentElem_of_evalOneₐ_eq_zero {e : AdicCompletion I A}
    (he : IsIdempotentElem e) (h0 : evalOneₐ I e = 0) : e = 0 := by
  have hjac : e ∈ (⊥ : Ideal (AdicCompletion I A)).jacobson :=
    (isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot I).2.2.2.2 h0
  have hu : IsUnit (1 - e) := by
    simpa [sub_eq_neg_add, add_comm] using (Ideal.mem_jacobson_bot.1 hjac) (-1)
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  exact (hu.mul_left_eq_zero).1 hmul

/-- **The completion is connected when `A ⧸ I` is**: if `0` and `1` are the only idempotents of
`A ⧸ I`, they are the only idempotents of the `I`-adic completion. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem
    (h : ∀ e : A ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1) (e : AdicCompletion I A)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases h _ (he.map (evalOneₐ I)) with h0 | h1
  · exact Or.inl (eq_zero_of_isIdempotentElem_of_evalOneₐ_eq_zero I he h0)
  · refine Or.inr (sub_eq_zero.1 ?_).symm
    exact eq_zero_of_isIdempotentElem_of_evalOneₐ_eq_zero I he.one_sub
      (by rw [map_sub, map_one, h1, sub_self])

/-- The map `Â → A ⧸ 𝔪` for an ideal `𝔪 ⊇ I`, through `Â → A ⧸ I`. -/
noncomputable def toQuotient {m : Ideal A} (hIm : I ≤ m) : AdicCompletion I A →+* A ⧸ m :=
  (Ideal.Quotient.factor hIm).comp (evalOneₐ I).toRingHom

theorem toQuotient_algebraMap {m : Ideal A} (hIm : I ≤ m) (a : A) :
    toQuotient I hIm (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk m a := by
  simp [toQuotient]

theorem toQuotient_surjective {m : Ideal A} (hIm : I ≤ m) :
    Function.Surjective (toQuotient I hIm) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_, toQuotient_algebraMap I hIm a⟩

end General

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- Every element of the completion is congruent modulo `IÂ` to the image of an element of
`A`. -/
theorem exists_sub_algebraMap_mem_map (y : AdicCompletion I A) :
    ∃ a : A, y - algebraMap A (AdicCompletion I A) a ∈
      I.map (algebraMap A (AdicCompletion I A)) := by
  obtain ⟨x, hx⟩ := (quotientMap_bijective I (IsNoetherian.noetherian I)).2
    (Ideal.Quotient.mk _ y)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_⟩
  rw [Ideal.quotientMap_mk] at hx
  exact Ideal.Quotient.eq.1 hx.symm

/-- The kernel of `Â → A ⧸ 𝔪` is `𝔪Â`. -/
theorem ker_toQuotient {m : Ideal A} (hIm : I ≤ m) :
    RingHom.ker (toQuotient I hIm) = m.map (algebraMap A (AdicCompletion I A)) := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map I y
    have hya : toQuotient I hIm (y - algebraMap A _ a) = 0 := by
      have hmap : I.map (algebraMap A (AdicCompletion I A)) ≤ RingHom.ker (toQuotient I hIm) :=
        Ideal.map_le_iff_le_comap.2 fun b hb => by
          simp [RingHom.mem_ker, toQuotient_algebraMap, Ideal.Quotient.eq_zero_iff_mem.2 (hIm hb)]
      exact hmap ha
    have hy0 : toQuotient I hIm y = 0 := hy
    rw [map_sub, hy0, zero_sub, neg_eq_zero, toQuotient_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem] at hya
    have := Ideal.add_mem _ (Ideal.map_mono hIm ha) (Ideal.mem_map_of_mem _ hya)
    simpa using this
  · exact Ideal.map_le_iff_le_comap.2 fun b hb => by
      simp [RingHom.mem_ker, toQuotient_algebraMap, Ideal.Quotient.eq_zero_iff_mem.2 hb]

/-- **`𝔪Â` is a maximal ideal** for a maximal ideal `𝔪 ⊇ I` of `A`: it is the kernel of the
surjection `Â → A ⧸ 𝔪`. -/
theorem map_isMaximal (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m) :
    (m.map (algebraMap A (AdicCompletion I A))).IsMaximal := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  rw [← ker_toQuotient I hIm]
  exact RingHom.ker_isMaximal_of_surjective _ (toQuotient_surjective I hIm)

/-- The map `A ⧸ 𝔪 → Â ⧸ 𝔪Â` is bijective for a maximal ideal `𝔪 ⊇ I`. -/
theorem bijective_quotientMap_of_le (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m) :
    Function.Bijective (Ideal.quotientMap (m.map (algebraMap A (AdicCompletion I A)))
      (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map) := by
  refine ⟨Ideal.quotientMap_injective' fun a ha => ?_, fun y => ?_⟩
  · rw [Ideal.mem_comap, ← ker_toQuotient I hIm, RingHom.mem_ker, toQuotient_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ha
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map I z
  refine ⟨Ideal.Quotient.mk m a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have := (Ideal.neg_mem_iff _).2 (Ideal.map_mono hIm ha)
  simpa using this

/-- **Every maximal ideal of `Â` is `𝔪Â` for a maximal ideal `𝔪 ⊇ I` of `A`.** It contains `IÂ`,
which lies in the Jacobson radical, so `A → Â ⧸ 𝔐` is surjective, and its kernel `𝔪` is
maximal with `𝔪Â ⊆ 𝔐`. -/
theorem exists_isMaximal_map_eq (M : Ideal (AdicCompletion I A)) [hM : M.IsMaximal] :
    ∃ m : Ideal A, m.IsMaximal ∧ I ≤ m ∧ m.map (algebraMap A (AdicCompletion I A)) = M := by
  have hIM : I.map (algebraMap A (AdicCompletion I A)) ≤ M := by
    intro x hx
    by_contra hxM
    obtain ⟨y, i, hi, hyi⟩ := hM.exists_inv hxM
    have hu : IsUnit (1 + -(y * x)) :=
      (isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot I).2.2.1 _
        ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ hx))
    have : i = 1 + -(y * x) := by linear_combination hyi
    exact hM.ne_top (M.eq_top_of_isUnit_mem hi (this ▸ hu))
  let f := (Ideal.Quotient.mk M).comp (algebraMap A (AdicCompletion I A))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map I y
    exact ⟨a, (Ideal.Quotient.eq.2 (hIM ha)).symm⟩
  have hker : RingHom.ker f = M.comap (algebraMap A (AdicCompletion I A)) := by
    ext a
    exact Ideal.Quotient.eq_zero_iff_mem
  let : Field (AdicCompletion I A ⧸ M) := Ideal.Quotient.field M
  have hmax : (M.comap (algebraMap A (AdicCompletion I A))).IsMaximal :=
    hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  have hIm : I ≤ M.comap (algebraMap A (AdicCompletion I A)) :=
    Ideal.map_le_iff_le_comap.1 hIM
  refine ⟨_, hmax, hIm, ?_⟩
  have := map_isMaximal I _ hIm
  exact this.eq_of_le hM.ne_top Ideal.map_comap_le

/-- **The completions of `A_𝔪` and of `Â_{𝔪Â}` are isomorphic**, for a maximal ideal `𝔪 ⊇ I`:
both are the `𝔪`-adic completion of `A`, the second through the flat map `A → Â`, which is an
isomorphism modulo `𝔪`. -/
theorem nonempty_ringEquiv_adicCompletion_localization (m : Ideal A) [m.IsMaximal]
    (hIm : I ≤ m) [(m.map (algebraMap A (AdicCompletion I A))).IsMaximal] :
    Nonempty (AdicCompletion (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m) ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime
          (m.map (algebraMap A (AdicCompletion I A)))))
        (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A))))) := by
  have : Module.Flat A (AdicCompletion I A) := flat_of_isNoetherian I
  obtain ⟨E1, -⟩ := exists_adicCompletionAlgEquiv_of_flat m
    (bijective_quotientMap_of_le I m hIm)
  obtain ⟨E2, -⟩ := Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime m
  obtain ⟨E3, -⟩ := Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime
    (m.map (algebraMap A (AdicCompletion I A)))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact ⟨(E2.toRingEquiv.symm.trans E1.toRingEquiv).trans E3.toRingEquiv⟩

/-- **Regularity of a completion.** If the localization of `A` at every maximal ideal containing
`I` is a regular local ring, then the `I`-adic completion is a regular ring: its localization at
a maximal ideal `𝔪Â` has the same completion as `A_𝔪`, so Stacks 07NY applies twice. -/
theorem isRegularRing_of_isRegularLocalRing
    (h : ∀ (m : Ideal A) [m.IsMaximal], I ≤ m → IsRegularLocalRing (Localization.AtPrime m)) :
    IsRegularRing (AdicCompletion I A) := by
  refine isRegularRing_of_isRegularLocalRing_localization_isMaximal _ fun M hM => ?_
  obtain ⟨m, hm, hIm, rfl⟩ := exists_isMaximal_map_eq I M
  have := hm
  have : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  have : IsNoetherianRing
      (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A)))) :=
    IsLocalization.isNoetherianRing (m.map (algebraMap A (AdicCompletion I A))).primeCompl _
      inferInstance
  obtain ⟨e⟩ := nonempty_ringEquiv_adicCompletion_localization I m hIm
  have := (isRegularLocalRing_iff_adicCompletion_maximalIdeal).1 (h m hIm)
  have := IsRegularLocalRing.of_ringEquiv e
  exact isRegularLocalRing_iff_adicCompletion_maximalIdeal.2 this

/-- The dimension of the localization of `Â` at `𝔪Â` is that of `A_𝔪` (Stacks 07NV twice). -/
theorem ringKrullDim_localization_map (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m)
    [(m.map (algebraMap A (AdicCompletion I A))).IsMaximal] :
    ringKrullDim (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A)))) =
      ringKrullDim (Localization.AtPrime m) := by
  have : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  have : IsNoetherianRing
      (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A)))) :=
    IsLocalization.isNoetherianRing (m.map (algebraMap A (AdicCompletion I A))).primeCompl _
      inferInstance
  obtain ⟨e⟩ := nonempty_ringEquiv_adicCompletion_localization I m hIm
  rw [ringKrullDim_adicCompletion_maximalIdeal, ringKrullDim_adicCompletion_maximalIdeal
    (A := Localization.AtPrime m), ringKrullDim_eq_of_ringEquiv e]

/-- **Dimension of a completion.** If `I ≠ A` and the localization of `A` at every maximal
ideal containing `I` has dimension `d`, then the `I`-adic completion has dimension `d`: every
prime of `Â` lies in a maximal ideal `𝔪Â`, whose height is the dimension of `A_𝔪`. -/
theorem ringKrullDim_eq_of_ringKrullDim_localization (hI : I ≠ ⊤) (d : ℕ∞)
    (h : ∀ (m : Ideal A) [m.IsMaximal], I ≤ m → ringKrullDim (Localization.AtPrime m) = d) :
    ringKrullDim (AdicCompletion I A) = d := by
  refine le_antisymm ((ringKrullDim_le_iff_height_le _).2 fun p hp => ?_) ?_
  · obtain ⟨M, hM, hpM⟩ := p.exists_le_maximal hp.ne_top
    obtain ⟨m, hm, hIm, rfl⟩ := exists_isMaximal_map_eq I M
    have := hm
    calc (p.height : WithBot ℕ∞) ≤ (m.map (algebraMap A (AdicCompletion I A))).height := by
          exact_mod_cast Ideal.height_mono hpM
      _ = ringKrullDim (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A)))) :=
          (IsLocalization.AtPrime.ringKrullDim_eq_height _
            (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A))))).symm
      _ = d := (ringKrullDim_localization_map I m hIm).trans (h m hIm)
  · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    have := hm
    have := map_isMaximal I m hIm
    rw [← h m hIm, ← ringKrullDim_localization_map I m hIm,
      IsLocalization.AtPrime.ringKrullDim_eq_height (m.map (algebraMap A (AdicCompletion I A)))
        (Localization.AtPrime (m.map (algebraMap A (AdicCompletion I A))))]
    exact Ideal.height_le_ringKrullDim_of_isPrime

end AdicCompletion

end
