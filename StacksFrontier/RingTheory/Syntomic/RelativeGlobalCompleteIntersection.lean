module

public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.Syntomic.Defs

/-!
# Relative global complete intersections are syntomic

Let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be a relative global complete intersection over `R`.
Then `R → S` is syntomic. Its fibres are global complete intersections over the residue fields,
presented by the base changed presentation, and it is of finite presentation; so the content of
the statement is flatness.

## Main results

* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersection_fiber`:
  the fibres of a relative global complete intersection are global complete intersections.
* `Algebra.Generators.localizationAtPrimeAlgEquiv`: for a presentation `S = R[x_1, …, x_n]/I` and
  a prime `𝔮` of `S` with corresponding prime `𝔮'`, the local ring `S_𝔮` is
  `R[x_1, …, x_n]_{𝔮'}/I R[x_1, …, x_n]_{𝔮'}`.
* `Algebra.Presentation.flat_localization_atPrime`: the local rings `S_𝔮` of a relative global
  complete intersection are flat over `R`.
* `Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection`: a relative global complete
  intersection is syntomic.

## Implementation notes

*Flatness is checked at the maximal ideals of `S`* (`Module.flat_of_isLocalized_maximal`). At a
prime `𝔮`, `Algebra.Presentation.flat_localization_quotient_relation` for `i = c` says that
`R[x_1, …, x_n]_{𝔮'}/(f_1, …, f_c)` is flat over `R`, and that ring is `S_𝔮`, by
`Algebra.Generators.localizationAtPrimeAlgEquiv`.

## References

* [Stacks 00SW](https://stacks.math.columbia.edu/tag/00SW), Lemma 10.136.13
* [Stacks 00SV](https://stacks.math.columbia.edu/tag/00SV), Lemma 10.136.12,
  `Algebra.Presentation.flat_localization_quotient_relation`
* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5
* [Stacks 00SL](https://stacks.math.columbia.edu/tag/00SL), Definition 10.136.1
-/

@[expose] public section

/-! ### The fibres -/

/-- The fibres of a relative global complete intersection are global complete intersections: if
`S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete intersection over `R`, then for
every prime `p` of `R` the fibre `κ(p) ⊗_R S` is a global complete intersection over `κ(p)`. -/
theorem Algebra.Presentation.IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersection_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n c : ℕ}
    {P : Algebra.Presentation R S (Fin n) (Fin c)} (hP : P.IsRelativeGlobalCompleteIntersection)
    (p : Ideal R) [p.IsPrime] :
    IsGlobalCompleteIntersection p.ResidueField (p.Fiber S) := by
  rcases subsingleton_or_nontrivial (p.Fiber S) with h | h
  · exact Or.inl h
  have hdim := hP.ringKrullDim_fiber_add_card_eq_card p h
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hdim
  obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hdim
  set Q := P.baseChange p.ResidueField
  exact Or.inr ⟨n, c, Q.relation, ((Ideal.quotientEquivAlgOfEq p.ResidueField
    Q.span_range_relation_eq_ker).trans (Q.quotientEquiv.restrictScalars p.ResidueField)).symm,
    hcn, hd⟩

/-! ### The local rings of a presented algebra -/

namespace Algebra.Generators

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*}
  (P : Algebra.Generators R S ι) (q : Ideal S) [q.IsPrime]

/-- The map `S → R[xᵢ]_{𝔮'}/I R[xᵢ]_{𝔮'}` induced by `R[xᵢ] → R[xᵢ]_{𝔮'}`, where `S = R[xᵢ]/I` and
`𝔮'` is the prime of `R[xᵢ]` corresponding to the prime `𝔮` of `S`. -/
noncomputable def toLocalizationQuotient :
    S →+* Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
      P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S)))) :=
  RingHom.liftOfSurjective (algebraMap P.Ring S) P.algebraMap_surjective
    ⟨(Ideal.Quotient.mk _).comp (algebraMap P.Ring _), fun x hx ↦ by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx⟩

/-- For a presentation `S = R[xᵢ]/I` and a prime `𝔮` of `S` with corresponding prime `𝔮'` of
`R[xᵢ]`, the local ring `S_𝔮` is the quotient `R[xᵢ]_{𝔮'}/I R[xᵢ]_{𝔮'}`, as an `R`-algebra. -/
noncomputable def localizationAtPrimeAlgEquiv :
    Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
      P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S)))) :=
  letI := (P.toLocalizationQuotient q).toAlgebra
  have hsurj := P.algebraMap_surjective
  have hmap : (q.comap (algebraMap P.Ring S)).primeCompl.map (algebraMap P.Ring S) =
      q.primeCompl := by
    ext s
    obtain ⟨x, rfl⟩ := hsurj s
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have : IsLocalization q.primeCompl (Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
      P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))) := by
    rw [← hmap]
    refine IsLocalization.of_surjective _ _ (algebraMap P.Ring S) hsurj _
      Ideal.Quotient.mk_surjective (RingHom.ext fun x ↦ ?_) ?_
    · exact (RingHom.liftOfSurjective_comp_apply _ hsurj _ x :
        P.toLocalizationQuotient q (algebraMap P.Ring S x) = _).symm
    · rw [Ideal.mk_ker]
      rfl
  have : IsScalarTower R S (Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
      P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))) :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R P.Ring S, RingHom.algebraMap_toAlgebra,
        toLocalizationQuotient, RingHom.liftOfSurjective_comp_apply, RingHom.comp_apply,
        Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _).restrictScalars R

end Algebra.Generators

/-! ### Relative global complete intersections are syntomic -/

/-- The local rings of a relative global complete intersection are flat: if
`S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete intersection over `R`, then
`S_𝔮` is flat over `R` for every prime `𝔮` of `S`. -/
theorem Algebra.Presentation.flat_localization_atPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} [Finite ι] {c : ℕ} (P : Algebra.Presentation R S ι (Fin c))
    [P.IsRelativeGlobalCompleteIntersection] (q : Ideal S) [q.IsPrime] :
    Module.Flat R (Localization.AtPrime q) := by
  have hker : P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S)))) =
      Ideal.ofList (((List.ofFn P.relation).map
        (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))).take c) := by
    rw [List.take_of_length_le (by simp), ← Ideal.map_ofList, ← P.span_range_relation_eq_ker]
    exact congrArg _ (congrArg Ideal.span (Set.ext fun x ↦ (List.mem_ofFn' _ x).symm))
  have := P.flat_localization_quotient_relation q c
  rw [← hker] at this
  exact Module.Flat.of_linearEquiv (P.localizationAtPrimeAlgEquiv q).toLinearEquiv

/-- A relative global complete intersection is syntomic: if `S = R[x_1, …, x_n]/(f_1, …, f_c)`
is a relative global complete intersection over `R`, then `R → S` is flat, of finite
presentation, and its fibres are local complete intersections over the residue fields. -/
@[stacks 00SW "Stated for the class `Algebra.IsRelativeGlobalCompleteIntersection R S` and
concluding `Algebra.Syntomic R S`, the whole of Definition 00SL, not only the flatness that the
source's \"i.e., flat\" singles out."]
theorem Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    Algebra.Syntomic R S := by
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R S›.out
  have : Module.Flat R S :=
    Module.flat_of_isLocalized_maximal S S (fun q _ ↦ Localization.AtPrime q)
      (fun q _ ↦ Algebra.linearMap S _) fun q _ ↦ P.flat_localization_atPrime q
  exact { finitePresentation := P.finitePresentation_of_isFinite
          isLocalCompleteIntersection_fiber := fun p _ ↦
            (hP.isGlobalCompleteIntersection_fiber p).isLocalCompleteIntersection }

end
