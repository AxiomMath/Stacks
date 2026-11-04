module

public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.RingHom.FinitePresentation

/-!
# The two spellings of "complete intersection over a field" agree

There are two Lean renderings of Stacks Definition 10.135.1 (tag 00S9):

* `IsGlobalCompleteIntersection` / `IsLocalCompleteIntersection` (Section 10.135, tag 00S9),
  which present `S` by a `k`-algebra isomorphism `S ≃ₐ[k] k[x₁, …, xₙ] ⧸ (f₁, …, f_c)` and record
  the dimension count as `c ≤ n` together with `dim S = (n - c : ℕ)`, using truncated
  natural-number subtraction, and which take the covering family of the local notion to be an
  arbitrary set `s ⊆ S` with `Ideal.span s = ⊤`;
* `IsGlobalCompleteIntersectionOver` / `IsLocalCompleteIntersectionOver` (Section 10.136,
  tag 00SO), which present `S` by a surjection `π : k[x₁, …, xₙ] ↠ S` with
  `ker π = (f₁, …, f_c)` and record the dimension count additively as `dim S + c = n`, and which
  take the covering family of the local notion to be a finite family `g : Fin t → S` with
  `Ideal.span (Set.range g) = ⊤`.

This file proves that the two pairs define the same predicates.

## Main results

* `isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection`
* `isLocalCompleteIntersectionOver_iff_isLocalCompleteIntersection`
* `isGlobalCompleteIntersectionOver_localization` and
  `isLocalCompleteIntersectionOver_localization`: Lemma 10.135.2 (tag 00SA) in the `…Over`
  spelling.
* `IsSyntomic.isLocalCompleteIntersection_fibre`: the fibres of a syntomic ring map are local
  complete intersections in the sense of `IsLocalCompleteIntersection`.

## Implementation notes

The two renderings differ in three ways, and their equivalence needs no hypothesis.

* *Presentation.* An isomorphism to a quotient and a surjection with prescribed kernel carry the
  same information: `Ideal.quotientKerAlgEquivOfSurjective` turns the surjection into the
  isomorphism, and composing the quotient map with the inverse isomorphism turns the isomorphism
  back into a surjection, whose kernel is computed by `RingHom.ker_comp_of_injective`.
* *Dimension.* `dim S + c = n` in `WithBot ℕ∞` already forces `dim S` to be a natural number:
  `⊥ + c = ⊥` and `⊤ + c = ⊤` are both different from `(n : WithBot ℕ∞)`. So it forces `c ≤ n`
  as well, and the two dimension conditions are interchangeable with no side condition.
* *Covering family.* An arbitrary generating set of the unit ideal contains a finite one, because
  `1` lies in the span of finitely many of its elements
  (`Submodule.mem_span_finite_of_mem_span`); so allowing infinite covers does not enlarge the
  local notion.

## References

* [StacksProject 00S9](https://stacks.math.columbia.edu/tag/00S9)
* [StacksProject 00SO](https://stacks.math.columbia.edu/tag/00SO)
-/

@[expose] public section

variable (k : Type*) [Field k]

/-- A natural number cast into `WithBot ℕ∞` directly is its cast into `ℕ∞` followed by the cast
into `WithBot ℕ∞`. -/
private theorem natCast_withBot_enat (a : ℕ) :
    ((a : ℕ) : WithBot ℕ∞) = (((a : ℕ∞)) : WithBot ℕ∞) := by
  norm_cast

/-- The additive and the truncated-subtraction forms of the dimension count agree.

For `d : WithBot ℕ∞` and `c n : ℕ`, the equation `d + c = n` holds if and only if `c ≤ n` and
`d = (n - c : ℕ)` with truncated natural subtraction. -/
private theorem add_natCast_eq_natCast_iff_le_and_eq_tsub {d : WithBot ℕ∞} {c n : ℕ} :
    d + (c : WithBot ℕ∞) = (n : WithBot ℕ∞) ↔ c ≤ n ∧ d = ((n - c : ℕ) : WithBot ℕ∞) := by
  rw [natCast_withBot_enat c, natCast_withBot_enat n, natCast_withBot_enat (n - c)]
  constructor
  · intro h
    induction d using WithBot.recBotCoe with
    | bot => rw [WithBot.bot_add] at h; exact absurd h.symm (by simp)
    | coe e =>
      rw [← WithBot.coe_add, WithBot.coe_inj] at h
      induction e using ENat.recTopCoe with
      | top => simp at h
      | coe m =>
        have hmc : m + c = n := by exact_mod_cast h
        exact ⟨by omega, by rw [show m = n - c by omega]⟩
  · rintro ⟨hcn, rfl⟩
    rw [← WithBot.coe_add, WithBot.coe_inj, ← Nat.cast_add]
    congr 1
    omega

/-- **The global bridge.** The two renderings of Stacks 00S9 (1) define the same predicate: a
`k`-algebra `S` is a global complete intersection over `k` in the sense of Section 10.136
(`IsGlobalCompleteIntersectionOver`, a surjection `k[x₁, …, xₙ] ↠ S` with kernel `(f₁, …, f_c)`
and `dim S + c = n`) if and only if it is one in the sense of Section 10.135
(`IsGlobalCompleteIntersection`, an isomorphism `S ≃ₐ[k] k[x₁, …, xₙ] ⧸ (f₁, …, f_c)` with
`c ≤ n` and `dim S = n - c`). -/
theorem isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection
    (S : Type*) [CommRing S] [Algebra k S] :
    IsGlobalCompleteIntersectionOver k S ↔ IsGlobalCompleteIntersection k S := by
  constructor
  · rintro (hsub | ⟨n, c, π, f, hπ, hker, hdim⟩)
    · exact Or.inl hsub
    · obtain ⟨hcn, hd⟩ := add_natCast_eq_natCast_iff_le_and_eq_tsub.mp hdim
      exact Or.inr ⟨n, c, f, (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.trans
        (Ideal.quotientEquivAlgOfEq k hker), hcn, hd⟩
  · rintro (hsub | ⟨n, c, f, e, hcn, hd⟩)
    · exact Or.inl hsub
    · refine Or.inr ⟨n, c, e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k _), f,
        e.symm.surjective.comp Ideal.Quotient.mk_surjective, ?_,
        add_natCast_eq_natCast_iff_le_and_eq_tsub.mpr ⟨hcn, hd⟩⟩
      have hcomp : (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k
          (Ideal.span (Set.range f)))).toRingHom
          = e.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) := rfl
      rw [hcomp, RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]

/-- **The local bridge.** The two renderings of Stacks 00S9 (2) define the same predicate: a
`k`-algebra `S` is a local complete intersection over `k` in the sense of Section 10.136
(`IsLocalCompleteIntersectionOver`, a *finite* family `g : Fin t → S` spanning the unit ideal with
each `S_{g i}` a global complete intersection) if and only if it is one in the sense of
Section 10.135 (`IsLocalCompleteIntersection`, an *arbitrary* set `s ⊆ S` spanning the unit ideal
with each `S_g`, `g ∈ s`, a global complete intersection). -/
theorem isLocalCompleteIntersectionOver_iff_isLocalCompleteIntersection
    (S : Type*) [CommRing S] [Algebra k S] :
    IsLocalCompleteIntersectionOver k S ↔ IsLocalCompleteIntersection k S := by
  constructor
  · rintro ⟨t, g, hspan, hg⟩
    refine ⟨Set.range g, hspan, ?_⟩
    rintro w ⟨i, rfl⟩
    exact (isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection k _).mp (hg i)
  · rintro ⟨s, hspan, hs⟩
    obtain ⟨T, hTs, hT1⟩ :=
      Submodule.mem_span_finite_of_mem_span (S := s) (x := (1 : S)) (hspan ▸ Submodule.mem_top)
    have hmem : ∀ i : Fin T.card, ((T.equivFin.symm i : S)) ∈ s :=
      fun i => hTs (T.equivFin.symm i).property
    refine ⟨T.card, fun i => (T.equivFin.symm i : S), ?_, fun i => ?_⟩
    · have hrange : Set.range (fun i => ((T.equivFin.symm i : S))) = (T : Set S) := by
        refine Set.eq_of_subset_of_subset ?_ fun x hx => ⟨T.equivFin ⟨x, hx⟩, by simp⟩
        rintro _ ⟨i, rfl⟩
        exact (T.equivFin.symm i).property
      rw [hrange]
      exact Ideal.eq_top_of_isUnit_mem _ hT1 isUnit_one
    · exact (isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection k _).mpr
        (hs _ (hmem i))

/-- **Stacks 00SA (1) in the `…Over` spelling.** Let `k` be a field, `S` a finite type `k`-algebra
and `g ∈ S`. If `S` is a global complete intersection over `k` in the sense of Section 10.136,
then so is the localization `S_g = Localization.Away g`. -/
theorem isGlobalCompleteIntersectionOver_localization
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (g : S)
    (hS : IsGlobalCompleteIntersectionOver k S) :
    IsGlobalCompleteIntersectionOver k (Localization.Away g) :=
  (isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection k _).mpr
    (isGlobalCompleteIntersection_localization k S g
      ((isGlobalCompleteIntersectionOver_iff_isGlobalCompleteIntersection k S).mp hS))

/-- **Stacks 00SA (2) in the `…Over` spelling.** Let `k` be a field, `S` a finite type `k`-algebra
and `g ∈ S`. If `S` is a local complete intersection over `k` in the sense of Section 10.136, then
so is the localization `S_g = Localization.Away g`. -/
theorem isLocalCompleteIntersectionOver_localization
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (g : S)
    (hS : IsLocalCompleteIntersectionOver k S) :
    IsLocalCompleteIntersectionOver k (Localization.Away g) :=
  (isLocalCompleteIntersectionOver_iff_isLocalCompleteIntersection k _).mpr
    (isLocalCompleteIntersection_localization k S g
      ((isLocalCompleteIntersectionOver_iff_isLocalCompleteIntersection k S).mp hS))

/-- The fibre condition in `IsSyntomic` read in the Section 10.135 vocabulary: if `R → S` is
syntomic then for every prime `p` of `R` the fibre `S ⊗_R κ(p)` is a local complete intersection
over `κ(p)` in the sense of `IsLocalCompleteIntersection`. -/
theorem IsSyntomic.isLocalCompleteIntersection_fibre
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] (h : IsSyntomic R S)
    (p : Ideal R) [p.IsPrime] :
    letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    IsLocalCompleteIntersection κ (TensorProduct R S κ) := by
  let κ := IsLocalRing.ResidueField (Localization.AtPrime p)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  exact (isLocalCompleteIntersectionOver_iff_isLocalCompleteIntersection κ _).mp (h.2.2 p)

end
