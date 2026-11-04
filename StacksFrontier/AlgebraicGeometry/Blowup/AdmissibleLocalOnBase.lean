module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.FlatBaseChange

/-!
# The blowup problem is local on the base

Let `S` be a quasi-compact and quasi-separated scheme and let `U ⊆ S` be a quasi-compact open.
Suppose that for every point of `S` we can solve a blowup problem on some quasi-compact open
neighbourhood, that is, produce an admissible blowup of that neighbourhood over its part of `U`.
Then a single `U`-admissible blowup of `S` solves all of them at once: its restriction to each
member of a finite subcover factors through the given local blowup.

This is the last paragraph of Remark 38.30.1 ([Stacks, Tag 080Y]), the one asserting that "the
general problem above is local on `S` as well". The remark deduces it from Divisors, Lemmas
31.35.3 and 31.35.4, and so do we: [Stacks, Tag 080M]
(`Stacks.Blowup.exists_admissibleBlowup_isPullback`) extends each local blowup to a
`U`-admissible blowup of `S` whose restriction to the neighbourhood is the given one, and
[Stacks, Tag 080N] (`Stacks.Blowup.exists_admissibleBlowup_dominating`) replaces the resulting
finite family of blowups of `S` by one dominating all of them.

## Main results

* `AlgebraicGeometry.exists_admissibleBlowup_forall_restrict_factors`: for a finite family of
  quasi-compact opens with an admissible blowup over each, one `U`-admissible blowup of `S`
  whose restriction to each open factors through that blowup.
* `AlgebraicGeometry.exists_admissibleBlowup_finite_cover_restrict_factors`: the same with the
  family indexed by the points of `S`, the finite subcover extracted from quasi-compactness.
  This is the paragraph's own formulation, "given `s ∈ S` we can find a quasi-compact open
  neighbourhood `W` of `s` such that the problem for `F_W/X_W/W` is solvable".

## Implementation notes

The restriction of the global blowup `p : S' ⟶ S` to a quasi-compact open `W` is taken to be
`p ∣_ W`, the morphism `p ⁻¹ᵁ W ⟶ W` of `AlgebraicGeometry.morphismRestrict`. That is the base
change of `p` to `W`, and it is what the remark denotes by a subscript. Only the commutation
`AlgebraicGeometry.morphismRestrict_ι` is needed to feed it to the cartesian square of
[Stacks, Tag 080M]: the factorisation is then that square's own lift.

No property `P` of `F/X/S` appears. The paragraph's hypothesis on `P` — that it is local on `S`,
in the sense that it descends from a finite open cover by quasi-compact opens — is about `P` and
not about blowups, and once the single blowup below is in hand it is that hypothesis, applied to
the cover, which concludes. What is proved here is the blowup-theoretic content, namely that one
`U`-admissible blowup of `S` simultaneously refines every local solution.

The conjunct a consumer of these statements wants is asserted: the factorisation `r` is itself
an admissible blowup of `V j`, which is what lets "`P` is stable under strict transform" carry
`P` from the local solution to the restriction of the global one. [Stacks, Tag 080N] supplies
admissibility of the factor map `k j : S' ⟶ T j` over `q j ⁻¹ᵁ U`, and `r` is the base change
of `k j` along `g j : V j ⟶ T j`: the square `IsPullback r (p ⁻¹ᵁ W j).ι (g j) (k j)` is the
left half of the rectangle whose right half is the cartesian square of [Stacks, Tag 080M] and
whose outer square is `AlgebraicGeometry.isPullback_morphismRestrict`. Since `g j` is a base
change of the open immersion `(W j).ι` it is flat, so
`Stacks.Blowup.IsAdmissibleBlowup.of_isPullback` applies, and the open it produces,
`g j ⁻¹ᵁ (q j ⁻¹ᵁ U)`, is `c j ⁻¹ᵁ ((W j).ι ⁻¹ᵁ U)` because `g j ≫ q j = c j ≫ (W j).ι`.

## References

* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080N](https://stacks.math.columbia.edu/tag/080N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **Stacks Project, Tag 080Y**, the locality on `S` of Remark 38.30.1, for a finite family of
quasi-compact opens. Let `S` be quasi-compact and quasi-separated, `U ⊆ S` a quasi-compact open,
and let `W j ⊆ S` be finitely many quasi-compact opens carrying `W j ∩ U`-admissible blowups
`c j : V j ⟶ W j`. There is one `U`-admissible blowup `p : S' ⟶ S` whose restriction to each
`W j` factors through `c j`.

Each `c j` extends to a `U`-admissible blowup `q j : T j ⟶ S` with `IsPullback (c j) _ (W j).ι
(q j)` by [Stacks, Tag 080M], and [Stacks, Tag 080N] produces a `U`-admissible `p : S' ⟶ S`
factoring through every `q j` by a `q j ⁻¹ᵁ U`-admissible blowup `k j`. The restriction
`p ∣_ W j` and the composite `(p ⁻¹ᵁ W j).ι ≫ k j` agree over `S`, so the cartesian square of
[Stacks, Tag 080M] lifts them to the required map `r` to `V j`; and `r` is the base change of
`k j` along the flat `g j`, hence admissible. -/
@[stacks 080Y "locality on S: finitely many admissible blowups of quasi-compact opens of S are \
all refined by the restrictions of a single U-admissible blowup of S, each refinement itself an \
admissible blowup of the local solution"]
public theorem exists_admissibleBlowup_forall_restrict_factors
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    {ι : Type*} [Finite ι] (W : ι → S.Opens) (hW : ∀ j, IsCompact ((W j : S.Opens) : Set S))
    (V : ι → Scheme.{u}) (c : ∀ j, V j ⟶ (W j).toScheme)
    (hc : ∀ j, Stacks.Blowup.IsAdmissibleBlowup ((W j).ι ⁻¹ᵁ U) (c j)) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), Stacks.Blowup.IsAdmissibleBlowup U p ∧
      ∀ j, ∃ r : (p ⁻¹ᵁ W j).toScheme ⟶ V j, r ≫ c j = p ∣_ (W j) ∧
        Stacks.Blowup.IsAdmissibleBlowup (c j ⁻¹ᵁ ((W j).ι ⁻¹ᵁ U)) r := by
  choose T q hq g hg using fun j ↦
    Stacks.Blowup.exists_admissibleBlowup_isPullback U (W j) hU (hW j) (c j) (hc j)
  obtain ⟨S', p, hp, k, hk, hkadm⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_dominating U T q hq
  refine ⟨S', p, hp, fun j ↦ ?_⟩
  have hcomm : p ∣_ (W j) ≫ (W j).ι = ((p ⁻¹ᵁ W j).ι ≫ k j) ≫ q j := by
    rw [Category.assoc, hk j]
    exact morphismRestrict_ι p (W j)
  refine ⟨(hg j).lift (p ∣_ (W j)) ((p ⁻¹ᵁ W j).ι ≫ k j) hcomm, (hg j).lift_fst _ _ _, ?_⟩
  have hA : IsPullback ((hg j).lift (p ∣_ (W j)) ((p ⁻¹ᵁ W j).ι ≫ k j) hcomm)
      ((p ⁻¹ᵁ W j).ι) (g j) (k j) := by
    refine IsPullback.of_right ?_ ((hg j).lift_snd _ _ _) (hg j)
    rw [(hg j).lift_fst _ _ _, hk j]
    exact isPullback_morphismRestrict p (W j)
  have : IsOpenImmersion (g j) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (hg j) inferInstance
  have hadm := Stacks.Blowup.IsAdmissibleBlowup.of_isPullback (hkadm j) hA
  have hopens : (g j) ⁻¹ᵁ (q j ⁻¹ᵁ U) = c j ⁻¹ᵁ ((W j).ι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hg j).w]
  rwa [hopens] at hadm

/-- **Stacks Project, Tag 080Y**, the locality on `S` of Remark 38.30.1 in the paragraph's own
formulation. Let `S` be quasi-compact and quasi-separated and `U ⊆ S` a quasi-compact open.
Suppose that every point `s` of `S` has a quasi-compact open neighbourhood `W s` carrying a
`W s ∩ U`-admissible blowup `c s : V s ⟶ W s`. Then there is a finite set of points whose
neighbourhoods already cover `S`, and one `U`-admissible blowup `p : S' ⟶ S` whose restriction
to each of those neighbourhoods factors through the blowup given there.

The finite set comes from quasi-compactness of `S`, the blowup from
`AlgebraicGeometry.exists_admissibleBlowup_forall_restrict_factors` applied to the finite
subfamily. -/
@[stacks 080Y "locality on S: a solution on a quasi-compact open neighbourhood of every point \
of S is refined, over a finite subcover, by the restrictions of a single U-admissible blowup \
of S, each refinement itself an admissible blowup of the local solution"]
public theorem exists_admissibleBlowup_finite_cover_restrict_factors
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    (W : S → S.Opens) (hWmem : ∀ s : S, s ∈ W s)
    (hW : ∀ s : S, IsCompact ((W s : S.Opens) : Set S))
    (V : S → Scheme.{u}) (c : ∀ s : S, V s ⟶ (W s).toScheme)
    (hc : ∀ s : S, Stacks.Blowup.IsAdmissibleBlowup ((W s).ι ⁻¹ᵁ U) (c s)) :
    ∃ (F : Finset S) (S' : Scheme.{u}) (p : S' ⟶ S),
      (∀ x : S, ∃ s ∈ F, x ∈ W s) ∧ Stacks.Blowup.IsAdmissibleBlowup U p ∧
        ∀ s ∈ F, ∃ r : (p ⁻¹ᵁ W s).toScheme ⟶ V s, r ≫ c s = p ∣_ (W s) ∧
          Stacks.Blowup.IsAdmissibleBlowup (c s ⁻¹ᵁ ((W s).ι ⁻¹ᵁ U)) r := by
  classical
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun s : S ↦ ((W s : S.Opens) : Set S))
    (fun s ↦ (W s).2) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hWmem x⟩
  have hcover : ∀ x : S, ∃ s ∈ F, x ∈ W s := by
    intro x
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
    exact ⟨s, hs, hx⟩
  obtain ⟨S', p, hp, hfac⟩ :=
    exists_admissibleBlowup_forall_restrict_factors U hU (fun s : {s : S // s ∈ F} ↦ W s.1)
      (fun s ↦ hW s.1) (fun s ↦ V s.1) (fun s ↦ c s.1) fun s ↦ hc s.1
  exact ⟨F, S', p, hcover, hp, fun s hs ↦ hfac ⟨s, hs⟩⟩

end AlgebraicGeometry

end
