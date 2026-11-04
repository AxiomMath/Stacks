module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ConnectednessApplication
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeProof

/-!
# Mixed components of the closed fibre of a closure, and the crossing point they produce

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, with `X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)`, and
let `x ∈ X` be a point with closure `W = V(𝔭_x)`. The closed fibre `W ∩ Y` of `W` is the zero
locus of `I(A/𝔭_x)` in `W = Spec(A/𝔭_x)`, and its intersection with `Z` is the zero locus of
`𝔞(A/𝔭_x)`. Suppose some irreducible component of `W ∩ Y` lies inside `Z` and some does not.
Writing `W ∩ Y = W_1 ∪ … ∪ W_n` with `W_1, …, W_m ⊆ Z` and `W_{m+1}, …, W_n ⊄ Z`, the set

`W ∩ Y ∖ ((W_1 ∪ … ∪ W_m) ∩ (W_{m+1} ∪ … ∪ W_n))`

is disconnected, so [Stacks, Tag 0EG5] applied to `A/𝔭_x` cannot have its dimension hypothesis;
that failure is a point `z` of `W ∩ Y ∩ Z` with `dim(𝒪_{W, z}) ≤ cd(A, I) + 1 ≤ d + 1`, lying on
a component of `W ∩ Y` not contained in `Z`, whose generic point `η` therefore specializes to `z`
and avoids `Z`. This is the first half of the proof of [Stacks, Tag 0EJ5].

## Main results

* `Stacks.Algebraization.exists_closed_cover_of_mixed_irreducibleComponents` — mixed components
  split a space into two closed pieces whose union is everything, the first inside the
  distinguished set, and removing their intersection disconnects it.
* `Stacks.Algebraization.exists_specializes_krullDimToEInt_le_of_mixed_irreducibleComponents` —
  the crossing point `z ∈ W ∩ Y ∩ Z` with `dim(𝒪_{W, z}) ≤ d + 1`, together with a point
  `η ⤳ z` of `W ∩ Y ∖ Z`.

## Implementation notes

### Why `A/𝔭_x` and not `A`

[Stacks, Tag 0EG5] needs its hypothesis (3) — every nonempty open containing `V(I) ∖ V(𝔞)` is
connected — and over `A/𝔭_x` that is free: the ring is a domain, so its spectrum is irreducible
and *every* nonempty open is connected. That is the whole reason the lemma is applied to the
quotient rather than to `A`. The two other inputs are supplied here rather than assumed: the
dualizing complex of `A/𝔭_x` comes from `Stacks.Algebraization.exists_isDualizingComplex_quotient`
(Stacks 0A7K for a quotient), and `I`-adic completeness from
`Stacks.Algebraization.isAdicComplete_map_quotient`. The bound `cd(A/𝔭_x, I(A/𝔭_x)) ≤ cd(A, I)`
is `Stacks.LocalCohomology.cohomologicalDimension_map_le` (Stacks 0DXA).

Because `A/𝔭_x` is a domain its only minimal prime is `⊥`, so hypothesis (2) of
[Stacks, Tag 0EG5] reads `dim((A/𝔭_x)_𝔮) > cd + 1` for every `𝔮` in the closed set being
removed; the contrapositive of the lemma is therefore exactly the existence of one `𝔮` there
with `dim((A/𝔭_x)_𝔮) ≤ cd + 1`, which is the crossing point. The quotient `(A/𝔭_x)_𝔮/⊥` of
hypothesis (2) is identified with `(A/𝔭_x)_𝔮` by `RingEquiv.quotientBot`.

### The closed fibre as a subspace of `Spec(A/𝔭_x)`

`W ∩ Y` is `PrimeSpectrum.zeroLocus (I(A/𝔭_x))` and its components are taken in that subspace;
the two closed pieces the components produce are pushed forward along the inclusion of the
subspace, which is a closed embedding because the zero locus is closed, so they are closed in
`Spec(A/𝔭_x)` and [Stacks, Tag 0EG5] can be applied with them. No homeomorphism with a subspace
of `Y` is needed: the closed fibre is read inside `W` throughout.

### The dimension bound lives in the extended integers

[Stacks, Tag 0EG5] compares `cd(A, I) + 1` with a Krull dimension in
`Stacks.Algebraization.EInt` through `Stacks.Algebraization.krullDimToEInt`, and the conclusion
here is the negation of that comparison, so it is stated in `EInt` as well. This needs no
truncation of `d + 1` to a natural number and is the form in which
`Stacks.Algebraization.one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities` consumes
dimension bounds.

### No `@[stacks 0EJ5]` attribute

What is proved here is one of the three inputs of [Stacks, Tag 0EJ5]: the passage from mixed
components on the closed fibre to a crossing point of low local dimension. The tag also needs
the immediate specialization of [Stacks, Tag 02IM] below that point and the identification of
`depth(ℱ_x)` with a depth of the completed stalk by [Stacks, Tag 0338] and
[Stacks, Tag 0EHW]. Neither is here, so no attribute for 0EJ5 (nor for 0EJ6, 0EJ7, 0EJ8, which
consume it) is placed.

## References

* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), whose first half this
  is.
* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5), the connectedness
  lemma applied to `A/𝔭_x`.
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K), the dualizing complex
  of the quotient.
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA), the cohomological
  dimension of the extended ideal.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Mixed irreducible components give a disconnection -/

/-- A space covered by two closed sets, each of which has a point outside the other, is
disconnected after the intersection of the two is removed: the two closed sets still cover what
is left, each still meets it, and they no longer meet each other there. -/
private lemma not_isConnected_sdiff_inter_of_union_eq_univ
    {T : Type*} [TopologicalSpace T] (F G : Set T) (hF : IsClosed F) (hG : IsClosed G)
    (hcover : F ∪ G = Set.univ) (hneF : (F \ G).Nonempty) (hneG : (G \ F).Nonempty) :
    ¬ _root_.IsConnected (Set.univ \ (F ∩ G)) := by
  intro hconn
  have hcover' : Set.univ \ (F ∩ G) ⊆ F ∪ G := by simp [hcover]
  have hmeetF : ((Set.univ \ (F ∩ G)) ∩ F).Nonempty := by
    obtain ⟨t, htF, htG⟩ := hneF
    exact ⟨t, ⟨Set.mem_univ t, fun ht => htG ht.2⟩, htF⟩
  have hmeetG : ((Set.univ \ (F ∩ G)) ∩ G).Nonempty := by
    obtain ⟨t, htG, htF⟩ := hneG
    exact ⟨t, ⟨Set.mem_univ t, fun ht => htF ht.1⟩, htG⟩
  obtain ⟨t, htS, htFG⟩ :=
    (isPreconnected_closed_iff.mp hconn.2) F G hF hG hcover' hmeetF hmeetG
  exact htS.2 htFG

/-- **The disconnection produced by mixed irreducible components.** Let `W` be a space with
finitely many irreducible components and let `Zc ⊆ W` be a subset such that some component is
contained in `Zc` and some component is not. Then the union `F` of the components inside `Zc`
and the union `G` of those outside are closed and cover `W`, `F` is contained in `Zc`, every
point of `G` lies on a component not contained in `Zc`, each of `F`, `G` has a point outside the
other, and `W ∖ (F ∩ G)` is disconnected.

This is the step "`W ∩ Y = W_1 ∪ … ∪ W_n` with `W_1, …, W_m ⊆ Z` and `W_{m+1}, …, W_n ⊄ Z`, so
`W ∩ Y ∖ ((W_1 ∪ … ∪ W_m) ∩ (W_{m+1} ∪ … ∪ W_n))` is disconnected" of the proof of
[Stacks, Tag 0EJ5]; the renumbering of the source is the partition of the (finite) set of
components according to whether they lie in `Zc`. -/
public theorem exists_closed_cover_of_mixed_irreducibleComponents
    {W : Type*} [TopologicalSpace W] (Zc : Set W) (hfin : (irreducibleComponents W).Finite)
    (hin : ∃ C, C ∈ irreducibleComponents W ∧ C ⊆ Zc)
    (hout : ∃ C, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Zc) :
    ∃ F G : Set W, IsClosed F ∧ IsClosed G ∧ F ∪ G = Set.univ ∧ F ⊆ Zc ∧
      (∀ t ∈ G, ∃ C, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Zc ∧ t ∈ C) ∧
      (F \ G).Nonempty ∧ (G \ F).Nonempty ∧
      ¬ _root_.IsConnected (Set.univ \ (F ∩ G)) := by
  classical
  let inside : Set (Set W) := {C | C ∈ irreducibleComponents W ∧ C ⊆ Zc}
  let outside : Set (Set W) := {C | C ∈ irreducibleComponents W ∧ ¬ C ⊆ Zc}
  have hinsub : inside ⊆ irreducibleComponents W := fun _ h => h.1
  have houtsub : outside ⊆ irreducibleComponents W := fun _ h => h.1
  have hinfin : inside.Finite := hfin.subset hinsub
  have houtfin : outside.Finite := hfin.subset houtsub
  have hFclosed : IsClosed (⋃₀ inside) := hinfin.isClosed_sUnion fun C hC =>
    isClosed_of_mem_irreducibleComponents C (hinsub hC)
  have hGclosed : IsClosed (⋃₀ outside) := houtfin.isClosed_sUnion fun C hC =>
    isClosed_of_mem_irreducibleComponents C (houtsub hC)
  have hcover : ⋃₀ inside ∪ ⋃₀ outside = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun t => ?_
    have htcomp : t ∈ ⋃₀ irreducibleComponents W := by simp [sUnion_irreducibleComponents]
    obtain ⟨C, hC, htC⟩ := Set.mem_sUnion.mp htcomp
    by_cases hCZ : C ⊆ Zc
    · exact Or.inl (Set.mem_sUnion.mpr ⟨C, ⟨hC, hCZ⟩, htC⟩)
    · exact Or.inr (Set.mem_sUnion.mpr ⟨C, ⟨hC, hCZ⟩, htC⟩)
  have hne : ∀ S T : Set (Set W), T.Finite → T ⊆ irreducibleComponents W →
      ∀ C ∈ S, C ∈ irreducibleComponents W → C ∉ T → (⋃₀ S \ ⋃₀ T).Nonempty := by
    intro S T hT hTsub C hCS hC hCT
    obtain ⟨t, htC, htT⟩ := Set.not_subset.mp fun hsub =>
      hCT (mem_of_subset_sUnion_irreducibleComponents C hC T hT hTsub hsub)
    exact ⟨t, Set.mem_sUnion.mpr ⟨C, hCS, htC⟩, htT⟩
  have hneF : (⋃₀ inside \ ⋃₀ outside).Nonempty := by
    obtain ⟨C, hC, hCZ⟩ := hin
    exact hne _ _ houtfin houtsub C ⟨hC, hCZ⟩ hC fun h => h.2 hCZ
  have hneG : (⋃₀ outside \ ⋃₀ inside).Nonempty := by
    obtain ⟨C, hC, hCZ⟩ := hout
    exact hne _ _ hinfin hinsub C ⟨hC, hCZ⟩ hC fun h => hCZ h.2
  refine ⟨⋃₀ inside, ⋃₀ outside, hFclosed, hGclosed, hcover, ?_, ?_, hneF, hneG,
    not_isConnected_sdiff_inter_of_union_eq_univ _ _ hFclosed hGclosed hcover hneF hneG⟩
  · intro t ht
    obtain ⟨C, hC, htC⟩ := Set.mem_sUnion.mp ht
    exact hC.2 htC
  · intro t ht
    obtain ⟨C, hC, htC⟩ := Set.mem_sUnion.mp ht
    exact ⟨C, hC.1, hC.2, htC⟩

/-! ### The crossing point over a domain -/

/-- The quotient of a localization by the extension of `⊥` has the Krull dimension of the
localization: `⊥` extends to `⊥`, and `R/⊥ ≃+* R`. -/
private lemma ringKrullDim_localization_quotient_map_bot {B : Type u} [CommRing B]
    (q : PrimeSpectrum B) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        (⊥ : Ideal B).map (algebraMap B (Localization.AtPrime q.asIdeal))) =
      ringKrullDim (Localization.AtPrime q.asIdeal) := by
  rw [Ideal.map_bot]
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)

/-- **The crossing point of two closed sets on the closed fibre of a complete domain.** Let `B`
be a Noetherian domain, `I`-adically complete with a dualizing complex, and let `F`, `G` be
closed subsets of `Spec(B)` such that `V(I)` meets `F ∖ G` and `V(I) ∖ (F ∩ G)` is disconnected.
Then some `𝔮 ∈ V(I) ∩ F ∩ G` has `dim(B_𝔮) ≤ cd(B, I) + 1`.

This is the contrapositive of [Stacks, Tag 0EG5] for the ideal `𝔞` cutting out
`V(I) ∩ F ∩ G`: hypothesis (3) of that lemma holds because `Spec(B)` is irreducible, and
hypothesis (2) — which over a domain only concerns the minimal prime `⊥` — is precisely the
negation of the conclusion here, so its failure is forced by the disconnection. -/
private lemma exists_mem_inter_krullDimToEInt_le {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] (I : Ideal B) [IsAdicComplete I B]
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : Dualizing.IsDualizingComplex K)
    (F G : Set (PrimeSpectrum B)) (hF : IsClosed F) (hG : IsClosed G)
    (hmeetF : (PrimeSpectrum.zeroLocus (I : Set B) ∩ (F \ G)).Nonempty)
    (hdisc : ¬ _root_.IsConnected (PrimeSpectrum.zeroLocus (I : Set B) \ (F ∩ G))) :
    ∃ q : PrimeSpectrum B, q ∈ PrimeSpectrum.zeroLocus (I : Set B) ∩ F ∩ G ∧
      krullDimToEInt (ringKrullDim (Localization.AtPrime q.asIdeal)) ≤
        ((cohomologicalDimension B I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) := by
  classical
  set C : Set (PrimeSpectrum B) := PrimeSpectrum.zeroLocus (I : Set B) ∩ F ∩ G with hC
  have hCclosed : IsClosed C := ((PrimeSpectrum.isClosed_zeroLocus _).inter hF).inter hG
  set b : Ideal B := PrimeSpectrum.vanishingIdeal C with hb
  have hbC : PrimeSpectrum.zeroLocus (b : Set B) = C := by
    rw [hb, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hCclosed.closure_eq]
  have hIb : I ≤ b := by
    intro r hr
    rw [hb, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hq.1.1 hr
  have hne : (PrimeSpectrum.zeroLocus (I : Set B) \
      PrimeSpectrum.zeroLocus (b : Set B)).Nonempty := by
    obtain ⟨q, hqI, hqF, hqG⟩ := hmeetF
    exact ⟨q, hqI, fun hqb => hqG (hbC.subset hqb).2⟩
  have hsdiff : PrimeSpectrum.zeroLocus (I : Set B) \ PrimeSpectrum.zeroLocus (b : Set B) =
      PrimeSpectrum.zeroLocus (I : Set B) \ (F ∩ G) := by
    ext q
    rw [hbC, hC]
    exact ⟨fun h => ⟨h.1, fun hFG => h.2 ⟨⟨h.1, hFG.1⟩, hFG.2⟩⟩,
      fun h => ⟨h.1, fun hq => h.2 ⟨hq.1.2, hq.2⟩⟩⟩
  by_contra! hcon
  have hdim : ∀ p q : PrimeSpectrum B, p.asIdeal ∈ minimalPrimes B → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → b ≤ q.asIdeal →
      ((cohomologicalDimension B I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap B (Localization.AtPrime q.asIdeal)))) := by
    intro p q hp _ _ hbq
    have hpbot : p.asIdeal = ⊥ := le_bot_iff.mp (hp.2 ⟨inferInstance, bot_le⟩ bot_le)
    rw [hpbot, ringKrullDim_localization_quotient_map_bot]
    exact hcon q (hbC.subset ((PrimeSpectrum.mem_zeroLocus _ _).mpr hbq))
  have hconn : ∀ V : Set (PrimeSpectrum B), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set B) \ PrimeSpectrum.zeroLocus (b : Set B) ⊆ V →
      _root_.IsConnected V := fun V hV hVne _ =>
    ⟨hVne, (PrimeSpectrum.irreducibleSpace.isPreirreducible_univ.open_subset hV
      (Set.subset_univ V)).isPreconnected⟩
  rcases eq_empty_or_isConnected_zeroLocus_sdiff B I b hIb K hK hdim hconn
    ⟨serreOneAlternativeComparison⟩ with
    hempty | hconn'
  · exact hne.ne_empty hempty
  · rw [hsdiff] at hconn'
    exact hdisc hconn'

/-! ### The crossing point on the closed fibre of a closure -/

/-- **Stacks 0EJ5, the passage from mixed components on the closed fibre to a crossing point of
low local dimension.** Let `I` and `𝔞` be ideals of a Noetherian ring `A` which is `I`-adically
complete and has a dualizing complex with `cd(A, I) ≤ d`, and let `𝔭` be a prime of `A`, so that
`W = V(𝔭) = Spec(A/𝔭)` is the closure of the corresponding point of `Spec(A)`. The closed fibre
`W ∩ Y` is the zero locus of `I(A/𝔭)` in `W` and `W ∩ Y ∩ Z` is cut out there by `𝔞(A/𝔭)`. If
some irreducible component of `W ∩ Y` lies in `Z` and some does not, then there are points
`η ⤳ z` of `W ∩ Y` with `z ∈ Z`, `η ∉ Z` and `dim(𝒪_{W, z}) ≤ d + 1`.

The components inside `Z` and those outside give two closed sets covering `W ∩ Y` whose
intersection, when removed, disconnects it
(`Stacks.Algebraization.exists_closed_cover_of_mixed_irreducibleComponents`). Applied over the
domain `A/𝔭` — which is where [Stacks, Tag 0EG5] has its connectedness hypothesis for free, and
which inherits adic completeness and a dualizing complex — that disconnection contradicts the
dimension hypothesis of [Stacks, Tag 0EG5], and the point at which it fails is `z`. The source's
`z ∈ W_i ∩ W_j` with `W_i ⊆ Z` and `W_j ⊄ Z` is recorded as `z ∈ Z` together with the generic
point `η` of `W_j`: it specializes to `z` and avoids `Z` because `W_j` does, which is the point
below which [Stacks, Tag 02IM] is applied next.

The standing inclusion `I ⊆ 𝔞` of the situation is not a hypothesis: the ideal cutting out the
closed set that [Stacks, Tag 0EG5] removes is the vanishing ideal of `W ∩ Y ∩ F ∩ G`, which
contains `I(A/𝔭)` by construction, so the inclusion is never used. -/
public theorem exists_specializes_krullDimToEInt_le_of_mixed_irreducibleComponents
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    [IsAdicComplete I A] (p : Ideal A) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (d : ℤ) (hcd : cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hmixed :
      let W : Set (PrimeSpectrum (A ⧸ p)) :=
        PrimeSpectrum.zeroLocus ((I.map (Ideal.Quotient.mk p) : Ideal (A ⧸ p)) : Set (A ⧸ p))
      let Zc : Set W := {w | a.map (Ideal.Quotient.mk p) ≤ w.1.asIdeal}
      (∃ C, C ∈ irreducibleComponents W ∧ C ⊆ Zc) ∧
        ∃ C, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Zc) :
    ∃ z η : PrimeSpectrum (A ⧸ p),
      I.map (Ideal.Quotient.mk p) ≤ η.asIdeal ∧
      ¬ a.map (Ideal.Quotient.mk p) ≤ η.asIdeal ∧
      η.asIdeal ≤ z.asIdeal ∧ a.map (Ideal.Quotient.mk p) ≤ z.asIdeal ∧
      krullDimToEInt (ringKrullDim (Localization.AtPrime z.asIdeal)) ≤
        ((d + 1 : ℤ) : EInt) := by
  classical
  dsimp only at hmixed
  set B := A ⧸ p
  set Ibar : Ideal B := I.map (Ideal.Quotient.mk p) with hIbar
  set abar : Ideal B := a.map (Ideal.Quotient.mk p)
  set V : Set (PrimeSpectrum B) := PrimeSpectrum.zeroLocus (Ibar : Set B)
  have hVclosed : IsClosed V := PrimeSpectrum.isClosed_zeroLocus _
  have : IsAdicComplete Ibar B := by
    rw [hIbar, ← Ideal.Quotient.algebraMap_eq]
    exact isAdicComplete_map_quotient A I p
  obtain ⟨Kbar, hKbar⟩ := exists_isDualizingComplex_quotient A p K hK
  have hfin : (irreducibleComponents V).Finite := NoetherianSpace.finite_irreducibleComponents
  obtain ⟨F₀, G₀, hF₀, hG₀, hcover, hF₀Z, hG₀cover, hneF₀, hneG₀, hdisc₀⟩ :=
    exists_closed_cover_of_mixed_irreducibleComponents
      (W := V) {w | abar ≤ w.1.asIdeal} hfin hmixed.1 hmixed.2
  set Fset : Set (PrimeSpectrum B) := Subtype.val '' F₀
  set Gset : Set (PrimeSpectrum B) := Subtype.val '' G₀
  have hFmem (w : V) : w.1 ∈ Fset ↔ w ∈ F₀ := Subtype.val_injective.mem_set_image
  have hGmem (w : V) : w.1 ∈ Gset ↔ w ∈ G₀ := Subtype.val_injective.mem_set_image
  have hF : IsClosed Fset :=
    hVclosed.isClosedEmbedding_subtypeVal.isClosedMap F₀ hF₀
  have hG : IsClosed Gset :=
    hVclosed.isClosedEmbedding_subtypeVal.isClosedMap G₀ hG₀
  have hmeetF : (V ∩ (Fset \ Gset)).Nonempty := by
    obtain ⟨w, hwF, hwG⟩ := hneF₀
    exact ⟨w.1, w.2, (hFmem w).mpr hwF, fun hw => hwG ((hGmem w).mp hw)⟩
  have himage : Subtype.val '' ((Set.univ : Set V) \ (F₀ ∩ G₀)) = V \ (Fset ∩ Gset) := by
    ext q
    refine ⟨fun ⟨w, hw, heq⟩ => heq ▸ ⟨w.2, fun hq =>
      hw.2 ⟨(hFmem w).mp (heq ▸ hq.1), (hGmem w).mp (heq ▸ hq.2)⟩⟩, fun hq => ?_⟩
    refine ⟨⟨q, hq.1⟩, ⟨Set.mem_univ _, fun hw => hq.2 ⟨(hFmem ⟨q, hq.1⟩).mpr hw.1,
      (hGmem ⟨q, hq.1⟩).mpr hw.2⟩⟩, rfl⟩
  have hdisc : ¬ _root_.IsConnected (V \ (Fset ∩ Gset)) := by
    intro hc
    refine hdisc₀ ⟨?_, ?_⟩
    · obtain ⟨q, hqV, hqFG⟩ := hc.1
      exact ⟨⟨q, hqV⟩, Set.mem_univ _, fun hw =>
        hqFG ⟨(hFmem ⟨q, hqV⟩).mpr hw.1, (hGmem ⟨q, hqV⟩).mpr hw.2⟩⟩
    · refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
      rw [himage]
      exact hc.2
  obtain ⟨z, hz, hzdim⟩ :=
    exists_mem_inter_krullDimToEInt_le Ibar Kbar hKbar Fset Gset hF hG hmeetF hdisc
  set zV : V := ⟨z, hz.1.1⟩
  obtain ⟨C, hC, hCZ, hzC⟩ := hG₀cover zV ((hGmem zV).mp hz.2)
  have : QuasiSober V := hVclosed.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  have hZclosed : IsClosed {w : V | abar ≤ w.1.asIdeal} :=
    (PrimeSpectrum.isClosed_zeroLocus (abar : Set B)).preimage continuous_subtype_val
  have hηZ : ¬ abar ≤ η.1.asIdeal := fun hmem =>
    hCZ ((hη.mem_closed_set_iff hZclosed).mp hmem)
  have hηz : η.1.asIdeal ≤ zV.1.asIdeal :=
    (PrimeSpectrum.le_iff_specializes η.1 zV.1).mpr
      ((hη.specializes hzC).map continuous_subtype_val)
  refine ⟨z, η.1, (PrimeSpectrum.mem_zeroLocus _ _).mp η.2, hηZ, hηz,
    hF₀Z ((hFmem zV).mp hz.1.2), hzdim.trans ?_⟩
  have hcdB : cohomologicalDimension B Ibar Ibar.fg_of_isNoetherianRing ≤ d :=
    (cohomologicalDimension_map_le (Ideal.Quotient.mk p) I I.fg_of_isNoetherianRing).trans hcd
  simp only [WithBotTop.coe_le_coe]
  omega

end Stacks.Algebraization

end
