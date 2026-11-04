module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.LocalConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteEtaleCompactification

/-!
# Dévissage of an étale sheaf on an affine scheme along basic locally closed pieces

Let `C` be a ring and `G` an abelian sheaf on the small étale site of `Spec C`. Suppose that
`Spec C` is covered by finitely many *basic locally closed* sets
`V(a₁, …, aₙ) ∩ D(g)` on each of which `G` is constant with finite value
(`Stacks.EtaleCohomology.IsConstantOnSet`). Then `G` lies in every class of sheaves which is
closed under extensions, contains the zero sheaves, and contains every sheaf which vanishes off a
basic locally closed set `V(B) ∩ D(c)` and is constant with finite value on it.

The proof cuts `G` along the short exact sequences `0 → j_! j^{-1} G → G → i_* i^{-1} G → 0`
of the open `D(a)` and the closed `V(a)`, for `a` one of the equations of a piece
(Stacks Tag 095L), and inducts on the total number of equations and pieces: on `D(a)` the piece
disappears, on `V(a)` it loses the equation `a`.

## Main definitions

* `Stacks.EtaleCohomology.cellSet`: the basic locally closed set `V(B) ∩ D(c)`.

## Main results

* `Stacks.EtaleCohomology.prop_of_isConstantOnSet_cover`: a sheaf constant with finite value on
  each of finitely many basic locally closed pieces covering its support lies in every class of
  sheaves containing the zero sheaves and the constant sheaves on basic locally closed sets and
  closed under extensions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {C : Type u} [CommRing C]

/-- The basic locally closed subset `V(B) ∩ D(c)` of `Spec C`. -/
def cellSet (B : List C) (c : C) : Set (Spec (.of C)) :=
  {x | (∀ b ∈ B, b ∈ x.asIdeal) ∧ c ∉ x.asIdeal}

/-- The open immersion of the basic open `D(a)`, as `Spec C[1/a] ⟶ Spec C`. -/
abbrev basicOpenImmersion (a : C) : Spec (.of (Localization.Away a)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a)))

/-- The closed immersion of the zero locus `V(a)`, as `Spec C/(a) ⟶ Spec C`. -/
abbrev zeroLocusImmersion (a : C) : Spec (.of (C ⧸ Ideal.span {a})) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))

/-- The morphism `Spec C/(a) ⟶ Spec C` is a closed immersion. -/
instance (a : C) : IsClosedImmersion (zeroLocusImmersion a) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- A point of `Spec C` lies in the image of `Spec C[1/a]` if and only if `a ∉ 𝔭`. -/
theorem mem_range_basicOpenImmersion (a : C) (x : Spec (.of C)) :
    x ∈ Set.range (basicOpenImmersion a).base ↔ a ∉ x.asIdeal := by
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away a))) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
  rfl

/-- A point of `Spec C` lies in the image of `Spec C/(a)` if and only if `a ∈ 𝔭`. -/
theorem mem_range_zeroLocusImmersion (a : C) (x : Spec (.of C)) :
    x ∈ Set.range (zeroLocusImmersion a).base ↔ a ∈ x.asIdeal := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := Ideal.span {a}))
  rw [Ideal.mk_ker] at h
  change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) ↔ _
  rw [h]
  change Ideal.span {a} ≤ x.asIdeal ↔ _
  rw [Ideal.span_le, Set.singleton_subset_iff]
  rfl

/-- The image of `D(a)` in `Spec C` is the complement of the image of `V(a)`. -/
theorem range_basicOpenImmersion_eq_compl (a : C) :
    Set.range (basicOpenImmersion a).base = (Set.range (zeroLocusImmersion a).base)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, mem_range_basicOpenImmersion, mem_range_zeroLocusImmersion]

/-- The measure of a list of pieces: the number of pieces plus the number of their equations. -/
def piecesMeasure (pieces : List (List C × C × AddCommGrpCat.{u + 1})) : ℕ :=
  (pieces.map fun p => p.1.length + 1).sum

/-- The union of the pieces. -/
def piecesUnion (pieces : List (List C × C × AddCommGrpCat.{u + 1})) : Set (Spec (.of C)) :=
  {x | ∃ p ∈ pieces, x ∈ cellSet p.1 p.2.1}

/-- `V(B) ∩ D(c a) = (V(B) ∩ D(c)) ∩ D(a)`, pointwise. -/
theorem mem_cellSet_mul {B : List C} {c a : C} {x : Spec (.of C)} :
    x ∈ cellSet B (c * a) ↔ x ∈ cellSet B c ∧ a ∉ x.asIdeal := by
  simp only [cellSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hB, hca⟩
    exact ⟨⟨hB, fun hc => hca (x.asIdeal.mul_mem_right a hc)⟩,
      fun ha => hca (x.asIdeal.mul_mem_left c ha)⟩
  · rintro ⟨⟨hB, hc⟩, ha⟩
    exact ⟨hB, fun h => (x.isPrime.mem_or_mem h).elim hc ha⟩

/-- `V(a, B) ∩ D(c) = (V(B) ∩ D(c)) ∩ V(a)`, pointwise. -/
theorem mem_cellSet_cons {B : List C} {c a : C} {x : Spec (.of C)} :
    x ∈ cellSet (a :: B) c ↔ x ∈ cellSet B c ∧ a ∈ x.asIdeal := by
  simp only [cellSet, Set.mem_ofPred_eq, List.mem_cons, forall_eq_or_imp]
  tauto

variable (P : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)

/-- **Dévissage along basic locally closed pieces.** Let `P` be a class of abelian sheaves on
`(Spec C)_étale` which contains the zero sheaves, is closed under extensions, and contains every
sheaf which vanishes off a basic locally closed set `V(B) ∩ D(c)` and is constant there with
finite value. Let `G` be a sheaf, and let `V(B) ∩ D(c)` be a basic locally closed set together
with finitely many pieces `V(Lₖ) ∩ D(gₖ)` such that `G` is constant with finite value on the
intersection of each piece with `V(B) ∩ D(c)` and vanishes off the part of `V(B) ∩ D(c)` they
cover. Then `G` belongs to `P`. -/
theorem prop_of_isConstantOnSet_cover
    (hzero : ∀ H, IsZero H → P H)
    (hext : ∀ S : ShortComplex (Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hbase : ∀ (B : List C) (c : C) (E : AddCommGrpCat.{u + 1}) [Finite E] (H),
      VanishesOffSet H (cellSet B c) → IsConstantOnSet H (cellSet B c) E → P H)
    (n : ℕ) :
    ∀ (pieces : List (List C × C × AddCommGrpCat.{u + 1})), piecesMeasure pieces ≤ n →
      ∀ (B : List C) (c : C) (G : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ p ∈ pieces, Finite p.2.2 ∧
        IsConstantOnSet G (cellSet B c ∩ cellSet p.1 p.2.1) p.2.2) →
      VanishesOffSet G (cellSet B c ∩ piecesUnion pieces) → P G := by
  induction n with
  | zero =>
    intro pieces hn B c G _ hvan
    have hp : pieces = [] := by
      cases pieces with
      | nil => rfl
      | cons p rest => simp [piecesMeasure] at hn
    subst hp
    refine hzero G ?_
    have h := hvan (𝟙 (Spec (.of C))) (by
      rw [Set.disjoint_right]
      rintro x ⟨-, p, hp, -⟩
      exact absurd hp (List.not_mem_nil))
    exact h.of_iso ((etaleAbelianInverseImageIdIso _).app G).symm
  | succ n ih =>
    intro pieces hn B c G hconst hvan
    rcases pieces with _ | ⟨⟨L, g, E⟩, rest⟩
    · exact ih [] (by simp [piecesMeasure]) B c G hconst hvan
    have hrest : piecesMeasure rest + (L.length + 1) = piecesMeasure ((L, g, E) :: rest) := by
      simp [piecesMeasure, add_comm]
    obtain ⟨hfin, hconst₁⟩ := hconst (L, g, E) List.mem_cons_self
    have hconstrest : ∀ p ∈ rest, Finite p.2.2 ∧
        IsConstantOnSet G (cellSet B c ∩ cellSet p.1 p.2.1) p.2.2 :=
      fun p hp => hconst p (List.mem_cons_of_mem _ hp)
    -- the sequence along an element `a`, with the transfer of constancy and vanishing
    have hseq : ∀ a : C, ∃ S : ShortComplex
        (Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}), S.ShortExact ∧
        S.X₂ = G ∧
        (∀ {B c T E}, IsConstantOnSet G (cellSet B c ∩ T) E →
          IsConstantOnSet S.X₁ (cellSet B (c * a) ∩ T) E) ∧
        (∀ {B c T}, VanishesOffSet G (cellSet B c ∩ T) →
          VanishesOffSet S.X₁ (cellSet B (c * a) ∩ T)) ∧
        (∀ {B c T E}, IsConstantOnSet G (cellSet B c ∩ T) E →
          IsConstantOnSet S.X₃ (cellSet (a :: B) c ∩ T) E) ∧
        (∀ {B c T}, VanishesOffSet G (cellSet B c ∩ T) →
          VanishesOffSet S.X₃ (cellSet (a :: B) c ∩ T)) := by
      intro a
      obtain ⟨h, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0}
        (zeroLocusImmersion a) (basicOpenImmersion a) (range_basicOpenImmersion_eq_compl a) G
      refine ⟨_, hS, rfl, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · exact (IsConstantOnSet.extensionByZero (basicOpenImmersion a) G h).mono
          fun x ⟨hx, hT⟩ => let ⟨hx, ha⟩ := mem_cellSet_mul.mp hx
            ⟨⟨hx, hT⟩, (mem_range_basicOpenImmersion a x).mpr ha⟩
      · exact (VanishesOffSet.extensionByZero (basicOpenImmersion a) G h).mono
          fun x ⟨⟨hx, hT⟩, ha⟩ =>
            ⟨mem_cellSet_mul.mpr ⟨hx, (mem_range_basicOpenImmersion a x).mp ha⟩, hT⟩
      · exact (IsConstantOnSet.directImage (zeroLocusImmersion a) G h).mono
          fun x ⟨hx, hT⟩ => let ⟨hx, ha⟩ := mem_cellSet_cons.mp hx
            ⟨⟨hx, hT⟩, (mem_range_zeroLocusImmersion a x).mpr ha⟩
      · exact (VanishesOffSet.directImage (zeroLocusImmersion a) G h).mono
          fun x ⟨⟨hx, hT⟩, ha⟩ =>
            ⟨mem_cellSet_cons.mpr ⟨hx, (mem_range_zeroLocusImmersion a x).mp ha⟩, hT⟩
    rcases L with _ | ⟨a, L'⟩
    · -- a piece without equations: split along its open `D(g)`
      obtain ⟨S, hS, h₂, hc₁, hv₁, hc₃, hv₃⟩ := hseq g
      rw [← h₂]
      refine hext S hS ?_ ?_
      · have := hfin
        exact hbase B (c * g) E _ ((hv₁ hvan).mono Set.inter_subset_left)
          ((hc₁ hconst₁).mono fun x hx => ⟨hx, by simp, (mem_cellSet_mul.mp hx).2⟩)
      · refine ih rest (by simp [piecesMeasure] at hn ⊢; omega) (g :: B) c _
          (fun p hp => ⟨(hconstrest p hp).1, hc₃ (hconstrest p hp).2⟩) ?_
        refine (hv₃ hvan).mono ?_
        rintro x ⟨hx, p, hp, hxp⟩
        refine ⟨hx, p, ?_, hxp⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact absurd (mem_cellSet_cons.mp hx).2 hxp.2
        · exact hp
    · -- a piece with an equation `a`: split along `D(a)` and `V(a)`
      obtain ⟨S, hS, h₂, hc₁, hv₁, hc₃, hv₃⟩ := hseq a
      rw [← h₂]
      refine hext S hS ?_ ?_
      · refine ih rest (by simp [piecesMeasure] at hn ⊢; omega) B (c * a) _
          (fun p hp => ⟨(hconstrest p hp).1, hc₁ (hconstrest p hp).2⟩) ?_
        refine (hv₁ hvan).mono ?_
        rintro x ⟨hx, p, hp, hxp⟩
        refine ⟨hx, p, ?_, hxp⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact absurd (hxp.1 a List.mem_cons_self) (mem_cellSet_mul.mp hx).2
        · exact hp
      · refine ih ((L', g, E) :: rest) (by simp [piecesMeasure] at hn ⊢; omega) (a :: B) c _ ?_
          ((hv₃ hvan).mono ?_)
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · refine ⟨hfin, (hc₃ hconst₁).mono ?_⟩
            rintro x ⟨hx, hxL, hxg⟩
            exact ⟨hx, fun b hb => (List.mem_cons.mp hb).elim (· ▸ (mem_cellSet_cons.mp hx).2)
              (hxL b), hxg⟩
          · exact ⟨(hconstrest p hp).1, hc₃ (hconstrest p hp).2⟩
        · rintro x ⟨hx, p, hp, hxp⟩
          refine ⟨hx, ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨(L', g, E), List.mem_cons_self,
              fun b hb => hxp.1 b (List.mem_cons_of_mem _ hb), hxp.2⟩
          · exact ⟨p, List.mem_cons_of_mem _ hp, hxp⟩

end Stacks.EtaleCohomology
