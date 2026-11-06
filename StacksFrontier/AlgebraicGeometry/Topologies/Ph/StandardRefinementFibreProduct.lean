module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre-product step in a standard ph refinement of a composite covering

Stacks 0DBF part (2) asserts that a composite of two standard ph coverings of an affine scheme
`T` has a refinement by a standard ph covering. Writing `g : U ⟶ T` for the proper surjection
presenting the first covering and `U = ⋃_j U_j` for its affine open covering, the Stacks proof
proceeds in two stages:

1. each proper surjection `W_j ⟶ U_j` presenting the second stage over `U_j` is replaced by a
   morphism that is proper over the *whole* of `U` and whose part over `U_j` is still `W_j`;
2. the resulting proper surjections `V_j ⟶ U` are multiplied together over `U`, and the product
   is covered by the affine opens obtained by putting a member of the second covering in one
   factor and an arbitrary affine open in the others.

Stage 1 is where Chow's lemma (Stacks 0202) enters, and Chow's lemma is not available in this
development; see `AlgebraicGeometry.HasChowModification` in
`StacksFrontier.AlgebraicGeometry.Limits.ChowLemma`. **This file proves stage 2**, which needs no
input from Chow's lemma, and derives from it the whole of Stacks 0DBF part (2) with stage 1 as
an explicit hypothesis.

The two cases of part (2) which need no compactification at all are in
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementBind` and
`StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct`.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpens_subset_of_isCompact`: a quasi-compact open of a
  scheme is covered by finitely many affine opens contained in it.
* `AlgebraicGeometry.isAffine_pullback_of_factorsThrough`: a fibre product of two affine schemes
  over a scheme is affine as soon as both structure morphisms factor through one affine
  subobject of the base.
* `AlgebraicGeometry.exists_finite_affine_cover_preimage_pullback_fst` and
  `AlgebraicGeometry.exists_finite_affine_cover_preimage_pullback_snd`: the preimage, under a
  projection of a fibre product over `U`, of an affine open lying over an affine open of `U` is
  covered by finitely many affine opens of the fibre product, each mapping to that affine open.
* `AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_properOver`: **stage 2**. Given a
  finite affine open covering `{U_j}` of `U` and, for each `j`, a proper surjection `V_j ⟶ U`
  whose part over `U_j` is covered by affine opens mapping into a fixed family `Z` of schemes
  over the `U_j`, the fibre product of the `V_j` over `U` is proper and surjective over `U` and
  is covered by finitely many affine opens, each mapping into a member of `Z`.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_extension`: Stacks 0DBF
  part (2), with stage 1 as a hypothesis.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_openCover`: the case of Stacks
  0DBF part (2) in which the second stage consists of Zariski open coverings, which needs
  neither stage above and is therefore proved outright.

## Implementation notes

The families produced here are indexed by `Fin n` or by a finite type in the universe of the
schemes; the index type of the covering asked for by Stacks 0DBF part (2) lives in a prescribed
universe, so the last step reindexes a finite type into it through `ULift (Fin n)`, exactly as
`AlgebraicGeometry.exists_finite_affine_refinement` does for part (1).

Stage 2 is proved by induction on the finite set of indices `j` whose opens `U_j` have already
been accounted for, multiplying in one new factor `V_j` at a time; only binary fibre products
occur, so no wide pullbacks are needed. Each induction step refines the affine opens already in
hand along the new factor, and the given affine opens of the new factor along the product
already built — the two symmetric halves of the step being the two lemmas
`exists_finite_affine_cover_preimage_pullback_fst` and `..._snd`.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A quasi-compact open of a scheme is covered by finitely many affine opens contained in it.
The affine opens form a basis of the topology, so the quasi-compact open is covered by the
affine opens it contains, and quasi-compactness extracts a finite subcover. -/
@[ega "IV 1.8.1" "partial"]
theorem exists_finite_affineOpens_subset_of_isCompact {X : Scheme.{u}} (O : X.Opens)
    (hO : IsCompact (O : Set X)) :
    ∃ (n : ℕ) (W : Fin n → X.Opens), (∀ l, IsAffineOpen (W l)) ∧ (∀ l, W l ≤ O) ∧
      (O : Set X) ⊆ ⋃ l, (W l : Set X) := by
  classical
  have hcov : (O : Set X) ⊆ ⋃ W ∈ {W : X.Opens | IsAffineOpen W ∧ W ≤ O}, (W : Set X) := by
    intro x hx
    obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset (U := O) (x := x) hx
    exact Set.mem_biUnion (⟨hW, hWO⟩ : W ∈ {W : X.Opens | IsAffineOpen W ∧ W ≤ O}) hxW
  obtain ⟨b, hb, hbfin, hbcov⟩ := hO.elim_finite_subcover_image
    (fun W (_ : W ∈ {W : X.Opens | IsAffineOpen W ∧ W ≤ O}) => W.isOpen) hcov
  have : Finite b := hbfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  refine ⟨n, fun l => ((e.symm l : b) : X.Opens), fun l => (hb (e.symm l).2).1,
    fun l => (hb (e.symm l).2).2, hbcov.trans ?_⟩
  rw [Set.biUnion_eq_iUnion]
  exact (e.symm.surjective.iUnion_comp fun W : b => ((W : X.Opens) : Set X)).ge

/-- A fibre product of two affine schemes over a scheme `U` is affine as soon as both structure
morphisms factor through one affine subobject `Uj ⟶ U`: the fibre product over `U` is then the
fibre product over `Uj`, because `Uj ⟶ U` is a monomorphism. -/
theorem isAffine_pullback_of_factorsThrough {U Uj A B : Scheme.{u}} {uj : Uj ⟶ U} [Mono uj]
    [IsAffine Uj] [IsAffine A] [IsAffine B] {f : A ⟶ U} {g : B ⟶ U} (a : A ⟶ Uj) (b : B ⟶ Uj)
    (ha : f = a ≫ uj) (hb : g = b ≫ uj) : IsAffine (pullback f g) := by
  subst ha hb
  have e := (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a b uj)).isoPullback
  have h : IsAffine (pullback a b) := inferInstance
  exact @IsAffine.of_isIso _ _ e.inv inferInstance h

/-- The two projections of a fibre product have the same image in the base. -/
private theorem apply_fst_eq_apply_snd {U V V' : Scheme.{u}} (ϖ : V ⟶ U) (π : V' ⟶ U)
    (x : (pullback ϖ π : Scheme.{u})) : ϖ (pullback.fst ϖ π x) = π (pullback.snd ϖ π x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

/-- Let `ϖ : V ⟶ U` and `π : V' ⟶ U` with `π` proper, and let `α : A ⟶ V` be an affine open of
`V` lying over an affine open `uj : Uj ⟶ U`. Then the preimage of `A` under the first projection
of `V ×_U V'` is covered by finitely many affine opens of `V ×_U V'`, each of which maps to `A`
over `V`.

The covering opens are the fibre products of `A` with the finitely many affine opens of `V'`
contained in `π ⁻¹ Uj`; they are affine by
`AlgebraicGeometry.isAffine_pullback_of_factorsThrough`, and they suffice because the second
projection carries the preimage of `A` into `π ⁻¹ Uj`. -/
theorem exists_finite_affine_cover_preimage_pullback_fst {U V V' A Uj : Scheme.{u}} (ϖ : V ⟶ U)
    (π : V' ⟶ U) [IsProper π] {uj : Uj ⟶ U} [IsOpenImmersion uj] [IsAffine Uj] {α : A ⟶ V}
    [IsOpenImmersion α] [IsAffine A] {c : A ⟶ Uj} (hc : α ≫ ϖ = c ≫ uj) :
    ∃ (n : ℕ) (B : Fin n → Scheme.{u}) (β : ∀ k, B k ⟶ pullback ϖ π) (ρ : ∀ k, B k ⟶ A),
      (∀ k, IsAffine (B k)) ∧ (∀ k, IsOpenImmersion (β k)) ∧
      (∀ k, β k ≫ pullback.fst ϖ π = ρ k ≫ α) ∧
      (pullback.fst ϖ π) ⁻¹' Set.range α ⊆ ⋃ k, Set.range (β k) := by
  classical
  have hUjc : IsCompact ((uj.opensRange : U.Opens) : Set U) := isCompact_range uj.continuous
  have hOc : IsCompact ((π ⁻¹ᵁ uj.opensRange : V'.Opens) : Set V') := by
    rw [Scheme.Hom.coe_preimage]
    exact π.isCompact_preimage hUjc
  obtain ⟨n, W, hWaff, hWle, hWcov⟩ := exists_finite_affineOpens_subset_of_isCompact _ hOc
  have hrange : ∀ l, Set.range ((W l).ι ≫ π) ⊆ Set.range uj := by
    intro l x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : (W l).ι y ∈ (π ⁻¹ᵁ uj.opensRange : V'.Opens) := hWle l y.2
    rw [Scheme.Hom.comp_apply]
    exact hy
  refine ⟨n, fun l => pullback (α ≫ ϖ) ((W l).ι ≫ π),
    fun l => pullback.map (α ≫ ϖ) ((W l).ι ≫ π) ϖ π α (W l).ι (𝟙 U) (by simp) (by simp),
    fun l => pullback.fst (α ≫ ϖ) ((W l).ι ≫ π), fun l => ?_, fun l => ?_, fun l => ?_, ?_⟩
  · have : IsAffine (W l).toScheme := hWaff l
    exact isAffine_pullback_of_factorsThrough c
      (IsOpenImmersion.lift uj ((W l).ι ≫ π) (hrange l)) hc
      (IsOpenImmersion.lift_fac uj ((W l).ι ≫ π) (hrange l)).symm
  · infer_instance
  · exact pullback.lift_fst _ _ _
  · intro x hx
    obtain ⟨y, hy⟩ := hx
    have hmem : (pullback.snd ϖ π) x ∈ (π ⁻¹ᵁ uj.opensRange : V'.Opens) := by
      change π ((pullback.snd ϖ π) x) ∈ Set.range uj
      rw [← apply_fst_eq_apply_snd, ← hy, ← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    obtain ⟨l, hxl⟩ := Set.mem_iUnion.mp (hWcov hmem)
    refine Set.mem_iUnion.mpr ⟨l, ?_⟩
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨y, hy⟩, by rw [Scheme.Opens.range_ι]; exact hxl⟩

/-- The mirror image of `AlgebraicGeometry.exists_finite_affine_cover_preimage_pullback_fst`
along the second projection, obtained from it by the symmetry of the fibre product. -/
theorem exists_finite_affine_cover_preimage_pullback_snd {U V V' A Uj : Scheme.{u}} (ϖ : V ⟶ U)
    (π : V' ⟶ U) [IsProper ϖ] {uj : Uj ⟶ U} [IsOpenImmersion uj] [IsAffine Uj] {α : A ⟶ V'}
    [IsOpenImmersion α] [IsAffine A] {c : A ⟶ Uj} (hc : α ≫ π = c ≫ uj) :
    ∃ (n : ℕ) (B : Fin n → Scheme.{u}) (β : ∀ k, B k ⟶ pullback ϖ π) (ρ : ∀ k, B k ⟶ A),
      (∀ k, IsAffine (B k)) ∧ (∀ k, IsOpenImmersion (β k)) ∧
      (∀ k, β k ≫ pullback.snd ϖ π = ρ k ≫ α) ∧
      (pullback.snd ϖ π) ⁻¹' Set.range α ⊆ ⋃ k, Set.range (β k) := by
  obtain ⟨n, B, β, ρ, hBaff, hβopen, hβfac, hβcov⟩ :=
    exists_finite_affine_cover_preimage_pullback_fst π ϖ hc
  have he : (pullbackSymmetry ϖ π).inv ≫ pullback.snd ϖ π = pullback.fst π ϖ := by
    rw [← pullbackSymmetry_hom_comp_fst ϖ π, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨n, B, fun k => β k ≫ (pullbackSymmetry ϖ π).inv, ρ, hBaff, fun k => ?_, fun k => ?_, ?_⟩
  · have := hβopen k
    infer_instance
  · rw [Category.assoc, he]; exact hβfac k
  · intro x hx
    have hx' : (pullback.fst π ϖ) ((pullbackSymmetry ϖ π).hom x) ∈ Set.range α := by
      rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
      exact hx
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp (hβcov hx')
    refine Set.mem_iUnion.mpr ⟨k, z, ?_⟩
    rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- **Stage 2 of the proof of Stacks 0DBF part (2).** Let `{u j : Uj j ⟶ U}` be a finite
covering of a scheme `U` by affine opens, let `z s : Z s ⟶ Uj (t s)` be a family of schemes over
those opens, and suppose that for every `j` there is a proper surjection `π j : V j ⟶ U` whose
part over `Uj j` is covered by finitely many affine opens, each mapping over `U` into some
`Z s`. Then the fibre product of the `V j` over `U` is proper and surjective over `U`, and is
covered by finitely many affine opens, each mapping over `U` into some `Z s`.

This is the construction `V = V_1 ×_U ⋯ ×_U V_m` of the Stacks proof, carried out one factor at
a time: the induction adds the factor `V j₀`, refines the affine opens already found along it
with `AlgebraicGeometry.exists_finite_affine_cover_preimage_pullback_fst`, and refines the given
affine opens of `V j₀` along the product already built with
`AlgebraicGeometry.exists_finite_affine_cover_preimage_pullback_snd`. A point of the product
lying over `Uj j₀` is caught by the second family, and one lying over an `Uj j` already treated
is caught by the first; since the `Uj j` cover `U`, the opens so obtained cover the product. -/
theorem exists_isProper_surjective_affine_cover_of_properOver {U : Scheme.{u}} {J : Type v}
    [Finite J] {Uj : J → Scheme.{u}} (u : ∀ j, Uj j ⟶ U) [∀ j, IsAffine (Uj j)]
    [∀ j, IsOpenImmersion (u j)] (hu : (⋃ j, Set.range (u j)) = Set.univ) {S : Type w}
    {Z : S → Scheme.{u}} {t : S → J} (z : ∀ s, Z s ⟶ Uj (t s)) {V : J → Scheme.{u}}
    (π : ∀ j, V j ⟶ U) (hπ : ∀ j, IsProper (π j)) (hπ' : ∀ j, Surjective (π j))
    (hcov : ∀ j, ∃ (n : ℕ) (A : Fin n → Scheme.{u}) (α : ∀ k, A k ⟶ V j) (σ : Fin n → S)
      (b : ∀ k, A k ⟶ Z (σ k)), (∀ k, IsAffine (A k)) ∧ (∀ k, IsOpenImmersion (α k)) ∧
      (∀ k, α k ≫ π j = b k ≫ z (σ k) ≫ u (t (σ k))) ∧
      (π j) ⁻¹' Set.range (u j) ⊆ ⋃ k, Set.range (α k)) :
    ∃ (W : Scheme.{u}) (ϖ : W ⟶ U), IsProper ϖ ∧ Surjective ϖ ∧
      ∃ (K : Type u) (_ : Finite K) (A : K → Scheme.{u}) (α : ∀ k, A k ⟶ W) (σ : K → S)
        (b : ∀ k, A k ⟶ Z (σ k)), (∀ k, IsAffine (A k)) ∧ (∀ k, IsOpenImmersion (α k)) ∧
        (∀ k, α k ≫ ϖ = b k ≫ z (σ k) ≫ u (t (σ k))) ∧
        (⋃ k, Set.range (α k)) = Set.univ := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have key : ∀ s : Finset J, ∃ (W : Scheme.{u}) (ϖ : W ⟶ U), IsProper ϖ ∧ Surjective ϖ ∧
      ∃ (K : Type u) (_ : Finite K) (A : K → Scheme.{u}) (α : ∀ k, A k ⟶ W) (σ : K → S)
        (b : ∀ k, A k ⟶ Z (σ k)), (∀ k, IsAffine (A k)) ∧ (∀ k, IsOpenImmersion (α k)) ∧
        (∀ k, α k ≫ ϖ = b k ≫ z (σ k) ≫ u (t (σ k))) ∧
        (⋃ j ∈ s, (ϖ ⁻¹' Set.range (u j))) ⊆ ⋃ k, Set.range (α k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨U, 𝟙 U, inferInstance, inferInstance, PEmpty.{u + 1}, inferInstance,
        fun k => k.elim, fun k => k.elim, fun k => k.elim, fun k => k.elim,
        fun k => k.elim, fun k => k.elim, fun k => k.elim, by simp⟩
    | insert j₀ s' hj₀ ih =>
      obtain ⟨W, ϖ, hϖp, hϖs, K, hK, A, α, σ, b, haff, hopen, hfac, hcovs⟩ := ih
      have hπp : IsProper (π j₀) := hπ j₀
      have hπs : Surjective (π j₀) := hπ' j₀
      have stepA : ∀ k : K, ∃ (n : ℕ) (B : Fin n → Scheme.{u})
          (β : ∀ l, B l ⟶ pullback ϖ (π j₀)) (ρ : ∀ l, B l ⟶ A k),
          (∀ l, IsAffine (B l)) ∧ (∀ l, IsOpenImmersion (β l)) ∧
          (∀ l, β l ≫ pullback.fst ϖ (π j₀) = ρ l ≫ α k) ∧
          (pullback.fst ϖ (π j₀)) ⁻¹' Set.range (α k) ⊆ ⋃ l, Set.range (β l) := by
        intro k
        have := haff k
        have := hopen k
        exact exists_finite_affine_cover_preimage_pullback_fst ϖ (π j₀) (uj := u (t (σ k)))
          (α := α k) (c := b k ≫ z (σ k)) (by rw [Category.assoc]; exact hfac k)
      choose nA B β ρ hBaff hβopen hβfac hβcov using stepA
      obtain ⟨m, A₀, α₀, σ₀, b₀, haff₀, hopen₀, hfac₀, hcov₀⟩ := hcov j₀
      have stepB : ∀ l : Fin m, ∃ (n : ℕ) (C : Fin n → Scheme.{u})
          (γ : ∀ r, C r ⟶ pullback ϖ (π j₀)) (δ : ∀ r, C r ⟶ A₀ l),
          (∀ r, IsAffine (C r)) ∧ (∀ r, IsOpenImmersion (γ r)) ∧
          (∀ r, γ r ≫ pullback.snd ϖ (π j₀) = δ r ≫ α₀ l) ∧
          (pullback.snd ϖ (π j₀)) ⁻¹' Set.range (α₀ l) ⊆ ⋃ r, Set.range (γ r) := by
        intro l
        have := haff₀ l
        have := hopen₀ l
        exact exists_finite_affine_cover_preimage_pullback_snd ϖ (π j₀) (uj := u (t (σ₀ l)))
          (α := α₀ l) (c := b₀ l ≫ z (σ₀ l)) (by rw [Category.assoc]; exact hfac₀ l)
      choose nB C γ δ hCaff hγopen hγfac hγcov using stepB
      refine ⟨pullback ϖ (π j₀), pullback.fst ϖ (π j₀) ≫ ϖ, inferInstance, inferInstance,
        (Σ k : K, Fin (nA k)) ⊕ (Σ l : Fin m, Fin (nB l)), inferInstance,
        Sum.elim (fun p => B p.1 p.2) (fun q => C q.1 q.2),
        Sum.rec (fun p => β p.1 p.2) (fun q => γ q.1 q.2),
        Sum.elim (fun p => σ p.1) (fun q => σ₀ q.1),
        Sum.rec (fun p => ρ p.1 p.2 ≫ b p.1) (fun q => δ q.1 q.2 ≫ b₀ q.1), ?_, ?_, ?_, ?_⟩
      · rintro (⟨k, l⟩ | ⟨l, r⟩)
        · exact hBaff k l
        · exact hCaff l r
      · rintro (⟨k, l⟩ | ⟨l, r⟩)
        · exact hβopen k l
        · exact hγopen l r
      · rintro (⟨k, l⟩ | ⟨l, r⟩)
        · change β k l ≫ pullback.fst ϖ (π j₀) ≫ ϖ = (ρ k l ≫ b k) ≫ z (σ k) ≫ u (t (σ k))
          rw [← Category.assoc, hβfac k l, Category.assoc, hfac k, Category.assoc]
        · change γ l r ≫ pullback.fst ϖ (π j₀) ≫ ϖ = (δ l r ≫ b₀ l) ≫ z (σ₀ l) ≫ u (t (σ₀ l))
          calc γ l r ≫ pullback.fst ϖ (π j₀) ≫ ϖ
              = (γ l r ≫ pullback.snd ϖ (π j₀)) ≫ π j₀ := by
                rw [pullback.condition, Category.assoc]
            _ = (δ l r ≫ α₀ l) ≫ π j₀ := by rw [hγfac l r]
            _ = (δ l r ≫ b₀ l) ≫ z (σ₀ l) ≫ u (t (σ₀ l)) := by
                rw [Category.assoc, hfac₀ l, Category.assoc]
      · intro x hx
        obtain ⟨j, hjmem, hjx⟩ := Set.mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hjmem with hj | hjs
        · rw [hj] at hjx
          have hxsnd : (pullback.snd ϖ (π j₀)) x ∈ (π j₀) ⁻¹' Set.range (u j₀) := by
            rw [Set.mem_preimage, ← apply_fst_eq_apply_snd]
            exact hjx
          obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hcov₀ hxsnd)
          obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hγcov l hl)
          exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨l, r⟩, hr⟩
        · have hxfst : (pullback.fst ϖ (π j₀)) x ∈ ⋃ k, Set.range (α k) := by
            refine hcovs (Set.mem_biUnion hjs ?_)
            rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
            exact hjx
          obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxfst
          obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hβcov k hk)
          exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨k, l⟩, hl⟩
  obtain ⟨W, ϖ, hϖp, hϖs, K, hK, A, α, σ, b, haff, hopen, hfac, hcovs⟩ := key Finset.univ
  refine ⟨W, ϖ, hϖp, hϖs, K, hK, A, α, σ, b, haff, hopen, hfac, Set.eq_univ_iff_forall.mpr ?_⟩
  intro x
  refine hcovs ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hu ▸ Set.mem_univ (ϖ x))
  exact Set.mem_biUnion (Finset.mem_univ j) hj

/-- **Stacks Project, Tag 0DBF, part (2), granted the compactification step.** Let `T` be
affine, let `g : U ⟶ T` be proper and surjective, and let `E` be a finite family of affine opens
`jj i : E.X i ⟶ U` covering `U`, so that `E` is the standard ph covering of `T` presented by
`g`. Let `F i` be a family of morphisms to `E.X i` for each `i`. If for every `i` there is a
proper surjection `π : V ⟶ U` whose part over `E.X i` is covered by finitely many affine opens,
each mapping over `U` into a member of some `F i'`, then the composite family `E.bind F` has a
refinement by a standard ph covering of `T`.

The hypothesis is what the Stacks proof extracts from Chow's lemma: with `W_i ⟶ E.X i` the
proper surjection presenting `F i`, Chow's lemma over the affine base `E.X i` makes `W_i`
projective over `E.X i` after a proper surjective modification, the scheme-theoretic closure of
`W_i` in `ℙⁿ_U` is then proper over `U` with `W_i` as its part over `E.X i`, and glueing on a
closed subscheme structure on `U ∖ E.X i` makes it surjective. Chow's lemma is not available in
this development, so the hypothesis is left as such; everything after it is proved here. -/
theorem exists_standardPHCovering_refinement_bind_of_extension {T U : Scheme.{u}} [IsAffine T]
    (g : U ⟶ T) [IsProper g] [Surjective g] {E : PreZeroHypercover.{v} T} [Finite E.I₀]
    [∀ i, IsAffine (E.X i)] (jj : ∀ i, E.X i ⟶ U) [∀ i, IsOpenImmersion (jj i)]
    (hjjcov : (⋃ i, Set.range (jj i)) = Set.univ) (hjj : ∀ i, jj i ≫ g = E.f i)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hext : ∀ i, ∃ (V : Scheme.{u}) (π : V ⟶ U), IsProper π ∧ Surjective π ∧
      ∃ (n : ℕ) (A : Fin n → Scheme.{u}) (α : ∀ k, A k ⟶ V) (σ : Fin n → Σ i, (F i).I₀)
        (b : ∀ k, A k ⟶ (F (σ k).1).X (σ k).2), (∀ k, IsAffine (A k)) ∧
        (∀ k, IsOpenImmersion (α k)) ∧
        (∀ k, α k ≫ π = b k ≫ (F (σ k).1).f (σ k).2 ≫ jj (σ k).1) ∧
        π ⁻¹' Set.range (jj i) ⊆ ⋃ k, Set.range (α k)) :
    ∃ G : PreZeroHypercover.{max v w} T,
      StandardPHCovering G.f ∧ Nonempty (G.Hom (E.bind F)) := by
  classical
  choose V π hπp hπs hrest using hext
  obtain ⟨W, ϖ, hϖp, hϖs, K, hK, A, α, σ, b, haff, hopen, hfac, hcover⟩ :=
    exists_isProper_surjective_affine_cover_of_properOver jj hjjcov
      (Z := fun s : Σ i, (F i).I₀ => (F s.1).X s.2) (t := Sigma.fst)
      (fun s => (F s.1).f s.2) π hπp hπs hrest
  -- reindex the finite index type `K` into the universe `max v w` demanded by the statement
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin K
  let e' : ULift.{max v w} (Fin n) ≃ K := Equiv.ulift.trans e.symm
  have hϖg : IsProper (ϖ ≫ g) := by have := hϖp; infer_instance
  have hϖgs : Surjective (ϖ ≫ g) := by have := hϖs; infer_instance
  have hfacg : ∀ k, α k ≫ ϖ ≫ g = b k ≫ (F (σ k).1).f (σ k).2 ≫ E.f (σ k).1 := by
    intro k
    rw [← hjj (σ k).1, ← Category.assoc, hfac k, Category.assoc, Category.assoc]
  refine ⟨PreZeroHypercover.mk (ULift.{max v w} (Fin n)) (fun i => A (e' i))
      (fun i => α (e' i) ≫ ϖ ≫ g),
    StandardPHCovering.of_presentation _ (fun i => haff (e' i)) (ϖ ≫ g) (fun i => α (e' i))
      hϖg hϖgs (fun i => hopen (e' i)) ?_ (fun _ => rfl),
    ⟨PreZeroHypercover.Hom.mk (fun i => σ (e' i)) (fun i => b (e' i))
      (fun i => (hfacg (e' i)).symm)⟩⟩
  rw [e'.surjective.iUnion_comp fun k => Set.range (α k)]
  exact hcover

/-- **The Zariski case of Stacks 0DBF part (2), in refinement form.** A standard ph covering `E`
of an affine scheme `T`, each of whose members is then covered by a Zariski open covering, has
its composite family refined by a standard ph covering of `T`.

No compactification, hence no input from Chow's lemma, is needed: each open covering of the
affine scheme `E.X i` is refined by a *finite* covering by affine opens
(`AlgebraicGeometry.exists_finite_affine_refinement`), and such a refinement of every member of
a standard ph covering is again a standard ph covering
(`AlgebraicGeometry.StandardPHCovering.bind`). -/
theorem exists_standardPHCovering_refinement_bind_openCover {T : Scheme.{u}} [IsAffine T]
    {E : PreZeroHypercover.{v} T} (hE : StandardPHCovering E.f) (𝒰 : ∀ i, (E.X i).OpenCover.{w}) :
    ∃ G : PreZeroHypercover.{max v w} T, StandardPHCovering G.f ∧
      Nonempty (G.Hom (E.bind fun i => (𝒰 i).toPreZeroHypercover)) := by
  choose F hFfin hFaff hFopen hFcov hFhom using fun i =>
    have : IsAffine (E.X i) := hE.isAffine i
    exists_finite_affine_refinement (𝒰 i)
  refine ⟨E.bind F, StandardPHCovering.bind hE F hFfin (fun i a => hFaff i a)
    (fun i a => hFopen i a) hFcov, ⟨PreZeroHypercover.Hom.mk
      (fun s => ⟨s.1, (hFhom s.1).some.s₀ s.2⟩) (fun s => (hFhom s.1).some.h₀ s.2) fun s => ?_⟩⟩
  change (hFhom s.1).some.h₀ s.2 ≫ (𝒰 s.1).f _ ≫ E.f s.1 = (F s.1).f s.2 ≫ E.f s.1
  rw [← Category.assoc, (hFhom s.1).some.w₀ s.2]

end AlgebraicGeometry

end
