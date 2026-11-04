module

public import StacksFrontier.AlgebraicGeometry.Size.Basic

/-!
# Size of an affine scheme (Stacks 000P)

For an affine scheme `S` with global sections `R = Γ(S, 𝒪_S)`, the size of `S` in the
sense of Stacks Sets, Section 3.9 — the maximum of `ℵ₀`, the number of affine opens of
`S`, and the supremum of `#Γ(S, U)` over affine opens `U` — is exactly `max ℵ₀ #R`.

The inequality `max ℵ₀ #R ≤ size S` is immediate: `⊤` is itself an affine open. The
other direction rests on two bounds, both proved by reducing an arbitrary affine open
to finitely many basic opens `D(f)`, `f ∈ R`:

* every affine open of `S` is quasi-compact, hence a *finite* union of basic opens
  (`Scheme.exists_finset_basicOpen_iSup_of_isAffine`), so `U ↦ {f : D(f) ⊆ U}` gives a
  surjection from `Finset R` onto the affine opens and `#S.affineOpens ≤ max ℵ₀ #R`;
* `Γ(S, D(f))` is the localization `R_f` (`IsAffineOpen.isLocalization_basicOpen`), so
  it is the image of `R × (powers f)` and has cardinality at most `max ℵ₀ #R`; the sheaf
  condition on the finite cover `U = ⋃_{f ∈ s} D(f)` then embeds `Γ(S, U)` into the
  finite product `∏_{f ∈ s} Γ(S, D(f))`, which is again bounded by `max ℵ₀ #R`.
-/

@[expose] public section

open Cardinal CategoryTheory Opposite TopologicalSpace

universe u

namespace Cardinal

/-- **A localization does not increase cardinality beyond `max ℵ₀ #R`.** Any `R`-algebra
`A` realizing the localization of `R` at a submonoid `M` is the image of `R × M`, and
`#M ≤ #R`, so `#A ≤ #R * #R ≤ max ℵ₀ #R`. -/
lemma mk_le_of_isLocalization {R : Type u} [CommRing R] (M : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization M A] :
    #A ≤ max ℵ₀ #R :=
  calc #A ≤ #(R × M) := mk_le_of_surjective (IsLocalization.mk'_surjective M)
    _ = #R * #M := by rw [mk_prod, lift_id, lift_id]
    _ ≤ #R * #R := mul_le_mul' le_rfl (mk_le_of_injective Subtype.val_injective)
    _ ≤ max ℵ₀ #R := (mul_le_max _ _).trans_eq (by rw [max_self, max_comm])

/-- A localization of a commutative ring `R` at a submonoid of powers has cardinality at
most `max ℵ₀ #R`. -/
lemma mk_localization_powers_le {R : Type u} [CommRing R] (f : R) :
    #(Localization (Submonoid.powers f)) ≤ max ℵ₀ #R :=
  mk_le_of_isLocalization (Submonoid.powers f) _

/-- Any `R`-algebra `A` realizing the localization of `R` away from `f` has cardinality
at most `max ℵ₀ #R`. -/
lemma mk_le_of_isLocalization_powers
    {R : Type u} [CommRing R] (f : R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization (Submonoid.powers f) A] :
    #A ≤ max ℵ₀ #R :=
  mk_le_of_isLocalization (Submonoid.powers f) A

/-- A finite product of cardinals, each bounded by an infinite cardinal `κ`, is bounded
by `κ`. -/
lemma prod_le_of_le_of_aleph0_le
    {ι : Type u} (s : Finset ι) (c : ι → Cardinal.{u}) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (h : ∀ i ∈ s, c i ≤ κ) :
    ∏ i ∈ s, c i ≤ κ := by
  classical
  revert h
  refine s.induction_on (fun _ => by simpa using one_le_aleph0.trans hκ) ?_
  intro a t ha ih h
  rw [Finset.prod_insert ha]
  exact (mul_le_mul' (h a (Finset.mem_insert_self a t))
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans_eq (mul_eq_self hκ)

end Cardinal

namespace AlgebraicGeometry

/-- For an affine scheme `S` and `f : Γ(S, ⊤)`, the sections over the basic open `D(f)`
form the localization of `Γ(S, ⊤)` away from `f`, hence number at most
`max ℵ₀ #Γ(S, ⊤)`. -/
lemma Scheme.mk_sections_basicOpen_le_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (f : Γ(S, ⊤)) :
    #Γ(S, S.basicOpen f) ≤ max ℵ₀ #Γ(S, ⊤) := by
  have : IsLocalization.Away f ↑Γ(S, S.basicOpen f) :=
    (isAffineOpen_top S).isLocalization_basicOpen f
  exact mk_le_of_isLocalization (Submonoid.powers f) _

/-- **Sheaf separatedness on a finite cover.** If the open `V` of a scheme `S` is a
finite union `V = ⨆ i ∈ s, U i`, then restriction `Γ(S, V) → (i : s) → Γ(S, U i)` is
injective. -/
lemma Scheme.sections_restrict_injective_of_iSup
    (S : Scheme.{u}) {ι : Type u} (s : Finset ι) (U : ι → S.Opens)
    (V : S.Opens) (hV : V = ⨆ i ∈ s, U i) :
    Function.Injective
      (fun (x : Γ(S, V)) =>
        fun (i : s) => S.presheaf.map
          (op (homOfLE
            (hV ▸ le_iSup₂ (f := fun j _ => U j) i.1 i.2 : U i.1 ≤ V))) x) := by
  intro x y h
  apply S.IsSheaf.section_ext
  intro p hp
  simp only [hV, Opens.mem_iSup] at hp
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨U i, hV ▸ le_iSup₂ (f := fun j _ => U j) i hi, hpi, congrFun h ⟨i, hi⟩⟩

/-- Injectivity of restriction on a finite cover `V = ⨆ i ∈ s, U i` bounds `#Γ(S, V)` by
the finite product `∏ i ∈ s, #Γ(S, U i)`. -/
lemma Scheme.mk_sections_le_prod_of_iSup
    (S : Scheme.{u}) {ι : Type u} (s : Finset ι) (U : ι → S.Opens)
    (V : S.Opens) (hV : V = ⨆ i ∈ s, U i) :
    #Γ(S, V) ≤ ∏ i ∈ s, #Γ(S, U i) := by
  refine (mk_le_of_injective (S.sections_restrict_injective_of_iSup s U V hV)).trans ?_
  rw [mk_pi, prod_eq_of_fintype, lift_id,
      ← Finset.prod_attach (s := s) (f := fun i => #Γ(S, U i))]
  rfl

/-- Every affine open of an affine scheme `S` is a finite union of basic opens `D(f)`
with `f ∈ Γ(S, ⊤)`: the basic opens form a basis and an affine open is quasi-compact. -/
lemma Scheme.exists_finset_basicOpen_iSup_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (U : S.affineOpens) :
    ∃ s : Finset Γ(S, ⊤), U.1 = ⨆ f ∈ s, S.basicOpen f := by
  classical
  obtain ⟨t, ht_fin, ht_eq⟩ :=
    (Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
      (b := (S.basicOpen : Γ(S, ⊤) → S.Opens)) (isBasis_basicOpen S)
      (fun f => ((isAffineOpen_top S).basicOpen f).isCompact)
      (U.1 : Set S)).mp ⟨U.2.isCompact, U.1.isOpen⟩
  refine ⟨ht_fin.toFinset, Opens.ext ?_⟩
  simp [ht_eq]

/-- For an affine scheme `S` with `R = Γ(S, ⊤)`, the affine opens of `S` number at most
`max ℵ₀ #R`: each one is the union of a `Finset` of basic opens. -/
lemma Scheme.mk_affineOpens_le_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    #S.affineOpens ≤ max ℵ₀ #Γ(S, ⊤) := by
  classical
  set R := Γ(S, ⊤)
  have hSurj :
      Function.Surjective
        (fun (p : {s : Finset R // IsAffineOpen (⨆ f ∈ s, S.basicOpen f)}) =>
          (⟨⨆ f ∈ p.1, S.basicOpen f, p.2⟩ : S.affineOpens)) := by
    rintro ⟨V, hV⟩
    obtain ⟨s, hs⟩ := S.exists_finset_basicOpen_iSup_of_isAffine ⟨V, hV⟩
    exact ⟨⟨s, hs ▸ hV⟩, Subtype.ext hs.symm⟩
  calc #S.affineOpens
      ≤ #{s : Finset R // IsAffineOpen (⨆ f ∈ s, S.basicOpen f)} := mk_le_of_surjective hSurj
    _ ≤ #(Finset R) := mk_subtype_le _
    -- `Finset.toList` is injective, so `#(Finset R) ≤ #(List R) = max #R ℵ₀`.
    _ ≤ #(List R) := mk_le_of_injective (f := Finset.toList) fun a b hab => by
        simpa using congr(List.toFinset $hab)
    _ = max #R ℵ₀ := mk_list_eq_max_mk_aleph0 R
    _ = max ℵ₀ #R := max_comm _ _

/-- For an affine scheme `S` with `R = Γ(S, ⊤)` and any affine open `U`, the sections
`Γ(S, U)` number at most `max ℵ₀ #R`. -/
lemma Scheme.mk_sections_le_of_isAffine (S : Scheme.{u}) [IsAffine S]
    (U : S.affineOpens) :
    #Γ(S, U.1) ≤ max ℵ₀ #Γ(S, ⊤) := by
  obtain ⟨s, hs⟩ := S.exists_finset_basicOpen_iSup_of_isAffine U
  exact (S.mk_sections_le_prod_of_iSup s S.basicOpen U.1 hs).trans <|
    prod_le_of_le_of_aleph0_le s _ _ (le_max_left _ _) fun f _ =>
      S.mk_sections_basicOpen_le_of_isAffine f

/-- **Stacks 000P.** Let `S` be an affine scheme and `R = Γ(S, 𝒪_S)`. Then
`size S = max ℵ₀ #R`. -/
@[stacks 000P]
theorem Scheme.size_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    S.size = max ℵ₀ #Γ(S, ⊤) := by
  have : Nonempty S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
  refine le_antisymm (max_le (le_max_left _ _) (max_le S.mk_affineOpens_le_of_isAffine
    (ciSup_le S.mk_sections_le_of_isAffine))) (max_le (le_max_left _ _) ?_)
  exact le_max_of_le_right <| le_max_of_le_right <|
    le_ciSup bddAbove_of_small (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)

end AlgebraicGeometry
