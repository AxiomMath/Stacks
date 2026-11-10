module

public import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Size.Basic

/-!
# Size under open covers, open subschemes and coproducts

If a scheme `X` is covered by opens `S i`, `i : I`, with `I` nonempty, then
`size X ≤ max #I (⨆ i, size (S i))` (Stacks 000Q). The index type must be nonempty: for empty
`I` the covering hypothesis forces `X = ∅`, while the right-hand side is `0 < ℵ₀ ≤ size X`.

It follows that an open subscheme of `X` has size at most `size X`, that size is invariant under
isomorphism, and that for an infinite cardinal `κ` a coproduct of at most `κ` schemes, each of
size at most `κ`, has size at most `κ`.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_iSup_eq_top`: the open-cover bound.
* `AlgebraicGeometry.Scheme.size_le_of_bounds`: a cardinal bounding `ℵ₀`, the number of
  affine opens and each ring of sections over an affine open bounds `Scheme.size`.
* `AlgebraicGeometry.Scheme.mk_sections_coe_opens`: `#Γ(↥U, ⊤) = #Γ(X, U)` for any open
  `U ⊆ X`.
* `AlgebraicGeometry.Scheme.size_coe_opens_le`: `size ↥U ≤ size X` for any open `U ⊆ X`.
* `AlgebraicGeometry.Scheme.size_congr`: isomorphic schemes have the same size.
* `AlgebraicGeometry.size_le_aleph0_of_isEmpty`: a scheme with empty carrier has size at most
  `ℵ₀`.
* `AlgebraicGeometry.schemeSize_coproduct_le`: a coproduct of at most `κ` schemes of size at
  most `κ` has size at most `κ`, for infinite `κ`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry

/-! ### Cardinal arithmetic -/

/-- A finite product of cardinals each bounded by an infinite cardinal `μ` is bounded by `μ`. -/
private lemma finset_prod_le_of_infinite {n : ℕ} (μ : Cardinal.{u})
    (hμ : ℵ₀ ≤ μ) (f : Fin n → Cardinal.{u}) (hf : ∀ k, f k ≤ μ) :
    ∏ k : Fin n, f k ≤ μ :=
  calc ∏ k : Fin n, f k
      ≤ ∏ _ : Fin n, μ := Finset.prod_le_prod fun i _ => hf i
    _ = μ ^ n := by simp
    _ ≤ μ := power_nat_le hμ

/-- The cardinality of a finite Π-type equals the Finset product of the cardinalities. -/
private lemma card_pi_fin_eq_finset_prod {n : ℕ} (α : Fin n → Type u) :
    #((k : Fin n) → α k) = ∏ k : Fin n, #(α k) := by
  simp [mk_pi, prod_eq_of_fintype]

/-- An `ℕ`-indexed sum of a constant infinite cardinal `ν` is at most `ν`. -/
private lemma cardinal_sum_nat_const_le {ν : Cardinal.{u}} (hν : ℵ₀ ≤ ν) :
    Cardinal.sum (fun (_ : ℕ) => ν) ≤ ν := by
  rw [Cardinal.sum_const]
  simpa using (aleph0_mul_eq hν).le

/-- If `ℵ₀ ≤ ν` and `#ι ≤ ν`, then the `ι`-indexed sum of the constant `ν` is at most `ν`. -/
private lemma sum_const_le_self {ι : Type u} (ν : Cardinal.{u}) (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν) :
    Cardinal.sum (fun (_ : ι) => ν) ≤ ν := by
  rw [Cardinal.sum_const']
  exact (mul_le_mul' hι le_rfl).trans (mul_eq_self hν).le

/-! ### Suprema of sizes -/

/-- Given a nonempty index set `I` and a family `S : I → X.Opens`,
`max (#I) (⨆ i, Scheme.size (S i))` is at least `ℵ₀`. -/
private lemma aleph0_le_max_of_nonempty {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) :
    ℵ₀ ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) :=
  (Scheme.aleph0_le_size _).trans <|
    (le_ciSup bddAbove_of_small (Classical.arbitrary I)).trans (le_max_right _ _)

/-- One term of an indexed family of `Scheme.size` values is bounded by the supremum. -/
private lemma schemeSize_le_iSup_schemeSize {X : Scheme.{u}} {I : Type u}
    (S : I → X.Opens) (i : I) :
    Scheme.size (S i : Scheme) ≤ ⨆ j, Scheme.size (S j : Scheme) :=
  le_ciSup bddAbove_of_small i

/-! ### Finite covers of affine opens -/

/-- The data of a finite cover of an affine open of `X` by affine opens of the `S i`'s. -/
private abbrev CoverData {X : Scheme.{u}} {I : Type u} (S : I → X.Opens) :=
  Σ n : ℕ, Σ f : Fin n → I, ∀ k : Fin n, ((S (f k) : Scheme).affineOpens)

/-- The union of the images of the affine opens chosen by a `CoverData` under the open immersions
`S (f k) ⟶ X`. -/
private noncomputable def CoverData.toOpens {X : Scheme.{u}} {I : Type u} {S : I → X.Opens} :
    CoverData S → X.Opens
  | ⟨n, f, V⟩ => ⨆ k : Fin n, (S (f k)).ι ''ᵁ (V k).1

/-- For each `x ∈ U` with `⨆ i, S i = ⊤`, there exists `i : I` and an affine open `V` of `S i` such
that the image `(S i).ι ''ᵁ V.1` contains `x` and lies in `U`. -/
private lemma exists_index_and_affineOpen {X : Scheme.{u}} {I : Type u}
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ (i : I) (V : ((S i : Scheme).affineOpens)),
      x ∈ ((S i).ι ''ᵁ V.1 : X.Opens) ∧ (S i).ι ''ᵁ V.1 ≤ U := by
  obtain ⟨i₀, hxi⟩ : ∃ i, x ∈ S i := Opens.mem_iSup.mp <| by simp [hcov]
  obtain ⟨V, hVaff, hyV, hVpre⟩ :=
    (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (S i₀ : Scheme)))
      (show (⟨x, hxi⟩ : (S i₀ : Scheme)) ∈ (S i₀).ι ⁻¹ᵁ U from hx)
  refine ⟨i₀, ⟨V, hVaff⟩, ⟨⟨x, hxi⟩, hyV, rfl⟩, ?_⟩
  rintro a ⟨b, hb, rfl⟩
  exact hVpre hb

/-- A compact open `U` covered by `W : α → X.Opens` (each contained in `U`) admits a finite
subcover reindexed by `Fin n`. -/
private lemma exists_fin_finite_subcover {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X))
    {α : Type*} (W : α → X.Opens)
    (hcov : (U : Set X) ⊆ ⋃ a, (W a : Set X))
    (hsub : ∀ a, W a ≤ U) :
    ∃ (n : ℕ) (g : Fin n → α), (⨆ k : Fin n, W (g k)) = U := by
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover (fun a => (W a : Set X))
    (fun a => (W a).isOpen) hcov
  refine ⟨T.card, fun k => (T.equivFin.symm k : α),
    le_antisymm (iSup_le fun _ => hsub _) fun x hx => ?_⟩
  obtain ⟨a, haT, hxWa⟩ : ∃ a ∈ T, x ∈ (W a : Set X) := by simpa using hT hx
  exact Opens.mem_iSup.mpr ⟨T.equivFin ⟨a, haT⟩, by simpa using hxWa⟩

/-- Given an open cover `S` of `X` and an affine open `U`, there exists a finite cover of `U.1` by
affine opens of the `S i`'s. -/
private lemma exists_finite_affineOpens_cover_in_S {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) (U : X.affineOpens) :
    ∃ (n : ℕ) (f : Fin n → I) (V : ∀ k : Fin n, ((S (f k) : Scheme).affineOpens)),
      (⨆ k : Fin n, (S (f k)).ι ''ᵁ (V k).1) = U.1 := by
  obtain ⟨U, hUaff⟩ := U
  choose chooseI chooseV hin hsub using fun x : U =>
    exists_index_and_affineOpen S hcov U x.2
  obtain ⟨n, g, hg⟩ := exists_fin_finite_subcover U hUaff.isCompact
    (fun x => (S (chooseI x)).ι ''ᵁ (chooseV x).1)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hin ⟨y, hy⟩⟩) hsub
  exact ⟨n, fun k => chooseI (g k), fun k => chooseV (g k), hg⟩

/-- Every affine open of `X` is the union of the opens of some `CoverData`. -/
private lemma exists_coverData {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) (U : X.affineOpens) :
    ∃ d : CoverData S, CoverData.toOpens d = U.1 := by
  obtain ⟨n, f, V, hUV⟩ := exists_finite_affineOpens_cover_in_S S hcov U
  exact ⟨⟨n, f, V⟩, hUV⟩

/-! ### Counting finite covers -/

/-- For a nonempty family `S`, `#(Fin n → I)` is bounded by
`ν := max (#I) (⨆ i, Scheme.size (S i))`. -/
private lemma card_arrow_fin_to_I_le {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (n : ℕ) :
    #(Fin n → I) ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) := by
  rw [card_pi_fin_eq_finset_prod (fun _ => I)]
  exact finset_prod_le_of_infinite _ (aleph0_le_max_of_nonempty S) (fun _ => #I)
    (fun _ => le_max_left _ _)

/-- The cardinality of the slice `Σ f : Fin n → I, ∀ k, (S (f k)).affineOpens` is bounded by
`ν := max (#I) (⨆ i, Scheme.size (S i))`. -/
private lemma coverData_slice_card_le {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (n : ℕ) :
    #(Σ f : Fin n → I, ∀ k : Fin n, (S (f k) : Scheme).affineOpens)
      ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) := by
  set ν := max #I (⨆ i, Scheme.size (S i : Scheme))
  have hν : ℵ₀ ≤ ν := aleph0_le_max_of_nonempty S
  rw [mk_sigma]
  have h_summand : ∀ f : Fin n → I, #((k : Fin n) → ↥((S (f k) : Scheme).affineOpens)) ≤ ν := by
    intro f
    rw [card_pi_fin_eq_finset_prod]
    refine finset_prod_le_of_infinite ν hν _ fun k => ?_
    calc #↥((S (f k) : Scheme).affineOpens)
        ≤ Scheme.size (S (f k) : Scheme) := Scheme.mk_affineOpens_le_size _
      _ ≤ ⨆ j, Scheme.size (S j : Scheme) := schemeSize_le_iSup_schemeSize S (f k)
      _ ≤ ν := le_max_right _ _
  exact (Cardinal.sum_le_sum _ _ h_summand).trans
    (sum_const_le_self ν hν (card_arrow_fin_to_I_le S n))

/-- The cardinality of `CoverData S` is at most `max (#I) (⨆ i, Scheme.size (S i))`. -/
private lemma coverData_card_le {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) :
    #(CoverData S) ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) := by
  rw [mk_sigma]
  exact (Cardinal.sum_le_sum _ _ (coverData_slice_card_le S)).trans
    (cardinal_sum_nat_const_le (aleph0_le_max_of_nonempty S))

/-- The map sending each affine open `U` to a chosen `CoverData` is injective. -/
private lemma exists_injection_affineOpens_to_coverData {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) :
    ∃ φ : X.affineOpens → CoverData S, Function.Injective φ := by
  classical
  choose φ hφ using exists_coverData S hcov
  refine ⟨φ, fun U₁ U₂ h => Subtype.ext ?_⟩
  rw [← hφ U₁, ← hφ U₂]
  exact congrArg CoverData.toOpens h

/-! ### Sections over a finite cover -/

/-- If `U = ⨆ k, V k`, the diagonal restriction map `Γ(X, U) → ∏ k, Γ(X, V k)` is injective. -/
private lemma sheaf_restriction_injective {X : Scheme.{u}} (U : X.Opens) {n : ℕ}
    (V : Fin n → X.Opens) (hVU : U = ⨆ k, V k) :
    ∃ f : Γ(X, U) → ((k : Fin n) → Γ(X, V k)), Function.Injective f :=
  have hle : ∀ k, V k ≤ U := fun k => hVU ▸ le_iSup V k
  ⟨fun s k => X.presheaf.map (homOfLE (hle k)).op s, fun _ _ h =>
    X.sheaf.eq_of_locally_eq' V U (fun k => homOfLE (hle k)) hVU.le _ _ (congrFun h)⟩

/-- If `U = ⨆ k, V k` for finitely many opens `V k`, then `#Γ(X, U) ≤ ∏ k, #Γ(X, V k)`. -/
private lemma card_sections_le_finset_prod_of_cover {X : Scheme.{u}} (U : X.Opens) {n : ℕ}
    (V : Fin n → X.Opens) (hVU : U = ⨆ k, V k) :
    #Γ(X, U) ≤ ∏ k : Fin n, #Γ(X, V k) := by
  obtain ⟨f, hf⟩ := sheaf_restriction_injective U V hVU
  calc #Γ(X, U)
      ≤ #((k : Fin n) → Γ(X, V k)) := mk_le_of_injective hf
    _ = ∏ k : Fin n, #Γ(X, V k) := card_pi_fin_eq_finset_prod (fun k => Γ(X, V k))

/-- For an open subscheme `S` of `X` and an affine open `V` of `S.toScheme`,
`#Γ(X, S.ι ''ᵁ V.1) ≤ Scheme.size (S : Scheme)`. -/
private lemma card_sections_image_le_schemeSize {X : Scheme.{u}} (S : X.Opens)
    (V : (S : Scheme).affineOpens) :
    #Γ(X, (S.ι ''ᵁ V.1)) ≤ Scheme.size (S : Scheme) :=
  le_max_of_le_right <| le_max_of_le_right <| le_ciSup bddAbove_of_small V

/-! ### The open-cover bound -/

/-- For any affine open `U` of `X`, `#Γ(X, U) ≤ max (#I) (⨆ i, Scheme.size (S i))` whenever `S`
covers `X`. -/
private lemma sections_le_of_cover {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) (U : X.affineOpens) :
    #Γ(X, U.1) ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) := by
  set μ := ⨆ i, Scheme.size (S i : Scheme)
  have hμ : ℵ₀ ≤ μ :=
    (Scheme.aleph0_le_size (S (Classical.arbitrary I) : Scheme)).trans
      (schemeSize_le_iSup_schemeSize S _)
  obtain ⟨⟨n, f, V⟩, hd⟩ := exists_coverData S hcov U
  refine ((card_sections_le_finset_prod_of_cover U.1 _ hd.symm).trans
    (finset_prod_le_of_infinite μ hμ _ fun k =>
      (card_sections_image_le_schemeSize (S (f k)) (V k)).trans
        (schemeSize_le_iSup_schemeSize S (f k)))).trans (le_max_right _ _)

/-- The cardinality of `X.affineOpens` is bounded by `max (#I) (⨆ i, Scheme.size (S i))` whenever
`S` covers `X`. -/
private lemma affineOpens_card_le_of_cover {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) :
    #X.affineOpens ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) := by
  obtain ⟨φ, hφ⟩ := exists_injection_affineOpens_to_coverData S hcov
  exact (mk_le_of_injective hφ).trans (coverData_card_le S)

/-- If `S : I → X.Opens` is an open cover of `X` indexed by a nonempty type `I`, then
`size X ≤ max #I (⨆ i, size (S i))`. -/
@[stacks 000Q]
theorem Scheme.size_le_of_iSup_eq_top {X : Scheme.{u}} {I : Type u} [Nonempty I]
    (S : I → X.Opens) (hcov : ⨆ i, S i = ⊤) :
    Scheme.size X ≤ max #I (⨆ i, Scheme.size (S i : Scheme)) :=
  max_le (aleph0_le_max_of_nonempty S) <|
    max_le (affineOpens_card_le_of_cover S hcov)
      (ciSup_le' fun U => sections_le_of_cover S hcov U)

end AlgebraicGeometry

open Cardinal CategoryTheory

namespace AlgebraicGeometry

/-- An infinite cardinal `c` dominating both the number of affine opens of `X` and each `#Γ(X, U)`
over an affine open dominates `Scheme.size X`. -/
theorem Scheme.size_le_of_bounds {X : Scheme.{u}} {c : Cardinal.{u}} (h0 : ℵ₀ ≤ c)
    (h1 : #X.affineOpens ≤ c) (h2 : ∀ U : X.affineOpens, #Γ(X, U.1) ≤ c) :
    X.size ≤ c :=
  max_le h0 (max_le h1 (ciSup_le' h2))

/-- The global sections of an open subscheme `↥U` have the same cardinality as the sections of `X`
over `U`. -/
theorem Scheme.mk_sections_coe_opens (X : Scheme.{u}) (U : X.Opens) :
    #Γ((↑U : Scheme.{u}), ⊤) = #Γ(X, U) := by
  have iso := U.ι.appIso ⊤
  rw [show U.ι ''ᵁ ⊤ = U by
    simp [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]] at iso
  exact (mk_congr iso.commRingCatIsoToRingEquiv.toEquiv).symm

/-- The source of an open immersion has size at most the size of the target. -/
private theorem size_le_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.size ≤ Y.size := by
  refine Scheme.size_le_of_bounds (Scheme.aleph0_le_size Y) ?_ fun U => ?_
  · exact (mk_le_of_injective (f := fun U : X.affineOpens =>
      (⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩ : Y.affineOpens))
      fun _ _ h => Subtype.ext (Scheme.Hom.image_injective f
        (congrArg Subtype.val h))).trans (Scheme.mk_affineOpens_le_size Y)
  · rw [← mk_congr (f.appIso U.1).commRingCatIsoToRingEquiv.toEquiv]
    exact Scheme.mk_sections_le_size Y ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩

/-- The size of an open subscheme is at most the size of the ambient scheme. -/
theorem Scheme.size_coe_opens_le (X : Scheme.{u}) (U : X.Opens) :
    (↑U : Scheme.{u}).size ≤ X.size :=
  size_le_of_isOpenImmersion U.ι

end AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

namespace AlgebraicGeometry

/-- `Scheme.size` is invariant under isomorphism. -/
theorem Scheme.size_congr {X Y : Scheme.{u}} (e : X ≅ Y) : X.size = Y.size :=
  le_antisymm (size_le_of_isOpenImmersion e.hom) (size_le_of_isOpenImmersion e.inv)

/-- A scheme with empty carrier has size at most `ℵ₀`. -/
theorem size_le_aleph0_of_isEmpty (X : Scheme.{u}) (hX : IsEmpty X) :
    X.size ≤ ℵ₀ := by
  refine Scheme.size_le_of_bounds le_rfl ?_ fun U => ?_
  · have : Subsingleton X.affineOpens :=
      ⟨fun _ _ => Subtype.ext (Opens.ext (by ext x; exact (hX.false x).elim))⟩
    exact (le_one_iff_subsingleton.mpr this).trans one_le_aleph0
  · have : Subsingleton Γ(X, U.1) := inferInstance
    exact (le_one_iff_subsingleton.mpr this).trans one_le_aleph0

/-- If the index type has cardinality at most an infinite cardinal `κ` and every component has size
at most `κ`, then the coproduct of the family has size at most `κ`. -/
theorem schemeSize_coproduct_le {ι : Type u} (Y : ι → Scheme.{u})
    (κ : Cardinal.{u}) (hℵ : ℵ₀ ≤ κ) (hι : #ι ≤ κ) (h : ∀ j, Scheme.size (Y j) ≤ κ) :
    Scheme.size (∐ Y) ≤ κ := by
  have hS : ⨆ i, (Sigma.ι Y i).opensRange = ⊤ := (sigmaOpenCover Y).iSup_opensRange
  rcases isEmpty_or_nonempty ι with hemp | hne
  · have hbot : (⊥ : (∐ Y).Opens) = ⊤ := by rw [← hS, iSup_of_empty]
    exact (size_le_aleph0_of_isEmpty _
      ⟨fun x => (hbot.symm ▸ trivial : x ∈ (⊥ : (∐ Y).Opens))⟩).trans hℵ
  · exact (Scheme.size_le_of_iSup_eq_top _ hS).trans (max_le hι (ciSup_le' fun i =>
      (Scheme.size_congr (Sigma.ι Y i).isoOpensRange).symm.trans_le (h i)))

end AlgebraicGeometry
