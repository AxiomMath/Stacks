module

public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.Stages

/-!
# Inseparable residue fields: the central claim of Stacks 07FG

The data `CoefficientSectionData` of a section `σ`, generators `λ₁, …, λ_d` of `𝔪` and a finitely
generated coefficient field `F₀` with the image of `k` inside `Ψ_σ(F₀[λ])`; its existence in
characteristic `p` when `dim_K H₁(L_{K/k}) < ∞`, by the source's induction on the nilpotency
order of `𝔪`; and Stacks 07FG, also with the residue field of the approximating subalgebra
prescribed.

This is the second part of `StacksFrontier.RingTheory.Smoothing.InseparableResidueField`.

## Main definitions

* `Stacks.Smoothing.CoefficientSectionData`: the data produced by the central claim.

## Main results

* `Stacks.Smoothing.nonempty_coefficientSectionData_of_finite_h1Cotangent`: the central claim.
* `Stacks.Smoothing.exists_directedOn_flat_essFiniteType`: Stacks 07FG.
* `Stacks.Smoothing.exists_subalgebra_residueField_image_eq_of_charP`: Stacks 07FG with the
  residue field of the approximating subalgebra prescribed.
-/

@[expose] public section

namespace Stacks.Smoothing

open IsLocalRing MvPolynomial
open scoped TensorProduct

/-! ### Stacks 07FG -/

/-- The data produced by the central claim in the proof of Stacks 07FG: a ring-theoretic section
`σ` of the residue map of an Artinian local `k`-algebra `Λ`, a finite family of generators of its
maximal ideal, and a finitely generated subfield `k ⊆ F₀ ⊆ K` of the residue field such that the
image of `k` in `Λ` already lies in the stage `Ψ_σ(F₀[λ₁, …, λ_d])`.

The section `σ` is a ring map only. Asking it to be a `k`-algebra map would make the claim
trivial but is impossible in general: it is exactly the inseparability of `K/k` that obstructs
it, and the source's claim is a substitute obtained from `dim H₁(L_{K/k}) < ∞`. -/
structure CoefficientSectionData (k Λ : Type*) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsLocalRing Λ] where
  /-- A ring-theoretic section of the residue map `Λ → K`, not required to be `k`-linear. -/
  σ : ResidueField Λ →+* Λ
  /-- `σ` is a section of the residue map. -/
  residue_σ : ∀ c, residue Λ (σ c) = c
  /-- The number of chosen generators of the maximal ideal. -/
  numGen : ℕ
  /-- The chosen generators `λ₁, …, λ_d` of the maximal ideal. -/
  gen : Fin numGen → Λ
  /-- The chosen elements generate the maximal ideal. -/
  span_range_gen : Ideal.span (Set.range gen) = maximalIdeal Λ
  /-- The finitely generated coefficient field `F₀` of the claim. -/
  base : IntermediateField k (ResidueField Λ)
  /-- `F₀` is finitely generated over `k`. -/
  base_fg : base.FG
  /-- The image of `k` in `Λ` lies in `Ψ_σ(F₀[λ₁, …, λ_d])`; this is the claim. -/
  range_algebraMap_mem : ∀ a : k, algebraMap k Λ a ∈ coefficientStage σ base gen

/-- The maximal ideal of an Artinian local ring is nilpotent. -/
private theorem isNilpotent_maximalIdeal_of_isArtinianRing (Λ : Type*) [CommRing Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ] : IsNilpotent (maximalIdeal Λ) := by
  rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal Λ) bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

/-- For the data `C` of `CoefficientSectionData` and a finite subset `S` of `Λ`, there is a finitely
generated `F₁` such that `S` lies in its stage and, for every finitely generated `F ≥ F₁`, the stage
`Ψ_σ(F[λ])` is a `k`-subalgebra `A` of `Λ` which is Artinian local, essentially of finite type over
`k`, has `Λ` flat over it, and satisfies `𝔪_A Λ = 𝔪`. -/
private theorem exists_stage_subalgebra_of_coefficientSectionData
    {k Λ : Type*} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ] (C : CoefficientSectionData k Λ) (S : Finset Λ) :
    ∃ F₁ : IntermediateField k (ResidueField Λ), F₁.FG ∧
      (∀ y ∈ S, y ∈ coefficientStage C.σ F₁ C.gen) ∧
      ∀ F : IntermediateField k (ResidueField Λ), F₁ ≤ F → F.FG →
        ∃ (A : Subalgebra k Λ) (_ : IsArtinianRing A) (_ : IsLocalRing A),
          A.toSubring = coefficientStage C.σ F C.gen ∧ Module.Flat A Λ ∧
          Algebra.EssFiniteType k A ∧
          Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ := by
  classical
  let : Algebra (ResidueField Λ) Λ := C.σ.toAlgebra
  have hsec : ∀ c, residue Λ (algebraMap (ResidueField Λ) Λ c) = c := C.residue_σ
  have hnil := isNilpotent_maximalIdeal_of_isArtinianRing Λ
  have hsurj := eval₂Hom_surjective_of_isSection C.σ C.residue_σ C.gen C.span_range_gen hnil
  -- `Λ` is a finite-dimensional `K`-vector space, by Stacks 07DT(1) applied to `σ`
  have hfinΛ : Module.Finite (ResidueField Λ) Λ := by
    have hid : (residue Λ).comp C.σ = RingHom.id _ := RingHom.ext C.residue_σ
    have h : C.σ.Finite := (finite_iff_residue_finite C.σ).mpr (by rw [hid]; exact .id _)
    exact h
  obtain ⟨m, b⟩ := (⟨_, Module.finBasis (ResidueField Λ) Λ⟩ :
    Σ m : ℕ, Module.Basis (Fin m) (ResidueField Λ) Λ)
  -- the finitely many residue-field coordinates that have to be adjoined to `F₀`
  set T : Finset (ResidueField Λ) :=
    (Finset.univ.image fun i : Fin m => b.repr 1 i) ∪
    (Finset.univ.image fun p : Fin C.numGen × Fin m => b.repr (C.gen p.1) p.2) ∪
    (Finset.univ.image fun t : Fin m × Fin m × Fin m => b.repr (b t.1 * b t.2.1) t.2.2) with hT
  obtain ⟨F', hF'base, hF'fg, hF'b⟩ := exists_fg_subset_coefficientStage C.σ C.gen hsurj
    C.base C.base_fg (Finset.univ.image b ∪ S)
  set F₁ := F' ⊔ IntermediateField.adjoin k (T : Set (ResidueField Λ)) with hF₁
  have hTF₁ : (T : Set (ResidueField Λ)) ⊆ (F₁ : Set (ResidueField Λ)) := fun y hy =>
    (le_sup_right : IntermediateField.adjoin k _ ≤ F₁)
      (IntermediateField.subset_adjoin k _ hy)
  have hF'F₁ : F' ≤ F₁ := le_sup_left
  refine ⟨F₁, IntermediateField.fg_sup hF'fg (IntermediateField.fg_adjoin_finset T),
    fun y hy => coefficientStage_mono C.σ C.gen hF'F₁ (hF'b y (Finset.mem_union_right _ hy)),
    fun F hF hfg => ?_⟩
  let A : Subalgebra k Λ :=
    { toSubsemiring := (coefficientStage C.σ F C.gen).toSubsemiring
      algebraMap_mem' := fun a => coefficientStage_mono C.σ C.gen
        ((hF'base.trans hF'F₁).trans hF) (C.range_algebraMap_mem a) }
  have hA : A.toSubring = coefficientStage C.σ F C.gen := rfl
  have h1 : ∀ i, b.repr 1 i ∈ F := fun i => hF (hTF₁ (by
    simp only [hT, Finset.coe_union, Finset.coe_image]
    exact Or.inl (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)))
  have h2 : ∀ j i, b.repr (C.gen j) i ∈ F := fun j i => hF (hTF₁ (by
    simp only [hT, Finset.coe_union, Finset.coe_image]
    exact Or.inl (Or.inr ⟨(j, i), Finset.mem_univ _, rfl⟩)))
  have h3 : ∀ i j l, b.repr (b i * b j) l ∈ F := fun i j l => hF (hTF₁ (by
    simp only [hT, Finset.coe_union, Finset.coe_image]
    exact Or.inr ⟨(i, j, l), Finset.mem_univ _, rfl⟩))
  obtain ⟨hart, hloc, hfree, heft, hmax⟩ := exists_stage hsec hnil b C.gen C.span_range_gen
    F hfg (fun i => coefficientStage_mono C.σ C.gen (hF'F₁.trans hF)
      (hF'b (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem b (Finset.mem_univ i)))))
    h1 h2 h3 A hA
  exact ⟨A, hart, hloc, hA, (by have := hfree; exact Module.Flat.of_free), heft, hmax⟩

/-- The deduction of the conclusion of Stacks 07FG from the central claim of its proof: for an
Artinian local `k`-algebra `(Λ, 𝔪, K)` carrying the data of `CoefficientSectionData` there is a
directed family `𝒜` of `k`-subalgebras of `Λ` which covers `Λ` — so that `Λ` is the filtered
colimit of `𝒜` — each member `A` of which is Artinian local, is essentially of finite type over
`k`, has `Λ` flat over it, and satisfies `𝔪_A Λ = 𝔪`.

The data is constructed from the source's own hypotheses in
`nonempty_coefficientSectionData_of_finite_h1Cotangent`, and the two steps are composed into the
lemma itself in `exists_directedOn_flat_essFiniteType`. -/
private theorem exists_directedOn_flat_essFiniteType_of_coefficientSectionData
    {k Λ : Type*} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ] (C : CoefficientSectionData k Λ) :
    ∃ 𝒜 : Set (Subalgebra k Λ), DirectedOn (· ≤ ·) 𝒜 ∧ (∀ y : Λ, ∃ A ∈ 𝒜, y ∈ A) ∧
      ∀ A ∈ 𝒜, ∃ (_ : IsArtinianRing A) (_ : IsLocalRing A),
        Module.Flat A Λ ∧ Algebra.EssFiniteType k A ∧
        Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ := by
  have hsurj := eval₂Hom_surjective_of_isSection C.σ C.residue_σ C.gen C.span_range_gen
    (isNilpotent_maximalIdeal_of_isArtinianRing Λ)
  obtain ⟨F₁, hF₁fg, -, hstage⟩ := exists_stage_subalgebra_of_coefficientSectionData C ∅
  refine ⟨{A | ∃ F : IntermediateField k (ResidueField Λ), F₁ ≤ F ∧ F.FG ∧
    A.toSubring = coefficientStage C.σ F C.gen}, ?_, ?_, ?_⟩
  · -- directedness: pass to the join of the two coefficient fields
    rintro A₁ ⟨G₁, hG₁, hG₁fg, hA₁⟩ A₂ ⟨G₂, hG₂, hG₂fg, hA₂⟩
    have hle : F₁ ≤ G₁ ⊔ G₂ := hG₁.trans le_sup_left
    have hfg : (G₁ ⊔ G₂).FG := IntermediateField.fg_sup hG₁fg hG₂fg
    obtain ⟨A₃, -, -, hA₃, -⟩ := hstage _ hle hfg
    refine ⟨A₃, ⟨_, hle, hfg, hA₃⟩, fun y hy => ?_, fun y hy => ?_⟩
    · change y ∈ A₃.toSubring
      rw [hA₃]
      exact coefficientStage_mono C.σ C.gen le_sup_left (by rw [← hA₁]; exact hy)
    · change y ∈ A₃.toSubring
      rw [hA₃]
      exact coefficientStage_mono C.σ C.gen le_sup_right (by rw [← hA₂]; exact hy)
  · -- the family covers `Λ`, since every element needs only finitely many coefficients
    intro y
    obtain ⟨F, hF, hfg, hy⟩ := exists_fg_mem_coefficientStage C.σ C.gen hsurj F₁ hF₁fg y
    obtain ⟨A, -, -, hA, -⟩ := hstage F hF hfg
    exact ⟨A, ⟨F, hF, hfg, hA⟩, by rw [← SetLike.mem_coe, ← Subalgebra.coe_toSubring, hA]; exact hy⟩
  · -- each stage has the four asserted properties
    rintro A ⟨F, hF, hfg, hA⟩
    obtain ⟨A', hart, hloc, hA', hflat, heft, hmax⟩ := hstage F hF hfg
    obtain rfl := Subalgebra.toSubring_injective (hA.trans hA'.symm)
    exact ⟨hart, hloc, hflat, heft, hmax⟩

/-- The data of `CoefficientSectionData` costs nothing when the residue field extension `K/k` is
finitely generated: take `F₀ = K`, for which the claim reads that the image of `k` lies in
`Ψ_σ(K[λ])`, which is all of `Λ`. The section is Lemma [stacks, 09EZ]. -/
theorem nonempty_coefficientSectionData (k Λ : Type*) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra.EssFiniteType k (ResidueField Λ)] :
    Nonempty (CoefficientSectionData k Λ) := by
  have hnil := isNilpotent_maximalIdeal_of_isArtinianRing Λ
  have hchar : CharP Λ p :=
    charP_of_injective_algebraMap (algebraMap k Λ).injective p
  obtain ⟨σ, hσ, -⟩ :=
    IsLocalRing.exists_residueField_section_compatible.{_, 0} (p := p) Λ hnil
  have hσ' : ∀ c, residue Λ (σ c) = c := fun c => by
    rw [← RingHom.comp_apply, hσ, RingHom.id_apply]
  obtain ⟨d, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal Λ))
  refine ⟨σ, hσ', d, gen, hgen, ⊤, IntermediateField.fg_top k (ResidueField Λ), fun a => ?_⟩
  obtain ⟨f, hf⟩ := eval₂Hom_surjective_of_isSection σ hσ' gen hgen hnil (algebraMap k Λ a)
  rw [← hf, MvPolynomial.coe_eval₂Hom]
  exact mem_coefficientStage_of_forall_coeff_mem σ gen ⊤ f fun _ => IntermediateField.mem_top

/-! ### Lifting ring maps out of a field of characteristic `p` -/

/-- A subring of a ring of characteristic `p` has characteristic `p`. -/
private theorem charP_subring {Λ : Type*} [CommRing Λ] (p : ℕ) [CharP Λ p] (R : Subring Λ) :
    CharP R p := by
  refine ⟨fun m => ?_⟩
  rw [← CharP.cast_eq_zero_iff Λ p m]
  refine ⟨fun h => by exact_mod_cast congrArg (Subring.subtype R) h,
    fun h => Subtype.ext (by push_cast; exact h)⟩

/-- A field `k` of characteristic `p` is formally smooth over `𝐅_p`, because `𝐅_p` is perfect;
hence a ring map out of `k` lifts along any surjection with nilpotent kernel.

This is the lifting step used twice in the proof of Stacks 07FG: once for the coefficient field
section `σ : K → Λ` and once for the map `k → A` of the source's argument. -/
@[ega "0 19.6.2" "special case"]
private theorem exists_ringHom_lift {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]
    {S T : Type*} [CommRing S] [CommRing T] [CharP S p]
    (g : S →+* T) (hg : Function.Surjective g) (hnil : IsNilpotent (RingHom.ker g))
    (f : k →+* T) : ∃ φ : k →+* S, g.comp φ = f := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra (ZMod p) S := ZMod.algebra S p
  let : Algebra (ZMod p) T := (g.comp (algebraMap (ZMod p) S)).toAlgebra
  have : Algebra.FormallySmooth (ZMod p) k :=
    (Algebra.FormallySmooth.iff_isSeparableExtension (ZMod p) k).2
      (Algebra.isSeparableExtension_of_perfectField _ _)
  have hfc : f.comp (algebraMap (ZMod p) k) = algebraMap (ZMod p) T := RingHom.ext_zmod _ _
  let fA : k →ₐ[ZMod p] T := { f with commutes' := fun z => RingHom.congr_fun hfc z }
  let gA : S →ₐ[ZMod p] T := { g with commutes' := fun _ => rfl }
  exact ⟨(Algebra.FormallySmooth.liftOfSurjective fA gA hg hnil).toRingHom,
    RingHom.ext (Algebra.FormallySmooth.liftOfSurjective_apply fA gA hg hnil)⟩

/-! ### Correcting a ring map by a derivation -/

/-- If `D : K → Λ` satisfies the Leibniz rule relative to a ring map `σ : K →+* Λ` and all
products of its values vanish, then `c ↦ σ c + D c` is again a ring map.

This is the step of the proof of Stacks 07FG at which the section `σ` is changed into `σ + D`. -/
def addDerivHom {K Λ : Type*} [CommRing K] [CommRing Λ] (σ : K →+* Λ) (D : K → Λ)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hleib : ∀ a b, D (a * b) = σ a * D b + σ b * D a)
    (hsq : ∀ a b, D a * D b = 0) : K →+* Λ where
  toFun c := σ c + D c
  map_one' := by
    have h1 : D 1 = D 1 + D 1 := by simpa using hleib 1 1
    have h : D 1 = 0 := by linear_combination -h1
    simp [h]
  map_mul' a b := by
    have h := hsq a b
    simp only [map_mul, hleib]
    linear_combination -h
  map_zero' := by
    have h0 : D 0 = D 0 + D 0 := by simpa using hadd 0 0
    have h : D 0 = 0 := by linear_combination -h0
    simp [h]
  map_add' a b := by simp only [map_add, hadd]; ring

/-- The ring map `addDerivHom σ D` sends `c` to `σ c + D c`. -/
@[simp]
lemma addDerivHom_apply {K Λ : Type*} [CommRing K] [CommRing Λ] (σ : K →+* Λ) (D : K → Λ)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hleib : ∀ a b, D (a * b) = σ a * D b + σ b * D a)
    (hsq : ∀ a b, D a * D b = 0) (c : K) : addDerivHom σ D hadd hleib hsq c = σ c + D c :=
  rfl

/-- Changing the coefficient map of an evaluation by a map `D` whose values annihilate every
nonconstant monomial in the chosen elements changes the value of the evaluation only by `D` of
the constant term. -/
private lemma eval₂_of_add {A Λ : Type*} [CommSemiring A] [CommRing Λ] {d : ℕ}
    (σ : A →+* Λ) (D : A → Λ) (hD0 : D 0 = 0) (lam : Fin d → Λ)
    (hD : ∀ (c : A) (e : Fin d →₀ ℕ), e ≠ 0 → D c * ∏ i, lam i ^ e i = 0)
    (τ : A →+* Λ) (hτ : ∀ c, τ c = σ c + D c) (f : MvPolynomial (Fin d) A) :
    MvPolynomial.eval₂ τ lam f = MvPolynomial.eval₂ σ lam f + D (f.coeff 0) := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  simp only [hτ, add_mul, Finset.sum_add_distrib]
  congr 1
  refine (Finset.sum_eq_single 0 (fun e he hne => hD _ e hne) ?_).trans ?_
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, hD0, zero_mul]
  · simp

open scoped TensorProduct

/-! ### The Jacobi–Zariski step -/

/-- Let `k ⊆ K` be fields with `dim_K H₁(L_{K/k}) < ∞` and let `M` be a `K`-vector space. Then
every derivation `θ : k → M` over `𝐙` agrees, after subtracting the restriction to `k` of a
derivation `D : K → M` over `𝐙`, with a map whose values lie in the `k`-span of a finite subset
of `M`.

This is the only place where `dim_K H₁(L_{K/k}) < ∞` is used in the proof of Stacks 07FG. The
Jacobi–Zariski sequence `H₁(L_{K/k}) → K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` exhibits the kernel of the
second map as the image of the first, hence as a finite-dimensional `K`-subspace; it therefore
involves only finitely many members of a chosen `k`-basis of `Ω_{k/𝐙}`, and `θ` may be corrected
to vanish on all the others. The base `𝐙` is used instead of `𝐅_p` only for convenience: a
derivation over `𝐙` is just an additive map satisfying the Leibniz rule, and exactness of the
Jacobi–Zariski sequence at `K ⊗_k Ω_{k/𝐙}` does not need `H₁(L_{K/𝐙}) = 0`. -/
private theorem exists_derivation_sub_mem_span {k K M : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M]
    [Module.Finite K (Algebra.H1Cotangent k K)] (θ : Derivation ℤ k M) :
    ∃ (D : Derivation ℤ K M) (s : Finset M), ∀ a : k,
      θ a - D (algebraMap k K a) ∈ Submodule.span k (s : Set M) := by
  classical
  obtain ⟨J, b⟩ := Module.Free.exists_basis k (Ω[k⁄ℤ])
  set θt : Ω[k⁄ℤ] →ₗ[k] M := θ.liftKaehlerDifferential with hθt
  set φ := KaehlerDifferential.mapBaseChange ℤ k K with hφ
  have hker : LinearMap.ker φ = LinearMap.range (Algebra.H1Cotangent.δ ℤ k K) :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ k K).linearMap_ker_eq
  have hfin : (LinearMap.ker φ).FG := by
    rw [← Module.Finite.iff_fg, hker]; exact Module.Finite.range _
  obtain ⟨t, ht⟩ := hfin
  set bK := b.baseChange K with hbK
  set J₀ : Finset J := t.biUnion fun x => (bK.repr x).support with hJ₀
  have hsub : LinearMap.ker φ ≤ Submodule.span K (bK '' (J₀ : Set J)) := by
    rw [← ht, Submodule.span_le]
    intro x hx
    exact (Module.Basis.mem_span_image bK).2 fun j hj =>
      Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, hx, hj⟩)
  -- the correction `ξ`, which only involves the basis vectors indexed by `J₀`
  set ξ : Ω[k⁄ℤ] →ₗ[k] M := b.constr k (fun j => if j ∈ J₀ then θt (b j) else 0) with hξ
  set η : Ω[k⁄ℤ] →ₗ[k] M := θt - ξ with hη
  set ηK : K ⊗[k] Ω[k⁄ℤ] →ₗ[K] M := LinearMap.liftBaseChange K η with hηK
  have hηJ₀ : ∀ j ∈ J₀, η (b j) = 0 := by
    intro j hj
    simp [hη, hξ, Module.Basis.constr_basis, hj]
  have hle : LinearMap.ker φ ≤ LinearMap.ker ηK := by
    refine hsub.trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hηK, hbK, Module.Basis.baseChange_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    exact hηJ₀ j hj
  -- `ηK` therefore factors through `Ω[K⁄𝐙]`
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Submodule.liftQ _ ηK hle).comp φ.quotKerEquivRange.symm.toLinearMap)
  have hgφ : ∀ x, g (φ x) = ηK x := by
    intro x
    have h1 := LinearMap.congr_fun hg ⟨φ x, ⟨x, rfl⟩⟩
    have h2 : φ.quotKerEquivRange.symm ⟨φ x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x :=
      φ.quotKerEquivRange.symm_apply_eq.2
        (Subtype.ext (LinearMap.quotKerEquivRange_apply_mk φ x).symm)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2,
      Submodule.liftQ_apply] at h1
    exact h1
  refine ⟨KaehlerDifferential.linearMapEquivDerivation ℤ K g,
    J₀.image fun j => θt (b j), fun a => ?_⟩
  have hmap : φ ((1 : K) ⊗ₜ[k] KaehlerDifferential.D ℤ k a)
      = KaehlerDifferential.D ℤ K (algebraMap k K a) := by
    rw [hφ, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  have hval : (KaehlerDifferential.linearMapEquivDerivation ℤ K g) (algebraMap k K a)
      = θ a - ξ (KaehlerDifferential.D ℤ k a) := by
    have h3 : (KaehlerDifferential.linearMapEquivDerivation ℤ K g) (algebraMap k K a)
        = g (KaehlerDifferential.D ℤ K (algebraMap k K a)) := rfl
    rw [h3, ← hmap, hgφ, hηK, LinearMap.liftBaseChange_tmul, one_smul, hη]
    simp [hθt, Derivation.liftKaehlerDifferential_comp_D]
  rw [hval, sub_sub_cancel]
  have hrange : ξ (KaehlerDifferential.D ℤ k a) ∈ LinearMap.range ξ := ⟨_, rfl⟩
  rw [hξ, Module.Basis.constr_range] at hrange
  refine Submodule.span_le.2 ?_ hrange
  rintro _ ⟨j, rfl⟩
  by_cases hj : j ∈ J₀
  · simp only [hj, ↓reduceIte]
    exact Submodule.subset_span (by simpa using ⟨j, hj, rfl⟩)
  · simp [hj]

/-! ### The central claim of Stacks 07FG -/

universe u

/-- The central claim in the proof of Stacks 07FG. Let `k` be a field of characteristic `p > 0`,
let `K/k` be a field extension with `dim_K H₁(L_{K/k}) < ∞`, and let `Λ` be a `k`-algebra with a
surjection `π : Λ → K` of `k`-algebras whose kernel `𝔪` is nilpotent and generated by
`x₁, …, x_d`. Then there are a ring-theoretic section `σ : K → Λ` of `π` and a finitely generated
intermediate field `k ⊆ F ⊆ K` such that the image of `k` in `Λ` lies in `Ψ_σ(F[x₁, …, x_d])`.

The source's induction on the least `n` with `𝔪 ^ n = 0` is run here with `π` as a parameter
rather than `IsLocalRing.residue`, because the induction replaces `Λ` by `Λ/𝔪^{n-1}` while
keeping the residue field `K` fixed. -/
theorem exists_section_mem_coefficientStage {p : ℕ} [Fact p.Prime] {k K : Type*}
    [Field k] [Field K] [Algebra k K] [CharP k p]
    [Module.Finite K (Algebra.H1Cotangent k K)] (n : ℕ) :
    ∀ (Λ : Type u) [CommRing Λ] [Algebra k Λ] (π : Λ →+* K), Function.Surjective π →
      (∀ a : k, π (algebraMap k Λ a) = algebraMap k K a) → RingHom.ker π ^ n = ⊥ →
      ∀ (d : ℕ) (x : Fin d → Λ), Ideal.span (Set.range x) = RingHom.ker π →
      ∃ σ : K →+* Λ, (∀ c, π (σ c) = c) ∧ ∃ F : IntermediateField k K, F.FG ∧
        ∀ a : k, algebraMap k Λ a ∈ coefficientStage σ F x := by
  induction n with
  | zero =>
    intro Λ _ _ π _ _ hker _ _ _
    rw [pow_zero, Ideal.one_eq_top] at hker
    have h1 : (1 : Λ) = 0 := Ideal.mem_bot.mp (hker ▸ Submodule.mem_top)
    exact absurd (show (1 : K) = 0 by rw [← map_one π, h1, map_zero]) one_ne_zero
  | succ n ih =>
    classical
    intro Λ _ _ π hπ hcompat hker d x hx
    have hnt : Nontrivial Λ :=
      ⟨⟨1, 0, fun h => one_ne_zero (show (1 : K) = 0 by rw [← map_one π, h, map_zero])⟩⟩
    have hcharΛ : CharP Λ p := charP_of_injective_algebraMap (algebraMap k Λ).injective p
    have hcharK : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `𝔪 = 0`: the quotient map is an isomorphism and `F = k` already works
      rw [pow_one] at hker
      have hinj : Function.Injective π := (RingHom.injective_iff_ker_eq_bot π).2 hker
      let e : Λ ≃+* K := RingEquiv.ofBijective π ⟨hinj, hπ⟩
      refine ⟨(e.symm : K →+* Λ), fun c => e.apply_symm_apply c, ⊥, ⟨∅, by simp⟩, fun a => ?_⟩
      have h : algebraMap k Λ a = (e.symm : K →+* Λ) (algebraMap k K a) := by
        rw [← hcompat a]
        exact (e.symm_apply_apply (algebraMap k Λ a)).symm
      rw [h]
      exact mem_coefficientStage_of_mem _ x ⊥
        ⟨algebraMap k K a, IntermediateField.mem_bot.2 ⟨a, rfl⟩⟩
    · -- the inductive step: correct a lift of the section modulo `I = 𝔪 ^ n`
      obtain ⟨I, hIdef⟩ : ∃ I : Ideal Λ, I = RingHom.ker π ^ n := ⟨_, rfl⟩
      have hIm : I ≤ RingHom.ker π := hIdef ▸ Ideal.pow_le_self (by omega)
      have hmI : ∀ y ∈ RingHom.ker π, ∀ z ∈ I, y * z = 0 := by
        intro y hy z hz
        have h : y * z ∈ RingHom.ker π ^ (n + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hy (hIdef ▸ hz)
        rw [hker] at h
        exact h
      have hII : ∀ y ∈ I, ∀ z ∈ I, y * z = 0 := fun y hy => hmI y (hIm hy)
      have hInil : IsNilpotent I := ⟨2, le_antisymm (by
        rw [pow_two]
        exact Ideal.mul_le.2 fun y hy z hz => Ideal.mem_bot.2 (hII y hy z hz)) bot_le⟩
      -- the quotient `Λ/I`, with the same residue field `K`
      have hkermk : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
      let π' : (Λ ⧸ I) →+* K := Ideal.Quotient.lift I π hIm
      have hπ'mk : ∀ y, π' (Ideal.Quotient.mk I y) = π y := fun _ => rfl
      have hkerπ' : RingHom.ker π' = Ideal.map (Ideal.Quotient.mk I) (RingHom.ker π) :=
        Ideal.ker_quotient_lift π hIm
      have hπ'surj : Function.Surjective π' := fun c => by
        obtain ⟨y, rfl⟩ := hπ c
        exact ⟨Ideal.Quotient.mk I y, rfl⟩
      have hker' : RingHom.ker π' ^ n = ⊥ := by
        rw [hkerπ', ← Ideal.map_pow, ← hIdef]
        exact Ideal.map_quotient_self I
      have hcompat' : ∀ a : k, π' (algebraMap k (Λ ⧸ I) a) = algebraMap k K a := fun a => by
        rw [show algebraMap k (Λ ⧸ I) a = Ideal.Quotient.mk I (algebraMap k Λ a) from rfl,
          hπ'mk, hcompat]
      have hx' : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) = RingHom.ker π' := by
        rw [hkerπ', ← hx, Ideal.map_span, ← Set.range_comp]
        rfl
      obtain ⟨σ', hσ', F, hFfg, hF⟩ :=
        ih (Λ ⧸ I) π' hπ'surj hcompat' hker' d (fun i => Ideal.Quotient.mk I (x i)) hx'
      -- lift the section along `Λ → Λ/I`
      obtain ⟨σ, hσcomp⟩ := exists_ringHom_lift (k := K) (p := p) (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective (by rw [hkermk]; exact hInil) σ'
      have hmkσ : ∀ c, Ideal.Quotient.mk I (σ c) = σ' c := fun c => RingHom.congr_fun hσcomp c
      have hπσ : ∀ c, π (σ c) = c := fun c => by rw [← hπ'mk, hmkσ, hσ']
      -- the stage of `F` in `Λ` surjects onto the stage of `F` in `Λ/I`
      have hcomp : ∀ f : MvPolynomial (Fin d) F,
          Ideal.Quotient.mk I (MvPolynomial.eval₂ (σ.comp F.val.toRingHom) x f)
            = MvPolynomial.eval₂ (σ'.comp F.val.toRingHom)
                (fun i => Ideal.Quotient.mk I (x i)) f := fun f => by
        rw [MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk I),
          show (Ideal.Quotient.mk I).comp (σ.comp F.val.toRingHom)
            = σ'.comp F.val.toRingHom from RingHom.ext fun c => hmkσ _]
        rfl
      -- `τ' : k → R'` and its lift `ρ : k → R`
      have hRR' : ∀ y ∈ coefficientStage σ F x,
          Ideal.Quotient.mk I y ∈
            coefficientStage σ' F (fun i => Ideal.Quotient.mk I (x i)) := by
        rintro _ ⟨f, rfl⟩
        refine ⟨f, ?_⟩
        simp only [MvPolynomial.coe_eval₂Hom]
        exact (hcomp f).symm
      have hR'R : ∀ y' ∈ coefficientStage σ' F (fun i => Ideal.Quotient.mk I (x i)),
          ∃ y ∈ coefficientStage σ F x, Ideal.Quotient.mk I y = y' := by
        rintro _ ⟨f, rfl⟩
        refine ⟨MvPolynomial.eval₂Hom (σ.comp F.val.toRingHom) x f, ⟨f, rfl⟩, ?_⟩
        simp only [MvPolynomial.coe_eval₂Hom]
        exact hcomp f
      let gR : coefficientStage σ F x →+*
          coefficientStage σ' F (fun i => Ideal.Quotient.mk I (x i)) :=
        RingHom.codRestrict ((Ideal.Quotient.mk I).comp (coefficientStage σ F x).subtype) _
          fun y => hRR' y y.2
      have hgRval : ∀ y : coefficientStage σ F x,
          ((gR y : Λ ⧸ I)) = Ideal.Quotient.mk I (y : Λ) := fun _ => rfl
      have hgRsurj : Function.Surjective gR := by
        intro y'
        obtain ⟨y, hy, hmky⟩ := hR'R y' y'.2
        exact ⟨⟨y, hy⟩, Subtype.ext hmky⟩
      have hgRkerI : ∀ y : coefficientStage σ F x, y ∈ RingHom.ker gR → (y : Λ) ∈ I := by
        intro y hy
        rw [RingHom.mem_ker] at hy
        have h : Ideal.Quotient.mk I (y : Λ) = 0 := by rw [← hgRval y, hy]; rfl
        rwa [← hkermk, RingHom.mem_ker]
      have hgRnil : IsNilpotent (RingHom.ker gR) := ⟨2, le_antisymm (by
        rw [pow_two]
        refine Ideal.mul_le.2 fun y hy z hz => Ideal.mem_bot.2 (Subtype.ext ?_)
        simpa using hII _ (hgRkerI y hy) _ (hgRkerI z hz)) bot_le⟩
      have hiR' : ∀ a : k, ((Ideal.Quotient.mk I).comp (algebraMap k Λ)) a ∈
          coefficientStage σ' F (fun i => Ideal.Quotient.mk I (x i)) := fun a => hF a
      have hcharR : CharP (coefficientStage σ F x) p := charP_subring p _
      obtain ⟨ψ, hψ⟩ := exists_ringHom_lift (p := p) gR hgRsurj hgRnil
        (RingHom.codRestrict ((Ideal.Quotient.mk I).comp (algebraMap k Λ)) _ hiR')
      let ρ : k →+* Λ := (coefficientStage σ F x).subtype.comp ψ
      have hρR : ∀ a, ρ a ∈ coefficientStage σ F x := fun a => (ψ a).2
      have hρI : ∀ a, algebraMap k Λ a - ρ a ∈ I := by
        intro a
        have h2 : Ideal.Quotient.mk I (ρ a) = Ideal.Quotient.mk I (algebraMap k Λ a) :=
          congrArg (fun z : coefficientStage σ' F (fun i => Ideal.Quotient.mk I (x i)) =>
            (z : Λ ⧸ I)) (RingHom.congr_fun hψ a)
        rw [← hkermk, RingHom.mem_ker, map_sub, h2, sub_self]
      -- `I` is a `K`-vector space, because `𝔪 I = 0`
      let instKI : Module K ↥I := Module.compHom (↥I) σ
      have hKsmul : ∀ (c : K) (z : ↥I), ((c • z : ↥I) : Λ) = σ c * (z : Λ) := fun _ _ => rfl
      have hksmul : ∀ (a : k) (z : ↥I), ((a • z : ↥I) : Λ) = algebraMap k Λ a * (z : Λ) :=
        fun a z => by rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
      have hσm : ∀ a : k, σ (algebraMap k K a) - algebraMap k Λ a ∈ RingHom.ker π := fun a => by
        rw [RingHom.mem_ker, map_sub, hπσ, hcompat, sub_self]
      have htow : IsScalarTower k K ↥I := by
        refine ⟨fun a c z => Subtype.ext ?_⟩
        rw [hKsmul, hksmul, hKsmul, Algebra.smul_def, map_mul]
        linear_combination hmI _ (hσm a) _ (I.mul_mem_left (σ c) z.2)
      -- the derivation `θ = i - Ψ_σ ∘ τ`
      let θadd : k →+ ↥I :=
        { toFun := fun a => ⟨algebraMap k Λ a - ρ a, hρI a⟩
          map_zero' := by apply Subtype.ext; simp
          map_add' := fun a b => by apply Subtype.ext; simp; ring }
      have hθval : ∀ a : k, ((θadd a : ↥I) : Λ) = algebraMap k Λ a - ρ a := fun _ => rfl
      let θ : Derivation ℤ k ↥I :=
        { θadd.toIntLinearMap with
          map_one_eq_zero' := by apply Subtype.ext; simp [hθval]
          leibniz' := fun a b => by
            apply Subtype.ext
            have h := hII _ (hρI a) _ (hρI b)
            rw [show ((a • (θadd.toIntLinearMap b) + b • (θadd.toIntLinearMap a) : ↥I) : Λ)
              = algebraMap k Λ a * (algebraMap k Λ b - ρ b)
                + algebraMap k Λ b * (algebraMap k Λ a - ρ a) by
                  rw [AddSubmonoid.coe_add, hksmul, hksmul]; rfl]
            rw [show ((θadd.toIntLinearMap (a * b) : ↥I) : Λ)
              = algebraMap k Λ (a * b) - ρ (a * b) from rfl, map_mul, map_mul]
            linear_combination -h }
      have hθa : ∀ a : k, ((θ a : ↥I) : Λ) = algebraMap k Λ a - ρ a := fun _ => rfl
      -- the Jacobi-Zariski step
      obtain ⟨D, s, hs⟩ := exists_derivation_sub_mem_span (K := K) θ
      have hDI : ∀ c, ((D c : ↥I) : Λ) ∈ I := fun c => (D c).2
      have hDadd : ∀ c c', ((D (c + c') : ↥I) : Λ)
          = ((D c : ↥I) : Λ) + ((D c' : ↥I) : Λ) := fun c c' => by
        rw [map_add, AddSubmonoid.coe_add]
      have hDleib : ∀ c c', ((D (c * c') : ↥I) : Λ)
          = σ c * ((D c' : ↥I) : Λ) + σ c' * ((D c : ↥I) : Λ) := fun c c' => by
        rw [D.leibniz, AddSubmonoid.coe_add, hKsmul, hKsmul]
      have hDsq : ∀ c c', ((D c : ↥I) : Λ) * ((D c' : ↥I) : Λ) = 0 :=
        fun c c' => hII _ (hDI c) _ (hDI c')
      let σ₁ : K →+* Λ := addDerivHom σ (fun c => ((D c : ↥I) : Λ)) hDadd hDleib hDsq
      have hσ₁ : ∀ c, σ₁ c = σ c + ((D c : ↥I) : Λ) := fun _ => rfl
      have hπσ₁ : ∀ c, π (σ₁ c) = c := fun c => by
        have h : π ((D c : ↥I) : Λ) = 0 := by
          rw [← RingHom.mem_ker]; exact hIm (hDI c)
        rw [hσ₁, map_add, hπσ, h, add_zero]
      -- the monomial estimate comparing `Ψ_σ` and `Ψ_{σ₁}`
      have hmono : ∀ y ∈ I, ∀ e : Fin d →₀ ℕ, e ≠ 0 → y * ∏ i, x i ^ e i = 0 := by
        intro y hy e he
        obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.2 he
        have hxm : ∏ i, x i ^ e i ∈ RingHom.ker π := by
          rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)]
          refine Ideal.mul_mem_left _ _ ?_
          rw [← hx]
          exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self j)) _
            (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hj))
        rw [mul_comm]
        exact hmI _ hxm y hy
      -- enlarge `F` so that the finitely many values of the correction lie in the stage
      have hmnil : IsNilpotent (RingHom.ker π) := ⟨n + 1, hker⟩
      obtain ⟨F₁, hFF₁, hF₁fg, hF₁s⟩ :=
        exists_fg_subset_stage σ₁ x (eval₂Hom_surjective_of_section π σ₁ hπσ₁ x hx hmnil)
          F hFfg (s.image fun z : ↥I => (z : Λ))
      refine ⟨σ₁, hπσ₁, F₁, hF₁fg, fun a => ?_⟩
      obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin d) F,
          MvPolynomial.eval₂ (σ.comp F.val.toRingHom) x f = ρ a := by
        obtain ⟨f, hf⟩ := hρR a
        exact ⟨f, by simpa only [MvPolynomial.coe_eval₂Hom] using hf⟩
      have hchange : MvPolynomial.eval₂ (σ₁.comp F.val.toRingHom) x f
          = ρ a + ((D ((f.coeff 0 : F) : K) : ↥I) : Λ) := by
        rw [eval₂_of_add (σ.comp F.val.toRingHom) (fun c : F => ((D ((c : F) : K) : ↥I) : Λ))
          (by simp) x (fun c e he => hmono _ (hDI _) e he) _ (fun c => rfl) f, hf]
      have hcoeff : ((f.coeff 0 : F) : K) = algebraMap k K a := by
        have h1 : π (ρ a) = algebraMap k K a := by
          have h : algebraMap k Λ a - ρ a ∈ RingHom.ker π := hIm (hρI a)
          rw [RingHom.mem_ker, map_sub, sub_eq_zero, hcompat] at h
          exact h.symm
        have h2 : π (MvPolynomial.eval₂ (σ.comp F.val.toRingHom) x f)
            = ((f.coeff 0 : F) : K) := by
          rw [MvPolynomial.eval₂_comp_left π,
            show π.comp (σ.comp F.val.toRingHom) = F.val.toRingHom from
              RingHom.ext fun c => hπσ _,
            show (⇑π ∘ x) = (fun _ : Fin d => (0 : K)) from funext fun i => by
              rw [Function.comp_apply, ← RingHom.mem_ker, ← hx]
              exact Ideal.subset_span ⟨i, rfl⟩,
            ← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_zero'_apply,
            MvPolynomial.constantCoeff_eq]
          rfl
        rw [← h2, hf, h1]
      -- `i(a)` is the corrected evaluation plus the correction term
      have hmain : algebraMap k Λ a
          = MvPolynomial.eval₂ (σ₁.comp F.val.toRingHom) x f
            + ((θ a - D (algebraMap k K a) : ↥I) : Λ) := by
        rw [hchange, hcoeff, AddSubgroupClass.coe_sub, hθa]
        ring
      rw [hmain]
      refine Subring.add_mem _ (coefficientStage_mono σ₁ x hFF₁ ⟨f, ?_⟩) ?_
      · rw [MvPolynomial.coe_eval₂Hom]
      · refine Submodule.span_induction
          (p := fun (z : ↥I) _ => (z : Λ) ∈ coefficientStage σ₁ F₁ x) ?_ ?_ ?_ ?_ (hs a)
        · exact fun z hz => hF₁s _ (Finset.mem_image.2 ⟨z, hz, rfl⟩)
        · simp only [ZeroMemClass.coe_zero]
          exact Subring.zero_mem _
        · exact fun z w _ _ hz hw => by
            simpa only [Submodule.coe_add] using Subring.add_mem _ hz hw
        · intro c z _ hz
          have hzI : (z : Λ) ∈ I := z.2
          have hrw : algebraMap k Λ c * (z : Λ) = σ₁ (algebraMap k K c) * (z : Λ) := by
            rw [hσ₁]
            have h1 := hmI _ (hσm c) _ hzI
            have h2 := hII _ (hDI (algebraMap k K c)) _ hzI
            linear_combination -h1 - h2
          rw [hksmul, hrw]
          exact Subring.mul_mem _ (mem_coefficientStage_of_mem σ₁ x F₁
            ⟨algebraMap k K c, F₁.algebraMap_mem c⟩) hz

/-- **Stacks 07FG**, the central claim of its proof: the data of `CoefficientSectionData` exists
for every Artinian local algebra over a field of characteristic `p > 0` whose residue field
extension has `dim_K H₁(L_{K/k}) < ∞`.

No finiteness is assumed of the residue field extension itself; the transcendence degree of `K`
over `k` may be infinite. -/
@[stacks 07FG "The central claim of the source's proof, the only place where char k = p and
dim H₁(L_{K/k}) < ∞ are used: there exist a ring-theoretic section σ : K → Λ of the residue map,
generators λ₁, …, λ_d of 𝔪, and a finitely generated k ⊆ F₀ ⊆ K with the image of k in Λ
contained in Ψ_σ(F₀[λ₁, …, λ_d]). The source's induction on the nilpotency order of 𝔪 is
followed, including the correction of σ by a derivation K → 𝔪^{n-1} read off the Jacobi-Zariski
sequence. NOT covered: the conclusion of the lemma, which is proved from this claim in
`exists_directedOn_flat_essFiniteType`."]
theorem nonempty_coefficientSectionData_of_finite_h1Cotangent {k Λ : Type*} [Field k]
    [CommRing Λ] [Algebra k Λ] [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Module.Finite (ResidueField Λ) (Algebra.H1Cotangent k (ResidueField Λ))] :
    Nonempty (CoefficientSectionData k Λ) := by
  have hnil := isNilpotent_maximalIdeal_of_isArtinianRing Λ
  obtain ⟨n, hn⟩ := hnil
  rw [Ideal.zero_eq_bot] at hn
  obtain ⟨d, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal Λ))
  have hkerres : RingHom.ker (residue Λ) = maximalIdeal Λ := IsLocalRing.ker_residue
  obtain ⟨σ, hσ, F, hFfg, hF⟩ := exists_section_mem_coefficientStage (p := p) (k := k)
    (K := ResidueField Λ) n Λ (residue Λ) residue_surjective (fun _ => rfl)
    (by rw [hkerres]; exact hn) d gen (by rw [hkerres]; exact hgen)
  exact ⟨σ, hσ, d, gen, hgen, F, hFfg, hF⟩

/-- **Stacks 07FG**. Let `k` be a field of characteristic `p > 0` and let `(Λ, 𝔪, K)` be an
Artinian local `k`-algebra with `dim_K H₁(L_{K/k}) < ∞`. Then there is a directed family `𝒜` of
`k`-subalgebras of `Λ` which covers `Λ` — so that `Λ` is the filtered colimit of `𝒜` — each
member `A` of which is Artinian local, is essentially of finite type over `k`, has `Λ` flat over
it, and satisfies `𝔪_A Λ = 𝔪`. -/
@[stacks 07FG "The lemma, under the source's own hypotheses and nothing else: char k = p > 0, Λ
an Artinian local k-algebra, and dim H₁(L_{K/k}) < ∞, with no finiteness assumed of K/k. The
conclusion is read in the directed-union form in which the source itself reads it (flatness of
A → Λ out of a local ring makes it injective, as the source's first line observes): the
approximating subalgebras are the stages Ψ_σ(F[λ]) for finitely generated F₀ ≤ F ≤ K, and they
are Artinian local k-subalgebras of Λ, essentially of finite type over k, with Λ flat (indeed
free) over each and with 𝔪_A Λ = 𝔪, and they are directed and cover Λ. The section σ and the
finitely generated F₀ are produced by the source's induction on the nilpotency order of 𝔪 in
`nonempty_coefficientSectionData_of_finite_h1Cotangent`, the only place where char k = p and
dim H₁(L_{K/k}) < ∞ are used; the properties of the stages are
`exists_directedOn_flat_essFiniteType_of_coefficientSectionData`."]
theorem exists_directedOn_flat_essFiniteType {k Λ : Type*} [Field k] [CommRing Λ]
    [Algebra k Λ] [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Module.Finite (ResidueField Λ) (Algebra.H1Cotangent k (ResidueField Λ))] :
    ∃ 𝒜 : Set (Subalgebra k Λ), DirectedOn (· ≤ ·) 𝒜 ∧ (∀ y : Λ, ∃ A ∈ 𝒜, y ∈ A) ∧
      ∀ A ∈ 𝒜, ∃ (_ : IsArtinianRing A) (_ : IsLocalRing A),
        Module.Flat A Λ ∧ Algebra.EssFiniteType k A ∧
        Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ :=
  exists_directedOn_flat_essFiniteType_of_coefficientSectionData
    (nonempty_coefficientSectionData_of_finite_h1Cotangent p).some

/-- **Stacks 07FG**, under the name used for it in the documentation of the Stacks 07FH material
in the second half of this file. The statement is that of
`exists_directedOn_flat_essFiniteType`. -/
@[stacks 07FG "The lemma, under the source's own hypotheses: the statement of
`exists_directedOn_flat_essFiniteType`, to which this reduces, under the name used for it in the
documentation of the Stacks 07FH material in the second half of this file."]
alias exists_directedOn_flat_essFiniteType_of_charP :=
  Stacks.Smoothing.exists_directedOn_flat_essFiniteType


/-! ### Stacks 07FG with a prescribed residue field -/

/-- The residue of an element of a stage lies in the coefficient field: a stage is generated by
the image under `σ` of `F`, whose residues are the elements of `F`, together with elements of the
maximal ideal, whose residues vanish. -/
lemma residue_mem_of_mem_coefficientStage {k Λ : Type*} [Field k] [CommRing Λ]
    [Algebra k Λ] [IsLocalRing Λ] (σ : ResidueField Λ →+* Λ) (hsec : ∀ c, residue Λ (σ c) = c)
    {d : ℕ} (x : Fin d → Λ) (hxm : ∀ i, x i ∈ maximalIdeal Λ)
    (F : IntermediateField k (ResidueField Λ)) {y : Λ} (hy : y ∈ coefficientStage σ F x) :
    residue Λ y ∈ F := by
  obtain ⟨f, rfl⟩ := hy
  refine MvPolynomial.induction_on
    (motive := fun g => residue Λ (MvPolynomial.eval₂Hom (σ.comp F.val.toRingHom) x g) ∈ F)
    f ?_ ?_ ?_
  · intro a
    simp [hsec]
  · intro q r hq hr
    simp only [map_add]
    exact add_mem hq hr
  · intro q i hq
    have h0 : residue Λ (x i) = 0 := (residue_eq_zero_iff _).mpr (hxm i)
    simp [h0]

/-- **Stacks 07FG with the residue field prescribed.** Let `k` be a field of characteristic
`p > 0` and let `(Λ, 𝔪, K)` be an Artinian local `k`-algebra with `dim_K H₁(L_{K/k}) < ∞`, and let
`S` be a finite subset of `Λ`. Then there is a finitely generated intermediate field
`k ⊆ F₀ ⊆ K` such that *every* finitely generated `F` with `F₀ ⊆ F ⊆ K` is realized as the
residue field of an approximating subalgebra of Stacks 07FG containing `S`: an Artinian local
`k`-subalgebra `A` of `Λ`, essentially of finite type over `k`, with `Λ` flat over `A` and
`𝔪_A Λ = 𝔪`, whose image under the residue map of `Λ` is exactly `F`.

The members of the directed family of `exists_directedOn_flat_essFiniteType_of_charP` are the
stages `Ψ_σ(F[λ])`, whose residue image is the coefficient field `F`; this records that, which
the bare statement of the tag does not. It is what lets a *basis* of `Ω_{F/k}` be chosen among
differentials of residues of prescribed elements of `Λ`. -/
theorem exists_subalgebra_residueField_image_eq_of_charP {k Λ : Type*} [Field k] [CommRing Λ]
    [Algebra k Λ] [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Module.Finite (ResidueField Λ) (Algebra.H1Cotangent k (ResidueField Λ))] (S : Finset Λ) :
    ∃ F₀ : IntermediateField k (ResidueField Λ), F₀.FG ∧
      ∀ F : IntermediateField k (ResidueField Λ), F₀ ≤ F → F.FG →
        ∃ (A : Subalgebra k Λ) (_ : IsArtinianRing A) (_ : IsLocalRing A),
          (∀ y ∈ S, y ∈ A) ∧ Module.Flat A Λ ∧ Algebra.EssFiniteType k A ∧
          Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ ∧
          (∀ y ∈ A, residue Λ y ∈ F) ∧ ∀ c ∈ F, ∃ y ∈ A, residue Λ y = (c : ResidueField Λ) := by
  obtain ⟨C⟩ := nonempty_coefficientSectionData_of_finite_h1Cotangent (k := k) (Λ := Λ) p
  have hxm : ∀ i, C.gen i ∈ maximalIdeal Λ := fun i =>
    C.span_range_gen ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨F₁, hF₁fg, hSF₁, hstage⟩ := exists_stage_subalgebra_of_coefficientSectionData C S
  refine ⟨F₁, hF₁fg, fun F hF hfg => ?_⟩
  obtain ⟨A, hart, hloc, hA, hflat, heft, hmax⟩ := hstage F hF hfg
  have hAmem : ∀ y, y ∈ A ↔ y ∈ coefficientStage C.σ F C.gen := fun y => by
    rw [← hA]; exact Iff.rfl
  refine ⟨A, hart, hloc, fun y hy => ?_, hflat, heft, hmax, fun y hy => ?_, fun c hc => ?_⟩
  · exact (hAmem y).2 (coefficientStage_mono C.σ C.gen hF (hSF₁ y hy))
  · exact residue_mem_of_mem_coefficientStage C.σ C.residue_σ C.gen hxm F ((hAmem y).1 hy)
  · exact ⟨C.σ c, (hAmem _).2 (mem_coefficientStage_of_mem C.σ C.gen F ⟨c, hc⟩), C.residue_σ c⟩

end Stacks.Smoothing
