module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentRationalIntersectionPoint
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality

/-!
# Separability of the fields of constants of the components in the equality case

In the situation of [Stacks, Tag 0C61] let `x` be a `k`-rational point of `X_k` at which
`X_k ⟶ Spec(k)` is smooth, and suppose equality holds in [Stacks, Tag 0CEA]:
`dim_k H¹((X_k)_red, 𝒪) = g_top + g_geom(X_k/k)`. [Stacks, Tag 0CEE] then says that every
component `C` of `X_k` not through `x` is smooth over `κ_C = H⁰(C, 𝒪_C)`, and the source adds that
`κ_C/k` is separable. That addition is false in general (see the module documentation of
`StacksFrontier/AlgebraicGeometry/Curves/Models/ReducedFibreGenusEquality.lean`): the base proves
separability only for components of positive genus.

The proof of the semistable reduction theorem in genus at least two ([Stacks, Section 0CEI])
uses the false addition: "Looking at Lemma 0CEE we conclude that every irreducible component of
`X_k` is smooth over `k`". This file fills that gap in the situation where it is used: when
moreover `X` is a minimal model and every multiplicity `mᵢ` is `1`, every `κ_C/k` is separable.

## The argument

Equality in [Stacks, Tag 0CEA] forces every step of its induction to have no slack, in any order
of the induction (`AlgebraicGeometry.NumericalType.genusDefect_le_genusDefect_univ`). Let `C_i` be
a component with `[κ_i : k] > 1` and genus `0`. Take a set `s` of components containing the
component through `x`, not containing `C_i`, with nonnegative defect and maximal; then `C_i` is
the only component outside `s` meeting `s`, and no slack forces `C_i` to meet `s` in a single
component with intersection number `[κ_i : k]`. As `mᵢ = 1` for all `i`, the row of `C_i` in the
intersection matrix sums to zero; minimality excludes `(C_i · C_i) = -[κ_i : k]`, so `C_i` meets
a component `C_V` outside `s ∪ {C_i}`. No slack for adding `C_V` to `s ∪ {C_i}` gives
`(C_V · C_i) = [κ_V : k]`, and `s ∪ {C_i}` is a larger set avoiding `C_V`. By induction on the size
of `s`, `κ_V/k` is separable. Finally `(C_V · C_i) = [κ_V : k]` makes `C_V ∩ C_i` a scheme with
ring of functions `κ_V` which is also a closed subscheme of `C_i`, so `κ_i` embeds into `κ_V`
over `k` and is separable. Components of positive genus are handled by [Stacks, Tag 0CEE], and
components with `[κ_i : k] = 1` trivially.

## Main results

* `AlgebraicGeometry.NumericalType.forall_of_genusDefect_univ_le_zero` — the combinatorial core.
* `RegularProperModelSituation.isSeparable_of_specialFiberIntersectionMatrix_eq_weight` —
  `(C_Z · C_W) = [κ_Z : k]` and `κ_Z/k` separable imply `κ_W/k` separable.

## References

* [Stacks Project, Tag 0CEE](https://stacks.math.columbia.edu/tag/0CEE)
* [Stacks Project, Tag 0CEA](https://stacks.math.columbia.edu/tag/0CEA)
* [Stacks Project, Section 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

variable (T : NumericalType)

private theorem card_univ_sdiff_insert_lt {n : ℕ} {s : Finset (Fin n)} {W : Fin n} (hW : W ∉ s) :
    (Finset.univ \ insert W s).card < (Finset.univ \ s).card := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨W, by simp [hW], by simp⟩
  exact Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert _ _)

/-- If the total defect is not positive, adding a component `W` meeting `s` to a set `s` of
nonnegative defect keeps the defect nonnegative and has no slack. -/
private theorem genusDefect_insert_nonneg_and_addSlack_nonpos
    {χ : Finset (Fin T.componentCount) → ℤ} {c gg : Fin T.componentCount → ℤ}
    (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
    (hgg : ∀ i, gg i ≤ T.weight i - c i) (hΔ : T.genusDefect χ gg Finset.univ ≤ 0)
    {s : Finset (Fin T.componentCount)} {W j₀ : Fin T.componentCount} (hj₀ : j₀ ∈ s)
    (hW : W ∉ s) (hD : 0 ≤ T.genusDefect χ gg s) (hmeet : ∃ j ∈ s, 0 < T.intersection W j) :
    0 ≤ T.genusDefect χ gg (insert W s) ∧ T.addSlack W s ≤ 0 := by
  obtain ⟨j, hj, hpos⟩ := hmeet
  have h1 := T.genusDefect_insert χ c gg hstep s hW
  have h2 := T.addSlack_nonneg s hW hj hpos
  have h3 := hgg W
  have h4 := T.genusDefect_le_genusDefect_univ χ c gg hstep hgg j₀ (insert W s)
    (Finset.mem_insert_of_mem hj₀)
  constructor <;> linarith

/-- If `W ∉ s` has weight `w_W > 1`, meets `s`, and adding it to `s` has no slack, then the
intersection of `W` with `s` is `w_W`. -/
private theorem sum_intersection_eq_weight_of_addSlack_nonpos {s : Finset (Fin T.componentCount)}
    {W : Fin T.componentCount} (hW : W ∉ s) (hsl : T.addSlack W s ≤ 0) (hw : 1 < T.weight W)
    {a : Fin T.componentCount} (ha : a ∈ s) (hpos : 0 < T.intersection W a) :
    ∑ j ∈ s, T.intersection W j = T.weight W := by
  classical
  set P' := s.filter fun j => 0 < T.intersection W j with hP'
  have hPw : ∀ j ∈ P', T.intersection W j = T.weight W := fun j hj =>
    T.intersection_eq_weight_of_addSlack_nonpos s hW hsl (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hj).2
  have hz : ∀ j ∈ s.filter (fun j => ¬ 0 < T.intersection W j), T.intersection W j = 0 :=
    fun j hj => by
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := T.intersection_nonneg W j (fun h => hW (h ▸ (Finset.mem_filter.mp hj).1))
      omega
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun j => 0 < T.intersection W j) (fun j => T.intersection W j)
  rw [Finset.sum_congr rfl hPw, Finset.sum_congr rfl hz, Finset.sum_const, Finset.sum_const_zero,
    add_zero, nsmul_eq_mul] at hsplit
  have hPcard : 1 ≤ P'.card := Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hpos⟩⟩
  have hsl' : ∑ j ∈ s, T.intersection W j - (P'.card : ℤ) - (T.weight W - 1) ≤ 0 := hsl
  rw [← hsplit] at hsl'
  have hPc1 : (P'.card : ℤ) = 1 := by
    have : ((P'.card : ℤ) - 1) * (T.weight W - 1) ≤ 0 := by nlinarith
    have h1 : (1 : ℤ) ≤ P'.card := by exact_mod_cast hPcard
    by_contra hc
    have h2 : (2 : ℤ) ≤ P'.card := by omega
    nlinarith
  rw [← hsplit, hPc1, one_mul]

/-- On a minimal numerical type with all multiplicities `1`, a component `W ∉ s` of genus `0`
whose intersection with `s` is `w_W` meets a component outside `s ∪ {W}`. -/
private theorem exists_intersection_pos_of_sum_intersection_eq_weight
    (hmult : ∀ i, T.multiplicity i = 1) (hmin : IsMinimal T)
    {s : Finset (Fin T.componentCount)} {W : Fin T.componentCount} (hW : W ∉ s)
    (hg : T.componentGenus W = 0) (hsum : ∑ j ∈ s, T.intersection W j = T.weight W) :
    ∃ V ∈ Finset.univ \ insert W s, 0 < T.intersection W V := by
  classical
  have hrow : ∑ j, T.intersection W j = 0 := by
    simpa [hmult] using T.intersection_mul_multiplicity W
  set rest := Finset.univ \ insert W s with hrest
  have hdecomp : ∑ j, T.intersection W j =
      T.intersection W W + ∑ j ∈ s, T.intersection W j + ∑ j ∈ rest, T.intersection W j := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (insert W s)), Finset.sum_insert hW]
    ring
  by_contra hcon
  push Not at hcon
  have hzero : ∑ j ∈ rest, T.intersection W j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjW : W ≠ j := fun h => by
      rw [hrest, Finset.mem_sdiff] at hj
      exact hj.2 (h ▸ Finset.mem_insert_self _ _)
    have := T.intersection_nonneg W j hjW
    have := hcon j hj
    omega
  exact hmin ⟨W, hg, by linarith⟩

/-- **The combinatorial core of the separability of the components in the equality case.** In
the induction of [Stacks, Tag 0CEA] (data `χ`, `c`, `g'` as in
`AlgebraicGeometry.NumericalType.le_genusDefect_univ`) suppose the total defect is not positive,
all multiplicities are `1`, and the numerical type is minimal. Let `P` be a property of components
which holds for components of weight `1` and of positive genus, and which passes from `V` to `i`
whenever `a_{Vi} = w_V`. Then `P` holds for every component. -/
theorem forall_of_genusDefect_univ_le_zero
    (χ : Finset (Fin T.componentCount) → ℤ) (c gg : Fin T.componentCount → ℤ)
    (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
    (hgg : ∀ i, gg i ≤ T.weight i - c i)
    (j₀ : Fin T.componentCount) (hw₀ : T.weight j₀ = 1) (hbase : χ {j₀} = c j₀)
    (hΔ : T.genusDefect χ gg Finset.univ ≤ 0)
    (hmult : ∀ i, T.multiplicity i = 1) (hmin : IsMinimal T)
    (P : Fin T.componentCount → Prop)
    (hw : ∀ i, T.weight i = 1 → P i) (hg : ∀ i, T.componentGenus i ≠ 0 → P i)
    (htrans : ∀ V i, V ≠ i → T.intersection V i = T.weight V → P V → P i) :
    ∀ i, P i := by
  classical
  have hD₀ : 0 ≤ T.genusDefect χ gg {j₀} := by
    unfold genusDefect
    rw [Finset.card_singleton, edgeCountOn_singleton, Finset.sum_singleton, hbase]
    push_cast
    linarith [hgg j₀]
  have key : ∀ r : ℕ, ∀ i s, j₀ ∈ s → i ∉ s → 0 ≤ T.genusDefect χ gg s →
      (Finset.univ \ s).card ≤ r → P i := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro i s hj₀ his hD hr
    by_cases hopen : ∃ W, W ∉ s ∧ W ≠ i ∧ ∃ j ∈ s, 0 < T.intersection W j
    · obtain ⟨W, hW, hWi, hmeet⟩ := hopen
      obtain ⟨hD', -⟩ := T.genusDefect_insert_nonneg_and_addSlack_nonpos hstep hgg hΔ hj₀ hW hD
        hmeet
      exact ih _ ((card_univ_sdiff_insert_lt hW).trans_le hr) i (insert W s)
        (Finset.mem_insert_of_mem hj₀) (by simp [Ne.symm hWi, his]) hD' le_rfl
    push Not at hopen
    by_cases hwi : T.weight i = 1
    · exact hw i hwi
    by_cases hgi : T.componentGenus i ≠ 0
    · exact hg i hgi
    push Not at hgi
    have hw2 : 1 < T.weight i := by have := T.weight_pos i; omega
    have hne : s ≠ Finset.univ := fun h => his (h ▸ Finset.mem_univ i)
    obtain ⟨a, ha, W, hW, hpos⟩ := T.exists_intersection_pos_of_ne_univ s hj₀ hne
    have hWi : W = i := Classical.byContradiction fun h => (hopen W hW h a ha).not_gt hpos
    subst hWi
    obtain ⟨hD', hsl⟩ := T.genusDefect_insert_nonneg_and_addSlack_nonpos hstep hgg hΔ hj₀ hW hD
      ⟨a, ha, hpos⟩
    obtain ⟨V, hV, hVpos⟩ := T.exists_intersection_pos_of_sum_intersection_eq_weight hmult hmin
      hW hgi (T.sum_intersection_eq_weight_of_addSlack_nonpos hW hsl hw2 ha hpos)
    have hVs : V ∉ insert W s := (Finset.mem_sdiff.mp hV).2
    have hpos' : 0 < T.intersection V W := by rwa [T.intersection_symm]
    obtain ⟨-, hslV⟩ := T.genusDefect_insert_nonneg_and_addSlack_nonpos hstep hgg hΔ
      (Finset.mem_insert_of_mem hj₀) hVs hD' ⟨W, Finset.mem_insert_self _ _, hpos'⟩
    exact htrans V W (fun h => hVs (h ▸ Finset.mem_insert_self _ _))
      (T.intersection_eq_weight_of_addSlack_nonpos (insert W s) hVs hslV
        (Finset.mem_insert_self _ _) hpos')
      (ih _ ((card_univ_sdiff_insert_lt hW).trans_le hr) V (insert W s)
        (Finset.mem_insert_of_mem hj₀) hVs hD' le_rfl)
  intro i
  by_cases hi : i = j₀
  · exact hw i (hi ▸ hw₀)
  exact key _ i {j₀} (Finset.mem_singleton_self _) (by simpa using hi) hD₀ le_rfl

end AlgebraicGeometry.NumericalType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The field structure on the constants `κ_Z = H⁰(C_Z, 𝒪)` of a component. -/
private noncomputable abbrev componentField (Z : irreducibleComponents S.specialFiber) :
    Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
  (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField

/-- The `k`-algebra structure on the constants `κ_Z = H⁰(C_Z, 𝒪)` of a component. -/
private noncomputable abbrev componentAlgebra (Z : irreducibleComponents S.specialFiber) :
    Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra

/-- The closed immersion `C_Z ∩ C_W ⟶ C_W` commutes with the structure morphisms to `Spec k`. -/
private theorem subschemeMap_comp_specialFiberComponentToSpec
    (Z W : irreducibleComponents S.specialFiber) :
    Scheme.IdealSheafData.subschemeMap (S.componentIntersectionIdeal Z W)
        (S.specialFiberComponentIdeal W) (S.specialFiberComponentIdeal Z).subschemeι
        (Scheme.IdealSheafData.le_map_comap _ _) ≫ S.specialFiberComponentToSpec W =
      (S.componentIntersectionIdeal Z W).subschemeι ≫ S.specialFiberComponentToSpec Z := by
  show _ ≫ (S.specialFiberComponentι W ≫ S.specialFiberToSpec) =
    _ ≫ (S.specialFiberComponentι Z ≫ S.specialFiberToSpec)
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono S.specialFiberι, Category.assoc, Category.assoc,
    S.specialFiberComponentι_specialFiberι, S.specialFiberComponentι_specialFiberι]
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- **Separability passes along an intersection of the expected degree.** Let `C_Z ≠ C_W` be
components of the special fibre with `(C_Z · C_W) = [κ_Z : k]`, where `κ_Z = H⁰(C_Z, 𝒪)`. Then the
intersection `D = C_Z ∩ C_W`, a closed subscheme of `C_Z`, has `H⁰(D, 𝒪) = κ_Z`, and since `D` is
also a closed subscheme of `C_W`, restriction of functions embeds `κ_W` into `κ_Z` over `k`. So if
`κ_Z/k` is separable, so is `κ_W/k`. -/
theorem isSeparable_of_specialFiberIntersectionMatrix_eq_weight
    {Z W : irreducibleComponents S.specialFiber} (hZW : Z ≠ W)
    (h : S.specialFiberIntersectionMatrix Z W = S.specialFiberComponentWeight Z)
    (hsep : letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
      letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
      Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) :
    letI : Field Γ((S.specialFiberComponentIdeal W).subscheme, ⊤) :=
      (S.isField_and_finite_globalSections_specialFiberComponent W).1.toField
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal W).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec W).appTop).hom.toAlgebra
    Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal W).subscheme, ⊤) := by
  let := S.componentField Z
  let := S.componentAlgebra Z
  let := S.componentField W
  let := S.componentAlgebra W
  let : Algebra S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      ((S.componentIntersectionIdeal Z W).subschemeι ≫
        S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have : FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (S.isField_and_finite_globalSections_specialFiberComponent Z).2
  have hdimI : Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) =
      Module.finrank S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
    have h1 := S.specialFiberIntersectionMatrix_eq_finrank_globalSections hZW
    rw [h] at h1
    exact_mod_cast h1.symm
  have hpos : 0 < Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    hdimI ▸ S.specialFiberComponentWeight_pos Z
  have : Nontrivial Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos hpos
  have : FiniteDimensional S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    Module.finite_of_finrank_pos hpos
  let φ : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) →ₐ[S.k]
      Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    { (S.componentIntersectionIdeal Z W).subschemeι.appTop.hom with
      commutes' := fun c => rfl }
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hφ : Function.Bijective φ :=
    ⟨hφinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      hdimI.symm).mp hφinj⟩
  let M : (S.componentIntersectionIdeal Z W).subscheme ⟶
      (S.specialFiberComponentIdeal W).subscheme :=
    Scheme.IdealSheafData.subschemeMap _ _ (S.specialFiberComponentIdeal Z).subschemeι
      (Scheme.IdealSheafData.le_map_comap _ _)
  have hM : M ≫ S.specialFiberComponentToSpec W =
      (S.componentIntersectionIdeal Z W).subschemeι ≫ S.specialFiberComponentToSpec Z :=
    S.subschemeMap_comp_specialFiberComponentToSpec Z W
  let ψ : Γ((S.specialFiberComponentIdeal W).subscheme, ⊤) →ₐ[S.k]
      Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    { M.appTop.hom with
      commutes' := fun c => by
        show (M.appTop.hom ((S.specialFiberComponentToSpec W).appTop.hom
            ((Scheme.ΓSpecIso (.of S.k)).inv.hom c))) =
          ((S.componentIntersectionIdeal Z W).subschemeι ≫
            S.specialFiberComponentToSpec Z).appTop.hom ((Scheme.ΓSpecIso (.of S.k)).inv.hom c)
        rw [← hM, Scheme.Hom.comp_appTop]
        rfl }
  exact Algebra.IsSeparable.of_algHom S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
    (((AlgEquiv.ofBijective φ hφ).symm : _ →ₐ[S.k] _).comp ψ)

/-- A component `C_Z` with `[κ_Z : k] = 1` has `κ_Z = k`, which is separable over `k`. -/
private theorem isSeparable_globalSections_specialFiberComponent_of_weight_eq_one
    (Z : irreducibleComponents S.specialFiber) (h : S.specialFiberComponentWeight Z = 1) :
    letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
  let := S.componentField Z
  let := S.componentAlgebra Z
  have h' : (⊥ : Subalgebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one h
  let eq : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ≃ₐ[S.k] S.k :=
    Subalgebra.topEquiv.symm.trans ((Subalgebra.equivOfEq _ _ h'.symm).trans
      (Algebra.botEquiv S.k _))
  exact Algebra.IsSeparable.of_algHom S.k S.k eq.toAlgHom

/-- In the equality case of [Stacks, Tag 0CEA], a component of positive genus has a field of
constants separable over `k`. -/
private theorem isSeparable_globalSections_specialFiberComponent_of_genus_ne_zero
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
    (Z : irreducibleComponents S.specialFiber) (hZ : S.specialFiberComponentGenus Z ≠ 0) :
    letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
  by_cases hxZ : x ∈ Z.1
  · exact S.isSeparable_globalSections_specialFiberComponent_of_weight_eq_one Z
      (S.specialFiberComponentWeight_eq_one_of_isRationalPoint Z x hx hxZ)
  · exact ((S.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction x hx hsm n e
      heq).2.2 Z hxZ).2.1 hZ

/-- The geometric genus of the special fibre is the sum of those of its components. -/
private theorem sum_geometricGenus_specialFiberComponentToSpec (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ∑ i, (geometricGenus S.k (S.specialFiberComponentToSpec (e i)) : ℤ) =
      geometricGenus S.k S.specialFiberToSpec := by
  rw [S.geometricGenus_specialFiberToSpec_eq_sum, Nat.cast_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- In the equality case of [Stacks, Tag 0CEA], on a minimal model with all multiplicities one,
a property of components holds for all of them if it holds for components of weight `1` and of
positive genus, and passes from `V` to `i` whenever `(C_V · C_i) = [κ_V : k]`. -/
private theorem forall_of_topologicalGenus_add_geometricGenus_eq
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
    (hmult : ∀ Z, S.specialFiberMultiplicity Z = 1)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (P : Fin (S.associatedNumericalType n e).componentCount → Prop)
    (hP1 : ∀ i, (S.associatedNumericalType n e).weight i = 1 → P i)
    (hPg : ∀ i, (S.associatedNumericalType n e).componentGenus i ≠ 0 → P i)
    (hPt : ∀ V i, V ≠ i → (S.associatedNumericalType n e).intersection V i =
      (S.associatedNumericalType n e).weight V → P V → P i)
    (i : Fin (S.associatedNumericalType n e).componentCount) : P i := by
  classical
  obtain ⟨Z₀, hZ₀⟩ := S.exists_mem_specialFiberComponent x
  let T := S.associatedNumericalType n e
  let e' : Fin T.componentCount ≃ irreducibleComponents S.specialFiber := e
  have hw : ∀ i, T.weight i = (S.specialFiberComponentWeight (e' i) : ℤ) := fun _ => rfl
  have hint : ∀ i j, T.intersection i j = S.specialFiberIntersectionMatrix (e' i) (e' j) :=
    fun i j => S.associatedNumericalType_intersection n e i j
  let χ : Finset (Fin T.componentCount) → ℤ :=
    fun s => S.specialFiberDivisorEulerChar fun Z => if Z ∈ s.map e'.toEmbedding then 1 else 0
  let c : Fin T.componentCount → ℤ := fun i =>
    eulerCharacteristic S.k (S.specialFiberComponentToSpec (e' i))
      (SheafOfModules.unit (S.specialFiberComponentIdeal (e' i)).subscheme.ringCatSheaf)
  let gg : Fin T.componentCount → ℤ :=
    fun i => (geometricGenus S.k (S.specialFiberComponentToSpec (e' i)) : ℤ)
  have hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W := by
    intro s W hW
    simp only [χ, c, Finset.map_insert, Equiv.coe_toEmbedding]
    rw [S.specialFiberDivisorEulerChar_indicator_insert _ (by simpa using hW), Finset.sum_map]
    simp only [hint, Equiv.coe_toEmbedding]
  have hgg : ∀ i, gg i ≤ T.weight i - c i := fun i => by
    rw [hw]
    exact S.geometricGenus_specialFiberComponent_le (e' i)
  have hw₀ : T.weight (e'.symm Z₀) = 1 := by
    rw [hw, Equiv.apply_symm_apply,
      S.specialFiberComponentWeight_eq_one_of_isRationalPoint Z₀ x hx hZ₀, Nat.cast_one]
  have hbase : χ {e'.symm Z₀} = c (e'.symm Z₀) := by
    simp only [χ, c, Finset.map_singleton, Equiv.coe_toEmbedding]
    exact S.specialFiberDivisorEulerChar_indicator_singleton _
  have huniv : (fun Z => if Z ∈ (Finset.univ : Finset (Fin T.componentCount)).map e'.toEmbedding
      then 1 else 0) = fun _ => 1 := by
    funext Z
    simp
  have hsum : ∑ i : Fin T.componentCount, gg i =
      (geometricGenus S.k S.specialFiberToSpec : ℤ) :=
    S.sum_geometricGenus_specialFiberComponentToSpec n e
  have hΔ : T.genusDefect χ gg Finset.univ ≤ 0 := by
    rw [T.genusDefect_univ, hsum]
    simp only [χ, huniv, S.specialFiberDivisorEulerChar_one x hx]
    rw [heq]
    simp
  have hmult' : ∀ i, T.multiplicity i = 1 := fun i => by
    show (S.specialFiberMultiplicity (e' i) : ℤ) = 1
    exact_mod_cast hmult (e' i)
  exact T.forall_of_genusDefect_univ_le_zero χ c gg hstep hgg (e'.symm Z₀) hw₀ hbase hΔ hmult'
    hmin P hP1 hPg hPt i

/-- **In the equality case of [Stacks, Tag 0CEA], on a minimal model with all multiplicities one,
every component of the special fibre has a field of constants separable over `k`.** See the
module documentation for the argument; this is the separability the proof of
[Stacks, Section 0CEI] takes from [Stacks, Tag 0CEE]. -/
theorem isSeparable_globalSections_specialFiberComponent_of_eq
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
    (hmult : ∀ Z, S.specialFiberMultiplicity Z = 1)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (Z : irreducibleComponents S.specialFiber) :
    letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
  let T := S.associatedNumericalType n e
  let e' : Fin T.componentCount ≃ irreducibleComponents S.specialFiber := e
  have hw : ∀ i, T.weight i = (S.specialFiberComponentWeight (e' i) : ℤ) := fun _ => rfl
  have hint : ∀ i j, T.intersection i j = S.specialFiberIntersectionMatrix (e' i) (e' j) :=
    fun i j => S.associatedNumericalType_intersection n e i j
  let P : Fin T.componentCount → Prop := fun i =>
    let := S.componentField (e' i)
    let := S.componentAlgebra (e' i)
    Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal (e' i)).subscheme, ⊤)
  have hP1 : ∀ i, T.weight i = 1 → P i := fun i hi =>
    S.isSeparable_globalSections_specialFiberComponent_of_weight_eq_one (e' i)
      (by exact_mod_cast (hw i).symm.trans hi)
  have hPg : ∀ i, T.componentGenus i ≠ 0 → P i := fun i hi =>
    S.isSeparable_globalSections_specialFiberComponent_of_genus_ne_zero x hx hsm n e heq (e' i)
      fun h0 => hi <| by
        show (S.specialFiberComponentGenus (e' i) : ℤ) = 0
        exact_mod_cast h0
  have hPt : ∀ V i, V ≠ i → T.intersection V i = T.weight V → P V → P i :=
    fun V i hVi hVw hPV => S.isSeparable_of_specialFiberIntersectionMatrix_eq_weight
      (fun h => hVi (e'.injective h)) (by rwa [hint, hw] at hVw) hPV
  obtain ⟨i, rfl⟩ := e'.surjective Z
  exact S.forall_of_topologicalGenus_add_geometricGenus_eq x hx n e heq hmult hmin P hP1 hPg hPt i

/-- **Every component of the special fibre is smooth over `k`** in the equality case of
[Stacks, Tag 0CEA], on a minimal model with all multiplicities one. The component through the
rational point is smooth over `k` by part (1) of [Stacks, Tag 0CEE]; any other component `C` is
smooth over `κ_C` by part (2), and `κ_C/k` is finite and separable
(`isSeparable_globalSections_specialFiberComponent_of_eq`), so `Spec κ_C ⟶ Spec k` is étale. -/
theorem smooth_specialFiberComponentToSpec_of_eq
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
    (hmult : ∀ Z, S.specialFiberMultiplicity Z = 1)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (Z : irreducibleComponents S.specialFiber) :
    Smooth (S.specialFiberComponentToSpec Z) := by
  have h0CEE :=
    S.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction x hx hsm n e heq
  by_cases hxZ : x ∈ Z.1
  · exact (h0CEE.2.1 Z hxZ).1
  have hsep := S.isSeparable_globalSections_specialFiberComponent_of_eq x hx hsm n e heq hmult
    hmin Z
  have h2 := h0CEE.2.2 Z hxZ
  let := S.componentField Z
  let := S.componentAlgebra Z
  have : FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := h2.1
  have : Smooth (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ := h2.2.2.2
  have : Algebra.Etale S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ⟨Algebra.FormallyEtale.of_isSeparable _ _, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 inferInstance)
  have hfac : S.specialFiberComponentToSpec Z = (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))) := by
    show _ = _ ≫ Spec.map ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiberComponentToSpec Z).appTop)
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [hfac]
  exact MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

end Stacks.Models.RegularProperModelSituation

end
