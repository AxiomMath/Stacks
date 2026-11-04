module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectionChain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaSubvariety

/-!
# The Moving Lemma over a fixed projective line with fixed points `0` and `∞`

Tag 0B1T asks for a family `C' ⊆ 𝐏^N × 𝐏^1` with conditions on its fibres over the points `0` and
`∞` of `𝐏^1`: the line and the two points are given in advance. This file proves the lemma in that
form, for *every* projective line `𝐏(W)`, `dim_k W = 2`, and *every* pair of distinct closed points
`0 ≠ ∞` of it.

The family of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety` lives over some
projective line `𝐏(W')` with some pair of distinct closed points `0', ∞'`. The group of linear
automorphisms acts transitively on pairs of distinct points of a projective line: if `0' = [μ₀']`,
`∞' = [μ₁']` and `0 = [ν₀]`, `∞ = [ν₁]` are cut out by functionals, the two pairs of functionals
are bases of the duals, and the linear isomorphism `e : W ≃ W'` whose transpose carries `μᵢ'` to
`νᵢ` induces an isomorphism `𝐏(W') ≅ 𝐏(W)` carrying `0'` to `0` and `∞'` to `∞`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv`). The family is transported along
the induced isomorphism of `𝐏(W') × 𝐏^N` with `𝐏(W) × 𝐏^N`; the four clauses are invariant,
being statements about images, fibres, dimensions and pulled-back ideal sheaves.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv_hom_linearFunctionalPoint`: the
  isomorphism induced by `e` carries the point `[μ]` to `[μ ∘ e]`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed`:
  **Tag 0B1T**, over a given projective line with given distinct points `0` and `∞`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

section Transport

variable {k : Type u} [Field k] {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N]

/-- **The isomorphism induced by a linear equivalence lies over `Spec k`.** -/
@[reassoc]
public theorem mapOfLinearEquiv_hom_comp_toSpec (e : M ≃ₗ[k] N) :
    (mapOfLinearEquiv e).hom ≫ projectiveSpaceOfModuleToSpec k M =
      projectiveSpaceOfModuleToSpec k N := by
  show Proj.map _ _ ≫ _ = _
  rw [projectiveSpaceOfModuleToSpec, projectiveSpaceOfModuleToSpec, ← Category.assoc,
    Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun r => Subtype.ext ((SymPow.symAlgMap e.toLinearMap).commutes r)

/-- **The isomorphism induced by `e` carries the point `[μ]` to the point `[μ ∘ e]`.** -/
public theorem mapOfLinearEquiv_hom_linearFunctionalPoint (e : M ≃ₗ[k] N)
    (μ : Module.Dual k N) (hμ : μ ≠ 0) (hμe : μ ∘ₗ e.toLinearMap ≠ 0) :
    (mapOfLinearEquiv e).hom.base (linearFunctionalPoint k N μ hμ) =
      linearFunctionalPoint k M (μ ∘ₗ e.toLinearMap) hμe := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun z => ?_))
  show SymPow.symAlgMap e.toLinearMap z ∈ (linearFunctionalPoint k N μ hμ).asHomogeneousIdeal ↔
    z ∈ (linearFunctionalPoint k M (μ ∘ₗ e.toLinearMap) hμe).asHomogeneousIdeal
  rw [linearFunctionalPoint_mem, linearFunctionalPoint_mem, SymPow.symAlgMap_comp_apply]

end Transport

/-- **A homeomorphism preserves the dimension of a subset carried along it.** -/
public theorem topologicalKrullDim_image_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (S : Set X) :
    topologicalKrullDim ↥(h '' S) = topologicalKrullDim ↥S :=
  (IsHomeomorph.topologicalKrullDim_eq _ (h.image S).isHomeomorph).symm

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- Two distinct closed points of a projective line are cut out by a basis of the dual. -/
private theorem linearIndependent_of_ne {W : Type u} [AddCommGroup W] [Module k W]
    {μ₀ μ₁ : Module.Dual k W} (h0 : μ₀ ≠ 0) (h1 : μ₁ ≠ 0)
    (hne : linearFunctionalPoint k W μ₀ h0 ≠ linearFunctionalPoint k W μ₁ h1) :
    LinearIndependent k ![μ₀, μ₁] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right h0, rfl⟩
  · exfalso
    have hs : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hst
      exact h1 ((smul_eq_zero.mp hst).resolve_left ht)
    set c : kˣ := Units.mk0 (-s / t) (div_ne_zero (neg_ne_zero.mpr hs) ht) with hc
    have hμ₁ : μ₁ = (c : k) • μ₀ := by
      have h2 : t • μ₁ = -(s • μ₀) := eq_neg_of_add_eq_zero_right hst
      have h3 : μ₁ = t⁻¹ • -(s • μ₀) := by rw [← h2, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h3, hc, Units.val_mk0, smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv, mul_comm,
        neg_mul]
    apply hne
    have hcμ : c • μ₀ ≠ 0 := by
      rw [Units.smul_def, ← hμ₁]
      exact h1
    have := linearFunctionalPoint_units_smul k W c μ₀ h0 hcμ
    have heq : linearFunctionalPoint k W μ₁ h1 = linearFunctionalPoint k W (c • μ₀) hcμ := by
      congr 1
    rw [heq, this]

omit [IsAlgClosed k] in
/-- **A basis of a two-dimensional space adapted to two independent functionals**: `νᵢ(dⱼ)` is
`1` for `i = j` and `0` otherwise. -/
private theorem exists_basis_dual_pair {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (hW : Module.finrank k W = 2) {ν₀ ν₁ : Module.Dual k W}
    (hli : LinearIndependent k ![ν₀, ν₁]) :
    ∃ d : Module.Basis (Fin 2) k W, ∀ i j, (![ν₀, ν₁] i) (d j) = if i = j then 1 else 0 := by
  have hcard : Fintype.card (Fin 2) = Module.finrank k (Module.Dual k W) := by
    rw [Subspace.dual_finrank_eq, hW, Fintype.card_fin]
  set c := basisOfLinearIndependentOfCardEqFinrank hli hcard with hc
  refine ⟨c.dualBasis.map (Module.evalEquiv k W).symm, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.apply_evalEquiv_symm_apply]
  have h := c.dualBasis_apply_self j i
  rw [hc, coe_basisOfLinearIndependentOfCardEqFinrank] at h
  exact h

omit [IsAlgClosed k] in
/-- **Two pairs of independent functionals are related by a linear isomorphism.** -/
private theorem exists_linearEquiv_dual_pair {W W' : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (hW : Module.finrank k W = 2) (hW' : Module.finrank k W' = 2)
    {ν₀ ν₁ : Module.Dual k W} (hν : LinearIndependent k ![ν₀, ν₁])
    {μ₀ μ₁ : Module.Dual k W'} (hμ : LinearIndependent k ![μ₀, μ₁]) :
    ∃ e : W ≃ₗ[k] W', μ₀ ∘ₗ e.toLinearMap = ν₀ ∧ μ₁ ∘ₗ e.toLinearMap = ν₁ := by
  obtain ⟨d, hd⟩ := exists_basis_dual_pair k hW hν
  obtain ⟨d', hd'⟩ := exists_basis_dual_pair k hW' hμ
  have key : ∀ i : Fin 2, ![μ₀, μ₁] i ∘ₗ (d.equiv d' (Equiv.refl _)).toLinearMap = ![ν₀, ν₁] i :=
    fun i => d.ext fun j => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
        hd' i j, hd i j]
  exact ⟨d.equiv d' (Equiv.refl _), key 0, key 1⟩

/-- **Stacks Project, Tag 0B1T, over a given projective line with given points `0 ≠ ∞`.** Let `C`
be a closed subvariety of `𝐏^N = 𝐏(V)`, `X` a subvariety of `𝐏^N` (irreducible and locally
closed, not necessarily closed), `T i ⊆ X` finitely many closed subvarieties of `X`, and assume
`C` and `X` intersect properly. Let `𝐏^1 = 𝐏(W)`, `dim_k W = 2`, and let `0 ≠ ∞` be closed points
of it. Then there is a closed subvariety `C'` of `𝐏^1 × 𝐏^N` such that

1. `C' → 𝐏^1` is dominant;
2. `C'_0 = C` scheme theoretically;
3. `C'` and `X × 𝐏^1` intersect properly;
4. `C'_∞` properly intersects each `T i`.

Proper intersection is the dimension criterion of Definition 0AZQ read on the subsets. The
instance `Nontrivial W` is implied by `dim_k W = 2` and is there only because the products and
sections of `𝐏(W)` are stated under it. The family
of `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety` is transported
along an isomorphism of projective lines carrying its points to the given ones. -/
@[stacks 0B1T "the whole lemma, at the source's hypotheses and no others, over the source's \
fixed 𝐏^1 with its fixed points: C a closed subvariety of 𝐏^N = 𝐏(V) (an irreducible closed \
subset with its reduced structure), X a subvariety of 𝐏^N (an irreducible locally closed subset, \
not necessarily closed), T i ⊆ X finitely many closed subvarieties of X (irreducible, closed in \
X), C and X intersecting properly; for every projective line 𝐏^1 = 𝐏(W), dim_k W = 2, and every \
pair of distinct closed points 0, ∞ of it, a closed subvariety C' of 𝐏^1 × 𝐏^N with (1) C' → \
𝐏^1 dominant, read as density of the image; (2) C'_0 = C scheme theoretically: the ideal sheaf \
of the reduced closed subscheme on C' pulled back along the section of 𝐏^1 × 𝐏^N → 𝐏^N at 0 is \
the ideal sheaf of the reduced closed subscheme on C; (3) C' and X × 𝐏^1 intersect properly; \
(4) C'_∞ intersects each T i properly. Proper intersection is the dimension criterion of \
Definition 0AZQ read on the subsets"]
public theorem exists_movingFamily_of_subvariety_fixed
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) + topologicalKrullDim ↥X)
    {ι : Type*} [Finite ι] (T : ι → Set (projectiveSpaceOfModule k V))
    (hTX : ∀ i, T i ⊆ X) (hTc : ∀ i, IsClosed {x : X | x.1 ∈ T i})
    (hTirr : ∀ i, IsIrreducible (T i))
    (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    (hW : Module.finrank k W = 2) (zero infty : projectiveSpaceOfModule k W)
    (hzero : IsClosed ({zero} : Set (projectiveSpaceOfModule k W)))
    (hinfty : IsClosed ({infty} : Set (projectiveSpaceOfModule k W))) (hne : zero ≠ infty) :
    ∃ Cfam : IrreducibleCloseds (lineProduct k V W),
      closure ((lineProductLine k V W).base '' (Cfam : Set (lineProduct k V W))) = Set.univ ∧
      (Scheme.IdealSheafData.vanishingIdeal
            (⟨Cfam, Cfam.isClosed'⟩ : Closeds (lineProduct k V W))).comap
          (lineProductSection k V W zero hzero) =
        Scheme.IdealSheafData.vanishingIdeal
          (⟨C, C.isClosed'⟩ : Closeds (projectiveSpaceOfModule k V)) ∧
      topologicalKrullDim ↥((Cfam : Set (lineProduct k V W)) ∩ lineProductConstant k V W X) +
          topologicalKrullDim (lineProduct k V W) ≤
        topologicalKrullDim ↥(Cfam : Set (lineProduct k V W)) +
          topologicalKrullDim ↥(lineProductConstant k V W X) ∧
      ∀ i, topologicalKrullDim
            ↥(lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W)) ∩ T i) +
          topologicalKrullDim (projectiveSpaceOfModule k V) ≤
        topologicalKrullDim
            ↥(lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W))) +
          topologicalKrullDim ↥(T i) := by
  obtain ⟨W', _, _, _, _, hW', zero', infty', hzero', hinfty', hne', Cfam', h1, h2, h3, h4⟩ :=
    exists_movingFamily_of_subvariety k V C X hX hXirr hCX T hTX hTc hTirr
  -- the functionals cutting out the four points
  obtain ⟨μ₀, hμ₀, rfl⟩ := exists_eq_linearFunctionalPoint k W' zero' hzero'
  obtain ⟨μ₁, hμ₁, rfl⟩ := exists_eq_linearFunctionalPoint k W' infty' hinfty'
  obtain ⟨ν₀, hν₀, rfl⟩ := exists_eq_linearFunctionalPoint k W zero hzero
  obtain ⟨ν₁, hν₁, rfl⟩ := exists_eq_linearFunctionalPoint k W infty hinfty
  obtain ⟨e, he₀, he₁⟩ := exists_linearEquiv_dual_pair k hW hW'
    (linearIndependent_of_ne k hν₀ hν₁ hne) (linearIndependent_of_ne k hμ₀ hμ₁ hne')
  -- the isomorphism of lines and of products
  set Φ := mapOfLinearEquiv e with hΦ
  have hΦS : Φ.hom ≫ projectiveSpaceOfModuleToSpec k W = projectiveSpaceOfModuleToSpec k W' :=
    mapOfLinearEquiv_hom_comp_toSpec e
  set ψ := pullback.map (projectiveSpaceOfModuleToSpec k W') (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k W) (projectiveSpaceOfModuleToSpec k V) Φ.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hΦS]) (by rw [Category.comp_id, Category.id_comp]) with hψ
  set Ψ : lineProduct k V W' ≅ lineProduct k V W := asIso ψ with hΨ
  have hψline : ψ ≫ lineProductLine k V W = lineProductLine k V W' ≫ Φ.hom :=
    pullback.lift_fst _ _ _
  have hψpoint : ψ ≫ lineProductPoint k V W = lineProductPoint k V W' := by
    rw [hψ]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k W) := by
    have := isProper_projectiveSpaceOfModuleToSpec k W
    infer_instance
  have hsec : ∀ (μ : Module.Dual k W') (hμ : μ ≠ 0) (ν : Module.Dual k W) (hν : ν ≠ 0),
      μ ∘ₗ e.toLinearMap = ν →
      lineProductSection k V W' _ (linearFunctionalPoint_isClosed k W' μ hμ) ≫ ψ =
        lineProductSection k V W _ (linearFunctionalPoint_isClosed k W ν hν) := by
    intro μ hμ ν hν he
    have hΦμ : Φ.hom.base (linearFunctionalPoint k W' μ hμ) = linearFunctionalPoint k W ν hν := by
      rw [hΦ, mapOfLinearEquiv_hom_linearFunctionalPoint e μ hμ (he ▸ hν)]
      exact linearFunctionalPoint_eq_of_eq k W _ hν he
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψline, lineProductSection_comp_lineProductLine_assoc,
        lineProductSection_comp_lineProductLine]
      congr 1
      refine ext_of_apply_closedPoint_eq (projectiveSpaceOfModuleToSpec k W) ?_
        (pointOfClosedPoint_comp _ _ _) ?_
      · rw [Category.assoc, hΦS, pointOfClosedPoint_comp]
      · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg Φ.hom.base
          (pointOfClosedPoint_apply _ _ _ _)).trans
          (hΦμ.trans (pointOfClosedPoint_apply _ _ _ _).symm))
    · rw [Category.assoc, hψpoint, lineProductSection_comp_lineProductPoint,
        lineProductSection_comp_lineProductPoint]
  set h := Scheme.homeoOfIso Ψ with hh
  have hhψ : ∀ z, h z = ψ.base z := fun z => rfl
  have hpre : ∀ S : Set (lineProduct k V W'), ψ.base ⁻¹' (h '' S) = S := fun S =>
    h.preimage_image S
  -- the transported family
  refine ⟨⟨h '' (Cfam' : Set _), Cfam'.isIrreducible'.image _ h.continuous.continuousOn,
    h.isClosedMap _ Cfam'.isClosed'⟩, ?_, ?_, ?_, ?_⟩
  · -- clause (1)
    have himg : (lineProductLine k V W).base '' (h '' (Cfam' : Set _)) =
        Scheme.homeoOfIso Φ '' ((lineProductLine k V W').base '' (Cfam' : Set _)) := by
      rw [Set.image_image, Set.image_image]
      refine Set.image_congr fun z _ => ?_
      rw [hhψ, ← Scheme.Hom.comp_apply, hψline]
      rfl
    show closure ((lineProductLine k V W).base '' (h '' (Cfam' : Set _))) = Set.univ
    rw [himg, ← Homeomorph.image_closure, h1,
      Set.image_univ_of_surjective (Homeomorph.surjective _)]
  · -- clause (2)
    rw [← hsec μ₀ hμ₀ ν₀ hν₀ he₀, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion]
    convert h2 using 3
    exact Closeds.ext (hpre _)
  · -- clause (3)
    have hconst : lineProductConstant k V W' X = ψ.base ⁻¹' lineProductConstant k V W X := by
      rw [lineProductConstant, lineProductConstant, ← Set.preimage_comp]
      congr 1
      rw [← TopCat.coe_comp, ← Scheme.Hom.comp_base, hψpoint]
    have hconst' : lineProductConstant k V W' X = h ⁻¹' lineProductConstant k V W X := hconst
    have hinter : h '' (Cfam' : Set _) ∩ lineProductConstant k V W X =
        h '' ((Cfam' : Set _) ∩ lineProductConstant k V W' X) := by
      rw [hconst', Set.image_inter_preimage]
    have hconstW : lineProductConstant k V W X = h '' lineProductConstant k V W' X := by
      rw [hconst', Set.image_preimage_eq _ h.surjective]
    show topologicalKrullDim ↥(h '' (Cfam' : Set _) ∩ lineProductConstant k V W X) + _ ≤
      topologicalKrullDim ↥(h '' (Cfam' : Set _)) + _
    rw [hinter, topologicalKrullDim_image_homeomorph, topologicalKrullDim_image_homeomorph,
      hconstW, topologicalKrullDim_image_homeomorph,
      ← IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph]
    exact h3
  · -- clause (4)
    intro i
    have hfib : lineProductFibre k V W _ (linearFunctionalPoint_isClosed k W ν₁ hν₁)
        (h '' (Cfam' : Set _)) =
        lineProductFibre k V W' _ (linearFunctionalPoint_isClosed k W' μ₁ hμ₁) (Cfam' : Set _) := by
      rw [lineProductFibre, lineProductFibre, ← hsec μ₁ hμ₁ ν₁ hν₁ he₁, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.preimage_comp, hpre]
    show topologicalKrullDim ↥(lineProductFibre k V W _ _ (h '' (Cfam' : Set _)) ∩ T i) + _ ≤
      topologicalKrullDim ↥(lineProductFibre k V W _ _ (h '' (Cfam' : Set _))) + _
    rw [hfib]
    exact h4 i

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
