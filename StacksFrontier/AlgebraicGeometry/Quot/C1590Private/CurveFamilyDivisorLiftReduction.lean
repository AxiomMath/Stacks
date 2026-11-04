module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorLift
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.IdealGlue
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ProjHyperplane
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.RelativeSum
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectClosedFibre

/-!
# Reducing the divisor lift at a closed fibre to divisors supported in one point

Let `X ⟶ S` be a family of curves over an affine base, `s` a closed point of `S` and `V` a scheme
presenting the fibre `X_s`. This module proves
`AlgebraicGeometry.C1590Private.DivisorLiftReduction`: if every effective Cartier divisor of `V`
supported in exactly one point lifts, after an affine elementary étale base change, to a relative
effective Cartier divisor of the family, then so does every effective Cartier divisor of `V` with
finite support. It is a step of the proof that families of curves are étale locally on the base
schemes (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.C1590Private.divisorLiftReduction`: the reduction.
* `AlgebraicGeometry.C1590Private.exists_mul_eq_of_mem_support`: on a locally Noetherian scheme an
  effective Cartier divisor with finite support of closed points splits off its component at a
  point of the support.
* `AlgebraicGeometry.C1590Private.isRelativeEffectiveCartierDivisor_sumClosedSubspaces`: the sum of
  two relative effective Cartier divisors of a morphism of algebraic spaces is one (the space form
  of Stacks 0B8U).
* `AlgebraicGeometry.C1590Private.isRelativeEffectiveCartierDivisor_preimage_totalMap`: a relative
  effective Cartier divisor of a family of curves pulls back to one along a morphism of families
  with étale morphism of bases.
* `AlgebraicGeometry.C1590Private.sumClosedSubspaces_closedSubspaceOfIdeal`: on a scheme, the sum
  of the closed subspaces cut out by two ideal sheaves is cut out by their product.

## The argument

The induction is on the number of points of the support, and composes the étale neighbourhoods
instead of forming their fibre product: the first lift lives on a family `Y'` over an étale
neighbourhood of `s`, and the residue point of `s` lifts to `Y'`, so the one-point lift can be
applied to `Y'` itself. No disjointness of the lifts is needed, since flatness of a sum of relative
effective Cartier divisors holds in general (Stacks 0B8U), and the space form of it is read on one
surjective étale chart square, where the sum is cut out by the product of the chart ideal sheaves.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0B8U](https://stacks.math.columbia.edu/tag/0B8U)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
* [Stacks Project, Tag 0840](https://stacks.math.columbia.edu/tag/0840)
* [Stacks Project, Tag 0EPN](https://stacks.math.columbia.edu/tag/0EPN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

open Stacks.Divisors

/-! ### Splitting a divisor with finite support on a scheme -/

/-- In a Jacobson space every point of a finite closed set is closed. -/
theorem isClosed_singleton_of_mem_of_finite {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {Z : Set X} (hZ : IsClosed Z) (hfin : Z.Finite) {y : X} (hy : y ∈ Z) :
    IsClosed ({y} : Set X) := by
  have hcl : IsClosed (Z ∩ closedPoints X) := by
    have h := (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun z (hz : z ∈ Z ∩ closedPoints X) => hz.2)
    rwa [Set.biUnion_of_singleton] at h
  have h := closure_inter_closedPoints hZ
  rw [hcl.closure_eq] at h
  exact (h.symm ▸ hy : y ∈ Z ∩ closedPoints X).2

/-- The inverse image of an ideal sheaf along a morphism missing its support is the unit ideal. -/
theorem comap_eq_top_of_forall_notMem {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (h : ∀ z, f z ∉ (I.support : Set Y)) : I.comap f = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine le_antisymm (fun z hz => ?_) bot_le
  rw [Scheme.IdealSheafData.support_comap] at hz
  exact absurd hz (h z)

/-- **Splitting off one point of a divisor with finite support.** On a locally Noetherian scheme,
an effective Cartier divisor `E` whose support is finite and consists of closed points is the sum
`E' + E₁` of two effective Cartier divisors, `E₁` supported in a prescribed point `x` of the
support of `E` and `E'` supported in the rest of it. -/
theorem exists_mul_eq_of_mem_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (hfin : (E.support : Set X).Finite)
    (hcl : ∀ y ∈ (E.support : Set X), IsClosed ({y} : Set X))
    (x : X) (hx : x ∈ (E.support : Set X)) :
    ∃ E₁ E' : X.IdealSheafData, IsEffectiveCartierDivisor E₁ ∧ IsEffectiveCartierDivisor E' ∧
      E = E' * E₁ ∧ (E₁.support : Set X) ⊆ {x} ∧
        (E'.support : Set X) ⊆ (E.support : Set X) \ {x} := by
  classical
  set R : Set X := (E.support : Set X) \ {x} with hRdef
  have hR : IsClosed R := by
    simpa only [Set.biUnion_of_singleton] using
      (hfin.subset (t := R) Set.sdiff_subset).isClosed_biUnion fun y hy => hcl y hy.1
  let W : Fin 2 → X.Opens := ![⟨Rᶜ, hR.isOpen_compl⟩, ⟨{x}ᶜ, (hcl x hx).isOpen_compl⟩]
  have hW0 : ∀ y, y ∈ W 0 ↔ y ∉ R := fun y => Iff.rfl
  have hW1 : ∀ y, y ∈ W 1 ↔ y ≠ x := fun y => Iff.rfl
  -- the two opens cover `X`, and they meet outside the support of `E`
  have hmem : ∀ y : X, ∃ i, y ∈ W i := by
    intro y
    by_cases hy : y = x
    · exact ⟨0, (hW0 y).2 fun h => h.2 hy⟩
    · exact ⟨1, (hW1 y).2 hy⟩
  have hcov : ∀ y : X, ∃ i, y ∈ Set.range (W i).ι := by
    intro y
    obtain ⟨i, hi⟩ := hmem y
    exact ⟨i, by rwa [Scheme.Opens.range_ι]⟩
  have hsup : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨i, hi⟩ := hmem y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rwa [Scheme.Opens.opensRange_ι]⟩
  have hdisj : ∀ y ∈ (E.support : Set X), y ∈ W 0 → y ∈ W 1 → False := by
    intro y hy h0 h1
    exact (hW0 y).1 h0 ⟨hy, (hW1 y).1 h1⟩
  have hι : ∀ i (z : W i), (W i).ι z ∈ W i := fun i z => by
    have := Set.mem_range_self (f := (W i).ι) z
    rwa [Scheme.Opens.range_ι] at this
  have hcross : ∀ i l, i ≠ l →
      E.comap (pullback.fst (W i).ι (W l).ι ≫ (W i).ι) = ⊤ := by
    intro i l hil
    refine comap_eq_top_of_forall_notMem E _ fun z hz => ?_
    have hzi : (pullback.fst (W i).ι (W l).ι ≫ (W i).ι) z ∈ W i := by
      rw [Scheme.Hom.comp_apply]; exact hι i _
    have hzl : (pullback.fst (W i).ι (W l).ι ≫ (W i).ι) z ∈ W l := by
      rw [pullback.condition, Scheme.Hom.comp_apply]; exact hι l _
    fin_cases i <;> fin_cases l
    · exact absurd rfl hil
    · exact hdisj _ hz hzi hzl
    · exact hdisj _ hz hzl hzi
    · exact absurd rfl hil
  -- the compatibility on overlaps, for a datum which is `E` on one open and `⊤` on the other
  have hcompat : ∀ (k : Fin 2) (Z : ∀ i, (W i).toScheme.IdealSheafData),
      (∀ i, Z i = if i = k then E.comap (W i).ι else ⊤) →
      ∀ i l, (Z i).comap (pullback.fst (W i).ι (W l).ι) =
        (Z l).comap (pullback.snd (W i).ι (W l).ι) := by
    intro k Z hZ i l
    rw [hZ i, hZ l]
    by_cases hik : i = k <;> by_cases hlk : l = k
    · subst hik; subst hlk
      rw [ite_eq_left rfl, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, pullback.condition]
    · rw [ite_eq_left hik, ite_eq_right hlk, Scheme.IdealSheafData.comap_top,
        ← Scheme.IdealSheafData.comap_comp]
      exact hcross i l fun h => hlk (h ▸ hik)
    · rw [ite_eq_right hik, ite_eq_left hlk, Scheme.IdealSheafData.comap_top,
        ← Scheme.IdealSheafData.comap_comp, ← pullback.condition]
      exact (hcross i l fun h => hik (h ▸ hlk)).symm
    · rw [ite_eq_right hik, ite_eq_right hlk, Scheme.IdealSheafData.comap_top,
        Scheme.IdealSheafData.comap_top]
  -- the two pieces: `E` on one open and the unit ideal on the other
  have hpiece : ∀ k : Fin 2, ∃ F : X.IdealSheafData, IsEffectiveCartierDivisor F ∧
      ∀ l, F.comap (W l).ι = if l = k then E.comap (W l).ι else ⊤ := fun k => by
    let Z : ∀ i, (W i).toScheme.IdealSheafData := fun i => if i = k then E.comap (W i).ι else ⊤
    have h := Stacks.LinearSystemScheme.comap_iInf_map_eq (fun i => (W i).ι) Z
      (hcompat k Z fun _ => rfl)
    refine ⟨⨅ i, (Z i).map (W i).ι,
      Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_of_comap (fun i => (W i).ι) hsup _
        fun i => ?_, h⟩
    rw [h]
    dsimp only [Z]
    split_ifs
    exacts [isPullbackDefined_of_flat (W i).ι E hE, isEffectiveCartierDivisor_top]
  obtain ⟨E₁, hE₁c, hE₁⟩ := hpiece 0
  obtain ⟨E', hE'c, hE'⟩ := hpiece 1
  have heq : E = E' * E₁ := by
    refine Stacks.LinearSystemScheme.ideal_ext_of_comap (fun i => (W i).ι) hcov fun i => ?_
    rw [Stacks.IdealSheaf.comap_mul, hE₁, hE']
    fin_cases i
    · simp
    · simp
  have hsupp : ∀ (F : X.IdealSheafData) (l : Fin 2), F.comap (W l).ι = ⊤ →
      ∀ y ∈ (F.support : Set X), y ∉ W l := by
    intro F l hF y hy hyl
    have : (⟨y, hyl⟩ : W l) ∈ ((F.comap (W l).ι).support : Set (W l)) := by
      rw [Scheme.IdealSheafData.support_comap]; exact hy
    rw [hF, Scheme.IdealSheafData.support_top] at this
    exact this
  refine ⟨E₁, E', hE₁c, hE'c, heq, ?_, ?_⟩
  · intro y hy
    by_contra hne
    exact hsupp E₁ 1 (by rw [hE₁]; simp) y hy ((hW1 y).2 hne)
  · intro y hy
    have hyE : y ∈ (E.support : Set X) := by
      rw [heq, Scheme.IdealSheafData.support_mul]; exact Or.inl hy
    refine ⟨hyE, fun hyx => ?_⟩
    exact hsupp E' 0 (by rw [hE']; simp) y hy ((hW0 y).2 fun h => h.2 hyx)

/-! ### Relative effective Cartier divisors on algebraic spaces -/

section Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The chart ideal sheaf of a closed subspace and the base change of its inclusion have the
same flatness over a scheme.** -/
theorem flat_chartKer_subschemeι_comp_iff (X : AlgebraicSpaces B S hS)
    (D : Space.ClosedSubspaces B S hS X.1) {U V : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1)
    (α : U ⟶ V) :
    Flat ((Space.chartKer B S hS X D p).subschemeι ≫ (BigFppfOver.toScheme B S hS).map α) ↔
      Flat ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p) ≫
        (BigFppfOver.toScheme B S hS).map α) := by
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p)) :=
    D.2.2.property_snd p
  rw [Space.chartKer_eq]
  set g := (BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p)
  set e := closedImmersionKerIso g
  have hg : g ≫ (BigFppfOver.toScheme B S hS).map α =
      e.hom ≫ g.ker.subschemeι ≫ (BigFppfOver.toScheme B S hS).map α := by
    rw [← Category.assoc, ← closedImmersion_eq_kerIso_comp g]
  rw [hg]
  refine ⟨fun _ => inferInstance, fun _ => ?_⟩
  have : Flat (e.inv ≫ e.hom ≫ g.ker.subschemeι ≫ (BigFppfOver.toScheme B S hS).map α) :=
    inferInstance
  simpa using this

/-- Flatness of a closed subspace over a morphism of algebraic spaces can be checked on the chart
squares given by a surjective étale presentation of the morphism. -/
private theorem isFlat_ι_comp_of_forall_chart {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (D : Space.ClosedSubspaces B S hS X.1)
    (h : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y.1) (Uc : Space.SmallEtale B S hS X.1)
      (α : (Space.SmallEtale.toOver B S hS X.1).obj Uc ⟶ V),
      (MorphismProperty.inverseImage (@Etale) (BigFppfOver.toScheme B S hS)).presheaf b →
      Uc.1.hom ≫ f.hom = yoneda.map α ≫ b →
      Flat (Space.chartBaseChangeHom B S hS X D Uc ≫ (BigFppfOver.toScheme B S hS).map α)) :
    Space.IsFlat B S hS (D.1.ι ≫ f.hom) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.2.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    Space.exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
  let Uc : Space.SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hpEtale⟩
  exact Space.isFlat_ι_comp_of_surjective_chart B S hS X Y f.hom _ Uc
    ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U p).1 hpSurj) V b
    (Space.isEtale_of_presheaf_etale B S hS hbEtale) α hcomm (h V b Uc α hbEtale hcomm)

/-- **The space form of Stacks 0B8U.** The sum of two relative effective Cartier divisors of a
morphism of algebraic spaces is a relative effective Cartier divisor. The sum is effective
Cartier by Stacks 083V; flatness over the target is read on one surjective étale chart square,
where the sum is cut out by the product of the chart ideal sheaves of the summands, so the scheme
case Stacks 0B8U applies. -/
theorem isRelativeEffectiveCartierDivisor_sumClosedSubspaces {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (D₁ D₂ : Space.ClosedSubspaces B S hS X.1)
    (h₁ : Space.IsRelativeEffectiveCartierDivisor B S hS f D₁)
    (h₂ : Space.IsRelativeEffectiveCartierDivisor B S hS f D₂) :
    Space.IsRelativeEffectiveCartierDivisor B S hS f
      (Space.sumClosedSubspaces B S hS X D₁ D₂) := by
  refine ⟨Space.isEffectiveCartierDivisor_sumClosedSubspaces B S hS X D₁ D₂ h₁.1 h₂.1,
    isFlat_ι_comp_of_forall_chart f _ fun V b Uc α hbEtale hcomm => ?_⟩
  set T := BigFppfOver.toScheme B S hS with hT
  set p := Uc.1.hom
  -- each summand is a relative effective Cartier divisor of the chart square
  have hrel : ∀ D : Space.ClosedSubspaces B S hS X.1,
      Space.IsRelativeEffectiveCartierDivisor B S hS f D →
      IsRelativeEffectiveCartierDivisor (T.map α) (Space.chartKer B S hS X D p) := by
    intro D hD
    refine ⟨?_, ?_⟩
    · exact (Space.isSchemeEffectiveCartierPullback_iff B S hS X D _ p).1
        (Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D hD.1 _ p
          (Space.isEtale_of_presheaf_etale B S hS Uc.2))
    · rw [flat_chartKer_subschemeι_comp_iff, ← Functor.map_comp]
      refine hD.2 _ V (Space.chartBaseChangeToSubspace B S hS X D Uc) b (D.2.2.rep.snd p ≫ α)
        (Space.presheaf_etale_of_isEtale B S hS
          (Space.isEtale_chartBaseChangeToSubspace B S hS X D Uc)) hbEtale ?_
      rw [Functor.map_comp, Category.assoc, ← hcomm, ← Category.assoc, ← D.2.2.rep.w p,
        Category.assoc]
  have hmul := isRelativeEffectiveCartierDivisor_mul (T.map α) _ _ (hrel D₁ h₁) (hrel D₂ h₂)
  rw [← Space.chartKer_sumClosedSubspaces_eq_mul X D₁ D₂ p] at hmul
  exact (flat_chartKer_subschemeι_comp_iff X _ p α).1 hmul.2

/-- **The empty closed subspace is a relative effective Cartier divisor** of every morphism of
algebraic spaces: it has no points, and on a chart its base change is the empty scheme. -/
theorem isRelativeEffectiveCartierDivisor_emptyClosedSubspace {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    Space.IsRelativeEffectiveCartierDivisor B S hS f (Space.emptyClosedSubspace X) := by
  refine ⟨Space.isEffectiveCartierDivisor_of_isEmpty_points B S hS X _
    (Space.isEmpty_points_sheafify_bot B S hS X.1),
    isFlat_ι_comp_of_forall_chart f _ fun V b Uc α hbEtale hcomm => ?_⟩
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((Space.emptyClosedSubspace X).2.2.rep.pullback Uc.1.hom)) :=
    (Scheme.Hom.ker_eq_top_iff_isEmpty _).1 (Space.chartKer_eq_top_of_subspacePointSet_eq_empty X _
      (Space.subspacePointSet_emptyClosedSubspace X) Uc.1.hom)
  exact Flat.of_stalkMap _ fun x => isEmptyElim x

end Spaces

/-! ### Families of curves -/

section Curves

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A relative effective Cartier divisor of a family of curves pulls back to one of a base
change along an étale morphism of bases.** Effective Cartier-ness is Stacks 0EPN; flatness over
the new base is the base change of flatness over the old one along the étale morphism of
bases. -/
theorem isRelativeEffectiveCartierDivisor_preimage_totalMap {Y Y' : CurveFamily B hZ}
    (φ : Y ⟶ Y') (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap))
    (D : Space.ClosedSubspaces B integerBase hZ Y'.total.obj)
    (hD : Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y'.toBase D) :
    Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase
      ⟨D.1.preimage φ.totalMap.hom, Space.isClosedSubspace_preimage B integerBase hZ
        φ.totalMap.hom D.1 Y'.total.2 Y.total.2 D.2⟩ := by
  refine ⟨Space.isPullbackDefined_of_isPullback_of_isFlat B integerBase hZ Y'.toBase
    (schemeSpaceMap φ.baseMap) φ.cartesian.flip D hD.1 hD.2, ?_⟩
  have hsq : IsPullback (D.1.fromPreimage φ.totalMap.hom)
      ((D.1.preimage φ.totalMap.hom).ι ≫ Y.toBase.hom) (D.1.ι ≫ Y'.toBase.hom)
      (schemeSpaceMap φ.baseMap).hom :=
    (Subfunctor.isPullback_preimage φ.totalMap.hom D.1).paste_vert
      (Space.isPullback_hom_of_isPullback B integerBase hZ φ.cartesian)
  exact Space.isFlat_of_isPullback B integerBase hZ hsq.flip
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ _ φ.baseMap).2 hφ) hD.2

/-- A morphism of the site into `V` which factors through a closed immersion `j₁` into `V` factors
through every closed immersion `j₂` into `V` whose ideal sheaf is contained in that of `j₁`. -/
theorem range_yoneda_map_le_of_ker_le {A₁ A₂ V : BigFppfOver B integerBase hZ}
    (j₁ : A₁ ⟶ V) (j₂ : A₂ ⟶ V)
    [IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map j₂)]
    (h : ((BigFppfOver.toScheme B integerBase hZ).map j₂).ker ≤
      ((BigFppfOver.toScheme B integerBase hZ).map j₁).ker) :
    Subfunctor.range (yoneda.map j₁) ≤ Subfunctor.range (yoneda.map j₂) := by
  rintro ⟨W⟩ g ⟨a, rfl⟩
  set T := BigFppfOver.toScheme B integerBase hZ
  have hle : (T.map j₂).ker ≤ (T.map (a ≫ j₁)).ker := by
    rw [Functor.map_comp]
    exact h.trans (Scheme.Hom.le_ker_comp _ _)
  let l : T.obj W ⟶ T.obj A₂ := IsClosedImmersion.lift (T.map j₂) (T.map (a ≫ j₁)) hle
  let b : W ⟶ A₂ := Over.homMk ⟨l⟩ (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  refine ⟨b, ?_⟩
  change b ≫ j₂ = a ≫ j₁
  ext1
  exact ObjectProperty.hom_ext _ (IsClosedImmersion.lift_fac (T.map j₂) (T.map (a ≫ j₁)) hle)

/-- **A closed subspace of a scheme of the site is determined by its ideal sheaf.** -/
theorem closedSubspace_ext_of_chartKer_eq {V : BigFppfOver B integerBase hZ}
    (D₁ D₂ : Space.ClosedSubspaces B integerBase hZ (schemeSpace V).obj)
    (h : Space.chartKer B integerBase hZ (schemeSpace V) D₁ (𝟙 (schemeSpace V).obj) =
      Space.chartKer B integerBase hZ (schemeSpace V) D₂ (𝟙 (schemeSpace V).obj)) :
    D₁ = D₂ := by
  have key : ∀ D : Space.ClosedSubspaces B integerBase hZ (schemeSpace V).obj,
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map
        (D.2.2.rep.snd (𝟙 (schemeSpace V).obj))) ∧
      Subfunctor.range (yoneda.map (D.2.2.rep.snd (𝟙 (schemeSpace V).obj))) = D.1 := fun D =>
    ⟨D.2.2.property_snd _, (Space.range_yoneda_snd_eq_preimage B integerBase hZ
      (𝟙 (schemeSpace V).obj) D.2.2.rep).trans (Subfunctor.preimage_id D.1)⟩
  obtain ⟨_, h₁⟩ := key D₁
  obtain ⟨_, h₂⟩ := key D₂
  refine Subtype.ext ?_
  have h₃ := le_antisymm (range_yoneda_map_le_of_ker_le _ _ h.symm.le)
    (range_yoneda_map_le_of_ker_le _ _ h.le)
  exact h₁.symm.trans (h₃.trans h₂)

/-- **The sum of the closed subspaces cut out by two ideal sheaves of a scheme is cut out by
their product.** -/
theorem sumClosedSubspaces_closedSubspaceOfIdeal (V : BigFppfOver B integerBase hZ)
    (K₁ K₂ : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData) :
    Space.sumClosedSubspaces B integerBase hZ (schemeSpace V) (Space.closedSubspaceOfIdeal V K₁)
        (Space.closedSubspaceOfIdeal V K₂) = Space.closedSubspaceOfIdeal V (K₁ * K₂) := by
  have e : ∀ K : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData,
      Space.chartKer B integerBase hZ (schemeSpace V) (Space.closedSubspaceOfIdeal V K)
        (𝟙 (schemeSpace V).obj) = K := fun K => Space.ker_rep_snd_closedSubspaceOfIdeal V K
  refine closedSubspace_ext_of_chartKer_eq _ _
    ((Space.chartKer_sumClosedSubspaces_eq_mul (schemeSpace V) _ _ _).trans ?_)
  exact (congrArg₂ (· * ·) (e K₁) (e K₂)).trans (e _).symm

/-- **P2b: the divisor lift reduces to divisors supported in one point.** If every effective
Cartier divisor of a closed fibre supported in exactly one point lifts, after an elementary étale
base change, to a relative effective Cartier divisor of the family, then so does every effective
Cartier divisor of the fibre with finite support.

The proof is by induction on the number of points of the support. A divisor with empty support
is the unit ideal, lifted over `X` itself by the empty closed subspace. The fibre `V` is locally of
finite type over a field, so it is locally Noetherian and Jacobson, and the points of the finite
support are closed. Split `E = E' + E₁` with `E₁` supported in one point and `E'` in the others,
lift `E'` over `Y' ⟶ X` by induction, and then lift `E₁` over `Y'' ⟶ Y'` by the hypothesis applied
to the family `Y'` at the residue point lifted to `Y'`. The sum of the pullback of the lift of
`E'` and the lift of `E₁` is a relative effective Cartier divisor of `Y''` (Stacks 0EPN, 083V and
the space form of 0B8U), and its preimage in the fibre is `E' + E₁` (Stacks 0840). -/
theorem divisorLiftReduction : DivisorLiftReduction B hZ := by
  intro hloc
  set T := BigFppfOver.toScheme B integerBase hZ with hT
  have hval : ∀ {Q : BigFppfOver B integerBase hZ}
      (P' : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj),
      yonedaEquiv.symm P'.value = yoneda.map (show P'.siteObject ⟶ Q from P'.value) := by
    intro Q P'
    ext W f
    rfl
  -- a divisor with empty support is the unit ideal, lifted by the empty closed subspace
  have hempty : ∀ (X : CurveFamily B hZ) (_ : IsAffine (T.obj X.base))
      (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (_ : IsClosedImmersion (T.map P.value))
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
      (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
      (E : (T.obj V).IdealSheafData), (E.support : Set (T.obj V)) = ∅ →
      ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
        (q' : yoneda.obj V ⟶ Y.total.obj)
        (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj),
        Etale (T.map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧ IsClosedImmersion (T.map t) ∧
        IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
        IsAffine (T.obj Y.base) ∧
        Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D ∧
        D.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1 := by
    intro X hX P hP V v q hq E hemp
    have hE : E = ⊤ := (Scheme.IdealSheafData.support_eq_bot_iff _).1
      (SetLike.coe_injective (by rw [hemp, TopologicalSpace.Closeds.coe_bot]))
    subst hE
    have hq0 := hq
    rw [hval] at hq0
    have hpts : Space.subspacePointSet B integerBase hZ (schemeSpace V).obj
        ((Space.emptyClosedSubspace X.total).1.preimage q) = ∅ := by
      have h := Space.isEmpty_points_preimage_of_disjoint_range B integerBase hZ q
        (Space.emptyClosedSubspace X.total).1 (by
          rw [show Set.range (Space.pointsMap B integerBase hZ
              (Space.emptyClosedSubspace X.total).1.toFunctor
              (Space.emptyClosedSubspace X.total).1.ι) = ∅ from
            Space.subspacePointSet_emptyClosedSubspace X.total]
          exact disjoint_bot_right)
      exact Set.range_eq_empty_iff.2 h
    have hpre : (⟨(Space.emptyClosedSubspace X.total).1.preimage q,
        Space.isClosedSubspace_preimage B integerBase hZ q (Space.emptyClosedSubspace X.total).1
          X.total.2 (schemeSpace V).2 (Space.emptyClosedSubspace X.total).2⟩ :
          Space.ClosedSubspaces B integerBase hZ (schemeSpace V).obj) =
        Space.closedSubspaceOfIdeal V ⊤ :=
      closedSubspace_ext_of_chartKer_eq _ _
        ((Space.chartKer_eq_top_of_subspacePointSet_eq_empty (schemeSpace V) _ hpts _).trans
          (Space.ker_rep_snd_closedSubspaceOfIdeal V ⊤).symm)
    refine ⟨X, 𝟙 X, P.value, q, Space.emptyClosedSubspace X.total, ?_, ?_, hP, hq0, ?_, hX,
      isRelativeEffectiveCartierDivisor_emptyClosedSubspace X.toBase, congrArg Subtype.val hpre⟩
    · change Etale (T.map (𝟙 X.base))
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    · exact Category.comp_id _
    · exact Category.comp_id _
  suffices H : ∀ (n : ℕ) (X : CurveFamily B hZ) (_ : IsAffine (T.obj X.base))
      (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (_ : IsClosedImmersion (T.map P.value))
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
      (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
      (E : (T.obj V).IdealSheafData), IsEffectiveCartierDivisor E →
      (E.support : Set (T.obj V)).Finite → (E.support : Set (T.obj V)).ncard ≤ n →
      ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
        (q' : yoneda.obj V ⟶ Y.total.obj)
        (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj),
        Etale (T.map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧ IsClosedImmersion (T.map t) ∧
        IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
        IsAffine (T.obj Y.base) ∧
        Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D ∧
        D.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1 by
    intro X hX P hP V v q hq E hE hfin
    exact H _ X hX P hP V v q hq E hE hfin le_rfl
  intro n
  induction n with
  | zero =>
    intro X hX P hP V v q hq E hE hfin hn
    exact hempty X hX P hP V v q hq E ((Set.ncard_eq_zero hfin).1 (Nat.le_zero.1 hn))
  | succ n ih =>
    intro X hX P hP V v q hq E hE hfin hn
    rcases (E.support : Set (T.obj V)).eq_empty_or_nonempty with hemp | ⟨x, hx⟩
    · exact hempty X hX P hP V v q hq E hemp
    -- the fibre `V` is locally of finite type over a field
    have hq0 := hq
    rw [hval] at hq0
    have hV : IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v)
        X.toBase (schemeSpaceMap (show P.siteObject ⟶ X.base from P.value)) :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hq0.w) hq0
    have : LocallyOfFinitePresentation (T.map v) :=
      X.locallyOfFinitePresentation_toScheme_map_of_isPullback hV
    have : IsLocallyNoetherian (T.obj P.siteObject) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (.of P.carrier)))
    have : JacobsonSpace (T.obj P.siteObject) :=
      inferInstanceAs (JacobsonSpace (Spec (.of P.carrier)))
    have : IsLocallyNoetherian (T.obj V) := LocallyOfFiniteType.isLocallyNoetherian (T.map v)
    have : JacobsonSpace (T.obj V) := LocallyOfFiniteType.jacobsonSpace (T.map v)
    -- split off the point `x`
    obtain ⟨E₁, E', hE₁, hE', rfl, hs₁, hs'⟩ := exists_mul_eq_of_mem_support E hE hfin
      (fun y hy => isClosed_singleton_of_mem_of_finite E.support.isClosed hfin hy) x hx
    have hfin' : (E'.support : Set (T.obj V)).Finite := hfin.subset (hs'.trans Set.sdiff_subset)
    have hn' : (E'.support : Set (T.obj V)).ncard ≤ n := by
      have h1 := Set.ncard_le_ncard hs' (hfin.subset Set.sdiff_subset)
      rw [Set.ncard_sdiff_singleton_of_mem hx] at h1
      omega
    have hsing : (E₁.support : Set (T.obj V)) = {x} := by
      refine Set.Subset.antisymm hs₁ (Set.singleton_subset_iff.2 ?_)
      have hx' := hx
      rw [Scheme.IdealSheafData.support_mul] at hx'
      exact hx'.resolve_left fun h => (hs' h).2 rfl
    -- lift the rest by induction
    obtain ⟨Y', φ', t', q', D', hφ'et, ht', ht'ci, hpb', hq', haff', hrel', hpre'⟩ :=
      ih X hX P hP V v q hq E' hE' hfin' hn'
    -- lift the component at `x` over `Y'`
    let P' : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y'.base).obj :=
      { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t' }
    have hpb'' : IsPullback q' (yoneda.map v) Y'.toBase.hom (yonedaEquiv.symm P'.value) := by
      rw [hval P']
      exact hpb'
    obtain ⟨Y'', φ₂, t'', q'', D₁, hφ₂et, ht'', ht''ci, hpb₂, hq₂, haff₂, hrel₁, hpre₁⟩ :=
      hloc Y' haff' P' ht'ci V v q' hpb'' E₁ hE₁ ⟨x, hsing⟩
    -- the sum of the pullback of the first lift and the second lift
    let D'' : Space.ClosedSubspaces B integerBase hZ Y''.total.obj :=
      ⟨D'.1.preimage φ₂.totalMap.hom, Space.isClosedSubspace_preimage B integerBase hZ
        φ₂.totalMap.hom D'.1 Y'.total.2 Y''.total.2 D'.2⟩
    refine ⟨Y'', φ₂ ≫ φ', t'', q'', Space.sumClosedSubspaces B integerBase hZ Y''.total D'' D₁,
      ?_, ?_, ht''ci, hpb₂, ?_, haff₂, ?_, ?_⟩
    · change Etale (T.map (φ₂.baseMap ≫ φ'.baseMap))
      rw [Functor.map_comp]
      have := hφ₂et
      have := hφ'et
      infer_instance
    · change t'' ≫ φ₂.baseMap ≫ φ'.baseMap = P.value
      rw [← Category.assoc, ht'']
      exact ht'
    · change q'' ≫ φ₂.totalMap.hom ≫ φ'.totalMap.hom = q
      rw [← Category.assoc, hq₂, hq']
    · exact isRelativeEffectiveCartierDivisor_sumClosedSubspaces Y''.toBase D'' D₁
        (isRelativeEffectiveCartierDivisor_preimage_totalMap φ₂ hφ₂et D' hrel') hrel₁
    · have h0840 := congrArg Subtype.val (Space.preimage_sumClosedSubspaces B integerBase hZ
        (ObjectProperty.homMk q'' : schemeSpace V ⟶ Y''.total) D'' D₁)
      have e : ∀ (D : Space.ClosedSubspaces B integerBase hZ Y''.total.obj)
          (K : (T.obj V).IdealSheafData), D.1.preimage q'' = (Space.closedSubspaceOfIdeal V K).1 →
          (⟨D.1.preimage q'', Space.isClosedSubspace_preimage B integerBase hZ q'' D.1
            Y''.total.2 (schemeSpace V).2 D.2⟩ :
              Space.ClosedSubspaces B integerBase hZ (schemeSpace V).obj) =
            Space.closedSubspaceOfIdeal V K := fun _ _ h => Subtype.ext h
      exact h0840.trans (congrArg Subtype.val
        ((congrArg₂ (Space.sumClosedSubspaces B integerBase hZ (schemeSpace V))
          (e D'' E' (by
            change (D'.1.preimage φ₂.totalMap.hom).preimage q'' = _
            rw [← Subfunctor.preimage_comp, hq₂, hpre'])) (e D₁ E₁ hpre₁)).trans
          (sumClosedSubspaces_closedSubspaceOfIdeal V E' E₁)))

end Curves

end AlgebraicGeometry.C1590Private

end
