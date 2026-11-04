module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairOpenExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# The kernel pair of an étale chart which is an isomorphism off an open subspace

Let `f : V ⟶ X` be an étale morphism from an object of the site to a presheaf, with kernel
pair `s, t : R ⟶ V` represented by an object of the site. Let `U ⊆ X` be a subfunctor with
inverse image `W ⊆ V`, an open subscheme, and let `T ⊆ X` be a subfunctor whose points are the
complement of those of `U`, over which `f` is an isomorphism: `V ×_X T ⟶ T` is an isomorphism.
Then the scheme `R = V ×_X V` is the union of the diagonal copy of `V` and of the inverse image
of `W` under either projection, which is `W ×_U W`.

Consequently two morphisms `a, b : Y ⟶ V` with the same image in `X` are, locally on `Y`,
either equal or both factor through `W` with the same image in `U`.

## Main results

* `AlgebraicGeometry.Space.ElementaryChart.opensRange_sup_preimage_eq_top`: the two opens cover
  `R`.
* `AlgebraicGeometry.Space.ElementaryChart.exists_eq_or_factor`: the local dichotomy for two
  morphisms with the same image in `X`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

/-- The data of an étale chart `f : V ⟶ X` which is an isomorphism off an open subspace: the
kernel pair `R`, the subfunctor `U` with inverse image the open `W ⊆ V`, and the subfunctor
`T` on the complementary points over which `f` is an isomorphism. -/
structure ElementaryChart (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS) where
  /-- The chart. -/
  f : yoneda.obj V ⟶ X
  /-- The chart is étale. -/
  etale_f : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  /-- The object representing the kernel pair. -/
  R : BigFppfOver B S hS
  /-- The first projection of the kernel pair. -/
  s : R ⟶ V
  /-- The second projection of the kernel pair. -/
  t : R ⟶ V
  /-- `R` with `s` and `t` is the kernel pair of `f`. -/
  isPullback : IsPullback (yoneda.map s) (yoneda.map t) f f
  /-- The open part of the target. -/
  U : Subfunctor X
  /-- Its inverse image in `V`. -/
  W : BigFppfOver B S hS
  /-- The open immersion `W ⟶ V`. -/
  j : W ⟶ V
  /-- `j` is an open immersion. -/
  isOpenImmersion_j : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)
  /-- The induced morphism `W ⟶ U`. -/
  p : yoneda.obj W ⟶ U.toFunctor
  /-- `W` is the inverse image of `U` under `f`. -/
  isPullback_W : IsPullback (yoneda.map j) p f U.ι
  /-- The complementary part of the target. -/
  T : Subfunctor X
  /-- The points of `T` are the complement of the points of `U`. -/
  range_T : Set.range (pointsMap B S hS T.toFunctor T.ι) =
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
  /-- The inclusion `T ⟶ X` is relatively representable. -/
  rep_T : yoneda.relativelyRepresentable T.ι
  /-- The base change `V ×_X T ⟶ T` of `f` is an isomorphism. -/
  isIso_fst : IsIso (pullback.fst T.ι f)

namespace ElementaryChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
  (E : ElementaryChart X V)

attribute [instance] isOpenImmersion_j isIso_fst

/-- The diagonal `V ⟶ R`. -/
noncomputable def Δ : V ⟶ E.R := kernelPairLift B S hS E.isPullback (𝟙 V) (𝟙 V) rfl

/-- The diagonal is a section of the first projection. -/
@[reassoc (attr := simp)]
theorem Δ_s : E.Δ ≫ E.s = 𝟙 V := kernelPairLift_fst _ _ _ _ _ _ _

/-- The diagonal is a section of the second projection. -/
@[reassoc (attr := simp)]
theorem Δ_t : E.Δ ≫ E.t = 𝟙 V := kernelPairLift_snd _ _ _ _ _ _ _

/-- The first projection `s : R ⟶ V` of the kernel pair is étale. -/
theorem etale_map_s : Etale ((F).map E.s) :=
  E.etale_f.property E.f (yoneda.map E.t) E.s E.isPullback.flip

/-- The diagonal is an open immersion, being a section of the étale morphism `s`. -/
instance isOpenImmersion_Δ : AlgebraicGeometry.IsOpenImmersion ((F).map E.Δ) := by
  have := E.etale_map_s
  exact isOpenImmersion_of_comp_eq_id_of_etale ((F).map E.s) ((F).map E.Δ)
    (by rw [← (F).map_comp, Δ_s, (F).map_id])

/-- A point of `V` maps into `U` exactly when its scheme point lies in `W`. -/
theorem mem_range_U_iff (v : points B S hS (yoneda.obj V)) :
    pointsMap B S hS _ E.f v ∈ Set.range (pointsMap B S hS E.U.toFunctor E.U.ι) ↔
      pointsToScheme B S hS V v ∈ Set.range ((F).map E.j) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS E.isPullback_W v x hx.symm
    refine ⟨pointsToScheme B S hS E.W w, ?_⟩
    rw [← hw, pointsToScheme_pointsMap_yoneda]
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := (pointsEquivScheme B S hS E.W).surjective y
    have hv : v = pointsMap B S hS _ (yoneda.map E.j) w := by
      apply injective_pointsToScheme B S hS V
      rw [pointsToScheme_pointsMap_yoneda, ← hy]
      rfl
    refine ⟨pointsMap B S hS _ E.p w, ?_⟩
    rw [hv, ← pointsMap_comp_apply, ← pointsMap_comp_apply, E.isPullback_W.w]

/-- The two projections of the kernel pair have the same inverse image of `W`. -/
theorem map_s_mem_iff (x : (F).obj E.R) :
    (F).map E.s x ∈ Set.range ((F).map E.j) ↔ (F).map E.t x ∈ Set.range ((F).map E.j) := by
  obtain ⟨w, rfl⟩ := (pointsEquivScheme B S hS E.R).surjective x
  show (F).map E.s (pointsToScheme B S hS _ w) ∈ _ ↔ (F).map E.t (pointsToScheme B S hS _ w) ∈ _
  rw [← pointsToScheme_pointsMap_yoneda, ← pointsToScheme_pointsMap_yoneda, ← E.mem_range_U_iff,
    ← E.mem_range_U_iff, ← pointsMap_comp_apply, ← pointsMap_comp_apply, E.isPullback.w]

/-- A point of `R` lying over the complement of `U` is on the diagonal. -/
theorem mem_range_Δ_of_not_mem (x : (F).obj E.R)
    (hx : (F).map E.s x ∉ Set.range ((F).map E.j)) : x ∈ Set.range ((F).map E.Δ) := by
  obtain ⟨w, rfl⟩ := (pointsEquivScheme B S hS E.R).surjective x
  show pointsToScheme B S hS _ w ∈ _
  replace hx : (F).map E.s (pointsToScheme B S hS _ w) ∉ Set.range ((F).map E.j) := hx
  set g : yoneda.obj E.R ⟶ X := yoneda.map E.s ≫ E.f with hg
  have hw : pointsMap B S hS _ g w ∈ Set.range (pointsMap B S hS E.T.toFunctor E.T.ι) := by
    rw [E.range_T, hg, pointsMap_comp_apply]
    intro hmem
    exact hx (by rw [← pointsToScheme_pointsMap_yoneda]; exact (E.mem_range_U_iff _).mp hmem)
  have hpre : w ∈ pointsMap B S hS _ g ⁻¹' Set.range (pointsMap B S hS E.T.toFunctor E.T.ι) :=
    hw
  rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS E.rep_T g] at hpre
  obtain ⟨z, rfl⟩ := hpre
  set σ := E.rep_T.snd g
  -- the two components of `σ` agree, because `f` is an isomorphism over `T`
  have hsq := E.rep_T.isPullback g
  have hα : yoneda.map (σ ≫ E.s) ≫ E.f = E.rep_T.fst g ≫ E.T.ι := by
    rw [yoneda.map_comp, Category.assoc, ← hg, hsq.w]
  have hβ : yoneda.map (σ ≫ E.t) ≫ E.f = E.rep_T.fst g ≫ E.T.ι := by
    rw [yoneda.map_comp, Category.assoc, ← E.isPullback.w, ← Category.assoc, ← yoneda.map_comp,
      hα]
  have hst : σ ≫ E.s = σ ≫ E.t := by
    apply yoneda.map_injective
    have h₁ : pullback.lift (E.rep_T.fst g) (yoneda.map (σ ≫ E.s)) hα.symm =
        pullback.lift (E.rep_T.fst g) (yoneda.map (σ ≫ E.t)) hβ.symm := by
      rw [← cancel_mono (pullback.fst E.T.ι E.f), pullback.lift_fst, pullback.lift_fst]
    simpa only [pullback.lift_snd] using congrArg (· ≫ pullback.snd E.T.ι E.f) h₁
  have hσ : σ = (σ ≫ E.s) ≫ E.Δ :=
    kernelPair_hom_ext B S hS E.isPullback _ _ (by rw [Category.assoc, Δ_s, Category.comp_id])
      (by rw [Category.assoc, Δ_t, Category.comp_id, hst])
  have hFσ : (F).map σ = (F).map (σ ≫ E.s) ≫ (F).map E.Δ := by rw [← (F).map_comp, ← hσ]
  refine ⟨(F).map (σ ≫ E.s) (pointsToScheme B S hS _ z), ?_⟩
  rw [pointsToScheme_pointsMap_yoneda, hFσ]
  rfl

/-- **The scheme `V ×_X V` is the union of the diagonal and of `W ×_U W`.** -/
theorem opensRange_sup_preimage_eq_top :
    ((F).map E.Δ).opensRange ⊔ (F).map E.s ⁻¹ᵁ ((F).map E.j).opensRange = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_preimage, Set.mem_preimage]
  exact or_iff_not_imp_right.mpr (E.mem_range_Δ_of_not_mem x)

/-- **Two morphisms with the same image in `X` are locally equal or both factor through `W`.**
Let `a, b : Y ⟶ V` have the same composite with `f`. Every point of `Y` has an open
neighbourhood on which either `a` and `b` agree, or both factor through the open `W ⊆ V`. -/
theorem exists_eq_or_factor {Y : BigFppfOver B S hS} (a b : Y ⟶ V)
    (h : yoneda.map a ≫ E.f = yoneda.map b ≫ E.f) (y : (F).obj Y) :
    ∃ O : ((F).obj Y).Opens, y ∈ O ∧
      (O.ι ≫ (F).map a = O.ι ≫ (F).map b ∨
        ∃ a' b' : O.toScheme ⟶ (F).obj E.W,
          a' ≫ (F).map E.j = O.ι ≫ (F).map a ∧ b' ≫ (F).map E.j = O.ι ≫ (F).map b) := by
  set c : Y ⟶ E.R := kernelPairLift B S hS E.isPullback a b h with hcdef
  have hcs : (F).map c ≫ (F).map E.s = (F).map a := by
    rw [← (F).map_comp, hcdef, kernelPairLift_fst]
  have hct : (F).map c ≫ (F).map E.t = (F).map b := by
    rw [← (F).map_comp, hcdef, kernelPairLift_snd]
  have hy : (F).map c y ∈ (((F).map E.Δ).opensRange ⊔
      (F).map E.s ⁻¹ᵁ ((F).map E.j).opensRange : ((F).obj E.R).Opens) := by
    rw [E.opensRange_sup_preimage_eq_top]
    trivial
  rcases hy with hy | hy
  · set O : ((F).obj Y).Opens := (F).map c ⁻¹ᵁ ((F).map E.Δ).opensRange
    have H : Set.range (O.ι ≫ (F).map c) ⊆ Set.range ((F).map E.Δ) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    refine ⟨O, hy, Or.inl ?_⟩
    rw [← hcs, ← hct, ← Category.assoc, ← Category.assoc,
      ← IsOpenImmersion.lift_fac ((F).map E.Δ) (O.ι ≫ (F).map c) H, Category.assoc,
      Category.assoc, ← (F).map_comp, ← (F).map_comp, Δ_s, Δ_t]
  · set O : ((F).obj Y).Opens := (F).map c ⁻¹ᵁ ((F).map E.s ⁻¹ᵁ ((F).map E.j).opensRange)
    have Ha : Set.range (O.ι ≫ (F).map a) ⊆ Set.range ((F).map E.j) := by
      rintro _ ⟨z, rfl⟩
      have hz := z.2
      change (F).map E.s ((F).map c (O.ι z)) ∈ Set.range ((F).map E.j) at hz
      show ((F).map a) (O.ι z) ∈ _
      rw [← hcs]
      exact hz
    have Hb : Set.range (O.ι ≫ (F).map b) ⊆ Set.range ((F).map E.j) := by
      rintro _ ⟨z, rfl⟩
      have hz := z.2
      change (F).map E.s ((F).map c (O.ι z)) ∈ Set.range ((F).map E.j) at hz
      show ((F).map b) (O.ι z) ∈ _
      rw [← hct]
      exact (E.map_s_mem_iff _).mp hz
    exact ⟨O, hy, Or.inr ⟨IsOpenImmersion.lift _ _ Ha, IsOpenImmersion.lift _ _ Hb,
      IsOpenImmersion.lift_fac _ _ Ha, IsOpenImmersion.lift_fac _ _ Hb⟩⟩

end ElementaryChart

end AlgebraicGeometry.Space

end
