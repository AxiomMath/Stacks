module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Powers of an ideal sheaf annihilating a coherent module on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S`, let `F` be a coherent `𝒪_X`-module
and let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals, cutting out the closed subspace
`Z ⊆ X`. Some power of `ℐ` annihilates `F` exactly when the support of `F` is contained in `Z`,
set theoretically.

The closed subspace is referred to through its point set `|V(ℐ)| =
AlgebraicGeometry.Space.idealZeroLocus`, the set of points at which `ℐ` is not the whole
structure sheaf.

## Main results

* `AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus`:
  **the support characterization.**
* `AlgebraicGeometry.Space.idealSmul_idealPow_top_eq_bot_iff`: `ℐⁿ F` vanishes exactly when
  `ℐ(W)ⁿ` annihilates the sections of `F` over every étale chart `W`.
* `AlgebraicGeometry.Space.isZero_etaleModulePullback_chartToSpace_iff`: the restriction of an
  `𝒪_X`-module to an étale chart vanishes exactly when the module has no sections over any
  étale chart lying over it.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton` and
  `AlgebraicGeometry.Space.subsingleton_sections_of_supportOfSheaf_subset_idealZeroLocus`:
  the support of `F` lies in `|V(ℐ)|` exactly when `F` has no sections over a chart on which
  `ℐ` is the whole structure sheaf.
* `AlgebraicGeometry.Space.exists_pow_sectionIdeal_smul_top_eq_bot`: over a Noetherian affine
  chart some power of the ideal of sections of `ℐ` annihilates the sections of `F`.
* `AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_hom_of_isAffine` and
  `AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart`: that
  annihilation transfers along a morphism of affine charts, hence from one surjective affine
  chart to every chart.
* `AlgebraicGeometry.Space.exists_surjective_isNoetherianAffineChart`: a Noetherian algebraic
  space has a surjective étale chart which is affine with Noetherian ring of sections.

## Implementation notes

A sheaf of ideals is a submodule with local membership of the structure sheaf read as a module
over itself, and `ℐⁿ F` is `Stacks.Sites.idealSmul (Stacks.Sites.idealPow ℐ n) ⊤`, the smallest
submodule with local membership containing every product of a section of `ℐⁿ` with a section of
`F`. Its vanishing is therefore tested chart by chart, and that is what
`AlgebraicGeometry.Space.idealSmul_idealPow_top_eq_bot_iff` provides; the sections of `ℐⁿ` over a
chart are only *locally* `n`-fold products, which is why the separatedness of `F` enters there.

The support condition is turned into the vanishing of `F` over the charts on which `ℐ` is the
whole structure sheaf. Both directions of that reduction rest on the same fact, that restriction
of a module to the algebraic space represented by a chart kills it exactly when the module has no
sections over any chart lying over it: the support of the restriction is the inverse image of the
support, by Stacks 04KB, and a module with empty support is zero.

The remaining content is local. Over a Noetherian affine chart `U` the sections of `F` form a
finite module, and for a section `f` of `ℐ` over `U` the chart cut out by the nonvanishing locus
of `f` carries the unit ideal, hence no sections of `F`; since the ring of that chart is the
localization away from `f`, a power of `f` annihilates the sections over `U`. So `ℐ(U)` lies in
the radical of the annihilator, and `ℐ(U)ⁿ` annihilates it for some `n` because the ring is
Noetherian. Quasi-coherence then carries that single annihilation to every chart: over a morphism
of affine charts the sections base change, so `ℐ` is generated there by restrictions and every
section of `F` is a combination of restrictions, and an arbitrary chart is covered by affine
charts mapping to `U` because `U` is surjective.

The module universe is the universe of the schemes, as it is in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian`: that is where finiteness of
the sections of a coherent module over an affine chart and Descent, Proposition 03DX(2) are
available. The statements which need neither are universe polymorphic in it.

## References

* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Vanishing of `Iⁿ F`, read chart by chart -/

section Chart

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sections of the largest submodule of an `𝒪_F`-module are all of its sections. -/
theorem top_submodule_obj (M : Modules.{u, m} B S hS F hF) (W : (SmallEtale B S hS F)ᵒᵖ) :
    (⊤ : M.Submodule).obj W = ⊤ := by
  rw [show (⊤ : M.Submodule).obj W = (⊤ : M.Submodule).toSubmodule.obj W from rfl,
    Stacks.SheafOfModules.toSubmodule_top]
  rfl

/-- Every section of an `𝒪_F`-module is a section of its largest submodule. -/
theorem mem_top_submodule_obj (M : Modules.{u, m} B S hS F hF)
    {W : (SmallEtale B S hS F)ᵒᵖ} (z : M.val.obj W) : z ∈ (⊤ : M.Submodule).obj W :=
  (top_submodule_obj B S hS F hF M W).ge Submodule.mem_top

/-- An ideal annihilates the largest submodule exactly when it kills every element. -/
private theorem ideal_smul_top_eq_bot_iff {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (J : Ideal R) :
    J • (⊤ : Submodule R M) = ⊥ ↔ ∀ r ∈ J, ∀ z : M, r • z = 0 := by
  rw [← Submodule.le_annihilator_iff]
  exact ⟨fun h r hr z => Submodule.mem_annihilator.1 (h hr) z trivial,
    fun h r hr => Submodule.mem_annihilator.2 fun z _ => h r hr z⟩

/-- **`Iⁿ F` vanishes exactly when `I(W)ⁿ` annihilates the sections of `F` over every étale
chart `W`.**

The sections of `Iⁿ` over a chart are only locally `n`-fold products of sections of `I`, so the
direction from the chartwise condition uses that a section of `F` killed along a covering family
is itself killed. -/
theorem idealSmul_idealPow_top_eq_bot_iff
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M : Modules.{u, m} B S hS F hF) (n : ℕ) :
    Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n) ⊤ = ⊥ ↔
      ∀ W : SmallEtale B S hS F,
        chartSectionIdeal B S hS F hF I W ^ n •
          (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) = ⊥ := by
  rw [← le_bot_iff]
  constructor
  · intro h W
    refine (ideal_smul_top_eq_bot_iff _).2 fun a ha z => ?_
    have hmem : a • z ∈ (Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n) ⊤).obj
        (op W) :=
      Stacks.Sites.smul_mem_idealSmul _ (Stacks.Sites.mem_idealPow_of_mem_pow I n ha)
        (mem_top_submodule_obj B S hS F hF M z)
    have hz := SheafOfModules.Submodule.le_iff.1 h (op W) hmem
    rw [SheafOfModules.Submodule.bot_obj] at hz
    exact (Submodule.mem_bot _).1 hz
  · intro h
    refine Stacks.SheafOfModules.sheafifySubmodule_le
      (Stacks.Sites.presheafIdealSmul_le (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n) ?_)
    intro W a ha z _
    rw [show (⊥ : M.Submodule).toSubmodule.obj W = ⊥ from
      SheafOfModules.Submodule.bot_obj M W]
    refine (Submodule.mem_bot _).2 ?_
    obtain ⟨Sv, hSv, hres⟩ :=
      Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule ha
    refine (Presheaf.IsSheaf.isSeparated M.isSheaf) W.unop Sv hSv (a • z) 0 ?_
    intro Y f hf
    have hmul : M.val.presheaf.map f.op (a • z) =
        (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.map
          f.op a) • M.val.presheaf.map f.op z := M.val.map_smul f.op a z
    rw [hmul, map_zero]
    exact (ideal_smul_top_eq_bot_iff _).1 (h Y) _ (hres f hf) _

/-- A module annihilated chartwise by a power of a sheaf of ideals has no nonzero sections over a
chart on which that sheaf of ideals is the whole structure sheaf. -/
theorem subsingleton_sections_of_chartIdeal_eq_top
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M : Modules.{u, m} B S hS F hF) {n : ℕ} {W : SmallEtale B S hS F}
    (hn : chartSectionIdeal B S hS F hF I W ^ n •
      (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) = ⊥)
    (hW : I.obj (op W) = ⊤) :
    Subsingleton (M.val.obj (op W)) := by
  rw [show chartSectionIdeal B S hS F hF I W = ⊤ from hW, Ideal.top_pow] at hn
  exact subsingleton_of_forall_eq 0 fun z => by
    simpa using (ideal_smul_top_eq_bot_iff _).1 hn 1 trivial z


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Restriction of the ideal of sections of a sheaf of ideals -/

/-- **Where the sections of a sheaf of ideals base change along a morphism of étale charts, the
ideal of sections over the smaller chart is generated by the restrictions of the sections over
the larger one.**

Surjectivity of the base change comparison writes a section over the smaller chart as a
combination of restricted sections, which is membership in the image ideal. -/
theorem chartIdeal_le_map_chartRestrict
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {U W : SmallEtale B S hS F} (g : W ⟶ U)
    (hI : Function.Surjective (sectionsBaseChange I.toSheafOfModules g)) :
    chartSectionIdeal B S hS F hF I W ≤
      Ideal.map (chartRestrict (hF := hF) g) (chartSectionIdeal B S hS F hF I U) := by
  let _ := chartAlgebra (hF := hF) g
  have key : ∀ t : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF W)
      (I.toSheafOfModules.val.obj (op U)),
      (chartSectionIdeal B S hS F hF I W).subtype (sectionsBaseChange I.toSheafOfModules g t) ∈
        Ideal.map (chartRestrict (hF := hF) g) (chartSectionIdeal B S hS F hF I U) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b y =>
      have hb : (chartSectionIdeal B S hS F hF I W).subtype
            (sectionsBaseChange I.toSheafOfModules g
              (TensorProduct.tmul (chartRing B S hS F hF U) b y))
          = b * chartRestrict (hF := hF) g ((chartSectionIdeal B S hS F hF I U).subtype y) := rfl
      rw [hb]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ y.2)
    | add x y hx hy =>
      simp only [map_add]
      exact Ideal.add_mem _ hx hy
  intro a ha
  obtain ⟨t, ht⟩ := hI ⟨a, ha⟩
  have h := key t
  rw [ht] at h
  exact h

/-- Restriction along a morphism of étale charts carries the ideal of sections of a sheaf of
ideals into the ideal of sections over the smaller chart. -/
theorem chartIdeal_map_mem
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {U W : SmallEtale B S hS F} (g : W ⟶ U) {a : chartRing B S hS F hF U}
    (ha : a ∈ chartSectionIdeal B S hS F hF I U) :
    chartRestrict (hF := hF) g a ∈ chartSectionIdeal B S hS F hF I W :=
  I.map_mem g.op ha

/-- Restriction along a morphism of étale charts carries the `n`-th power of the ideal of
sections of a sheaf of ideals into the `n`-th power of the ideal of sections over the smaller
chart. -/
theorem map_chartIdeal_pow_le
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {U W : SmallEtale B S hS F} (g : W ⟶ U) (n : ℕ) :
    Ideal.map (chartRestrict (hF := hF) g) (chartSectionIdeal B S hS F hF I U ^ n) ≤
      chartSectionIdeal B S hS F hF I W ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun _ ha =>
    Ideal.mem_comap.2 (chartIdeal_map_mem B S hS F hF I g ha)) n

/-! ### Transfer of the annihilation along a morphism of affine charts -/

/-- **An annihilation of a module by a power of a sheaf of ideals transfers along a morphism of
affine étale charts.**  Let `M` be an `𝒪_F`-module and `ℐ ⊆ 𝒪_F` a sheaf of ideals, both
cartesian on affine charts, and let `g : W ⟶ U` be a morphism of étale charts with affine
underlying schemes.  If `ℐ(U)ⁿ · M(U) = 0` then `ℐ(W)ⁿ · M(W) = 0`.

The ideal `ℐ(W)` is generated by the restrictions of `ℐ(U)`, so `ℐ(W)ⁿ` is contained in the ideal
generated by the restrictions of `ℐ(U)ⁿ`; and the restriction of a section of `ℐ(U)ⁿ` kills every
section of `M` over `W`, because such a section is a combination of restricted sections and
restriction is semilinear. -/
theorem sectionIdeal_pow_smul_top_eq_bot_of_hom_of_isAffine
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M)
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    {U W : SmallEtale B S hS F} (hU : IsAffine (chartScheme U)) (hW : IsAffine (chartScheme W))
    (g : W ⟶ U) (n : ℕ)
    (hn : chartSectionIdeal B S hS F hF I U ^ n •
      (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) = ⊥) :
    chartSectionIdeal B S hS F hF I W ^ n •
      (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) = ⊥ := by
  let _ := chartAlgebra (hF := hF) g
  let _ := chartSectionsModule M g
  have _ := chartSections_isScalarTower M g
  -- the restriction of a section of `ℐ(U)ⁿ` kills every section of `M` over `W`
  have key : ∀ c ∈ chartSectionIdeal B S hS F hF I U ^ n, ∀ z : M.val.obj (op W),
      chartRestrict (hF := hF) g c • z = 0 := by
    intro c hc z
    obtain ⟨t, rfl⟩ := (hMcart U W hU hW g).2 z
    induction t using TensorProduct.inductionOn with
    | tmul b m =>
      have hcm : (c • m : M.val.obj (op U)) = 0 := by
        exact (ideal_smul_top_eq_bot_iff _).1 hn c hc m
      have hrs : chartRestrictLinear M g (c • m)
          = chartRestrict (hF := hF) g c • chartRestrictLinear M g m :=
        map_smul (chartRestrictLinear M g) c m
      rw [chartBaseChange_tmul M g b m, smul_smul, mul_comm, ← smul_smul, ← hrs, hcm, map_zero,
        smul_zero]
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  -- the `n`-th power of the ideal over `W` consists of restrictions of sections of `ℐ(U)ⁿ`
  have hKn : chartSectionIdeal B S hS F hF I W ^ n ≤
      Ideal.map (chartRestrict (hF := hF) g) (chartSectionIdeal B S hS F hF I U ^ n) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono
      (chartIdeal_le_map_chartRestrict B S hS F hF I g (hIcart U W hU hW g).2) n
  have hann : Ideal.map (chartRestrict (hF := hF) g) (chartSectionIdeal B S hS F hF I U ^ n) ≤
      (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))).annihilator := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Submodule.mem_annihilator]
    exact fun z _ => key c hc z
  exact Submodule.le_annihilator_iff.1 (hKn.trans hann)

/-! ### Covering a chart by affine charts over a surjective chart -/

/-- **A chart of an algebraic space carrying a surjective étale chart `U` is covered by charts
with affine underlying scheme which map to `U`.**

The fibre product `W ×_F U` maps onto `W`, because `U` maps onto `F`, so it alone covers `W`; any
chart over it is covered by the affine opens of its underlying scheme, and those map to `U`
through `W ×_F U`. -/
theorem exists_covering_through_affine_over (U : SmallEtale B S hS F)
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.1.hom)
    (W : SmallEtale B S hS F) :
    ∃ Sv : Sieve W, Sv ∈ SmallEtale.topology B S hS F W ∧
      ∀ ⦃Y : SmallEtale B S hS F⦄ (h : Y ⟶ W), Sv h →
        ∃ (A : SmallEtale B S hS F) (l : Y ⟶ A) (m : A ⟶ W) (_ : A ⟶ U),
          IsAffine (chartScheme A) ∧ h = l ≫ m := by
  let c : SmallEtale.prodObj B S hS F W U ⟶ W := SmallEtale.prodFst B S hS F W U
  let d : SmallEtale.prodObj B S hS F W U ⟶ U := SmallEtale.prodSnd B S hS F W U
  have hcs : Surjective ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map c)) :=
    hUsurj.property W.1.hom (yoneda.map (W.property.rep.snd U.1.hom))
      (W.property.rep.fst' U.1.hom) (W.property.rep.isPullback' U.1.hom).flip
  let Sv : Sieve W :=
    { arrows := fun Y h => ∃ (A : SmallEtale B S hS F) (l : Y ⟶ A) (m : A ⟶ W) (_ : A ⟶ U),
        IsAffine (chartScheme A) ∧ h = l ≫ m
      downward_closed := by
        rintro Y Z h ⟨A, l, m, e, hA, rfl⟩ q
        exact ⟨A, q ≫ l, m, e, hA, by simp⟩ }
  refine ⟨Sv, ?_, fun Y h hh => hh⟩
  refine (SmallEtale.topology B S hS F).transitive
    (sieve_generate_singleton_chart_mem_topology B S hS F c hcs) Sv ?_
  rintro Z f ⟨Y', g₁, g₂, hg₂, rfl⟩
  obtain ⟨⟩ := hg₂
  obtain ⟨ι, Y, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F Z
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hcov
  rintro Y₀ k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, q, rfl⟩ := hk
  exact ⟨Y j, q, a j ≫ g₁ ≫ c, a j ≫ g₁ ≫ d, haff j, by simp⟩

/-! ### Globalisation -/

/-- **The globalisation step of Stacks 07UK.**  Let `M` be a quasi-coherent `𝒪_F`-module and
`ℐ ⊆ 𝒪_F` a quasi-coherent sheaf of ideals on an algebraic space `F`, and let `U` be an étale
chart with affine underlying scheme whose structure morphism is surjective.  If
`ℐ(U)ⁿ · M(U) = 0` then `ℐ(W)ⁿ · M(W) = 0` for every étale chart `W`.

Every chart is covered by affine charts mapping to `U`, on each of which the annihilation holds
by `AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_hom_of_isAffine`; restriction
carries a section of `ℐ(W)ⁿ` into the `n`-th power of the ideal over the covering chart and is
semilinear, so the restricted product vanishes, and `M` is separated. -/
theorem sectionIdeal_pow_smul_top_eq_bot_of_presheafSurjective_affine_chart
    (M : Modules.{u, u} B S hS F hF) (hMqc : M.IsQuasicoherentOnSite)
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIqc : I.toSheafOfModules.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.1.hom)
    (n : ℕ)
    (hn : chartSectionIdeal B S hS F hF I U ^ n •
      (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) = ⊥) :
    ∀ W : SmallEtale B S hS F,
      chartSectionIdeal B S hS F hF I W ^ n •
        (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) = ⊥ := by
  have hMcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hMqc
  have hIcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
    I.toSheafOfModules hIqc
  intro W
  obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_affine_over B S hS F U hUsurj W
  refine (ideal_smul_top_eq_bot_iff _).2 fun r hr z => ?_
  -- the product vanishes on every chart over `W` which is affine and maps to `U`
  have hzero : ∀ {A : SmallEtale B S hS F} (m : A ⟶ W), IsAffine (chartScheme A) →
      (A ⟶ U) → chartRestrictLinear M m (r • z) = 0 := by
    intro A m hA e
    let _ := chartAlgebra (hF := hF) m
    let _ := chartSectionsModule M m
    have _ := chartSections_isScalarTower M m
    have hAbot := sectionIdeal_pow_smul_top_eq_bot_of_hom_of_isAffine B S hS F hF M hMcart I
      hIcart hU hA e n hn
    have hlin : chartRestrictLinear M m (r • z)
        = chartRestrict (hF := hF) m r • chartRestrictLinear M m z :=
      map_smul (chartRestrictLinear M m) r z
    rw [hlin]
    exact (ideal_smul_top_eq_bot_iff _).1 hAbot _
      (map_chartIdeal_pow_le B S hS F hF I m n (Ideal.mem_map_of_mem _ hr)) _
  -- hence on every member of the covering
  have hsieve : ∀ {Y : SmallEtale B S hS F} (f : Y ⟶ W), Sv f →
      chartRestrictLinear M f (r • z) = 0 := by
    intro Y f hf
    obtain ⟨A, l, m, e, hA, rfl⟩ := hfac f hf
    rw [chartRestrictLinear_comp M m l (r • z), hzero m hA e, map_zero]
  refine M.isSheaf.isSeparated W Sv hSv (r • z) 0 ?_
  intro Y f hf
  rw [show M.val.presheaf.map f.op (r • z) = 0 from hsieve f hf]
  exact (map_zero _).symm

/-- **The globalisation step of Stacks 07UK**, with surjectivity of the affine chart spelled out
on points.

This is the same statement as
`AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_presheafSurjective_affine_chart`,
the two forms of surjectivity being identified by Stacks 03H5. -/
theorem sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart
    (M : Modules.{u, u} B S hS F hF) (hMqc : M.IsQuasicoherentOnSite)
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIqc : I.toSheafOfModules.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hUsurj : Function.Surjective (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.1.hom))
    (n : ℕ)
    (hn : chartSectionIdeal B S hS F hF I U ^ n •
      (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) = ⊥) :
    ∀ W : SmallEtale B S hS F,
      chartSectionIdeal B S hS F hF I W ^ n •
        (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) = ⊥ :=
  sectionIdeal_pow_smul_top_eq_bot_of_presheafSurjective_affine_chart B S hS F hF M hMqc I hIqc
    U hU ((surjective_iff_surjective_pointsMap B S hS F hF
      ((SmallEtale.toOver B S hS F).obj U) U.1.hom).2 hUsurj) n hn




/-! ### A finite module with vanishing localization -/

/-- A finite module whose localization away from an element of the base ring vanishes is
annihilated by a power of that element. -/
@[sga "6 IX 1.1" "(f), special case"]
private theorem exists_pow_mem_annihilator_of_subsingleton_tensor {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] (hN : Module.Finite A N) (f : A)
    (A' : Type*) [CommRing A'] [Algebra A A'] (hA' : IsLocalization.Away f A')
    (hsub : Subsingleton (A' ⊗[A] N)) :
    ∃ k : ℕ, f ^ k ∈ Module.annihilator A N := by
  classical
  have := hN
  have := hA'
  have hmono : ∀ (y : N) (j m : ℕ), f ^ j • y = 0 → j ≤ m → f ^ m • y = 0 := by
    intro y j m hj hjm
    rw [← Nat.sub_add_cancel hjm, pow_add, mul_smul, hj, smul_zero]
  have hzero : ∀ y : N, ∃ k : ℕ, f ^ k • y = 0 := by
    intro y
    have h0 : TensorProduct.mk A A' N 1 y = 0 := hsub.allEq _ _
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (TensorProduct.mk A A' N 1)).1 h0
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    exact ⟨k, by rw [hk]; exact hs⟩
  obtain ⟨r, x, hx⟩ := Module.Finite.exists_fin (R := A) (M := N)
  choose k hk using fun i : Fin r => hzero (x i)
  refine ⟨Finset.univ.sup k, ?_⟩
  rw [← Submodule.annihilator_top, ← hx, Submodule.mem_annihilator_span]
  rintro ⟨_, i, rfl⟩
  exact hmono (x i) (k i) _ (hk i) (Finset.le_sup (Finset.mem_univ i))

/-! ### The chart cut out by a nonvanishing locus -/

variable {B S hS F hF}

/-- **The regular functions on the nonvanishing locus of a regular function `f` on an affine
étale chart are the localization away from `f` of the regular functions on the chart.**

The nonvanishing locus is a Zariski open of the chart, hence again an étale chart, and the
statement is the corresponding one for the scheme underlying the chart. -/
theorem isLocalization_away_chartRing_basicOpen {U : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (f : chartRing B S hS F hF U) :
    letI := chartAlgebra (hF := hF)
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
    IsLocalization.Away f
      (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen f))) := by
  have := hU
  have hmap : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))) =
      ((chartScheme U).basicOpen f).ι :=
    toScheme_map_toOver_map_openChartInclusion B S hS F U ((chartScheme U).basicOpen f)
  have hring : chartRestrict (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) =
      ((chartScheme U).basicOpen f).ι.appTop.hom := by
    rw [chartRestrict_eq_appTop, hmap]
    rfl
  have halg : chartAlgebra (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) =
      AlgebraicGeometry.ΓRestrictAlgebra ((chartScheme U).basicOpen f) :=
    congrArg RingHom.toAlgebra hring
  change @IsLocalization.Away (chartRing B S hS F hF U) _ f _ _
    (chartAlgebra (hF := hF)
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)))
  rw [halg]
  exact AlgebraicGeometry.Γ_restrict_isLocalization (chartScheme U) f

/-! ### A power of a function annihilating the sections over a chart -/

/-- **A regular function on a Noetherian affine étale chart which kills the sections of a
coherent module over its own nonvanishing locus has a power annihilating the sections over the
chart.**

A coherent module is cartesian on affine charts, so its sections over the nonvanishing locus
are the localization away from the function of its sections over the chart, and the latter form
a finite module. -/
theorem exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen
    (M : Modules.{u, u} B S hS F hF) (hM : IsCoherent B S hS F hF M)
    {U : SmallEtale B S hS F} (hU : IsNoetherianAffineChart B S hS F U)
    (f : chartRing B S hS F hF U)
    (hsub : Subsingleton
      (M.val.obj (op (openChart B S hS F U ((chartScheme U).basicOpen f))))) :
    ∃ k : ℕ, ∀ x : M.val.obj (op U), f ^ k • x = 0 := by
  have hUaff : IsAffine (chartScheme U) := hU.1
  have hVaff : IsAffine
      (chartScheme (openChart B S hS F U ((chartScheme U).basicOpen f))) :=
    (isAffineOpen_top (chartScheme U)).basicOpen f
  let _ := chartAlgebra (hF := hF)
    (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
  have hfin : Module.Finite (chartRing B S hS F hF U) (M.val.obj (op U)) :=
    moduleFinite_sections_of_isNoetherianAffineChart B S hS F hF M hM hU
  have hbij := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M
    hM.toIsQuasicoherentOnSite U (openChart B S hS F U ((chartScheme U).basicOpen f))
    hUaff hVaff (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
  obtain ⟨k, hk⟩ := exists_pow_mem_annihilator_of_subsingleton_tensor hfin f
    (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen f)))
    (isLocalization_away_chartRing_basicOpen hUaff f)
    ⟨fun a b => hbij.1 (hsub.allEq _ _)⟩
  exact ⟨k, fun x => Module.mem_annihilator.1 hk x⟩

/-! ### A power of the ideal annihilating the sections over a chart -/

variable (B S hS F hF)

/-- **Stacks 07UK, the local step.**  Let `M` be a coherent `𝒪_F`-module on an algebraic space
and let `I ⊆ 𝒪_F` be a sheaf of ideals which is the unit ideal only over charts carrying no
sections of `M`.  Over a Noetherian affine étale chart `U` some power of the ideal `I(U)`
annihilates the sections `M(U)`. -/
theorem exists_pow_sectionIdeal_smul_top_eq_bot
    (M : Modules.{u, u} B S hS F hF) (hM : IsCoherent B S hS F hF M)
    (I : (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (U : SmallEtale B S hS F) (hU : IsNoetherianAffineChart B S hS F U)
    (h : ∀ V : SmallEtale B S hS F, I.obj (op V) = ⊤ → Subsingleton (M.val.obj (op V))) :
    ∃ n : ℕ, chartSectionIdeal B S hS F hF I U ^ n •
      (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) = ⊥ := by
  have hUaff : IsAffine (chartScheme U) := hU.1
  have hUn : IsNoetherianRing (chartRing B S hS F hF U) := hU.2
  have hrad : chartSectionIdeal B S hS F hF I U ≤
      (Module.annihilator (chartRing B S hS F hF U) (M.val.obj (op U))).radical := by
    intro f hf
    let _ := chartAlgebra (hF := hF)
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
    have := isLocalization_away_chartRing_basicOpen (hF := hF) hUaff f
    have hunit : IsUnit (chartRestrict (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) f) :=
      IsLocalization.map_units (M := Submonoid.powers f)
        (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen f)))
        ⟨f, Submonoid.mem_powers f⟩
    have hmem : chartRestrict (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) f ∈
        chartSectionIdeal B S hS F hF I
          (openChart B S hS F U ((chartScheme U).basicOpen f)) :=
      Stacks.Sites.map_mem_sectionIdeal I
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)).op hf
    have htop : I.obj (op (openChart B S hS F U ((chartScheme U).basicOpen f))) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hmem hunit
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen M hM hU f
      (h _ htop)
    exact Ideal.mem_radical_iff.2 ⟨k, Module.mem_annihilator.2 hk⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (chartSectionIdeal B S hS F hF I U))
  refine ⟨n, ?_⟩
  rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff] at hn



end Chart

/-! ### Vanishing of a module read on its sections -/

/-- An `𝒪_X`-module all of whose groups of sections are subsingletons is zero. -/
theorem isZero_of_subsingleton_val_obj (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, m} B S hS X.1 X.2)
    (h : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, Subsingleton (F.val.obj U)) :
    IsZero F := by
  refine (IsZero.iff_id_eq_zero F).mpr ?_
  ext U s
  exact (h U).elim _ _

/-! ### Restriction to an étale chart -/

/-- An étale chart of the algebraic space represented by `V`, read as an étale chart of `X`,
comes with a morphism of charts to `V`: its structure morphism to `V` is the morphism of the big
fppf site given by the Yoneda lemma. -/
private def chartHomOver (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)
    (A : SmallEtale B S hS (chartSpace B S hS X V).1) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj A ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yonedaEquiv A.obj.hom)
    (congrArg (fun α => α ≫ V.obj.hom)
      (yonedaEquiv.injective rfl : yoneda.map (yonedaEquiv A.obj.hom) = A.obj.hom)))

/-- An étale chart of `X` over `V`, read as an étale chart of the algebraic space represented
by `V`. -/
private def chartOfHom (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)
    {W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    SmallEtale B S hS (chartSpace B S hS X V).1 :=
  ⟨CostructuredArrow.mk (yoneda.map g.hom.left),
    SmallEtale.presheaf_etale_yoneda_map B S hS g.hom.left W.property V.property
      (CostructuredArrow.w g.hom)⟩

/-- Reading an étale chart of `X` over `V` as a chart of the space represented by `V` and
pushing it back down recovers the chart. -/
private theorem smallEtalePostcomp_chartOfHom (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) {W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj (chartOfHom B S hS X V g) = W :=
  ObjectProperty.FullSubcategory.ext
    (congrArg (fun α : yoneda.obj W.obj.left ⟶ X.1 =>
      (CostructuredArrow.mk α : CostructuredArrow yoneda X.1)) (CostructuredArrow.w g.hom))

/-- **The restriction of an `𝒪_X`-module to an étale chart `V` vanishes exactly when the module
has no sections over any étale chart of `X` lying over `V`.** The étale charts of the algebraic
space represented by `V` are the étale charts of `X` over `V`, and restriction along an étale
morphism is restriction of sections. -/
theorem isZero_etaleModulePullback_chartToSpace_iff (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2) :
    IsZero ((etaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj F) ↔
      ∀ W : SmallEtale B S hS X.1, (W ⟶ V) → Subsingleton (F.val.obj (op W)) := by
  constructor
  · intro hz W g
    have h2 := subsingleton_sections_of_isZero B S hS (chartSpace B S hS X V) hz
      (op (chartOfHom B S hS X V g))
    exact (congrArg (fun Z : SmallEtale B S hS X.1 => Subsingleton (F.val.obj (op Z)))
      (smallEtalePostcomp_chartOfHom B S hS X V g)).mp h2
  · intro h
    refine isZero_of_subsingleton_val_obj B S hS (chartSpace B S hS X V) _ fun A => ?_
    exact h ((smallEtalePostcomp B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj A.unop) (chartHomOver B S hS X V A.unop)

/-! ### The support and the zero locus of a sheaf of ideals -/

/-- **A module with no sections over any chart lying over a chart on which the sheaf of ideals is
the whole structure sheaf has its support inside the zero locus of the ideal.** A point of the
unit locus lies in the image of such a chart, over which the module vanishes, so the support of
the module misses that image. -/
theorem supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ →
      ∀ W : SmallEtale B S hS X.1, (W ⟶ V) → Subsingleton (F.val.obj (op W))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      idealZeroLocus B S hS X I := by
  intro x hx
  rw [mem_idealZeroLocus_iff]
  rintro V hV ⟨y, hy⟩
  have hempty := (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X V)
    ((etaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj F)).mpr
    ((isZero_etaleModulePullback_chartToSpace_iff B S hS X V F).mpr (h V hV))
  rw [supportOfSheaf_chartToSpace] at hempty
  have hyx : pointsMap B S hS (chartSpace B S hS X V).1
      (chartToSpace B S hS X V).hom y = x := hy
  have hy2 : pointsMap B S hS (chartSpace B S hS X V).1
      (chartToSpace B S hS X V).hom y ∈
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
    rw [hyx]
    exact hx
  exact Set.eq_empty_iff_forall_notMem.mp hempty y hy2

/-- **A module whose support lies in the zero locus of a sheaf of ideals has no sections over a
chart on which the sheaf of ideals is the whole structure sheaf.** The image of such a chart lies
in the unit locus, which misses the support, so the restriction of the module to the chart has
empty support and therefore vanishes. -/
theorem subsingleton_sections_of_supportOfSheaf_subset_idealZeroLocus
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hsupp : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      idealZeroLocus B S hS X I)
    (V : SmallEtale B S hS X.1) (hV : I.obj (op V) = ⊤) :
    Subsingleton (F.val.obj (op V)) := by
  refine (isZero_etaleModulePullback_chartToSpace_iff B S hS X V F).mp ?_ V (𝟙 V)
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X V) _).mp ?_
  rw [supportOfSheaf_chartToSpace]
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  have hy2 : pointsMap B S hS (chartSpace B S hS X V).1
      (chartToSpace B S hS X V).hom y ∈
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := hy
  exact (mem_idealZeroLocus_iff B S hS X I _).mp (hsupp hy2) V hV ⟨y, rfl⟩

/-! ### A surjective Noetherian affine chart -/

/-- **A quasi-compact, locally Noetherian algebraic space has a surjective Noetherian affine
chart.** There is an étale chart of `X` whose underlying scheme is affine with Noetherian ring of
global sections and which is surjective, both as a relatively representable morphism and on
points. No quasi-separatedness is needed. -/
theorem exists_surjective_isNoetherianAffineChart_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    ∃ U : SmallEtale B S hS X.1,
      IsNoetherianAffineChart B S hS X.1 U ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf U.1.hom ∧
          Function.Surjective (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) := by
  obtain ⟨U₀, f, hAff, hSurj, hEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hqc
  have hEt' : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    presheaf_etale_of_isEtale B S hS hEt
  refine ⟨⟨CostructuredArrow.mk f, hEt'⟩, ⟨hAff, ?_⟩, hSurj,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ f).1 hSurj⟩
  have hLN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) X.2).1 hLN U₀ f hEt'
  exact isNoetherianRing_Γ_of_isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).obj U₀) hAff hLN

/-- **A Noetherian algebraic space has a surjective Noetherian affine chart.** There is an étale
chart of `X` whose underlying scheme is affine with Noetherian ring of global sections and which
is surjective, both as a relatively representable morphism and on points. -/
theorem exists_surjective_isNoetherianAffineChart
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hN : IsNoetherian B S hS hZ X.1) :
    ∃ U : SmallEtale B S hS X.1,
      IsNoetherianAffineChart B S hS X.1 U ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf U.1.hom ∧
          Function.Surjective (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) :=
  exists_surjective_isNoetherianAffineChart_of_isQuasiCompactSpace B S hS X hN.1 hN.2.2

/-! ### The forward implication -/

/-- **The easy half of Stacks 07UK.** If a power of a sheaf of ideals annihilates a module, the
support of the module lies in the zero locus of the ideal.  No finiteness hypothesis is needed:
over a chart on which the sheaf of ideals is the whole structure sheaf, and over every chart
below it, the module has no sections at all. -/
theorem supportOfSheaf_subset_idealZeroLocus_of_idealSmul_idealPow_top_eq_bot
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, m} B S hS X.1 X.2)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) {n : ℕ}
    (hn : Stacks.Sites.idealSmul (M := M)
      (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) I n) ⊤ = ⊥) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      idealZeroLocus B S hS X I := by
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X M I
    fun V hV W g => ?_
  exact subsingleton_sections_of_chartIdeal_eq_top B S hS X.1 X.2 I M
    ((idealSmul_idealPow_top_eq_bot_iff B S hS X.1 X.2 I M n).1 hn W)
    (SheafOfModules.Submodule.unit_obj_eq_top_of_map I g.op hV)

/-! ### Stacks 07UK -/

/-- **The substantial half of Stacks 07UK, chart by chart, on a quasi-compact locally Noetherian
algebraic space.** If a coherent module `F` has no sections over the charts on which the
quasi-coherent sheaf of ideals `ℐ` is the unit ideal, then `ℐⁿ F = 0` for some `n`. -/
theorem exists_idealPowSmul_eq_bot_of_forall_subsingleton (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (h : ∀ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ → Subsingleton (M.val.obj (op V))) :
    ∃ n : ℕ, Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) I n) ⊤ = ⊥ := by
  obtain ⟨U, hU, -, hUsurj⟩ :=
    exists_surjective_isNoetherianAffineChart_of_isQuasiCompactSpace B S hS X hqc hLN
  obtain ⟨n, hn⟩ := exists_pow_sectionIdeal_smul_top_eq_bot B S hS X.1 X.2 M hM I U hU h
  exact ⟨n, (idealSmul_idealPow_top_eq_bot_iff B S hS X.1 X.2 I M n).2
    (sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart B S hS X.1 X.2 M
      hM.toIsQuasicoherentOnSite I hI U hU.1 hUsurj n hn)⟩

/-- **Stacks 07UK, on a quasi-compact locally Noetherian algebraic space.** The statement of
`AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus`
without quasi-separatedness: `ℐⁿ F = 0` for some `n` if and only if the support of the coherent
module `F` lies in the zero locus of the quasi-coherent sheaf of ideals `ℐ`. -/
theorem exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) :
    (∃ n : ℕ, Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) I n) ⊤ = ⊥) ↔
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
        idealZeroLocus B S hS X I :=
  ⟨fun ⟨_, hn⟩ => supportOfSheaf_subset_idealZeroLocus_of_idealSmul_idealPow_top_eq_bot
      B S hS X M I hn,
    fun hsupp => exists_idealPowSmul_eq_bot_of_forall_subsingleton B S hS X hqc hLN M hM I hI
      fun V hV => subsingleton_sections_of_supportOfSheaf_subset_idealZeroLocus
        B S hS X M I hsupp V hV⟩

/-- **Stacks 07UK.** Let `X` be a Noetherian algebraic space over a scheme `S`, let `F` be a
coherent `𝒪_X`-module and let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals, cutting out the
closed subspace `Z ⊆ X`.  Then `ℐⁿ F = 0` for some `n ≥ 0` if and only if the support of `F` is
contained in `Z`, set theoretically.

The closed subspace enters only through its point set `|V(ℐ)|`, which is what the set-theoretic
containment refers to.  For the forward implication no finiteness is needed: over a chart on
which `ℐ` is the whole structure sheaf, and over every chart below it, `F` has no sections at
all, so the support misses the image of that chart.  The converse is the substantial half: on a
surjective affine chart with Noetherian ring of sections, which a Noetherian algebraic space has,
the sections of `F` form a finite module annihilated by a power of each section of `ℐ`, hence by
a power of `ℐ(U)` because the ring is Noetherian; and quasi-coherence carries that single
annihilation to every chart. -/
@[stacks 07UK, ega "I 9.3.4" "more general"]
theorem exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hN : IsNoetherian B S hS hZ X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) :
    (∃ n : ℕ, Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) I n) ⊤ = ⊥) ↔
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
        idealZeroLocus B S hS X I :=
  exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus_of_isQuasiCompactSpace
    B S hS X hN.1 hN.2.2 M hM I hI

end AlgebraicGeometry.Space

end
