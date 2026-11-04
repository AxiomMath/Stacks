module

public import Mathlib.RingTheory.Filtration
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange

/-!
# Artin-Rees for coherent sheaves on a Noetherian algebraic space

Let `F` be a Noetherian algebraic space, `M` a coherent `𝒪_F`-module, `G ⊆ M` a quasi-coherent
submodule and `I ⊆ 𝒪_F` a quasi-coherent sheaf of ideals.  One Artin-Rees constant `c` works
uniformly over the whole space: `I ⁿ⁻ᶜ (I ᶜ M ⊓ G) = I ⁿ M ⊓ G` for every `n ≥ c`.

## Main results

* `ArtinReesBaseChange.pow_inf_eq_pow_smul_baseChange`: an Artin-Rees identity survives flat base
  change.
* `AlgebraicGeometry.Space.pow_chartIdeal_inf_eq_of_chartHom`: the identity on sections transfers
  from an affine chart to any affine chart over it, with the same constant.
* `AlgebraicGeometry.Space.exists_idealPowSmul_inf_eq`: Artin-Rees on a Noetherian algebraic
  space.

## References

* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped TensorProduct

universe u m

/-! ### Base change of an Artin-Rees identity -/

/-- Base change of an ideal multiple of a submodule: `(J • X) ⊗ B = JB • (X ⊗ B)`. -/
theorem ArtinReesBaseChange.baseChange_ideal_smul {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] (J : Ideal A) (X : Submodule A M) :
    Submodule.baseChange B (J • X)
      = (Ideal.map (algebraMap A B) J) • Submodule.baseChange B X := by
  have h1 : J • X = Submodule.map X.subtype (J • (⊤ : Submodule A X)) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [h1, ← ArtinReesBaseChange.map_baseChange, ← ArtinReesBaseChange.ideal_smul_top,
    Submodule.map_smul'', Submodule.map_top, ArtinReesBaseChange.range_subtype_baseChange]

/-- An Artin-Rees identity survives flat base change: if the identity
`Jⁿ M ⊓ N = J ⁿ⁻ᶜ (J ᶜ M ⊓ N)` holds over `A`, the corresponding identity for `JB` and
`N ⊗ B ⊆ M ⊗ B` holds over a flat `A`-algebra `B`. -/
theorem ArtinReesBaseChange.pow_inf_eq_pow_smul_baseChange {A B M : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M] (J : Ideal A)
    (N : Submodule A M) {c n : ℕ}
    (h : J ^ n • (⊤ : Submodule A M) ⊓ N = J ^ (n - c) • (J ^ c • (⊤ : Submodule A M) ⊓ N)) :
    (Ideal.map (algebraMap A B) J) ^ n • (⊤ : Submodule B (B ⊗[A] M))
          ⊓ Submodule.baseChange B N
        = (Ideal.map (algebraMap A B) J) ^ (n - c) •
          ((Ideal.map (algebraMap A B) J) ^ c • (⊤ : Submodule B (B ⊗[A] M))
            ⊓ Submodule.baseChange B N) := by
  rw [← Ideal.map_pow, ArtinReesBaseChange.ideal_smul_top,
    ← ArtinReesBaseChange.baseChange_inf, h, ArtinReesBaseChange.baseChange_ideal_smul,
    Ideal.map_pow, ← Ideal.map_pow (I := J) (n := c), ArtinReesBaseChange.ideal_smul_top,
    ← ArtinReesBaseChange.baseChange_inf]

/-- An Artin-Rees identity for `J` and `N ⊆ M` over `A` gives the identity for the extension `J'`
of `J` and the submodule `N'` corresponding to `N`, over a flat `A`-algebra `B` and a
`B`-module `M'` isomorphic to `B ⊗[A] M`. -/
theorem ArtinReesBaseChange.pow_inf_eq_pow_smul_of_equiv {A B M M' : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module B M'] (e : (B ⊗[A] M) ≃ₗ[B] M') (J : Ideal A)
    (N : Submodule A M) {J' : Ideal B} {N' : Submodule B M'}
    (hJ' : Ideal.map (algebraMap A B) J = J')
    (hN' : Submodule.map e.toLinearMap (Submodule.baseChange B N) = N') {c n : ℕ}
    (h : J ^ n • (⊤ : Submodule A M) ⊓ N = J ^ (n - c) • (J ^ c • (⊤ : Submodule A M) ⊓ N)) :
    J' ^ n • (⊤ : Submodule B M') ⊓ N'
      = J' ^ (n - c) • (J' ^ c • (⊤ : Submodule B M') ⊓ N') := by
  subst hJ' hN'
  have hmap := congrArg (Submodule.map e.toLinearMap)
    (ArtinReesBaseChange.pow_inf_eq_pow_smul_baseChange (B := B) J N h)
  rwa [Submodule.map_inf e.toLinearMap e.injective, Submodule.map_smul'', Submodule.map_top,
    e.range, Submodule.map_smul'', Submodule.map_inf e.toLinearMap e.injective,
    Submodule.map_smul'', Submodule.map_top, e.range] at hmap

/-- An Artin-Rees constant may be enlarged. -/
theorem Ideal.pow_inf_eq_pow_smul_of_le {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (P : Submodule R N) {c C : ℕ} (hc : c ≤ C)
    (h : ∀ n : ℕ, c ≤ n → J ^ n • (⊤ : Submodule R N) ⊓ P
      = J ^ (n - c) • (J ^ c • (⊤ : Submodule R N) ⊓ P)) :
    ∀ n : ℕ, C ≤ n → J ^ n • (⊤ : Submodule R N) ⊓ P
      = J ^ (n - C) • (J ^ C • (⊤ : Submodule R N) ⊓ P) := by
  intro n hn
  rw [h n (hc.trans hn), h C hc, ← mul_smul, ← pow_add]
  congr 2
  lia

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Transfer of the identity along a morphism of affine charts -/

/-- The sections of a submodule over a smaller chart are spanned by the restrictions of its
sections over the larger one, as soon as the base change comparison of the submodule is
surjective. -/
theorem span_image_chartRestrictLinear_eq (M : Modules.{u, u} B S hS F hF) (G : M.Submodule)
    {U V : SmallEtale B S hS F} (φ : V ⟶ U)
    (hG : Function.Surjective (sectionsBaseChange G.toSheafOfModules φ)) :
    letI := chartAlgebra (hF := hF) φ
    Submodule.span (chartRing B S hS F hF V)
        (chartRestrictLinear M φ '' (chartSubmodule B S hS F hF G U : Set (M.val.obj (op U))))
      = chartSubmodule B S hS F hF G V := by
  let _ := chartAlgebra (hF := hF) φ
  let _ := chartSectionsModule M φ
  refine le_antisymm (Submodule.span_le.2 ?_) fun y hy => ?_
  · rintro z ⟨x, hx, rfl⟩
    exact G.map_mem φ.op hx
  · have key : ∀ t : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (G.toSheafOfModules.val.obj (op U)),
        (G.ι.val.app (op V)).hom (sectionsBaseChange G.toSheafOfModules φ t)
          ∈ Submodule.span (chartRing B S hS F hF V)
            (chartRestrictLinear M φ '' (chartSubmodule B S hS F hF G U : Set (M.val.obj (op U))))
              := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b g =>
          rw [chartBaseChange_tmul, map_smul]
          refine Submodule.smul_mem _ b ?_
          have hnat : (G.ι.val.app (op V)).hom (chartRestrictLinear G.toSheafOfModules φ g)
              = chartRestrictLinear M φ ((G.ι.val.app (op U)).hom g) :=
            PresheafOfModules.naturality_apply G.ι.val φ.op g
          rw [hnat]
          exact Submodule.subset_span ⟨(G.ι.val.app (op U)).hom g, g.2, rfl⟩
      | add t₁ t₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
    obtain ⟨t, ht⟩ := hG ⟨y, hy⟩
    have h := key t
    rwa [ht] at h

/-- The extension of the ideal of sections of a sheaf of ideals along a chart morphism is the
ideal of sections over the smaller chart, as soon as the base change comparison is surjective. -/
theorem ideal_map_chartRestrict_chartIdeal (I : IdealSheaves B S hS F hF)
    {U V : SmallEtale B S hS F} (φ : V ⟶ U)
    (hI : Function.Surjective (sectionsBaseChange I.toSheafOfModules φ)) :
    letI := chartRing_commRing B S hS F hF U
    letI := chartAlgebra (hF := hF) φ
    Ideal.map (algebraMap (chartRing B S hS F hF U) (chartRing B S hS F hF V))
        (chartSectionIdeal B S hS F hF I U)
      = chartSectionIdeal B S hS F hF I V := by
  let _ := chartRing_commRing B S hS F hF U
  let _ := chartAlgebra (hF := hF) φ
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun a ha => I.map_mem φ.op ha) fun y hy => ?_
  refine Submodule.span_le.2 ?_ ((span_image_chartRestrictLinear_eq B S hS F hF
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I φ hI).ge hy)
  rintro z ⟨x, hx, rfl⟩
  exact Ideal.mem_map_of_mem _ hx

/-- The image of the base change of a submodule of the sections under the comparison
equivalence is the span of the restricted sections. -/
theorem map_ofBijective_baseChange_eq_span (M : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (φ : V ⟶ U)
    (hM : Function.Bijective (sectionsBaseChange M φ))
    (P : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) :
    letI := chartRing_commRing B S hS F hF U
    letI := chartAlgebra (hF := hF) φ
    Submodule.map (LinearEquiv.ofBijective (sectionsBaseChange M φ) hM).toLinearMap
        (Submodule.baseChange (chartRing B S hS F hF V) P)
      = Submodule.span (chartRing B S hS F hF V)
          (chartRestrictLinear M φ '' (P : Set (M.val.obj (op U)))) := by
  let _ := chartRing_commRing B S hS F hF U
  let _ := chartAlgebra (hF := hF) φ
  let _ := chartSectionsModule M φ
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  rw [Submodule.map_coe, ← Set.image_comp]
  exact Set.image_congr fun x _ => chartBaseChange_one_tmul M φ x

/-- The Artin-Rees identity on sections transfers from an affine chart to an affine chart over
it, with the same constant, when the sections of `M`, `G` and `I` over the smaller chart are the
base changes of those over the larger one. -/
theorem pow_chartIdeal_inf_eq_of_chartHom (M : Modules.{u, u} B S hS F hF) (G : M.Submodule)
    (I : IdealSheaves B S hS F hF) {U V : SmallEtale B S hS F} (φ : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hMbij : Function.Bijective (sectionsBaseChange M φ))
    (hGsurj : Function.Surjective (sectionsBaseChange G.toSheafOfModules φ))
    (hIsurj : Function.Surjective (sectionsBaseChange I.toSheafOfModules φ))
    {c n : ℕ}
    (h : chartSectionIdeal B S hS F hF I U ^ n •
            (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U)))
              ⊓ chartSubmodule B S hS F hF G U
          = chartSectionIdeal B S hS F hF I U ^ (n - c) •
            (chartSectionIdeal B S hS F hF I U ^ c •
              (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U)))
                ⊓ chartSubmodule B S hS F hF G U)) :
    chartSectionIdeal B S hS F hF I V ^ n •
          (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))
            ⊓ chartSubmodule B S hS F hF G V
        = chartSectionIdeal B S hS F hF I V ^ (n - c) •
          (chartSectionIdeal B S hS F hF I V ^ c •
            (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))
              ⊓ chartSubmodule B S hS F hF G V) := by
  let _ := chartRing_commRing B S hS F hF U
  let _ := chartAlgebra (hF := hF) φ
  let _ := chartSectionsModule M φ
  have : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) :=
    moduleFlat_chartRing_of_isAffine (hF := hF) φ hU hV
  exact ArtinReesBaseChange.pow_inf_eq_pow_smul_of_equiv
    (LinearEquiv.ofBijective (sectionsBaseChange M φ) hMbij) (chartSectionIdeal B S hS F hF I U)
    (chartSubmodule B S hS F hF G U)
    (ideal_map_chartRestrict_chartIdeal B S hS F hF I φ hIsurj)
    ((map_ofBijective_baseChange_eq_span B S hS F hF M φ hMbij _).trans
      (span_image_chartRestrictLinear_eq B S hS F hF M G φ hGsurj)) h

/-! ### A uniform Artin-Rees constant -/

/-- A section of the objectwise product `Iⁿ · M` restricts, on a covering sieve, into the
objectwise product of the `n`-th power of the ideal of sections with all of `M`. -/
theorem exists_sieve_mem_pow_chartIdeal_smul_top (I : IdealSheaves B S hS F hF)
    (M : Modules.{u, m} B S hS F hF) (n : ℕ) {X : SmallEtale B S hS F}
    (P : Submodule (chartRing B S hS F hF X) (M.val.obj (op X))) {x : M.val.obj (op X)}
    (hx : x ∈ chartIdealPow B S hS F hF I n X • P) :
    ∃ Sv : Sieve X, Sv ∈ SmallEtale.topology B S hS F X ∧
      ∀ ⦃Y : SmallEtale B S hS F⦄ (f : Y ⟶ X), Sv f →
        chartRestrictLinear M f x ∈ chartSectionIdeal B S hS F hF I Y ^ n •
          (⊤ : Submodule (chartRing B S hS F hF Y) (M.val.obj (op Y))) := by
  refine Submodule.smul_induction_on hx (fun a ha w _ => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · obtain ⟨Sv, hSv, ha'⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule
      (N := Stacks.Sites.presheafIdealPow (O := siteStructure B S hS F hF) I n) ha
    refine ⟨Sv, hSv, fun Y f hf => ?_⟩
    rw [chartRestrictLinear_smul M]
    exact Submodule.smul_mem_smul (ha' f hf) Submodule.mem_top
  · obtain ⟨S₁, hS₁, h₁'⟩ := h₁
    obtain ⟨S₂, hS₂, h₂'⟩ := h₂
    refine ⟨S₁ ⊓ S₂, (SmallEtale.topology B S hS F).intersection_covering hS₁ hS₂,
      fun Y f hf => ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (h₁' f hf.1) (h₂' f hf.2)

/-- A section of the objectwise Artin-Rees right-hand side over a chart is a section of the
objectwise product `I ᵃ · (I ᵇ M ⊓ G)`. -/
theorem mem_presheafIdealSmul_of_mem_pow_chartIdeal_smul_inf (I : IdealSheaves B S hS F hF)
    (M : Modules.{u, m} B S hS F hF) (G : M.Submodule) (a b : ℕ)
    (X : SmallEtale B S hS F) {y : M.val.obj (op X)}
    (hy : y ∈ chartSectionIdeal B S hS F hF I X ^ a •
      (chartSectionIdeal B S hS F hF I X ^ b •
        (⊤ : Submodule (chartRing B S hS F hF X) (M.val.obj (op X)))
          ⊓ chartSubmodule B S hS F hF G X)) :
    y ∈ chartIdealPow B S hS F hF I a X • chartSubmodule B S hS F hF (idealPowSubmodule I b M
      ⊓ G) X := by
  refine Submodule.smul_induction_on hy (fun r hr w hw => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · refine Submodule.smul_mem_smul (pow_chartSectionIdeal_le_chartIdealPow B S hS F hF I a X hr) ?_
    exact Submodule.mem_inf.2
      ⟨pow_chartSectionIdeal_smul_top_le_chartSubmodule B S hS F hF I b X hw.1, hw.2⟩
  · exact Submodule.add_mem _ h₁ h₂

include hF in
/-- A family of charts refining a chart whose structure morphism is surjective covers the final
object of the small étale site. -/
theorem ofObjects_mem_topology_of_ofArrows {ι : Type*} {U : SmallEtale B S hS F}
    (hUsurj : IsSurjective B S hS U.1.hom) (A : ι → SmallEtale B S hS F)
    (mm : ∀ i, A i ⟶ U) (hcov : Sieve.ofArrows A mm ∈ SmallEtale.topology B S hS F U)
    (X : SmallEtale B S hS F) :
    Sieve.ofObjects A X ∈ SmallEtale.topology B S hS F X := by
  refine (SmallEtale.topology B S hS F).transitive
    (SmallEtale.coversTop_of_isSurjective B S hS F hF U hUsurj X) _ ?_
  intro Z g hg
  obtain ⟨-, ⟨q⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    ((SmallEtale.topology B S hS F).pullback_stable q hcov)
  rintro Y k ⟨C, t, p, ⟨i⟩, -⟩
  exact ⟨i, ⟨t⟩⟩

include hF in
/-- Every chart carries a covering sieve each of whose members factors through a Noetherian
affine chart lying over a member of a covering family. -/
theorem exists_covering_through_noetherianAffine_over
    (hLN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {ι : Type*} (A : ι → SmallEtale B S hS F)
    (hA : ∀ X : SmallEtale B S hS F,
      Sieve.ofObjects A X ∈ SmallEtale.topology B S hS F X)
    (W : SmallEtale B S hS F) :
    ∃ Sv : Sieve W, Sv ∈ SmallEtale.topology B S hS F W ∧
      ∀ ⦃Y : SmallEtale B S hS F⦄ (h : Y ⟶ W), Sv h →
        ∃ (i : ι) (C : SmallEtale B S hS F) (l : Y ⟶ C) (mc : C ⟶ W),
          Nonempty (C ⟶ A i) ∧ IsNoetherianAffineChart B S hS F C ∧ h = l ≫ mc := by
  classical
  let Sv : Sieve W :=
    { arrows := fun Y h => ∃ (i : ι) (C : SmallEtale B S hS F) (l : Y ⟶ C)
        (mc : C ⟶ W),
        Nonempty (C ⟶ A i) ∧ IsNoetherianAffineChart B S hS F C ∧ h = l ≫ mc
      downward_closed := by
        rintro Y Z h ⟨i, C, l, mc, hCA, hC, rfl⟩ g
        exact ⟨i, C, g ≫ l, mc, hCA, hC, (Category.assoc g l mc).symm⟩ }
  refine ⟨Sv, ?_, fun Y h hh => hh⟩
  refine (SmallEtale.topology B S hS F).transitive (hA W) Sv ?_
  intro Z g hg
  obtain ⟨i, ⟨q⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  obtain ⟨Sz, hSz, hfac⟩ := exists_covering_through_noetherianAffine B S hS F hF hLN Z
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hSz
  intro Y k hk
  obtain ⟨C, l, mc, hC, rfl⟩ := hfac k hk
  exact ⟨i, C, l, mc ≫ g, ⟨mc ≫ q⟩, hC, (Category.assoc l mc g).symm⟩

/-- The sieve of maps `g` along which the restriction of a section `w` lies in the objectwise
product `I ᵏ · (I ᶜ M ⊓ G)`. -/
private def artinReesSieve (I : IdealSheaves B S hS F hF) (M : Modules.{u, u} B S hS F hF)
    (G : M.Submodule) (k c : ℕ) {Y : SmallEtale B S hS F} (w : M.val.obj (op Y)) : Sieve Y where
  arrows Y' g := chartRestrictLinear M g w ∈ chartIdealPow B S hS F hF I k Y' •
    chartSubmodule B S hS F hF (idealPowSubmodule I c M ⊓ G) Y'
  downward_closed := by
    intro Y' Y'' g hg k'
    rw [chartRestrictLinear_comp M g k' w]
    exact chartRestrictLinear_mem_chartIdealPow_smul B S hS F hF I k _ k' hg

/-- A section of `Iⁿ M ⊓ G` over a chart lies, on a covering sieve, in the objectwise product
`I ⁿ⁻ᶜ · (I ᶜ M ⊓ G)`, provided the Artin-Rees identity with constant `c` holds on the sections
over each member of a covering family of affine charts. -/
theorem exists_sieve_mem_presheafIdealSmul_of_artinRees
    (I : IdealSheaves B S hS F hF) (M : Modules.{u, u} B S hS F hF) (G : M.Submodule)
    (hLN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hMcart : IsCartesianOnAffineCharts M)
    (hGcart : IsCartesianOnAffineCharts G.toSheafOfModules)
    (hIcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    {ι : Type*} (A : ι → SmallEtale B S hS F)
    (hAaff : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (A i)))
    (hA : ∀ X : SmallEtale B S hS F,
      Sieve.ofObjects A X ∈ SmallEtale.topology B S hS F X)
    {c n : ℕ}
    (hid : ∀ i, chartSectionIdeal B S hS F hF I (A i) ^ n •
            (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
            ⊓ chartSubmodule B S hS F hF G (A i)
          = chartSectionIdeal B S hS F hF I (A i) ^ (n - c) •
            (chartSectionIdeal B S hS F hF I (A i) ^ c •
              (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
              ⊓ chartSubmodule B S hS F hF G (A i)))
    (Y : SmallEtale B S hS F) {w : M.val.obj (op Y)}
    (hw1 : w ∈ chartIdealPow B S hS F hF I n Y •
      chartSubmodule B S hS F hF (⊤ : M.Submodule) Y)
    (hw2 : w ∈ G.obj (op Y)) :
    ∃ Sw : Sieve Y, Sw ∈ SmallEtale.topology B S hS F Y ∧
      ∀ ⦃Y' : SmallEtale B S hS F⦄ (g : Y' ⟶ Y), Sw g →
        chartRestrictLinear M g w ∈ chartIdealPow B S hS F hF I (n - c) Y' •
          chartSubmodule B S hS F hF (idealPowSubmodule I c M ⊓ G) Y' := by
  classical
  obtain ⟨S₁, hS₁, hS₁'⟩ :=
    exists_sieve_mem_pow_chartIdeal_smul_top B S hS F hF I M n _ hw1
  refine ⟨artinReesSieve B S hS F hF I M G (n - c) c w, ?_, fun Y' g hg => hg⟩
  refine (SmallEtale.topology B S hS F).transitive hS₁ _ ?_
  intro Y' g hg
  obtain ⟨S₂, hS₂, hS₂'⟩ :=
    exists_covering_through_noetherianAffine_over B S hS F hF hLN A hA Y'
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hS₂
  intro Y'' k hk
  obtain ⟨i, C, l, mc, ⟨t⟩, hC, rfl⟩ := hS₂' k hk
  have hCaff : IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj C) := hC.1
  have hidC := pow_chartIdeal_inf_eq_of_chartHom B S hS F hF M G I t (hAaff i) hCaff
    (hMcart (A i) C (hAaff i) hCaff t) (hGcart (A i) C (hAaff i) hCaff t).2
    (hIcart (A i) C (hAaff i) hCaff t).2 (hid i)
  have hu1 : chartRestrictLinear M mc (chartRestrictLinear M g w) ∈
      chartSectionIdeal B S hS F hF I C ^ n •
        (⊤ : Submodule (chartRing B S hS F hF C) (M.val.obj (op C))) :=
    map_mem_pow_chartSectionIdeal_smul_top B S hS F hF I M mc n (hS₁' g hg)
  have hu2 : chartRestrictLinear M mc (chartRestrictLinear M g w) ∈
      chartSubmodule B S hS F hF G C :=
    chartRestrictLinear_mem_chartSubmodule B S hS F hF G mc
      (chartRestrictLinear_mem_chartSubmodule B S hS F hF G g hw2)
  have hu : chartRestrictLinear M mc (chartRestrictLinear M g w) ∈
      chartIdealPow B S hS F hF I (n - c) C •
        chartSubmodule B S hS F hF (idealPowSubmodule I c M ⊓ G) C :=
    mem_presheafIdealSmul_of_mem_pow_chartIdeal_smul_inf B S hS F hF I M G (n - c) c C
      (hidC ▸ Submodule.mem_inf.2 ⟨hu1, hu2⟩)
  have hfin := (Stacks.Sites.presheafIdealSmul (O := siteStructure B S hS F hF) (M := M)
          (Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I (n - c))
    (idealPowSubmodule I c M ⊓ G).toSubmodule).map l.op
    ((presheafIdealSmul_obj_eq B S hS F hF I (n - c) _ C).le hu)
  rw [← presheafIdealSmul_obj_eq] at hfin
  show chartRestrictLinear M ((l ≫ mc) ≫ g) w ∈ _
  rw [chartRestrictLinear_comp M g (l ≫ mc) w,
    chartRestrictLinear_comp M mc l]
  exact hfin

include hF in
/-- The inclusion `Iⁿ M ⊓ G ≤ I ⁿ⁻ᶜ (I ᶜ M ⊓ G)`, as soon as the Artin-Rees identity with
constant `c` holds on the sections over each member of a covering family of affine charts. -/
theorem idealPowSubmodule_inf_le_idealPowSmul
    (I : IdealSheaves B S hS F hF) (M : Modules.{u, u} B S hS F hF) (G : M.Submodule)
    (hLN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hMcart : IsCartesianOnAffineCharts M)
    (hGcart : IsCartesianOnAffineCharts G.toSheafOfModules)
    (hIcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    {ι : Type*} (A : ι → SmallEtale B S hS F)
    (hAaff : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (A i)))
    (hA : ∀ X : SmallEtale B S hS F,
      Sieve.ofObjects A X ∈ SmallEtale.topology B S hS F X)
    {c n : ℕ}
    (hid : ∀ i, chartSectionIdeal B S hS F hF I (A i) ^ n •
            (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
            ⊓ chartSubmodule B S hS F hF G (A i)
          = chartSectionIdeal B S hS F hF I (A i) ^ (n - c) •
            (chartSectionIdeal B S hS F hF I (A i) ^ c •
              (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
              ⊓ chartSubmodule B S hS F hF G (A i))) :
    idealPowSubmodule I n M ⊓ G
      ≤ Stacks.Sites.idealPowSmul I (n - c) (idealPowSubmodule I c M ⊓ G) := by
  classical
  refine _root_.SheafOfModules.Submodule.le_iff.2 fun X z hz => ?_
  obtain ⟨W, rfl⟩ : ∃ W : SmallEtale B S hS F, X = op W := ⟨X.unop, rfl⟩
  obtain ⟨hzI, hzG⟩ := hz
  obtain ⟨S₀, hS₀, hS₀'⟩ :=
    exists_sieve_of_mem_idealPowSmul B S hS F hF I n (⊤ : M.Submodule) hzI
  refine mem_idealPowSmul_of_sieve B S hS F hF I (n - c) _
    (Sv := artinReesSieve B S hS F hF I M G (n - c) c z) ?_ (fun Y f hf => hf)
  refine (SmallEtale.topology B S hS F).transitive hS₀ _ ?_
  intro Y f hf
  obtain ⟨Sw, hSw, hSw'⟩ := exists_sieve_mem_presheafIdealSmul_of_artinRees
    B S hS F hF I M G hLN hMcart hGcart hIcart A hAaff hA hid Y
    (hS₀' f hf) (chartRestrictLinear_mem_chartSubmodule B S hS F hF G f hzG)
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hSw
  intro Y' g hg
  show chartRestrictLinear M (g ≫ f) z ∈ _
  rw [chartRestrictLinear_comp M f g z]
  exact hSw' g hg

/-- Artin-Rees for a quasi-coherent submodule `G` of a coherent module `M` and a quasi-coherent
sheaf of ideals `I` on a quasi-compact, étale-locally Noetherian algebraic space: there is a
`c ≥ 0` with `I ⁿ⁻ᶜ (I ᶜ M ⊓ G) = I ⁿ M ⊓ G` for every `n ≥ c`. -/
theorem exists_idealPowSmul_inf_eq_of_isQuasiCompactSpace (hqc : IsQuasiCompactSpace B S hS F)
    (hLN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS F hF)
    (hM : IsCoherent B S hS F hF M) (G : M.Submodule)
    (hG : G.toSheafOfModules.IsQuasicoherentOnSite) (I : IdealSheaves B S hS F hF)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      Stacks.Sites.idealPowSmul I (n - c) (idealPowSubmodule I c M ⊓ G)
        = idealPowSubmodule I n M ⊓ G := by
  classical
  have hMcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M
    hM.toIsQuasicoherentOnSite
  have hGcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
    G.toSheafOfModules hG
  have hIcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
    I.toSheafOfModules hI
  obtain ⟨U₀, f₀, hU₀aff, hU₀surj, hU₀et⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hqc
  let U : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk f₀, presheaf_etale_of_isEtale B S hS hU₀et⟩
  have hUaff : IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) := hU₀aff
  have hUsurj : IsSurjective B S hS U.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U₀ f₀).1 hU₀surj
  obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_noetherianAffine B S hS F hF hLN U
  obtain ⟨ι, hιfin, V, fV, -, hVle, hVcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F U hUaff Sv hSv
  choose A l mc hA hfactor using fun i => hfac (fV i) (hVle _ (Sieve.ofArrows_mk V fV i))
  have hAaff : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (A i)) :=
    fun i => (hA i).1
  have hAcov : Sieve.ofArrows A mc ∈ SmallEtale.topology B S hS F U := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_ hVcov
    rintro Y k ⟨W', t, p, ⟨i⟩, hcomp⟩
    refine ⟨A i, t ≫ l i, mc i, ⟨i⟩, ?_⟩
    rwa [Category.assoc, ← hfactor i]
  have hAtop := ofObjects_mem_topology_of_ofArrows B S hS F hF hUsurj A mc hAcov
  have hcc : ∀ i, ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      chartSectionIdeal B S hS F hF I (A i) ^ n •
            (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
            ⊓ chartSubmodule B S hS F hF G (A i)
          = chartSectionIdeal B S hS F hF I (A i) ^ (n - c) •
            (chartSectionIdeal B S hS F hF I (A i) ^ c •
              (⊤ : Submodule (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))))
              ⊓ chartSubmodule B S hS F hF G (A i)) := by
    intro i
    have : IsNoetherianRing (chartRing B S hS F hF (A i)) := (hA i).2
    have : Module.Finite (chartRing B S hS F hF (A i)) (M.val.obj (op (A i))) :=
      moduleFinite_sections_of_isNoetherianAffineChart B S hS F hF M hM (hA i)
    exact Ideal.exists_pow_inf_eq_pow_smul (chartSectionIdeal B S hS F hF I (A i))
      (chartSubmodule B S hS F hF G (A i))
  choose ci hci using hcc
  let _ := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup ci, fun n hn => le_antisymm ?_ ?_⟩
  · refine le_inf ?_ (le_trans (Stacks.Sites.idealPowSmul_le_self I _ _) inf_le_right)
    refine le_trans (Stacks.Sites.idealPowSmul_mono_right I _ inf_le_left) ?_
    refine le_trans (idealPowSmul_idealPowSubmodule_le I _ _ M) (le_of_eq ?_)
    exact congrArg (fun k => idealPowSubmodule I k M) (Nat.sub_add_cancel hn)
  · exact idealPowSubmodule_inf_le_idealPowSmul B S hS F hF I M G hLN hMcart hGcart hIcart
      A hAaff hAtop
      (fun i => Ideal.pow_inf_eq_pow_smul_of_le _ _ (Finset.le_sup (Finset.mem_univ i))
        (hci i) n hn)

/-- Artin-Rees for a quasi-coherent submodule `G` of a coherent module `M` and a quasi-coherent
sheaf of ideals `I` on a Noetherian algebraic space: there is a `c ≥ 0` with
`I ⁿ⁻ᶜ (I ᶜ M ⊓ G) = I ⁿ M ⊓ G` for every `n ≥ c`. -/
@[stacks 07UL]
theorem exists_idealPowSmul_inf_eq (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) (M : Modules.{u, u} B S hS F hF)
    (hM : IsCoherent B S hS F hF M) (G : M.Submodule)
    (hG : G.toSheafOfModules.IsQuasicoherentOnSite) (I : IdealSheaves B S hS F hF)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      Stacks.Sites.idealPowSmul I (n - c) (idealPowSubmodule I c M ⊓ G)
        = idealPowSubmodule I n M ⊓ G :=
  exists_idealPowSmul_inf_eq_of_isQuasiCompactSpace B S hS F hF hN.1 hN.2.2 M hM G hG I hI

end AlgebraicGeometry.Space

end
