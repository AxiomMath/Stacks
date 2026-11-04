module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineOverlaps
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffinePresentationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Sections of a finitely presented module over an affine étale chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be a
quasi-coherent `𝒪_F`-module of finite presentation on the small étale site.  This file proves that
the sections of `G` over an affine étale chart `W` form a finitely presented module over the chart
ring `𝒪_F(W)`.

Finite presentation gives a finite global presentation only on *some* covering of `W`, and the
sections of a cokernel of sheaves are not the cokernel of the sections, so the conclusion does not
follow formally: it needs the exactness of the sections of a presentation at an object with affine
underlying scheme, and then faithfully flat descent along a finite affine étale refinement of that
covering together with the base change comparison of Stacks 03DX(2).

## Main results

* `AlgebraicGeometry.Space.SmallEtale.module_finitePresentation_sections_of_presentation`: **the
  sections over an object of a slice with affine underlying scheme of a module with a finite global
  presentation on that slice are finitely presented over the chart ring.**
* `AlgebraicGeometry.Space`'s
  `module_finitePresentation_sections_of_isCartesian_of_isFinitePresentationOnSite` and
  `module_finitePresentation_sections_of_isFinitePresentationOnSite`: **the sections of an
  `𝒪_F`-module of finite presentation which is cartesian on affine charts, respectively
  quasi-coherent, over an affine étale chart form a finitely presented module over the chart
  ring.**

## Implementation notes

Both halves of the exactness of the sections at an object with affine underlying scheme are
already available for the small étale site and carry no open hypothesis: the presenting morphism
is surjective there by
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver`, and a
section it kills is a value of the relation morphism by
`AlgebraicGeometry.Space.SmallEtale.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`.
The two coproducts of the presentation have free sections there
(`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffine`), so the kernel is the image of a finite
module and `Module.finitePresentation_of_free_of_surjective` applies.

A finite global presentation presents the universe lift of the module, whose sections are the
sections lifted, so the conclusion for the module itself is obtained along `ULift.moduleEquiv`.

The descent runs in the free modules of coefficients.  The relations over a member among the
restrictions of finitely many generating sections over the chart are finitely generated, because
the sections over the member are finitely presented, and they are combinations of restrictions of
relations over the chart by `Module.BaseChange.mem_span_image_ker_of_liftBaseChange`, whose only
non-free input is the injectivity half of
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`.  Finitely many relations over the chart
therefore generate the relations over every member, and
`Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange` descends that to the chart
with both comparisons bijective because both modules are free.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The sections over an object with affine underlying scheme of a module which has a finite
global presentation on the slice of the small étale site at `V` form a finitely presented module
over the chart ring.**

The presenting morphism is surjective on those sections and a section it kills is a value of the
relation morphism, so the kernel of the surjection from the free module of sections of the
presenting coproduct is the image of the free module of sections of the relation coproduct. -/
theorem module_finitePresentation_sections_of_presentation (G : Modules.{u, u} B S hS F hF)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : SheafOfModules.HasFiniteGlobalPresentation (G.over V)) (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    Module.FinitePresentation (chartRing B S hS F hF W.left) (G.val.obj (op W.left)) := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hV
  have _ : HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1}
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : ((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    _root_.AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u}
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : Epi b := Cofork.IsColimit.epi hcok
  have hab' : a.val ≫ b.val = 0 := by
    rw [← SheafOfModules.comp_val, hab]
    rfl
  have hsurj : Function.Surjective (b.val.app (op W)) :=
    surjective_val_app_of_isColimit_of_isAffineOver B S hS F hF κ ι hQ hP a b hab' hab hcok W hW
  have basP := tautBasisOfIsAffine B S hS F hF ι hP W hW
  have _ := Module.Free.of_basis basP
  have _ := Module.Finite.of_basis basP
  have hker : LinearMap.ker (b.val.app (op W)).hom =
      LinearMap.range (a.val.app (op W)).hom := by
    refine le_antisymm (fun z hz => mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver
      B S hS F hF κ ι hQ hP a b hab hab' hcok W hW (LinearMap.mem_ker.mp hz)) ?_
    rintro z ⟨q, rfl⟩
    have h : ((a.val ≫ b.val).app (op W)).hom q = 0 := by
      rw [hab']
      rfl
    simpa [PresheafOfModules.comp_app] using h
  have hkerfg : (LinearMap.ker (b.val.app (op W)).hom).FG := by
    rw [hker, LinearMap.range_eq_map]
    exact Submodule.FG.map _ (Module.finite_def.mp
      (Module.Finite.of_basis (tautBasisOfIsAffine B S hS F hF κ hQ W hW)))
  have hfp := Module.finitePresentation_of_free_of_surjective (b.val.app (op W)).hom hsurj hkerfg
  have : Module.FinitePresentation (chartRing B S hS F hF W.left)
      (ULift.{u + 1} (G.val.obj (op W.left) : Type u)) := hfp
  exact Module.FinitePresentation.of_equiv
    (ULift.moduleEquiv (R := chartRing B S hS F hF W.left)
      (M := (G.val.obj (op W.left) : Type u)))

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

variable {B S hS F hF}

/-- Applying a linear map to a linear combination is the linear combination of the images, with
coefficients pushed along `algebraMap`. -/
private theorem map_linearCombination_eq {R A M N ι : Type*} [Fintype ι] [CommSemiring R]
    [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [Module A N] [IsScalarTower R A N] (f : M →ₗ[R] N) (v : ι → M) (q : ι → R) :
    f (Fintype.linearCombination R v q) =
      Fintype.linearCombination A (fun l => f (v l)) ((Algebra.linearMap R A).compLeft ι q) := by
  rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun l _ => by simp

/-- Extending scalars along `R → A` the coefficientwise map `(ι → R) → (ι → A)` is bijective. -/
private theorem bijective_liftBaseChange_compLeft {R A ι : Type*} [Finite ι] [CommRing R]
    [CommRing A] [Algebra R A] :
    Function.Bijective (((Algebra.linearMap R A).compLeft ι).liftBaseChange A) := by
  classical
  refine Module.BaseChange.bijective_liftBaseChange_of_basis (Pi.basisFun R ι) (Pi.basisFun A ι)
    _ fun l => funext fun j => ?_
  change algebraMap R A (Pi.basisFun R ι l j) = Pi.basisFun A ι l j
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  by_cases h : j = l
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- **The sections of an `𝒪_F`-module of finite presentation which is cartesian on affine charts
over an affine étale chart form a finitely presented module over the chart ring.**

Finite presentation provides a covering of the chart on whose members the module has a finite
global presentation; the sections over the affine charts of a finite jointly faithfully flat
refinement of that covering are finitely presented by
`AlgebraicGeometry.Space.SmallEtale.module_finitePresentation_sections_of_presentation`, so the
relations there among the restrictions of finitely many generating sections over the chart are
finitely generated, and `Module.BaseChange.mem_span_image_ker_of_liftBaseChange` exhibits them as
combinations of the restrictions of relations over the chart.  Faithfully flat descent of
membership in a span then makes finitely many relations over the chart generate all of them. -/
theorem module_finitePresentation_sections_of_isCartesian_of_isFinitePresentationOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W)) := by
  classical
  have hfin : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) :=
    module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite G hG
      inferInstance W hW
  obtain ⟨kk, τ, hτ⟩ :=
    Module.Finite.exists_fin (R := chartRing B S hS F hF W) (M := (G.val.obj (op W) : Type u))
  obtain ⟨I₀, V, fV, hcov, hpres⟩ := hfp.locally_hasFiniteGlobalPresentation W
  obtain ⟨m, z, φ, hzaff, hzmem, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW hcov
  have hfpz : ∀ i, Module.FinitePresentation (chartRing B S hS F hF (z i))
      (G.val.obj (op (z i))) := by
    intro i
    obtain ⟨j, c, -⟩ := (Sieve.mem_ofArrows_iff V fV (φ i)).1 (hzmem i)
    exact SmallEtale.module_finitePresentation_sections_of_presentation B S hS F hF G
      (hpres j) (Over.mk c) (hzaff i)
  let algI : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (z i)) :=
    fun i => chartAlgebra (hF := hF) (φ i)
  let modI : ∀ i, Module (chartRing B S hS F hF W) (G.val.obj (op (z i))) :=
    fun i => chartSectionsModule G (φ i)
  have towI : ∀ i, IsScalarTower (chartRing B S hS F hF W) (chartRing B S hS F hF (z i))
      (G.val.obj (op (z i))) := fun i => chartSections_isScalarTower G (φ i)
  have towK : ∀ i, IsScalarTower (chartRing B S hS F hF W) (chartRing B S hS F hF (z i))
      (Fin kk → chartRing B S hS F hF (z i)) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hFF : Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (z i)) := hff
  let bT := Fintype.linearCombination (chartRing B S hS F hF W) τ
  let rN : ∀ i, (G.val.obj (op W) : Type u) →ₗ[chartRing B S hS F hF W]
      (G.val.obj (op (z i)) : Type u) := fun i => chartRestrictLinear G (φ i)
  let bW : ∀ i, (Fin kk → chartRing B S hS F hF (z i)) →ₗ[chartRing B S hS F hF (z i)]
      (G.val.obj (op (z i)) : Type u) := fun i => Fintype.linearCombination _ fun l => rN i (τ l)
  let rP : ∀ i, (Fin kk → chartRing B S hS F hF W) →ₗ[chartRing B S hS F hF W]
      (Fin kk → chartRing B S hS F hF (z i)) :=
    fun _ => (Algebra.linearMap _ _).compLeft (Fin kk)
  have hsq : ∀ (i) (q : Fin kk → chartRing B S hS F hF W), rN i (bT q) = bW i (rP i q) := by
    intro i q
    exact map_linearCombination_eq (A := chartRing B S hS F hF (z i)) (rN i) τ q
  have hPbij : ∀ i,
      Function.Bijective ((rP i).liftBaseChange (chartRing B S hS F hF (z i))) :=
    fun _ => bijective_liftBaseChange_compLeft
  have hN : ∀ i, Function.Injective ((rN i).liftBaseChange (chartRing B S hS F hF (z i))) :=
    fun i => (hG W (z i) hW (hzaff i) (φ i)).1
  have hbT : Function.Surjective bT := by
    rwa [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  have hbW : ∀ i, Function.Surjective (bW i) := by
    intro i
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    refine top_unique fun y _ => ?_
    obtain ⟨ζ, hζ⟩ := (hG W (z i) hW (hzaff i) (φ i)).2 y
    obtain ⟨cz, t, mm, hmm⟩ := TensorProduct.exists_sum_tmul_eq ζ
    rw [← hζ, hmm, map_sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [chartBaseChange_tmul G (φ i) (t p) (mm p)]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun
      (chartRing B S hS F hF W)).mp (show mm p ∈ Submodule.span (chartRing B S hS F hF W)
        (Set.range τ) by simp [hτ])
    rw [← hd, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hgen : ∀ i, ∃ (J : Type) (_ : Fintype J) (x : J → (Fin kk → chartRing B S hS F hF W)),
      (∀ q, x q ∈ LinearMap.ker bT) ∧
        LinearMap.ker (bW i) ≤ Submodule.span (chartRing B S hS F hF (z i))
          (Set.range fun q => rP i (x q)) := by
    intro i
    have _ := hfpz i
    obtain ⟨mi, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.FinitePresentation.fg_ker (bW i) (hbW i))
    have hgp : ∀ p, g p ∈ Submodule.span (chartRing B S hS F hF (z i))
        (rP i '' (LinearMap.ker bT : Set (Fin kk → chartRing B S hS F hF W))) := by
      intro p
      refine Module.BaseChange.mem_span_image_ker_of_liftBaseChange bT (bW i) (rP i) (rN i)
        (hsq i) (hPbij i).2 (hN i) hbT ?_
      exact LinearMap.mem_ker.mp (hg ▸ Submodule.subset_span ⟨p, rfl⟩ :
        g p ∈ LinearMap.ker (bW i))
    choose cnt co el hel using fun p => Submodule.mem_span_set'.mp (hgp p)
    choose xx hxxmem hxxeq using fun (p : Fin mi) (q : Fin (cnt p)) => (el p q).2
    refine ⟨Σ p : Fin mi, Fin (cnt p), inferInstance, fun w => xx w.1 w.2,
      fun w => hxxmem _ _, ?_⟩
    rw [← hg]
    refine Submodule.span_le.2 ?_
    rintro y ⟨p, rfl⟩
    rw [← hel p]
    refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
    rw [← hxxeq p q]
    exact Submodule.subset_span ⟨⟨p, q⟩, rfl⟩
  choose J fJ x hxmem hxle using hgen
  let _ : ∀ i, Fintype (J i) := fJ
  have hkerfg : (LinearMap.ker bT).FG := by
    have towT : ∀ i, IsScalarTower (chartRing B S hS F hF W) (chartRing B S hS F hF (z i))
        ((Σ i : Fin m, J i) → chartRing B S hS F hF (z i)) :=
      fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let bTT := Fintype.linearCombination (chartRing B S hS F hF W)
      fun w : Σ i : Fin m, J i => x w.1 w.2
    let bWT : ∀ i, ((Σ i : Fin m, J i) → chartRing B S hS F hF (z i)) →ₗ[
        chartRing B S hS F hF (z i)] (Fin kk → chartRing B S hS F hF (z i)) :=
      fun i => Fintype.linearCombination _ fun w => rP i (x w.1 w.2)
    let rPT : ∀ i, ((Σ i : Fin m, J i) → chartRing B S hS F hF W) →ₗ[
        chartRing B S hS F hF W]
        ((Σ i : Fin m, J i) → chartRing B S hS F hF (z i)) :=
      fun _ => (Algebra.linearMap _ _).compLeft (Σ i : Fin m, J i)
    have hsqT : ∀ (i) (q : (Σ i : Fin m, J i) → chartRing B S hS F hF W),
        rP i (bTT q) = bWT i (rPT i q) := by
      intro i q
      exact map_linearCombination_eq (A := chartRing B S hS F hF (z i)) (rP i) _ q
    have hPTbij : ∀ i,
        Function.Bijective ((rPT i).liftBaseChange (chartRing B S hS F hF (z i))) :=
      fun _ => bijective_liftBaseChange_compLeft
    have hspan : LinearMap.ker bT = Submodule.span (chartRing B S hS F hF W)
        (Set.range fun w : Σ i : Fin m, J i => x w.1 w.2) := by
      refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
      · have hmem : ∀ i, rP i y ∈ LinearMap.range (bWT i) := by
          intro i
          have hyk : rP i y ∈ LinearMap.ker (bW i) := by
            refine LinearMap.mem_ker.2 ?_
            rw [← hsq i y, LinearMap.mem_ker.mp hy, map_zero]
          have hsub : Submodule.span (chartRing B S hS F hF (z i))
              (Set.range fun q => rP i (x i q)) ≤
              Submodule.span (chartRing B S hS F hF (z i))
                (Set.range fun w : Σ i : Fin m, J i => rP i (x w.1 w.2)) := by
            refine Submodule.span_mono ?_
            rintro y' ⟨q, rfl⟩
            exact ⟨⟨i, q⟩, rfl⟩
          rw [show LinearMap.range (bWT i) = Submodule.span (chartRing B S hS F hF (z i))
            (Set.range fun w : Σ i : Fin m, J i => rP i (x w.1 w.2)) from
              Fintype.range_linearCombination _ _]
          exact hsub (hxle i hyk)
        have hy' := Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
          (chartRing B S hS F hF W) (fun i => chartRing B S hS F hF (z i)) bTT bWT rPT rP hsqT
          (fun i => (hPTbij i).2) (fun i => (hPbij i).1) hmem
        rwa [show LinearMap.range bTT = Submodule.span (chartRing B S hS F hF W)
          (Set.range fun w : Σ i : Fin m, J i => x w.1 w.2) from
            Fintype.range_linearCombination _ _] at hy'
      · rintro y ⟨w, rfl⟩
        exact hxmem w.1 w.2
    rw [hspan]
    exact Submodule.fg_span (Set.finite_range _)
  exact Module.finitePresentation_of_free_of_surjective bT hbT hkerfg

/-- **The sections of a quasi-coherent `𝒪_F`-module of finite presentation over an affine étale
chart form a finitely presented module over the chart ring.**

Quasi-coherence makes the module cartesian on affine charts by Stacks 03DX(2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, and
`AlgebraicGeometry.Space`'s
`module_finitePresentation_sections_of_isCartesian_of_isFinitePresentationOnSite` concludes.

This is the étale-local reading of finite presentation used by the conventions of Stacks 0CZ3,
and it is the hypothesis `hfp` of `AlgebraicGeometry.Space`'s
`isFiniteTypeQuasicoherentIdeal_fittingIdeal` (Stacks 0CZ5). -/
theorem module_finitePresentation_sections_of_isFinitePresentationOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : G.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W)) :=
  fun W hW => module_finitePresentation_sections_of_isCartesian_of_isFinitePresentationOnSite G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG) hfp W hW

end AlgebraicGeometry.Space

end
