module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Points

/-!
# The theorem of the cube: cohomology and base change on a chart

On an affine chart `V` of an abelian variety over an algebraically closed field, the cone
conditions at rational points with trivial fibre propagate, by the Nakayama arguments of
`StacksFrontier/Algebra/Module/ConeNakayamaGlobal.lean`, to:

* a lift of the constant face cocycle, after multiplication by a function not vanishing at the
  point (`Stacks.Cube.exists_lift_at`);
* injectivity on `H⁰` relative to the faces when all fibres are trivial
  (`Stacks.Cube.ker_cone_eq_bot`);
* vanishing of `H⁰` when one fibre has no sections (`Stacks.Cube.ker_d₀_eq_bot_of_fibre`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator Stacks.FlatComplexNakayama

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} [Fintype ι] [DecidableEq ι]
  (U : ι → A.left.Opens) (N : (P A).Modules) {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)

attribute [local instance] faceModule chartAlgebra secAlg secAlgB

/-- The constant face cocycle `(1, 1)`. -/
noncomputable def w₁ : FaceCochain V U 0 × FaceCochain V U 0 :=
  letI := cochainModule U A.hom 0
  (faceψ V U 0 (one U), faceψ V U 0 (one U))

omit [Fintype ι] [DecidableEq ι] in
/-- The constant face cocycle `w₁` lies in the kernel of `targetD`. -/
theorem targetD_w₁ : targetD V U ha₀ (w₁ U (V := V)) = 0 := by
  let := cochainModule U A.hom 0
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change faceD V U 0 (faceψ V U 0 (one U)) = 0
    rw [faceD_faceψ, rawD_one]
    exact map_zero (faceψ V U 1)
  · change faceD V U 0 (faceψ V U 0 (one U)) = 0
    rw [faceD_faceψ, rawD_one]
    exact map_zero (faceψ V U 1)
  · exact sub_self _

/-- The standing hypotheses on a chart. -/
structure ChartHyp : Prop where
  /-- The structure morphism of the chart is separated. -/
  sep : IsSeparated (chartMap hV)
  /-- The structure morphism of the chart is proper. -/
  proper : IsProper (chartMap hV)
  /-- The restriction of `N` to the chart is quasi-coherent. -/
  qcoh : (chartModule N V).IsQuasicoherent
  /-- The restriction of `N` to the chart is coherent. -/
  coh : (chartModule N V).IsCoherent
  /-- The restriction of `N` to the chart is flat over the ring of functions of `V`. -/
  flat : IsFlatOver (chartMap hV).toLRSHom.toShHom (chartModule N V)
  /-- Every member of the induced cover of the chart is affine. -/
  aff : ∀ ab, IsAffineOpen (chartCover U V ab)
  /-- The members of the induced cover cover the chart. -/
  cov : (⊤ : (PV V).toScheme.Opens) = ⨆ ab, chartCover U V ab

variable {hV U N}

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- Every term of the chart complex is flat over the ring of functions of `V`. -/
theorem ChartHyp.flatC [Finite ι] (h : ChartHyp hV U N) (p : ℕ) :
    Module.Flat (chartRing V) (CX hV U N p) := by
  have := h.sep
  have := h.qcoh
  exact Stacks.Cech.alternatingCechModuleComplex_flat (chartMap hV) (chartCover U V)
    (chartModule N V) h.aff h.flat p

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- After base change to a Noetherian algebra `S`, the degree-one cohomology of the chart complex
is a finite `S`-module. -/
theorem ChartHyp.finC [Finite ι] (h : ChartHyp hV U N) (S : Type u) [CommRing S]
    [Algebra (chartRing V) S] [IsNoetherianRing S] :
    Module.Finite S (homology (d₀ hV U N) (d₁ hV U N) S) := by
  have := h.sep; have := h.proper; have := h.qcoh; have := h.coh
  classical
  let : LinearOrder (ι × ι) := linearOrderOfSTO WellOrderingRel
  exact Stacks.CechBaseChange.finite_homology_baseChange (chartMap hV) (chartCover U V)
    (chartModule N V) h.cov h.aff S

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- After base change to a Noetherian algebra `S`, the kernel of `d₀` is a finite `S`-module. -/
theorem ChartHyp.finK [Finite ι] (h : ChartHyp hV U N) (S : Type u) [CommRing S]
    [Algebra (chartRing V) S] [IsNoetherianRing S] :
    Module.Finite S (LinearMap.ker ((d₀ hV U N).baseChange S)) := by
  have := h.sep; have := h.proper; have := h.qcoh; have := h.coh
  classical
  let : LinearOrder (ι × ι) := linearOrderOfSTO WellOrderingRel
  exact Stacks.CechBaseChange.finite_ker_baseChange (chartMap hV) (chartCover U V)
    (chartModule N V) h.cov h.aff S

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- The composite of the first two differentials of the chart complex vanishes. -/
theorem d₁_comp_d₀' : d₁ hV U N ∘ₗ d₀ hV U N = 0 :=
  Stacks.CechBaseChange.d₁_comp_d₀ (chartMap hV) (chartCover U V) (chartModule N V)

variable (hV U N)

section Main

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom] [Smooth A.hom]
  (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
  (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
  (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
  (hBc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ (A ⊗ A).hom.appTop))

variable {hV U N}

omit [Fintype ι] [DecidableEq ι] [IsAlgClosed k] [LocallyOfFiniteType A.hom] in
include hU hUcov hAc hBc in
/-- **A normalized lift near a point with trivial fibre.** -/
theorem exists_lift_at [Finite ι] (h : ChartHyp hV U N) (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))
    (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤)
    {σ₀ : Γ(fibreModule z hzk hzV N, ⊤)} (hσ₀ : IsGen _ σ₀) :
    ∃ a : chartRing V, evz z hzV a ≠ 0 ∧ ∃ y : CX hV U N 0, d₀ hV U N y = 0 ∧
      phi₀ hV U ha₀ N hg₁ hg₂ y = a • w₁ U := by
  obtain ⟨σY, hσY, hnY⟩ := exists_normY z hzk hzV N hg₁ hσ₀ hAc
  obtain ⟨σX, hσX, hnX⟩ := exists_normX z hzk hzV N hg₂ hσ₀ hAc
  have := h.sep; have := h.qcoh
  have ht := transfer_at z hzk hV hzV U N ha₀ hg₁ hg₂ hσY hσX hU h.aff hUcov hAc hBc hnorm hnY hnX
  let : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  have hsurj := evz_surjective z hzk hzV
  have hm : (RingHom.ker (evz z hzV)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hφ := phi₁_comp_d₀ hV U ha₀ N hg₁ hg₂ hnorm
  have hbase : SurjZero (d₀ hV U N) (targetD V U ha₀) (phi₀ hV U ha₀ N hg₁ hg₂)
        (chartRing V ⧸ RingHom.ker (evz z hzV)) ∧
      InjOne (d₀ hV U N) (d₁ hV U N) (targetD V U ha₀) (phi₁ hV U ha₀ N hg₁ hg₂)
        (chartRing V ⧸ RingHom.ker (evz z hzV)) := by
    rw [← isExactAt_cone_iff _ _ _ _ _ _ hφ] at ht ⊢
    exact Stacks.FlatComplexNakayama.isExactAt_congr _ _ (quotEquiv z hzk hzV).symm ht.1
  have := isRegularLocalRing_atPrime hV (RingHom.ker (evz z hzV))
  have := h.flatC 2
  have := flat_faceCochain U hV hU 0
  have := flat_faceCochain U hV hU 1
  have : Module.Flat (chartRing V) (FaceCochain V U 1 × chartRing V) :=
    Stacks.TwoTermComplex.flat_prod
  have : Module.Flat (chartRing V) (FaceCochain V U 1 × FaceCochain V U 1 × chartRing V) :=
    Stacks.TwoTermComplex.flat_prod
  have hloc := Stacks.ConeNakayama.isExactAt_cone_localization (d₀ hV U N) (d₁ hV U N)
    (targetD V U ha₀) (phi₀ hV U ha₀ N hg₁ hg₂) (phi₁ hV U ha₀ N hg₁ hg₂) d₁_comp_d₀' hφ
    (fun S _ _ _ => h.finC S) (fun S _ _ _ => finite_ker_targetD_baseChange U hV hU hUcov hAc ha₀ S)
    (RingHom.ker (evz z hzV)) hbase
  obtain ⟨a, ha, y, hy0, hy⟩ := Stacks.ConeNakayama.exists_lift_of_surjZero (d₀ hV U N)
    (targetD V U ha₀) (phi₀ hV U ha₀ N hg₁ hg₂) (RingHom.ker (evz z hzV)) hloc.1 (w₁ U)
    (targetD_w₁ U ha₀)
  exact ⟨a, fun h0 => ha (RingHom.mem_ker.mpr h0), y, hy0, hy⟩

omit [Fintype ι] [DecidableEq ι] in
include hU hUcov hAc hBc in
/-- **Injectivity on `H⁰` relative to the faces when all fibres are trivial.** -/
theorem ker_cone_eq_bot [Finite ι] (h : ChartHyp hV U N)
    (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))
    (hall : ∀ (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤),
      ∃ σ₀ : Γ(fibreModule z hzk hzV N, ⊤), IsGen _ σ₀) :
    LinearMap.ker (coneD₀ (d₀ hV U N) (phi₀ hV U ha₀ N hg₁ hg₂)) = ⊥ := by
  have := h.sep; have := h.qcoh
  have := h.flatC 1
  have := flat_faceCochain U hV hU 0
  have : Module.Flat (chartRing V) (FaceCochain V U 0 × FaceCochain V U 0) :=
    Stacks.TwoTermComplex.flat_prod
  refine Stacks.ConeNakayama.ker_coneD₀_eq_bot (d₀ hV U N) (phi₀ hV U ha₀ N hg₁ hg₂)
    (fun S _ _ _ => h.finK S) (fun m _ => isRegularLocalRing_atPrime hV m) fun m _ => ?_
  obtain ⟨z, hzk, hzV, rfl⟩ := exists_point_of_isMaximal hV m
  obtain ⟨σ₀, hσ₀⟩ := hall z hzk hzV
  obtain ⟨σY, hσY, hnY⟩ := exists_normY z hzk hzV N hg₁ hσ₀ hAc
  obtain ⟨σX, hσX, hnX⟩ := exists_normX z hzk hzV N hg₂ hσ₀ hAc
  have ht := transfer_at z hzk hV hzV U N ha₀ hg₁ hg₂ hσY hσX hU h.aff hUcov hAc hBc hnorm hnY hnX
  let : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  exact Stacks.FlatComplexNakayama.ker_eq_bot_congr _ (quotEquiv z hzk hzV).symm ht.2

omit [GrpObj A] [Fintype ι] [DecidableEq ι] [IsAlgClosed k] [LocallyOfFiniteType A.hom] in
include hUcov in
/-- **Vanishing of `H⁰` when one fibre has no sections.** -/
theorem ker_d₀_eq_bot_of_fibre [Finite ι] (h : ChartHyp hV U N) [IsDomain (chartRing V)]
    (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤)
    (h0 : ∀ s : Γ(fibreModule z hzk hzV N, ⊤), s = 0) :
    LinearMap.ker (d₀ hV U N) = ⊥ := by
  have := h.sep; have := h.qcoh
  have := h.flatC 0
  have := h.flatC 1
  have ht := ker_d₀_evz z hzk hV hzV U N h.aff hUcov h0
  let : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  have hm : (RingHom.ker (evz z hzV)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (evz_surjective z hzk hzV)
  have := isRegularLocalRing_atPrime hV (RingHom.ker (evz z hzV))
  exact Stacks.ConeNakayama.ker_d₀_eq_bot (d₀ hV U N) (fun S _ _ _ => h.finK S)
    (RingHom.ker (evz z hzV))
    (Stacks.FlatComplexNakayama.ker_eq_bot_congr _ (quotEquiv z hzk hzV).symm ht)

end Main

end Stacks.Cube

end
