module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyCechProjections
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyCechVanishing
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel

/-!
# Surjectivity on affine-chart sections from the Amitsur complex of a covering family

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  This file
proves the uniform form of Descent, Proposition 03DW carried as a hypothesis throughout this
tree,

    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))

— an epimorphism `q : P ⟶ Q` of `𝒪_F`-modules whose *kernel* is cartesian on affine charts is
surjective on the sections over an affine étale chart.  Nothing is asked of the source or of the
target, which is what distinguishes it from
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent` and from
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian`: both of those ask
cartesianness of the source, which is exactly what the middle term of a short exact sequence
cannot supply, and that is why the content here is a first cohomology group.

No `@[stacks 03DW]` attribute is claimed.  Stacks 03DW is the comparison of the cohomology of a
quasi-coherent module computed in several topologies and in all degrees; what is proved here is
the degree-zero surjectivity consequence the rest of this tree consumes.

The route is the classical one.  A covering sieve of an affine chart contains a finite family of
affine charts which is étale, hence flat, in schemes
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`); over such a family
the Čech complex of a module cartesian on affine charts is the Amitsur complex of the product of
the rings of the members over the ring of the chart, which is faithfully flat, so its first
cohomology vanishes
(`PresheafOfModules.exists_familyCechDiff₀_eq_of_baseChange`); and a morphism whose kernel has
vanishing first Čech cohomology along a covering family has its images jointly detected by that
family (`SheafOfModules.jointlyDetectsRange_of_familyCechH1Vanishing`), which
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` turns into surjectivity.

## Main results

* `SheafOfModules.exists_app_kernel_ι_eq`: **a section killed by a morphism of sheaves of modules
  comes from a section of the kernel.**  With `Stacks.SheafOfModules.injective_app_kernel_ι` this
  says that the sections of `kernel b` over an object are the sections of the source killed
  by `b`.
* `SheafOfModules.exists_restrictₛₗ_eq_of_isPullback`: **a family of sections of a sheaf of
  modules over the members of a covering family which agrees on the fibre products descends**, the
  sheaf axiom in the shape the Čech argument consumes.
* `AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorChartRing_of_isPullback`: **the ring
  of sections over a fibre product of two affine charts is the tensor product of the rings of the
  two factors**, as a ring isomorphism.
* `AlgebraicGeometry.Space.SmallEtale.exists_overlaps_familyCechH1Vanishing`: **the first Čech
  cohomology of a module cartesian on affine charts vanishes along a finite flat covering family
  of affine charts of an affine chart.**
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts_kernel`: **the
  uniform form of Descent, Proposition 03DW**, with no hypothesis.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v r m u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A section killed by a morphism of sheaves of modules comes from a section of the kernel.**
Evaluation at an object preserves finite limits, so it carries the kernel of `b` to the kernel of
`b` on sections; the comparison map is then an isomorphism and the section with the given value
is transported back along it.

This is the surjective direction of the sectionwise description of a kernel, the companion of
`Stacks.SheafOfModules.injective_app_kernel_ι`. -/
theorem exists_app_kernel_ι_eq {P N : SheafOfModules.{r} R} (b : P ⟶ N) (X : Cᵒᵖ)
    (x : P.val.obj X) (hx : b.val.app X x = 0) :
    ∃ y : (kernel b).val.obj X, (kernel.ι b).val.app X y = x := by
  let ev := SheafOfModules.evaluation R X
  let f := ev.map b
  have hmem : x ∈ LinearMap.ker (ModuleCat.Hom.hom f) := hx
  have h2 : inv (kernelComparison b ev) ≫ ev.map (kernel.ι b) = kernel.ι f := by
    rw [← kernelComparison_comp_ι b ev, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have h4 : ∀ e, ev.map (kernel.ι b) (inv (kernelComparison b ev) e) = kernel.ι f e := by
    intro e
    rw [← h2]
    rfl
  have h5 : ModuleCat.Hom.hom (kernel.ι f)
      (ModuleCat.Hom.hom (ModuleCat.kernelIsoKer f).inv ⟨x, hmem⟩) = x := by
    rw [← ModuleCat.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  exact ⟨inv (kernelComparison b ev) ((ModuleCat.kernelIsoKer f).inv ⟨x, hmem⟩),
    (h4 _).trans h5⟩

/-- **A family of sections over the members of a covering family which agrees on the fibre
products of the members descends to a section over the object covered.**

This is the sheaf axiom for the family, with compatibility asked only at the fibre products of
pairs of members rather than at every pair of arrows below them: a pair of arrows agreeing over
the base factors through the fibre product, so the two restrictions of the family agree there
as well.  Only the existence half of the sheaf condition is stated; uniqueness is
`SheafOfModules.injective_restrict`. -/
theorem exists_restrictₛₗ_eq_of_isPullback (M : SheafOfModules.{r} R) {W : C} {I : Type u}
    {V : I → C} {Pb : I → I → C} (a : ∀ i, V i ⟶ W)
    (pr₁ : ∀ i j, Pb i j ⟶ V i) (pr₂ : ∀ i j, Pb i j ⟶ V j)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (a i) (a j))
    (ha : Sieve.ofArrows V a ∈ J W) (p : ∀ i, M.val.obj (op (V i)))
    (hp : ∀ i j, M.val.restrictₛₗ (pr₁ i j).op (p i) = M.val.restrictₛₗ (pr₂ i j).op (p j)) :
    ∃ p₀ : M.val.obj (op W), ∀ i, M.val.restrictₛₗ (a i).op p₀ = p i := by
  have hcompat : Presieve.Arrows.Compatible
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{r}) a p := by
    intro i j Z gi gj hcomm
    obtain ⟨l, h1, h2⟩ : ∃ l : Z ⟶ Pb i j, l ≫ pr₁ i j = gi ∧ l ≫ pr₂ i j = gj :=
      ⟨(hpb i j).lift gi gj hcomm, (hpb i j).lift_fst gi gj hcomm,
        (hpb i j).lift_snd gi gj hcomm⟩
    have hres : ∀ {T : C} (pr : Pb i j ⟶ T) (g : Z ⟶ T), l ≫ pr = g → ∀ x : M.val.obj (op T),
        M.val.restrictₛₗ l.op (M.val.restrictₛₗ pr.op x) = M.val.restrictₛₗ g.op x :=
      fun pr g h x ↦ by
        rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
          PresheafOfModules.restrictₛₗ_apply, ← M.val.map_comp_apply]
        exact M.val.congr_map_apply (congrArg Quiver.Hom.op h) x
    change M.val.restrictₛₗ gi.op (p i) = M.val.restrictₛₗ gj.op (p j)
    rw [← hres _ _ h1, ← hres _ _ h2, hp i j]
  exact ((Presieve.isSheafFor_arrows_iff _ a).1 (M.isSheafFor_ofArrows a ha) p hcompat).exists

end SheafOfModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Restricting chart sections along `b` and then `a` is restricting along any `c = a ≫ b`. -/
theorem SmallEtale.chartRestrict_chartRestrict_of_comp_eq {X Z T : SmallEtale B S hS F}
    (a : Z ⟶ X) (b : X ⟶ T) (c : Z ⟶ T) (habc : a ≫ b = c) (x : chartRing B S hS F hF T) :
    chartRestrict (hF := hF) a (chartRestrict (hF := hF) b x) = chartRestrict (hF := hF) c x := by
  subst habc
  exact (RingHom.congr_fun (chartRestrict_comp (hF := hF) b a) x).symm

/-- **The ring of sections over a fibre product of two affine étale charts over an affine chart is
the tensor product of the rings of sections of the two factors**, as a ring isomorphism taking a
pure tensor to the product of the two restrictions along the projections.

This is `AlgebraicGeometry.Space.SmallEtale.exists_tensorEquiv_chartRing_of_isPullback` with the
identification returned as a `RingEquiv` rather than as a linear equivalence over the ring of the
chart covered, which is the shape a family descent datum asks for: there the two factors may be
the same member, so the two maps into the ring of the overlap cannot both be algebra structures.

Taking the second factor to be a double overlap of a covering family rather than a member gives
the same statement for the triple overlaps, a triple overlap being a fibre product of a member
with a double overlap. -/
theorem SmallEtale.exists_ringEquivTensorChartRing_of_isPullback
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hY : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Y))
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z)) :
    letI := chartAlgebra (hF := hF) f
    letI := chartAlgebra (hF := hF) g
    ∃ ψ : TensorProduct (chartRing B S hS F hF W) (chartRing B S hS F hF Y)
          (chartRing B S hS F hF Z) ≃+* chartRing B S hS F hF Pb,
      ∀ x y, ψ (TensorProduct.tmul _ x y) =
        chartRestrict (hF := hF) fst x * chartRestrict (hF := hF) snd y := by
  have hcfst := SmallEtale.chartRestrict_chartRestrict_of_comp_eq (hF := hF) fst f _ rfl
  have hcsnd := SmallEtale.chartRestrict_chartRestrict_of_comp_eq (hF := hF) snd g _ h.w.symm
  let alg {X T : SmallEtale B S hS F} (a : X ⟶ T) : Algebra
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T, ⊤)
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj X, ⊤) :=
    chartAlgebra (hF := hF) a
  let := alg f
  let := alg g
  let := alg (fst ≫ f)
  exact ⟨(AlgebraicGeometry.algEquivTensorAppTopOfIsPullback
      (SmallEtale.isPullback_toScheme_of_isPullback_charts h) rfl rfl hcfst
      hcsnd).toRingEquiv,
    AlgebraicGeometry.algEquivTensorAppTopOfIsPullback_tmul
      (SmallEtale.isPullback_toScheme_of_isPullback_charts h) rfl rfl hcfst hcsnd⟩

/-- **The double and triple overlaps of a family of affine charts of an affine chart**, as chosen
fibre products, with their projections, the fibre product squares, the commutations between the
projections, and the affineness of every overlap. -/
theorem SmallEtale.exists_familyCechOverlaps {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {ι : Type*} {Y : ι → SmallEtale B S hS F} (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i))) :
    ∃ (Pb : ι → ι → SmallEtale B S hS F) (Pb₃ : ι → ι → ι → SmallEtale B S hS F)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
      (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
      (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (qq : ∀ i j k, Pb₃ i j k ⟶ Y i),
      (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j)) ∧
      (∀ i j k, IsPullback (qq i j k) (s₁ i j k) (g i) (pr₁ j k ≫ g j)) ∧
      (∀ i j k, s₃ i j k ≫ pr₁ i j = qq i j k) ∧
      (∀ i j k, s₂ i j k ≫ pr₁ i k = qq i j k) ∧
      (∀ i j k, s₃ i j k ≫ pr₂ i j = s₁ i j k ≫ pr₁ j k) ∧
      (∀ i j k, s₂ i j k ≫ pr₂ i k = s₁ i j k ≫ pr₂ j k) ∧
      (∀ i j, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
        (Pb i j))) ∧
      (∀ i j k, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
        (Pb₃ i j k))) := by
  have hpb : ∀ i j, IsPullback (pullback.fst (g i) (g j)) (pullback.snd (g i) (g j))
      (g i) (g j) := fun i j ↦ IsPullback.of_hasPullback (g i) (g j)
  have hpb₃ : ∀ i j k, IsPullback
      (pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j))
      (pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j))
      (g i) (pullback.fst (g j) (g k) ≫ g j) := fun i j k ↦ IsPullback.of_hasPullback _ _
  obtain ⟨t₁₂, t₁₃, hq₁₂, hq₁₃, hc₂, hc₃⟩ := IsPullback.exists_familyCechProjections hpb hpb₃
  have hPbaff : ∀ i j, IsAffine ((SmallEtale.toOver B S hS F ⋙
      BigFppfOver.toScheme B S hS).obj (pullback (g i) (g j))) := fun i j ↦
    SmallEtale.isAffine_of_isPullback_charts (hpb i j) hW (hY i) (hY j)
  exact ⟨fun i j ↦ pullback (g i) (g j),
    fun i j k ↦ pullback (g i) (pullback.fst (g j) (g k) ≫ g j),
    fun i j ↦ pullback.fst (g i) (g j), fun i j ↦ pullback.snd (g i) (g j),
    fun i j k ↦ pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j), t₁₃, t₁₂,
    fun i j k ↦ pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j),
    hpb, hpb₃, hq₁₂, hq₁₃, hc₂, hc₃, hPbaff,
    fun i j k ↦ SmallEtale.isAffine_of_isPullback_charts (hpb₃ i j k) hW (hY i)
      (hPbaff j k)⟩

/-- **The first Čech cohomology of a module cartesian on affine charts vanishes along a finite
flat covering family of affine charts of an affine chart.**

Returned together with the overlaps it is stated over: the double overlaps `Pb i j` with their
two projections, the triple overlaps `Pb₃ i j k` with the three projections onto the double
overlaps, the fibre product squares and the three commutations between the projections.  A
degree-one Čech cocycle of the family — a family of sections over the double overlaps whose
alternating restriction to each triple overlap vanishes — is then the Čech coboundary of a family
of sections over the members.

The overlaps are the chosen fibre products of the site and are again affine
(`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_charts`), so the cartesian condition
applies at every one of them; the rings of the overlaps are the tensor products of the rings of
the factors
(`AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorChartRing_of_isPullback`), the product
of the rings of the members is faithfully flat over the ring of the chart
(`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_chartRing`), and
`PresheafOfModules.exists_familyCechDiff₀_eq_of_baseChange` concludes. -/
theorem SmallEtale.exists_overlaps_familyCechH1Vanishing
    {K : Modules.{u, u} B S hS F hF} (hK : IsCartesianOnAffineCharts K)
    {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {ι : Type*} [Finite ι] (Y : ι → SmallEtale B S hS F) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i))
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fppfPrecoverage
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    ∃ (Pb : ι → ι → SmallEtale B S hS F) (Pb₃ : ι → ι → ι → SmallEtale B S hS F)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
      (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
      (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j),
      (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j)) ∧
      (∀ i j k, s₃ i j k ≫ pr₁ i j = s₂ i j k ≫ pr₁ i k) ∧
      (∀ i j k, s₃ i j k ≫ pr₂ i j = s₁ i j k ≫ pr₁ j k) ∧
      (∀ i j k, s₂ i j k ≫ pr₂ i k = s₁ i j k ≫ pr₂ j k) ∧
      ∀ ζ : ∀ i j, K.val.obj (op (Pb i j)),
        (∀ i j k, K.val.restrictₛₗ (s₁ i j k).op (ζ j k) -
            K.val.restrictₛₗ (s₂ i j k).op (ζ i k) +
              K.val.restrictₛₗ (s₃ i j k).op (ζ i j) = 0) →
          ∃ z : ∀ i, K.val.obj (op (Y i)), ∀ i j,
            K.val.restrictₛₗ (pr₁ i j).op (z i) -
              K.val.restrictₛₗ (pr₂ i j).op (z j) = ζ i j := by
  classical
  obtain ⟨Pb, Pb₃, pr₁, pr₂, s₁, s₂, s₃, qq, hpb, hpb₃, hq₁₂, hq₁₃, hc₂, hc₃, hPbaff,
    hPb₃aff⟩ := SmallEtale.exists_familyCechOverlaps hW g hY
  refine ⟨Pb, Pb₃, pr₁, pr₂, s₁, s₂, s₃, hpb,
    fun i j k ↦ (hq₁₂ i j k).trans (hq₁₃ i j k).symm, hc₂, hc₃, fun ζ hζ ↦ ?_⟩
  let algY : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Y i)) :=
    fun i ↦ chartAlgebra (hF := hF) (g i)
  let algD : ∀ i j, Algebra (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Pb i j)) := fun i j ↦ chartAlgebra (hF := hF) (pr₁ i j ≫ g i)
  let algE : ∀ i j k, Algebra (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Pb₃ i j k)) :=
    fun i j k ↦ chartAlgebra (hF := hF) (s₁ i j k ≫ pr₁ j k ≫ g j)
  let : Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (Y i)) :=
    SmallEtale.faithfullyFlat_pi_chartRing (hF := hF) Y g hW hY hfppf
  choose ψ hψ using fun i j ↦
    SmallEtale.exists_ringEquivTensorChartRing_of_isPullback (hF := hF) (hpb i j) hW
      (hY i) (hY j)
  choose ψ₃ hψ₃ using fun i j k ↦
    SmallEtale.exists_ringEquivTensorChartRing_of_isPullback (hF := hF) (hpb₃ i j k) hW
      (hY i) (hPbaff j k)
  exact PresheafOfModules.exists_familyCechDiff₀_eq_of_baseChange (N := K.val) (T := W)
    g pr₁ pr₂ s₁ s₂ s₃ (chartRing B S hS F hF W) (fun i ↦ chartRing B S hS F hF (Y i))
    (fun i j ↦ chartRing B S hS F hF (Pb i j))
    (fun i j k ↦ chartRing B S hS F hF (Pb₃ i j k))
    (fun i ↦ LinearEquiv.ofBijective (sectionsBaseChange K (g i))
      (hK W (Y i) hW (hY i) (g i))) (fun i ↦ chartBaseChange_one_tmul K (g i))
    (fun i j ↦ LinearEquiv.ofBijective (sectionsBaseChange K (pr₁ i j ≫ g i))
      (hK W (Pb i j) hW (hPbaff i j) (pr₁ i j ≫ g i)))
    (fun i j ↦ chartBaseChange_one_tmul K (pr₁ i j ≫ g i))
    (fun i j k ↦ LinearEquiv.ofBijective (sectionsBaseChange K (s₁ i j k ≫ pr₁ j k ≫ g j))
      (hK W (Pb₃ i j k) hW (hPb₃aff i j k) (s₁ i j k ≫ pr₁ j k ≫ g j)))
    (fun i j k ↦ chartBaseChange_one_tmul K (s₁ i j k ≫ pr₁ j k ≫ g j))
    (fun i j ↦ AlgHom.mk (chartRestrict (hF := hF) (pr₁ i j))
      (chartRestrict_chartRestrict_of_comp_eq _ (g i) _ rfl))
    (fun i j ↦ AlgHom.mk (chartRestrict (hF := hF) (pr₂ i j))
      (chartRestrict_chartRestrict_of_comp_eq _ (g j) _ (hpb i j).w.symm)) ψ hψ
    (fun i j k ↦ AlgHom.mk (chartRestrict (hF := hF) (qq i j k))
      (chartRestrict_chartRestrict_of_comp_eq _ (g i) _ (hpb₃ i j k).w))
    (fun i j k ↦ AlgHom.mk (chartRestrict (hF := hF) (s₁ i j k))
      (chartRestrict_chartRestrict_of_comp_eq _ (pr₁ j k ≫ g j) _ rfl))
    ψ₃ hψ₃ (fun i j k ↦ chartRestrict (hF := hF) (s₂ i j k))
    (fun i j k ↦ chartRestrict (hF := hF) (s₃ i j k)) (fun i j ↦ (hpb i j).w)
    (fun i j k ↦ ((Category.assoc (s₂ i j k) (pr₁ i k) (g i)).symm.trans
      (congrArg (· ≫ g i) (hq₁₃ i j k))).trans (hpb₃ i j k).w)
    (fun i j k ↦ ((Category.assoc (s₃ i j k) (pr₁ i j) (g i)).symm.trans
      (congrArg (· ≫ g i) (hq₁₂ i j k))).trans (hpb₃ i j k).w)
    (fun i j b x ↦ K.val.map_smul (pr₁ i j).op b x)
    (fun i j b x ↦ K.val.map_smul (pr₂ i j).op b x)
    (fun i j k d x ↦ K.val.map_smul (s₁ i j k).op d x)
    (fun i j k d x ↦ K.val.map_smul (s₂ i j k).op d x)
    (fun i j k d x ↦ K.val.map_smul (s₃ i j k).op d x)
    (fun i j k ↦ chartRestrict_chartRestrict_of_comp_eq
      (s₂ i j k) (pr₁ i k) (qq i j k) (hq₁₃ i j k))
    (fun i j k ↦ chartRestrict_chartRestrict_of_comp_eq
      (s₂ i j k) (pr₂ i k) (s₁ i j k ≫ pr₂ j k) (hc₃ i j k))
    (fun i j k ↦ chartRestrict_chartRestrict_of_comp_eq
      (s₃ i j k) (pr₁ i j) (qq i j k) (hq₁₂ i j k))
    (fun i j k ↦ chartRestrict_chartRestrict_of_comp_eq
      (s₃ i j k) (pr₂ i j) (s₁ i j k ≫ pr₁ j k) (hc₂ i j k)) hζ

/-! ### Surjectivity on the sections over an affine chart -/

/-- **An epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on
the sections over every affine étale chart.**

This is the uniform form of Descent, Proposition 03DW carried as a hypothesis throughout this
tree, with nothing asked of the source or of the target.

An epimorphism of sheaves of modules is locally surjective, so a covering sieve of the chart
suffices; such a sieve contains a finite family of affine charts which is étale, hence flat, in
schemes, and along that family the first Čech cohomology of the kernel vanishes
(`AlgebraicGeometry.Space.SmallEtale.exists_overlaps_familyCechH1Vanishing`), the sections of the
kernel over an object being the sections of the source killed by `q`
(`SheafOfModules.exists_app_kernel_ι_eq` and `Stacks.SheafOfModules.injective_app_kernel_ι`).  The
remaining two inputs of
`SheafOfModules.jointlyDetectsRange_of_familyCechH1Vanishing` are the two halves of the sheaf
condition along the family, `SheafOfModules.exists_restrictₛₗ_eq_of_isPullback` for the source
and `SheafOfModules.injective_restrict` for the target. -/
theorem surjective_val_app_of_epi_of_isCartesianOnAffineCharts_kernel
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) (hq : Epi q)
    (hker : IsCartesianOnAffineCharts (kernel q)) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  have hab : (kernel.ι q).val ≫ q.val = 0 := by
    rw [← SheafOfModules.comp_val, kernel.condition q]
    rfl
  have hzero : ∀ (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) (x : (kernel q).val.obj X),
      q.val.app X ((kernel.ι q).val.app X x) = 0 := fun X x ↦
    congrArg (fun φ : (kernel q).val ⟶ Q.val ↦ φ.app X x) hab
  have hnat : ∀ (X X' : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) (f : X ⟶ X')
      (x : (kernel q).val.obj X),
      (kernel.ι q).val.app X' ((kernel q).val.restrictₛₗ f x) =
        P.val.restrictₛₗ f ((kernel.ι q).val.app X x) :=
    fun _ _ f x ↦ PresheafOfModules.naturality_apply (kernel.ι q).val f x
  refine SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange.{0} q fun Sv hSv ↦ ?_
  obtain ⟨n, Z, φ, hZaff, hZS, hZcov, hZet⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hW hSv
  obtain ⟨Pb, Pb₃, pr₁, pr₂, s₁, s₂, s₃, hpb, hc₁, hc₂, hc₃, hH1⟩ :
      ∃ (Pb : Fin n → Fin n → (smallEtaleRingedSite B S hS F hF).C)
        (Pb₃ : Fin n → Fin n → Fin n → (smallEtaleRingedSite B S hS F hF).C)
        (pr₁ : ∀ i j, Pb i j ⟶ Z i) (pr₂ : ∀ i j, Pb i j ⟶ Z j)
        (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
        (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j),
        (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (φ i) (φ j)) ∧
        (∀ i j k, s₃ i j k ≫ pr₁ i j = s₂ i j k ≫ pr₁ i k) ∧
        (∀ i j k, s₃ i j k ≫ pr₂ i j = s₁ i j k ≫ pr₁ j k) ∧
        (∀ i j k, s₂ i j k ≫ pr₂ i k = s₁ i j k ≫ pr₂ j k) ∧
        ∀ ζ : ∀ i j, (kernel q).val.obj (op (Pb i j)),
          (∀ i j k, (kernel q).val.restrictₛₗ (s₁ i j k).op (ζ j k) -
              (kernel q).val.restrictₛₗ (s₂ i j k).op (ζ i k) +
                (kernel q).val.restrictₛₗ (s₃ i j k).op (ζ i j) = 0) →
            ∃ z : ∀ i, (kernel q).val.obj (op (Z i)), ∀ i j,
              (kernel q).val.restrictₛₗ (pr₁ i j).op (z i) -
                (kernel q).val.restrictₛₗ (pr₂ i j).op (z j) = ζ i j :=
    SmallEtale.exists_overlaps_familyCechH1Vanishing (hF := hF) hker hW Z φ hZaff
      (Scheme.etalePrecoverage_le_fppfPrecoverage _ hZet)
  refine ⟨Fin n, Z, φ, hZS, SheafOfModules.jointlyDetectsRange_of_familyCechH1Vanishing.{0} q
    φ pr₁ pr₂ s₁ s₂ s₃ (fun i j ↦ (hpb i j).w) hc₁ hc₂ hc₃ ?_ ?_
    (SheafOfModules.injective_restrict Q φ hZcov)⟩
  · intro ζ hζb hζc
    choose ζ' hζ' using fun i j ↦
      SheafOfModules.exists_app_kernel_ι_eq q (op (Pb i j)) (ζ i j) (hζb i j)
    have hcoc : ∀ i j k, (kernel q).val.restrictₛₗ (s₁ i j k).op (ζ' j k) -
        (kernel q).val.restrictₛₗ (s₂ i j k).op (ζ' i k) +
          (kernel q).val.restrictₛₗ (s₃ i j k).op (ζ' i j) = 0 := by
      intro i j k
      refine Stacks.SheafOfModules.injective_app_kernel_ι q (op (Pb₃ i j k)) ?_
      rw [map_add, map_sub, hnat, hnat, hnat, hζ', hζ', hζ', map_zero]
      exact hζc i j k
    obtain ⟨z, hz⟩ := hH1 ζ' hcoc
    refine ⟨fun i ↦ (kernel.ι q).val.app (op (Z i)) (z i), fun i ↦ hzero _ (z i), fun i j ↦ ?_⟩
    rw [← hnat, ← hnat, ← map_sub, hz i j, hζ' i j]
  · exact SheafOfModules.exists_restrictₛₗ_eq_of_isPullback P φ pr₁ pr₂ hpb hZcov

end AlgebraicGeometry.Space

end
