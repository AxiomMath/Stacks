module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.StalkSupportBridges
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.QuotientTilde
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.Examples.Scheme.DoubledClosedPointPowerSeries

/-!
# Grothendieck's existence theorem fails without separatedness

Let `k` be a field, `A = k⟦t⟧` and `I = (t)`. Let `X` be `Spec A` with its closed point doubled,
`Stacks.Examples.doubledClosedPoint k`: two copies of `Spec A` glued along `D(t)`. Its structure
morphism `f : X ⟶ Spec A` is locally of finite type and quasi-compact but not separated, and the
completion functor of Stacks 088D,

  `Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, t 𝒪_X)`,

is **not essentially surjective**. So Grothendieck's existence theorem, Stacks 088E
(`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`), is false once the
hypothesis that `f` is separated is dropped: this is part (1) of Stacks 0ARF.

The source glues two copies of `Spec A[x]` away from the origin; any counterexample serves for the
existential claim "false if we drop separatedness", and the doubled closed point is the smallest.

## The formal object

On the first copy `U ≅ Spec A` take the completion `(𝒪_U / t ^ (n + 1))` of the structure sheaf,
and extend it by zero to `X`, i.e. push it forward along `U ⟶ X`. Every term is supported at the
first copy `c₁` of the closed point, which is a closed point of `X`, so the direct images are
coherent and form a coherent adic system along `t 𝒪_X`
(`Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_image_supp_subset`, the version
of `Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_isProperOver` in which the
closed set carrying the support is given rather than produced from separatedness). Its support
`{c₁}` is proper over `A`, being the image of the closed immersion `Spec k ⟶ X`.

## Why it is not a completion

Suppose its system is the completion of a coherent `𝒪_X`-module `𝒢`.

* The second copy `c₂` of the closed point is not in the support of `𝒢`: it lies over `V(t)`, so
  by Nakayama it would be in the support of `𝒢 / t 𝒢`, which is the first term of the system and
  is supported at `c₁ ≠ c₂`.
* Every point of `X` other than `c₁` specialises to `c₂`, and the support is closed, so the support
  of `𝒢` lies over the closed point of `Spec A`. By Stacks 01Y9 some power `t ^ N` kills `𝒢`,
  hence every term of its completion, hence `𝒪_U / t ^ (N + 1)`.
* On global sections of `U` this says `t ^ N ∈ (t ^ (N + 1))` in `k⟦t⟧`, which is false.

## Main results

* `Stacks.Examples.doubledClosedPointFormalObject` — the coherent adic system above.
* `Stacks.Examples.false_of_completionFunctorProperOver_obj_iso` — it has no algebraization.
* `Stacks.Examples.not_essSurj_completionFunctorProperOver_doubledClosedPoint` — the completion
  functor of the doubled closed point is not essentially surjective.
* `Stacks.Algebraization.not_forall_isEquivalence_completionFunctorProperOver` — the statement of
  Stacks 088E without separatedness is false.

## References

* [Stacks Project, Tag 0ARF](https://stacks.math.columbia.edu/tag/0ARF)
* [Stacks Project, Tag 0ARE](https://stacks.math.columbia.edu/tag/0ARE)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-- **The direct image along the inclusion of an open of a coherent adic system supported in a
closed subset of that open is a coherent adic system.** Let `U ⊆ X` be open, `ℐ` a quasi-coherent
ideal sheaf on `X` and `(F_n)` a coherent adic system on `U` along `ℐ|_U` whose zeroth term has
support with image inside a closed subset `T ⊆ X` contained in `U`. Then `((U.ι)_* F_n)` is a
coherent adic system on `X` along `ℐ`.

This is `Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_isProperOver` with the
closed set `T` given instead of produced: there separatedness of the structure morphism is used
only to show that the image of a closed subset of `U` proper over the base is closed in `X`. -/
public theorem isCoherentAdicSystem_pushforward_opens_of_image_supp_subset {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (I : X.IdealSheafData)
    (F : ℕᵒᵖ ⥤ (U : Scheme.{u}).Modules)
    (hF : Stacks.Coherent.IsCoherentAdicSystem (I.comap U.ι) F)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (hFT : U.ι.base '' _root_.SheafOfModules.supp (F.obj (op 0)) ⊆ T) :
    Stacks.Coherent.IsCoherentAdicSystem I (F ⋙ Scheme.Modules.pushforward U.ι) := by
  have hNU : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  have hsupp : ∀ n : ℕ, U.ι.base '' _root_.SheafOfModules.supp (F.obj (op n)) ⊆ T := fun n =>
    (Set.image_mono (supp_subset_supp_obj_zero (I.comap U.ι) ⟨F, hF⟩ n)).trans hFT
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have : _root_.SheafOfModules.IsCoherent.{u} (F.obj (op n)) := hF.isCoherent n
    exact Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset
      U T hT hTU (F.obj (op n)) (hsupp n)
  · exact idealPowerMultiple_pushforward_eq_bot_of_comap U.ι I (n + 1) (F.obj (op n))
      (hF.idealPowerMultiple_eq_bot n)
  · have : _root_.SheafOfModules.IsCoherent.{u} (F.obj (op (n + 1))) := hF.isCoherent (n + 1)
    have : IsIso (C := X.Modules)
        (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) (F.obj (op (n + 1)))) :=
      isIso_directImageQuotientComparison_of_supp_subset U I n (F.obj (op (n + 1)))
        T hT hTU (hsupp (n + 1))
    refine ⟨asIso (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1)
        (F.obj (op (n + 1)))) ≪≫
      (Scheme.Modules.pushforward U.ι).mapIso (hF.quotientIso n), ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward U.ι).map (hF.quotientIso n).hom)
          (Stacks.Coherent.directImageQuotientComparison_π U.ι I (n + 1)
            (F.obj (op (n + 1))))).trans
        (((Scheme.Modules.pushforward U.ι).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward U.ι).map
            (hF.cokernel_π_comp_quotientIso n))))

/-- **The direct image along the inclusion of an open of a coherent module supported in a closed
subset of that open proper over the base has support proper over the base.** The companion of
`Stacks.Algebraization.hasProperSupport_pushforward_opens_of_isProperOver` with the closed set
`T ⊆ U` carrying the support given, so that no separatedness is needed. -/
public theorem hasProperSupport_pushforward_opens_of_image_supp_subset {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (p : X ⟶ S) [LocallyOfFiniteType p]
    (N : (U : Scheme.{u}).Modules) [N.IsCoherent] (T : Closeds X)
    (hTU : (T : Set X) ⊆ (U : Set X)) (hT : IsProperOver p T)
    (hN : U.ι.base '' _root_.SheafOfModules.supp N ⊆ (T : Set X)) :
    HasProperSupport p ((Scheme.Modules.pushforward U.ι).obj N) := by
  have : ((Scheme.Modules.pushforward U.ι).obj N).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset
      U T T.2 hTU N hN
  have : ((Scheme.Modules.pushforward U.ι).obj N).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
      (M := (Scheme.Modules.pushforward U.ι).obj N)
  exact ⟨⟨_root_.SheafOfModules.supp ((Scheme.Modules.pushforward U.ι).obj N),
    _root_.SheafOfModules.isClosed_supp _⟩, rfl, isProperOver_of_le p
    (supp_pushforward_subset_of_isClosed U (T : Set X) T.2 N hN) hT⟩

/-- On an affine scheme, if `K ^ k` kills `𝒪 / K ^ (k + 1)`, then `K(X) ^ k ≤ K(X) ^ (k + 1)`
for the ideal `K(X)` of global functions: `r • 1 = 0` in the quotient for `r ∈ K(X) ^ k`, and the
kernel of `Γ(X, 𝒪) ⟶ Γ(X, 𝒪 / K ^ (k + 1))` is `K ^ (k + 1)` over `X`. -/
public theorem ideal_top_pow_le_of_idealPowerMultiple_unitQuotient_eq_bot {Y : Scheme.{u}}
    [IsAffine Y] (K : Y.IdealSheafData) (k : ℕ)
    (h : idealPowerMultiple K k (idealPowerQuotient K (k + 1) Y.unitModule) = ⊥) :
    K.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ k ≤ (K ^ (k + 1)).ideal ⟨⊤, isAffineOpen_top Y⟩ := by
  intro r hr
  have h0 := affine_sections_annihilated_of_idealPowerMultiple_eq_bot h ⟨⊤, isAffineOpen_top Y⟩
    hr ((unitIdealPowerQuotientπ K (k + 1)).app ⊤ (1 : Γ(Y, ⊤)))
  have h1 : (unitIdealPowerQuotientπ K (k + 1)).app ⊤ (r • (1 : Γ(Y, ⊤))) = 0 :=
    (Scheme.Modules.Hom.app_smul _ r _).trans h0
  rw [smul_eq_mul, mul_one] at h1
  exact (app_top_unitIdealPowerQuotientπ_eq_zero_iff K (k + 1) r).1 h1

end Stacks.Algebraization


namespace Stacks.Examples

open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

variable (k : Type u) [Field k]

attribute [local instance] SectionCoverData.isOpenImmersion_chart

/-- The structure morphism sends the image of `y` under either chart to `y`. -/
public theorem doubledClosedPoint_proj_chart_apply (b : Bool) (y : Spec (.of (PowerSeries k))) :
    (doubledClosedPoint k).proj ((doubledClosedPoint k).chart b y) = y := by
  rw [← Scheme.Hom.comp_apply, (doubledClosedPoint k).chart_comp_proj]
  rfl

/-- A prime of `k⟦t⟧` containing `t` is the closed point. -/
public theorem eq_closedPoint_of_span_X_le (p : PrimeSpectrum (PowerSeries k))
    (hp : Ideal.span {(PowerSeries.X : PowerSeries k)} ≤ p.asIdeal) :
    p = IsLocalRing.closedPoint (PowerSeries k) := by
  by_contra hne
  have hmem := (mem_powerSeriesGenericLocus_iff k p).2 hne
  exact hmem (hp (Ideal.subset_span rfl))

/-- A point of the doubled closed point lies in the support of `t 𝒪` exactly when it lies over
the closed point. -/
public theorem mem_support_baseIdealSheaf_doubledClosedPoint_iff
    (x : (doubledClosedPoint k).total) :
    x ∈ (baseIdealSheaf (PowerSeries k) (Ideal.span {PowerSeries.X})
        (doubledClosedPoint k).proj).support ↔
      (doubledClosedPoint k).proj x = IsLocalRing.closedPoint (PowerSeries k) := by
  refine ⟨fun hx => eq_closedPoint_of_span_X_le k _ (support_baseIdealSheaf_le _ _ hx),
    fun hx => mem_support_baseIdealSheaf _ _ ?_⟩
  rw [hx]
  change _ ≤ IsLocalRing.maximalIdeal (PowerSeries k)
  rw [PowerSeries.maximalIdeal_eq_span_X]

/-- No point of the second chart is the first copy of the closed point. -/
public theorem doubledClosedPoint_chart_false_ne (y : Spec (.of (PowerSeries k))) :
    (doubledClosedPoint k).chart false y ≠
      (doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k)) := fun e =>
  closedPoint_notMem_powerSeriesGenericLocus k
    (mem_powerSeriesGenericLocus_of_chart_eq k (by decide) e.symm)

/-- Every point other than the first copy of the closed point lies on the second chart. -/
public theorem exists_chart_false_eq_of_ne (x : (doubledClosedPoint k).total)
    (hx : x ≠ (doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k))) :
    ∃ y, (doubledClosedPoint k).chart false y = x := by
  obtain ⟨b, y, rfl⟩ := (doubledClosedPoint k).exists_chart_eq x
  cases b with
  | false => exact ⟨y, rfl⟩
  | true =>
    have hy : y ∈ powerSeriesGenericLocus k :=
      (mem_powerSeriesGenericLocus_iff k y).2 fun h => hx (by rw [h])
    refine ⟨y, ?_⟩
    have := doubledClosedPoint_chart_true_apply_eq k ⟨y, hy⟩
    simp only [Scheme.Opens.ι_apply] at this
    exact this.symm

/-- The first copy of the closed point is a closed point of the doubled closed point. -/
public theorem isClosed_singleton_chart_true_closedPoint :
    IsClosed {(doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k))} := by
  have hc : ({(doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k))} :
      Set (doubledClosedPoint k).total)ᶜ = Set.range ((doubledClosedPoint k).chart false) := by
    ext x
    refine ⟨fun hx => exists_chart_false_eq_of_ne k x hx, ?_⟩
    rintro ⟨y, rfl⟩
    exact doubledClosedPoint_chart_false_ne k y
  rw [← isOpen_compl_iff, hc]
  exact ((doubledClosedPoint k).chart false).isOpenEmbedding.isOpen_range

/-- The first copy of the closed point, as a closed subset. -/
public def doubledClosedPointFirstClosedPoint : Closeds (doubledClosedPoint k).total :=
  ⟨{(doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k))},
    isClosed_singleton_chart_true_closedPoint k⟩

/-- The first copy of the closed point is proper over `k⟦t⟧`: it is the image of the closed
immersion `Spec k ⟶ X` through the first chart, which is finite over the base. -/
public theorem isProperOver_doubledClosedPointFirstClosedPoint :
    IsProperOver (doubledClosedPoint k).proj (doubledClosedPointFirstClosedPoint k) := by
  set m := IsLocalRing.maximalIdeal (PowerSeries k) with hm
  let i : Spec (.of (PowerSeries k ⧸ m)) ⟶ Spec (.of (PowerSeries k)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_quotient_mk (R := .of (PowerSeries k)) m
  let q := i ≫ (doubledClosedPoint k).chart true
  have hi : ∀ z, i z = IsLocalRing.closedPoint (PowerSeries k) := fun z => by
    refine eq_closedPoint_of_span_X_le k _ ?_
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    intro a ha
    change Ideal.Quotient.mk m a ∈ z.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact zero_mem _
  have hrange : Set.range q = (doubledClosedPointFirstClosedPoint k : Set _) := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨z, rfl⟩
      change (doubledClosedPoint k).chart true (i z) = _
      rw [hi z]
    · have : Field (PowerSeries k ⧸ m) := Ideal.Quotient.field m
      obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of (PowerSeries k ⧸ m))))
      refine ⟨z, ?_⟩
      rw [Set.mem_singleton_iff.1 hx]
      change (doubledClosedPoint k).chart true (i z) = _
      rw [hi z]
  have hclosed : IsClosed (Set.range q) := by
    rw [hrange]
    exact (doubledClosedPointFirstClosedPoint k).2
  have : IsClosedImmersion q := .of_isPreimmersion q hclosed
  have hqf : q ≫ (doubledClosedPoint k).proj = i := by
    simp only [q, Category.assoc, (doubledClosedPoint k).chart_comp_proj, Category.comp_id]
  have : IsClosedImmersion (q ≫ (doubledClosedPoint k).proj) := by
    rw [hqf]
    infer_instance
  have hZ : IsProperOver (q ≫ (doubledClosedPoint k).proj) ⊤ := by
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫
      q ≫ (doubledClosedPoint k).proj)
    exact inferInstance
  have himg := isProperOver_closedImage q (doubledClosedPoint k).proj ⊤ hZ
  have hle : doubledClosedPointFirstClosedPoint k ≤ q.closedImage ⊤ := by
    intro x hx
    have hx' : x ∈ Set.range q := by
      rw [hrange]
      exact hx
    obtain ⟨z, hz⟩ := hx'
    change x ∈ q.base '' ((⊤ : Closeds (Spec (.of (PowerSeries k ⧸ m)))) : Set _)
    rw [Closeds.coe_top]
    exact ⟨z, Set.mem_univ z, hz⟩
  exact isProperOver_of_le (doubledClosedPoint k).proj hle himg

/-- The ideal sheaf `t 𝒪_X` on the doubled closed point. -/
public abbrev doubledClosedPointIdealSheaf : (doubledClosedPoint k).total.IdealSheafData :=
  baseIdealSheaf (PowerSeries k) (Ideal.span {PowerSeries.X}) (doubledClosedPoint k).proj

/-- The doubled closed point is locally Noetherian. -/
public instance isLocallyNoetherian_doubledClosedPoint_total :
    IsLocallyNoetherian (doubledClosedPoint k).total :=
  LocallyOfFiniteType.isLocallyNoetherian (doubledClosedPoint k).proj

/-- The image of the first chart, an affine open of the doubled closed point. -/
public abbrev doubledClosedPointFirstChart : (doubledClosedPoint k).total.Opens :=
  ((doubledClosedPoint k).chart true).opensRange

/-- The image of the first chart is affine. -/
public instance isAffine_doubledClosedPointFirstChart :
    IsAffine (doubledClosedPointFirstChart k) :=
  isAffineOpen_opensRange _

/-- The completion of the structure sheaf of the first chart along `t`. -/
public def doubledClosedPointChartCompletion :
    Stacks.Coherent.CoherentAdicSystems
      ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι) :=
  (completionFunctor (doubledClosedPointFirstChart k) _).obj
    ⟨Scheme.unitModule _,
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _⟩

/-- The terms of the completion of `𝒪` on the first chart are the quotients `𝒪 / t ^ (n + 1)`. -/
public theorem doubledClosedPointChartCompletion_obj (n : ℕ) :
    (doubledClosedPointChartCompletion k).obj.obj (op n) =
      idealPowerQuotient
        ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι) (n + 1)
        (Scheme.unitModule (doubledClosedPointFirstChart k : Scheme.{u})) :=
  completionFunctor_obj _ _ _ n

/-- The first copy of the closed point lies on the first chart. -/
public theorem doubledClosedPointFirstClosedPoint_subset :
    (doubledClosedPointFirstClosedPoint k : Set (doubledClosedPoint k).total) ⊆
      (doubledClosedPointFirstChart k : Set (doubledClosedPoint k).total) := by
  rintro x rfl
  rw [Scheme.Hom.coe_opensRange]
  exact ⟨_, rfl⟩

/-- The completion of the structure sheaf of the first chart is supported at the first copy of
the closed point. -/
public theorem image_supp_doubledClosedPointChartCompletion_subset :
    (doubledClosedPointFirstChart k).ι.base ''
        _root_.SheafOfModules.supp ((doubledClosedPointChartCompletion k).obj.obj (op 0)) ⊆
      (doubledClosedPointFirstClosedPoint k : Set (doubledClosedPoint k).total) := by
  set U := doubledClosedPointFirstChart k
  set Q := doubledClosedPointChartCompletion k
  have : IsNoetherian (U : Scheme.{u}) := ⟨⟩
  have : _root_.SheafOfModules.IsCoherent.{u} (Q.obj.obj (op 0)) := Q.property.isCoherent 0
  have hsupp := (exists_idealPowerMultiple_eq_bot_iff_supp_subset (Q.obj.obj (op 0))
    ((doubledClosedPointIdealSheaf k).comap U.ι)).1 ⟨1, Q.property.idealPowerMultiple_eq_bot 0⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h2 : x ∈ ((doubledClosedPointIdealSheaf k).comap U.ι).support := hsupp hx
  rw [Scheme.IdealSheafData.support_comap] at h2
  have h3 : (doubledClosedPoint k).proj (U.ι x) = IsLocalRing.closedPoint (PowerSeries k) :=
    (mem_support_baseIdealSheaf_doubledClosedPoint_iff k _).1 h2
  have hU : U.ι x ∈ Set.range ((doubledClosedPoint k).chart true) := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hU
  rw [← hz, doubledClosedPoint_proj_chart_apply] at h3
  rw [← hxy, ← hz, h3]
  rfl

/-- The termwise direct image of the completion of `𝒪` on the first chart is a coherent adic
system on the doubled closed point. -/
public theorem isCoherentAdicSystem_doubledClosedPointFormalSystem :
    Stacks.Coherent.IsCoherentAdicSystem (doubledClosedPointIdealSheaf k)
      ((doubledClosedPointChartCompletion k).obj ⋙
        Scheme.Modules.pushforward (doubledClosedPointFirstChart k).ι) :=
  isCoherentAdicSystem_pushforward_opens_of_image_supp_subset _ _ _
    (doubledClosedPointChartCompletion k).property _ (doubledClosedPointFirstClosedPoint k).2
    (doubledClosedPointFirstClosedPoint_subset k)
    (image_supp_doubledClosedPointChartCompletion_subset k)

/-- **The formal object.** The coherent adic system `(A / t ^ (n + 1))~` on the first chart,
extended by zero to the doubled closed point, as an object of
`Coh_{support proper over A}(X, t 𝒪_X)`. -/
public def doubledClosedPointFormalObject :
    CoherentAdicSystemsProperOver (doubledClosedPoint k).proj (doubledClosedPointIdealSheaf k) :=
  ⟨⟨_, isCoherentAdicSystem_doubledClosedPointFormalSystem k⟩, by
    have : _root_.SheafOfModules.IsCoherent.{u}
        ((doubledClosedPointChartCompletion k).obj.obj (op 0)) :=
      (doubledClosedPointChartCompletion k).property.isCoherent 0
    exact hasProperSupport_pushforward_opens_of_image_supp_subset _ _ _ _
      (doubledClosedPointFirstClosedPoint_subset k)
      (isProperOver_doubledClosedPointFirstClosedPoint k)
      (image_supp_doubledClosedPointChartCompletion_subset k)⟩

/-- The second copy of the closed point is outside the support of every algebraization of the
formal object. -/
public theorem chart_false_closedPoint_notMem_supp_of_iso
    (G : CoherentModulesProperOver (doubledClosedPoint k).proj)
    (e : (completionFunctorProperOver (PowerSeries k) (Ideal.span {PowerSeries.X})
      (doubledClosedPoint k).proj).obj G ≅ doubledClosedPointFormalObject k) :
    (doubledClosedPoint k).chart false (IsLocalRing.closedPoint (PowerSeries k)) ∉
      _root_.SheafOfModules.supp G.obj.obj := by
  intro hx
  have h1 := mem_supp_completionFunctor_obj_of_mem_supp (doubledClosedPointIdealSheaf k) G.obj 0
    hx ((mem_support_baseIdealSheaf_doubledClosedPoint_iff k _).2
      (doubledClosedPoint_proj_chart_apply k false _))
  have e0 := ((ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso e)).app (op 0)
  have h2 := (_root_.SheafOfModules.supp_eq_of_iso e0).subset h1
  exact doubledClosedPoint_chart_false_ne k _
    (supp_pushforward_subset_of_isClosed _ _ (doubledClosedPointFirstClosedPoint k).2 _
      (image_supp_doubledClosedPointChartCompletion_subset k) h2)

/-- A closed subset of the doubled closed point avoiding the second copy of the closed point lies
over the closed point of `Spec k⟦t⟧`: every other point specialises to that second copy. -/
public theorem subset_support_of_isClosed_of_chart_false_notMem
    (Z : Set (doubledClosedPoint k).total) (hZ : IsClosed Z)
    (hc : (doubledClosedPoint k).chart false (IsLocalRing.closedPoint (PowerSeries k)) ∉ Z) :
    Z ⊆ ((doubledClosedPointIdealSheaf k).support : Set (doubledClosedPoint k).total) := by
  intro x hx
  obtain ⟨b, y, hby⟩ := (doubledClosedPoint k).exists_chart_eq x
  by_cases hy : y = IsLocalRing.closedPoint (PowerSeries k)
  · rw [← hby]
    exact (mem_support_baseIdealSheaf_doubledClosedPoint_iff k _).2
      ((doubledClosedPoint_proj_chart_apply k b y).trans hy)
  · exfalso
    have hyD : y ∈ powerSeriesGenericLocus k := (mem_powerSeriesGenericLocus_iff k y).2 hy
    have hb : (doubledClosedPoint k).chart b y = (doubledClosedPoint k).chart false y := by
      cases b with
      | false => rfl
      | true =>
        have := doubledClosedPoint_chart_true_apply_eq k ⟨y, hyD⟩
        simpa only [Scheme.Opens.ι_apply] using this
    have hspec : (doubledClosedPoint k).chart false y ⤳
        (doubledClosedPoint k).chart false (IsLocalRing.closedPoint (PowerSeries k)) :=
      ((PrimeSpectrum.le_iff_specializes y _).mp
        (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)).map
        ((doubledClosedPoint k).chart false).continuous
    rw [← hby, hb] at hx
    exact hc (hspec.mem_closed hZ hx)

/-- After a ring map with a left inverse, `t ^ m` is not a multiple of `t ^ (m + 1)`. -/
public theorem not_map_span_X_pow_le {B : Type*} [CommRing B] (θ : PowerSeries k →+* B)
    (ρ : B →+* PowerSeries k) (h : ∀ a, ρ (θ a) = a) (m : ℕ) :
    ¬ Ideal.map θ (Ideal.span {PowerSeries.X}) ^ m ≤
      Ideal.map θ (Ideal.span {PowerSeries.X}) ^ (m + 1) := by
  intro hle
  have h1 := Ideal.map_mono (f := ρ) hle
  rw [Ideal.map_pow, Ideal.map_pow, Ideal.map_map,
    show ρ.comp θ = RingHom.id _ from RingHom.ext h, Ideal.map_id,
    Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  have h2 := h1 (Ideal.mem_span_singleton_self _)
  rw [Ideal.mem_span_singleton] at h2
  have hX : ¬ IsUnit (PowerSeries.X : PowerSeries k) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  exact absurd ((pow_dvd_pow_iff PowerSeries.X_ne_zero hX).1 h2) (by omega)

/-- The first chart is a section of `Spec k⟦t⟧`: the ring map `k⟦t⟧ ⟶ Γ(U, 𝒪)` has a left
inverse. -/
public theorem doubledClosedPointFirstChart_leftInverse (a : PowerSeries k) :
    (((doubledClosedPoint k).chart true).isoOpensRange.hom.appTop ≫
        (Scheme.ΓSpecIso (.of (PowerSeries k))).hom).hom
      (((Scheme.ΓSpecIso (.of (PowerSeries k))).inv ≫
        ((doubledClosedPointFirstChart k).ι ≫ (doubledClosedPoint k).proj).appTop).hom a) =
      a := by
  have hch : ((doubledClosedPoint k).chart true).isoOpensRange.hom ≫
      (doubledClosedPointFirstChart k).ι ≫ (doubledClosedPoint k).proj = 𝟙 _ := by
    rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
    exact (doubledClosedPoint k).chart_comp_proj true
  have key : (Scheme.ΓSpecIso (.of (PowerSeries k))).inv ≫
      (((doubledClosedPoint k).chart true).isoOpensRange.hom ≫
        (doubledClosedPointFirstChart k).ι ≫ (doubledClosedPoint k).proj).appTop ≫
      (Scheme.ΓSpecIso (.of (PowerSeries k))).hom = 𝟙 _ := by
    rw [hch, Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun φ => φ.hom a) key

/-- Over the whole first chart, the ideal of `t 𝒪` is generated by the image of `t`. -/
public theorem doubledClosedPointFirstChart_ideal_top :
    ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv ≫
        ((doubledClosedPointFirstChart k).ι ≫ (doubledClosedPoint k).proj).appTop).hom
        (Ideal.span {PowerSeries.X}) := by
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap, baseIdealSheaf_ideal]
  change Ideal.map ((doubledClosedPointFirstChart k : Scheme.{u}).presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rfl

/-- On the first chart, `t ^ m` does not kill `𝒪 / t ^ (m + 1)`. -/
public theorem idealPowerMultiple_chart_unitQuotient_ne_bot (m : ℕ) :
    idealPowerMultiple
        ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι) m
      (idealPowerQuotient
        ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι) (m + 1)
        (doubledClosedPointFirstChart k : Scheme.{u}).unitModule) ≠ ⊥ := by
  intro h
  have hle := ideal_top_pow_le_of_idealPowerMultiple_unitQuotient_eq_bot _ m h
  have hpow : ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι ^
      (m + 1)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((doubledClosedPointIdealSheaf k).comap (doubledClosedPointFirstChart k).ι).ideal
        ⟨⊤, isAffineOpen_top _⟩ ^ (m + 1) := by
    rw [Scheme.IdealSheafData.ideal_pow]
    rfl
  rw [hpow, doubledClosedPointFirstChart_ideal_top] at hle
  exact not_map_span_X_pow_le k _ _ (doubledClosedPointFirstChart_leftInverse k) m hle

/-- The doubled closed point is a Noetherian scheme. -/
public instance isNoetherian_doubledClosedPoint_total :
    IsNoetherian (doubledClosedPoint k).total := by
  have : CompactSpace (Spec (.of (PowerSeries k))) := PrimeSpectrum.compactSpace
  have : CompactSpace (doubledClosedPoint k).total :=
    QuasiCompact.compactSpace_of_compactSpace (doubledClosedPoint k).proj
  exact ⟨⟩

/-- **The formal object has no algebraization.** No coherent module with support proper over
`k⟦t⟧` has completion isomorphic to `doubledClosedPointFormalObject k`. -/
public theorem false_of_completionFunctorProperOver_obj_iso
    (G : CoherentModulesProperOver (doubledClosedPoint k).proj)
    (e : (completionFunctorProperOver (PowerSeries k) (Ideal.span {PowerSeries.X})
      (doubledClosedPoint k).proj).obj G ≅ doubledClosedPointFormalObject k) : False := by
  set J := doubledClosedPointIdealSheaf k
  set U := doubledClosedPointFirstChart k
  set Q := doubledClosedPointChartCompletion k
  have hG : _root_.SheafOfModules.IsCoherent.{u} G.obj.obj := G.obj.property
  have hGq : G.obj.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G.obj.obj).1
  have hGf : G.obj.obj.IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := G.obj.obj)
  have hsupp : _root_.SheafOfModules.supp G.obj.obj ⊆ (J.support : Set _) :=
    subset_support_of_isClosed_of_chart_false_notMem k _ (_root_.SheafOfModules.isClosed_supp _)
      (chart_false_closedPoint_notMem_supp_of_iso k G e)
  obtain ⟨N, hN⟩ := (exists_idealPowerMultiple_eq_bot_iff_supp_subset G.obj.obj J).2 hsupp
  -- the `N`-th term of the completion of `G` is killed by `J ^ N`
  have hT : _root_.SheafOfModules.IsCoherent.{u}
      (((completionFunctor _ J).obj G.obj).obj.obj (op N)) :=
    ((completionFunctor _ J).obj G.obj).property.isCoherent N
  have hTq : (((completionFunctor _ J).obj G.obj).obj.obj (op N)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hπ : Epi (C := (doubledClosedPoint k).total.Modules)
      (cokernel.π (C := (doubledClosedPoint k).total.Modules)
        (idealPowerMultiple J (N + 1) G.obj.obj).ι) := coequalizer.π_epi
  have hQq := isQuasicoherent_idealPowerQuotient J (N + 1) G.obj.obj
  have h1' : idealPowerMultiple J N (idealPowerQuotient J (N + 1) G.obj.obj) = ⊥ :=
    idealPowerMultiple_eq_bot_of_epi J N (cokernel.π (C := (doubledClosedPoint k).total.Modules)
      (idealPowerMultiple J (N + 1) G.obj.obj).ι) hN
  have h1 : idealPowerMultiple J N (((completionFunctor _ J).obj G.obj).obj.obj (op N)) = ⊥ :=
    (congrArg (fun T : (doubledClosedPoint k).total.Modules => idealPowerMultiple J N T = ⊥)
      (completionFunctor_obj _ J G.obj N)).mpr h1'
  -- transport to the formal object
  have e0 := ((ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso e)).app (op N)
  have hTq' : (((ObjectProperty.ι _).obj ((ObjectProperty.ι _).obj
      ((completionFunctorProperOver (PowerSeries k) (Ideal.span {PowerSeries.X})
        (doubledClosedPoint k).proj).obj G))).obj (op N)).IsQuasicoherent := hTq
  have hP : _root_.SheafOfModules.IsCoherent.{u}
      ((Scheme.Modules.pushforward U.ι).obj (Q.obj.obj (op N))) :=
    (doubledClosedPointFormalObject k).obj.property.isCoherent N
  have hPq : ((Scheme.Modules.pushforward U.ι).obj (Q.obj.obj (op N))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have h2 : idealPowerMultiple J N ((Scheme.Modules.pushforward U.ι).obj (Q.obj.obj (op N))) =
      ⊥ :=
    have he0 : Epi (C := (doubledClosedPoint k).total.Modules) e0.hom :=
      ⟨fun g h hh => (cancel_epi e0.hom).1 hh⟩
    @idealPowerMultiple_eq_bot_of_epi _ J N _ _ hTq' hPq e0.hom he0 h1
  -- restrict to the first chart
  have h3 := idealPowerMultiple_restrict_eq_bot U.ι J N _ h2
  have hQN : _root_.SheafOfModules.IsCoherent.{u} (Q.obj.obj (op N)) := Q.property.isCoherent N
  have hQNq : (Q.obj.obj (op N)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hRq : ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward U.ι).obj (Q.obj.obj (op N)))).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  let ε := (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app (Q.obj.obj (op N))
  have hε : Epi (C := (U : Scheme.{u}).Modules) ε.hom :=
    ⟨fun g h hh => (cancel_epi ε.hom).1 hh⟩
  have h4 : idealPowerMultiple (J.comap U.ι) N (Q.obj.obj (op N)) = ⊥ :=
    @idealPowerMultiple_eq_bot_of_epi _ (J.comap U.ι) N _ _ hRq hQNq ε.hom hε h3
  exact idealPowerMultiple_chart_unitQuotient_ne_bot k N
    ((congrArg (fun T : (U : Scheme.{u}).Modules => idealPowerMultiple (J.comap U.ι) N T = ⊥)
      (doubledClosedPointChartCompletion_obj k N)).mp h4)

/-- **Grothendieck's existence theorem fails without separatedness** (Stacks 0ARF, part (1)).
For the spectrum of `k⟦t⟧` with its closed point doubled, the completion functor
`Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, t 𝒪_X)` of Stacks 088D is
not essentially surjective: the system `(A / t ^ (n + 1))~` on one copy of `Spec A`, extended by
zero, is not the completion of any coherent module. -/
public theorem not_essSurj_completionFunctorProperOver_doubledClosedPoint :
    ¬ (completionFunctorProperOver (PowerSeries k) (Ideal.span {PowerSeries.X})
      (doubledClosedPoint k).proj).EssSurj := by
  intro h
  obtain ⟨G, ⟨e⟩⟩ := h.mem_essImage (doubledClosedPointFormalObject k)
  exact false_of_completionFunctorProperOver_obj_iso k G e

end Stacks.Examples

namespace Stacks.Algebraization

/-- **Stacks 088E is false without separatedness** (Stacks 0ARF, part (1)). The statement of
Grothendieck's existence theorem `isEquivalence_completionFunctorProperOver_holds` with the
hypothesis that `X ⟶ Spec A` is separated removed does not hold: the doubled closed point of
`Spec ℚ⟦t⟧` is a counterexample. -/
public theorem not_forall_isEquivalence_completionFunctorProperOver :
    ¬ (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
        {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f],
        (completionFunctorProperOver A I f).IsEquivalence) := by
  intro h
  have := h (PowerSeries (ULift.{u} ℚ)) (Ideal.span {PowerSeries.X})
    (Stacks.Examples.doubledClosedPoint (ULift.{u} ℚ)).proj
  exact Stacks.Examples.not_essSurj_completionFunctorProperOver_doubledClosedPoint
    (ULift.{u} ℚ) inferInstance

end Stacks.Algebraization

end
