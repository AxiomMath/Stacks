module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral

/-!
# The fibre-integral chart of a support finite over the base

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type and locally
quasi-finite as a morphism of schemes, let `V` be étale over `Y` and let `E` be a support of
`X_V = V ×_Y X` finite over `V` in the sense of `AlgebraicGeometry.FiniteSupport`. The group
`H_E(F)` out of which the colimit defining `f_{p!}F` is formed lives on the canonical open
`coborder E` of `X_V`, so the fibre integral of
`AlgebraicGeometry.fibreIntegral` has to be applied to that open. This file assembles the data
`(U, h, π, g, Z, i)` that `AlgebraicGeometry.isLocallyConstant_fibreIntegral` asks for out of `E`
alone:

* `U` is the canonical open of `E`;
* `π : U ⟶ V` is its projection and `h : U ⟶ X` its structure map;
* `g : V ⟶ Y` is the étale structure morphism of `V`;
* `i : Z ⟶ U` is a closed immersion, finite over `V`, with image the part of `E` inside `U`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.baseChangeChartProj` and
  `AlgebraicGeometry.SmallEtale.baseChangeChartToSource` — the two legs `X_V ⟶ V` and `X_V ⟶ X`
  of the base change of `f` along `V`, named at the type in which `X_V` is an object of the
  small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.finiteSupportChartProj` — the projection `π : U ⟶ V` of the
  chart of a finite support.
* `AlgebraicGeometry.SmallEtale.finiteSupportChartToSource` — the structure map `h : U ⟶ X` of
  the chart of a finite support.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportChart_comm` — the chart is a commutative square
  over `f`.
* `AlgebraicGeometry.SmallEtale.isOpenImmersion_finiteSupportChartLift` — the chart is an open
  subscheme of `X ×_Y V`.
* `AlgebraicGeometry.SmallEtale.exists_isClosedImmersion_isFinite_range_finiteSupportChart` —
  the subscheme witnessing that `E` is finite over `V` factors through the canonical open as a
  closed immersion, still finite over `V`, whose image is the part of `E` inside that open.
* `AlgebraicGeometry.SmallEtale.isLocallyConstant_fibreIntegral_finiteSupportChart` — the fibre
  integral over the chart of a finite support is locally constant.
* `AlgebraicGeometry.SmallEtale.fibreIntegral_add_finiteSupportChart` — the fibre integral over
  the chart of a finite support is additive in the section.
* `SmallEtale.fibreIntegral_eq_separableDegreeWeightedFiberSum_finiteSupportChart` — the fibre
  integral over the chart of a finite support is the weighted fibre sum of `s · w`.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Target

variable (B : BigEtaleSite.{u}) {Y : B.Scheme} (V : SmallEtale B Y.obj Y.property)

/-- The structure morphism of an object of the small étale site of `Y` is étale. -/
public theorem etale_finiteSupportChartTarget : Etale (B.inclusion.map V.obj.hom) :=
  V.property

end Target

section BaseChangeChart

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property)

/-- The projection `X_V ⟶ V` of the base change of `f` along `V`, named at the type
`(SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶ B.inclusion.obj V.obj.left`
in which `X_V` is an object of the small étale site of `X`. -/
public def baseChangeChartProj :
    (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶
      B.inclusion.obj V.obj.left :=
  B.inclusion.map (pullback.fst V.obj.hom f)

/-- The structure map `X_V ⟶ X` of the base change of `f` along `V`, named at the type
`(SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶ X.obj` in which `X_V` is an
object of the small étale site of `X`. -/
public def baseChangeChartToSource :
    (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶ X.obj :=
  B.inclusion.map (pullback.snd V.obj.hom f)

/-- `X_V` is the fibre product of `X` and `V` over `Y`, with the structure map and the
projection as its two legs. -/
public theorem isPullback_baseChangeChartProj :
    IsPullback (baseChangeChartToSource B f V) (baseChangeChartProj B f V)
      (B.inclusion.map f) (B.inclusion.map V.obj.hom) :=
  ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).flip

/-- The projection `X_V ⟶ V` is locally of finite type, being a base change of `f`. -/
public instance locallyOfFiniteType_baseChangeChartProj
    [LocallyOfFiniteType (B.inclusion.map f)] :
    LocallyOfFiniteType (baseChangeChartProj B f V) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeChartProj B f V) inferInstance

/-- The projection `X_V ⟶ V` is locally quasi-finite, being a base change of `f`. -/
public instance locallyQuasiFinite_baseChangeChartProj
    [LocallyQuasiFinite (B.inclusion.map f)] :
    LocallyQuasiFinite (baseChangeChartProj B f V) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeChartProj B f V) inferInstance

end BaseChangeChart

section Chart

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)

/-- The projection `π` of the chart of a finite support: the canonical open of `E` inside
`X_V = V ×_Y X`, projected to `V`. -/
public def finiteSupportChartProj :
    (finiteSupportOpen B f V E).toScheme ⟶ B.inclusion.obj V.obj.left :=
  (finiteSupportOpen B f V E).ι ≫ baseChangeChartProj B f V

/-- The structure map `h` of the chart of a finite support: the canonical open of `E` inside
`X_V = V ×_Y X`, mapped to `X`. -/
public def finiteSupportChartToSource :
    (finiteSupportOpen B f V E).toScheme ⟶ X.obj :=
  (finiteSupportOpen B f V E).ι ≫ baseChangeChartToSource B f V

/-- The chart of a finite support is a commutative square over `f`: its structure map followed
by `f` is its projection followed by the structure morphism of `V`. -/
public theorem finiteSupportChart_comm :
    finiteSupportChartToSource B f V E ≫ B.inclusion.map f =
      finiteSupportChartProj B f V E ≫ B.inclusion.map V.obj.hom := by
  rw [finiteSupportChartToSource, finiteSupportChartProj, Category.assoc, Category.assoc,
    (isPullback_baseChangeChartProj B f V).w]

/-- The chart of a finite support is an open subscheme of the fibre product `X ×_Y V`: it is an
open subscheme of `V ×_Y X`, and the two fibre products of the same cospan are canonically
isomorphic. -/
public theorem isOpenImmersion_finiteSupportChartLift :
    IsOpenImmersion (pullback.lift (finiteSupportChartToSource B f V E)
      (finiteSupportChartProj B f V E) (finiteSupportChart_comm B f V E)) := by
  have heq : pullback.lift (finiteSupportChartToSource B f V E)
      (finiteSupportChartProj B f V E) (finiteSupportChart_comm B f V E) =
      (finiteSupportOpen B f V E).ι ≫
        (isPullback_baseChangeChartProj B f V).isoPullback.hom := by
    apply pullback.hom_ext <;>
      simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc,
        (isPullback_baseChangeChartProj B f V).isoPullback_hom_fst,
        (isPullback_baseChangeChartProj B f V).isoPullback_hom_snd,
        finiteSupportChartToSource, finiteSupportChartProj]
  rw [heq]
  infer_instance

/-- **The support datum of the chart of a finite support.** The subscheme witnessing that `E` is
finite over `V` factors through the canonical open of `E`, as a closed immersion which is still
finite over `V` and whose image is the part of `E` lying in that open. -/
public theorem exists_isClosedImmersion_isFinite_range_finiteSupportChart :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ (finiteSupportOpen B f V E).toScheme), IsClosedImmersion i ∧
      IsFinite (i ≫ finiteSupportChartProj B f V E) ∧
      Set.range i.base = (finiteSupportOpen B f V E).ι.base ⁻¹' E.1 := by
  obtain ⟨Z, i₀, hi₀, hfin, hrange⟩ := E.property
  have hsub : Set.range i₀.base ⊆ Set.range (finiteSupportOpen B f V E).ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
    exact subset_supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)
  obtain ⟨i, hfac⟩ : ∃ i : Z ⟶ (finiteSupportOpen B f V E).toScheme,
      i ≫ (finiteSupportOpen B f V E).ι = i₀ :=
    ⟨IsOpenImmersion.lift (finiteSupportOpen B f V E).ι i₀ hsub,
      IsOpenImmersion.lift_fac _ _ hsub⟩
  have happ (z : Z) : (finiteSupportOpen B f V E).ι.base (i.base z) = i₀.base z := by
    rw [← hfac]
    rfl
  have hrange' : Set.range i.base = (finiteSupportOpen B f V E).ι.base ⁻¹' E.1 := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨z, rfl⟩
      rw [Set.mem_preimage, happ z, ← hrange]
      exact Set.mem_range_self z
    · intro x hx
      obtain ⟨z, hz⟩ : (finiteSupportOpen B f V E).ι.base x ∈ Set.range i₀.base := by
        rwa [hrange]
      exact ⟨z, (finiteSupportOpen B f V E).ι.isOpenEmbedding.injective ((happ z).trans hz)⟩
  have hcompimm : IsImmersion (i ≫ (finiteSupportOpen B f V E).ι) := by rwa [hfac]
  have himm : IsImmersion i := IsImmersion.of_comp i (finiteSupportOpen B f V E).ι
  have hclosed : IsClosed (Set.range i.base) := by
    rw [hrange']
    exact isClosed_supportOpen_preimage B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)
  refine ⟨Z, i, IsClosedImmersion.of_isPreimmersion i hclosed, ?_, hrange'⟩
  rwa [finiteSupportChartProj, ← Category.assoc, hfac]

/-- The projection of the chart of a finite support is locally of finite type, being an open
immersion followed by a base change of `f`. -/
public instance locallyOfFiniteType_finiteSupportChartProj
    [LocallyOfFiniteType (B.inclusion.map f)] :
    LocallyOfFiniteType (finiteSupportChartProj B f V E) :=
  inferInstanceAs
    (LocallyOfFiniteType ((finiteSupportOpen B f V E).ι ≫ baseChangeChartProj B f V))

/-- The projection of the chart of a finite support is locally quasi-finite, being an open
immersion followed by a base change of `f`. -/
public instance locallyQuasiFinite_finiteSupportChartProj
    [LocallyQuasiFinite (B.inclusion.map f)] :
    LocallyQuasiFinite (finiteSupportChartProj B f V E) :=
  inferInstanceAs
    (LocallyQuasiFinite ((finiteSupportOpen B f V E).ι ≫ baseChangeChartProj B f V))

/-- **The fibre integral over the chart of a finite support is locally constant.** For a
locally constant `s` on the canonical open of `E` supported in `E`, the fibre integral of `s`
against a weighting `w` of `f` is locally constant on `V`. -/
public theorem isLocallyConstant_fibreIntegral_finiteSupportChart
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)
    {s : (finiteSupportOpen B f V E).toScheme → ℤ} (hs : IsLocallyConstant s)
    (hsupp : ∀ x, s x ≠ 0 → x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1) :
    IsLocallyConstant (fibreIntegral (finiteSupportChartToSource B f V E)
      (finiteSupportChartProj B f V E) w hs) := by
  obtain ⟨Z, i, hi, hZ, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_finiteSupportChart B f V E
  exact isLocallyConstant_fibreIntegral hw (finiteSupportChart_comm B f V E)
    (etale_finiteSupportChartTarget B V) (isOpenImmersion_finiteSupportChartLift B f V E)
    hs i hZ fun x hx => hrange.ge (hsupp x hx)

/-- **The fibre integral over the chart of a finite support is additive in the section.** -/
public theorem fibreIntegral_add_finiteSupportChart
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (w : X.obj → ℤ) {s₁ s₂ : (finiteSupportOpen B f V E).toScheme → ℤ}
    (hs₁ : IsLocallyConstant s₁) (hs₂ : IsLocallyConstant s₂)
    (hs : IsLocallyConstant fun x => s₁ x + s₂ x)
    (hsupp₁ : ∀ x, s₁ x ≠ 0 → x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1)
    (hsupp₂ : ∀ x, s₂ x ≠ 0 → x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1) :
    fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w hs =
      fun v => fibreIntegral (finiteSupportChartToSource B f V E)
          (finiteSupportChartProj B f V E) w hs₁ v +
        fibreIntegral (finiteSupportChartToSource B f V E)
          (finiteSupportChartProj B f V E) w hs₂ v := by
  obtain ⟨Z, i, hi, hZ, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_finiteSupportChart B f V E
  exact fibreIntegral_add hs₁ hs₂ hs i hZ (fun x hx => hrange.ge (hsupp₁ x hx))
    fun x hx => hrange.ge (hsupp₂ x hx)

/-- **The fibre integral over the chart of a finite support is the weighted fibre sum of
`s · w`.** In particular it does not depend on the subscheme structure chosen to witness that
`E` is finite over `V`. -/
public theorem fibreIntegral_eq_separableDegreeWeightedFiberSum_finiteSupportChart
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (w : X.obj → ℤ) {s : (finiteSupportOpen B f V E).toScheme → ℤ}
    (hs : IsLocallyConstant s)
    (hsupp : ∀ x, s x ≠ 0 → x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1) :
    fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w hs =
      separableDegreeWeightedFiberSum (finiteSupportChartProj B f V E)
        fun x => s x * w (finiteSupportChartToSource B f V E x) := by
  obtain ⟨Z, i, hi, hZ, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_finiteSupportChart B f V E
  exact fibreIntegral_eq_separableDegreeWeightedFiberSum hs i hZ
    fun x hx => hrange.ge (hsupp x hx)

end Chart

end AlgebraicGeometry.SmallEtale

end
