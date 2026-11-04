module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs

/-!
# Coherence of `F ∩ f_*G`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `F` be a
quasi-coherent `𝒪_X`-module, let `G` be an `𝒪_Y`-module and let `φ : G ⟶ f^*F` be a map of
`𝒪_Y`-modules.  **Stacks 0GPR** asserts that the fibre product `F ∩ f_*G` of
`F ⟶ f_*f^*F ⟵ f_*G` (`AlgebraicGeometry.Space.intersectionPushforward`) is a coherent
`𝒪_X`-module when `φ` is injective, `f` is quasi-compact, quasi-separated, flat and surjective,
`X` and `Y` are locally Noetherian, and `G` is coherent.  This file proves it.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_sections_of_isFiniteType_restrictToChart`: the sections
  of a quasi-coherent module over an affine étale chart form a finite module as soon as its
  restriction to that chart is of finite type.
* `AlgebraicGeometry.Space.isCoherent_of_isCoherent_modulePullback`: coherence of a
  quasi-coherent module descends along a quasi-compact, flat and surjective morphism onto a
  locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.isCoherent_intersectionPushforward`: **Stacks 0GPR**.

## Implementation notes

The source argues: coherence of `F ∩ f_*G` follows from coherence of `f^*(F ∩ f_*G)` by descent
along `f` (Stacks 060U); for `f` flat this is `f^*F ∩ f^*f_*G`; flat base change identifies
`f^*f_*G` with `p_*q^*G` for the projections `p, q : Y ×_X Y ⟶ Y`, and as `p` has a section the
intersection lies in the image of `G`.

The last two steps are replaced by the formal argument of
`AlgebraicGeometry.Space.mono_intersectionPushforwardAdj`: the morphism
`f^*(F ∩ f_*G) ⟶ G` adjoint to the projection onto `f_*G` is injective for `f` flat and `φ`
injective, so `f^*(F ∩ f_*G)` is a quasi-coherent submodule of the coherent `G`, hence coherent
on the locally Noetherian `Y` by Stacks 07UD.

Quasi-coherence of `F ∩ f_*G` is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_intersectionPushforward`, fed with
quasi-coherence of the two direct images `f_*G` and `f_*f^*F`, which is Stacks 03M9 for the
quasi-compact and quasi-separated `f`.

The descent step reads finite type on the étale scheme charts: Stacks 060U for the fpqc covering
`{f}` gives finite type of the restriction of `F ∩ f_*G` to every étale chart of `X`, which over
an affine chart is finiteness of the sections, and on a locally Noetherian algebraic space a
quasi-coherent module with finite sections over the affine charts is coherent.

The module universe is the universe `u` of the schemes, the only one at which the direct and
inverse images of `𝒪`-modules along a morphism of algebraic spaces exist.

## References

* [Stacks Project, Tag 0GPR](https://stacks.math.columbia.edu/tag/0GPR)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 060U](https://stacks.math.columbia.edu/tag/060U)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Descent of coherence along a quasi-compact flat surjection -/

/-- **The sections of a quasi-coherent module over an affine étale chart form a finite module as
soon as its restriction to that chart is of finite type.**  The restriction needs no
sheafification (`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`), its global
sections over the affine scheme of the chart are finite (Stacks 01XZ), and they are the sections
of the module over the chart, by
`AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`, linearly over the functions on the
chart. -/
theorem moduleFinite_sections_of_isFiniteType_restrictToChart (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (qcoh : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (affine : IsAffine (chartScheme A))
    (finiteType : (restrictToChart B S hS X.2 M A).IsFiniteType) :
    Module.Finite (chartRing B S hS X.1 X.2 A) (M.val.obj (Opposite.op A)) := by
  have : (chartRestrictionSheaf B S hS X M A).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS X M qcoh A
  have := finiteType
  have : (chartRestrictionSheaf B S hS X M A).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso (restrictToChartIsoChartRestrictionSheaf B S hS X M A)
  have hfin : Module.Finite Γ(chartScheme A, ⊤) Γ(chartRestrictionSheaf B S hS X M A, ⊤) :=
    moduleFinite_sections_on_affine _ ⊤ (isAffineOpen_top _)
  have h : Module.Finite Γ(chartScheme A, ⊤) (M.val.obj (Opposite.op A)) :=
    Module.Finite.equiv (chartRestrictionSheafTopEquiv B S hS X M A).symm
  exact h

/-- **Coherence descends along a quasi-compact, flat and surjective morphism onto a locally
Noetherian algebraic space.**  Let `f : Y ⟶ X` be quasi-compact, flat and surjective, let `X`
be locally Noetherian and let `M` be a quasi-coherent `𝒪_X`-module with `f^*M` coherent.  Then
`M` is coherent.

The family `{f}` is an fpqc covering, so finite type of `f^*M` on the étale charts of `Y`
descends to finite type of `M` on the étale charts of `X` by Stacks 060U; on the affine charts
this is finiteness of the sections, which on a locally Noetherian algebraic space is coherence of
a quasi-coherent module. -/
theorem isCoherent_of_isCoherent_modulePullback (f : Y ⟶ X)
    (quasiCompact : IsQuasiCompact B S hS f.hom) (flat : IsFlat B S hS f.hom)
    (surjective : IsSurjective B S hS f.hom)
    (X_noetherian : HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS X.1 X.2) (qcoh : M.IsQuasicoherentOnSite)
    (coherent : IsCoherent B S hS Y.1 Y.2 ((modulePullback B S hS f).obj M)) :
    IsCoherent B S hS X.1 X.2 M := by
  have hcov : IsFpqcCovering B S hS (fun _ : Unit ↦ f.hom) :=
    isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B S hS f quasiCompact flat
      surjective
  have hpb : ((modulePullback B S hS f).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f M qcoh
  have : SheafOfModules.IsCoherentOnSite ((modulePullback B S hS f).obj M) :=
    coherent.toIsCoherentOnSite
  have hft := isFiniteType_of_pullback_fpqc B S hS (fun _ : Unit ↦ Y) (fun _ ↦ f) M qcoh hcov
    fun _ W ↦ isFiniteType_restrictToChart B S hS Y _ hpb
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS Y _) W
  exact isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS X.1 X.2
    X_noetherian M qcoh fun A hA ↦
      moduleFinite_sections_of_isFiniteType_restrictToChart B S hS X M qcoh A hA (hft A)

/-! ### Stacks 0GPR -/

/-- **Stacks 0GPR.**  Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let
`F` be a quasi-coherent `𝒪_X`-module, let `G` be an `𝒪_Y`-module and let `φ : G ⟶ f^*F` be a map
of `𝒪_Y`-modules.  Assume that `φ` is injective, that `f` is quasi-compact, quasi-separated,
flat and surjective, that `X` and `Y` are locally Noetherian, and that `G` is coherent.  Then
`F ∩ f_*G`, the fibre product of `F ⟶ f_*f^*F ⟵ f_*G`, is a coherent `𝒪_X`-module.

The two direct images `f_*G` and `f_*f^*F` are quasi-coherent by Stacks 03M9, so `F ∩ f_*G` is
quasi-coherent.  Its inverse image `f^*(F ∩ f_*G)` is a quasi-coherent submodule of `G`, by
`AlgebraicGeometry.Space.mono_intersectionPushforwardAdj`, hence coherent by Stacks 07UD, and
coherence descends along `f` by
`AlgebraicGeometry.Space.isCoherent_of_isCoherent_modulePullback`. -/
@[stacks 0GPR]
theorem isCoherent_intersectionPushforward (f : Y ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (φ : G ⟶ (modulePullback B S hS f).obj F) (mono : Mono φ)
    (quasiCompact : IsQuasiCompact B S hS f.hom)
    (quasiSeparated : IsQuasiSeparated B S hS f.hom)
    (flat : IsFlat B S hS f.hom) (surjective : IsSurjective B S hS f.hom)
    (X_noetherian : HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (Y_noetherian : HasEtaleLocalProperty B S hS Y.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (F_qcoh : F.IsQuasicoherentOnSite) (G_coherent : IsCoherent B S hS Y.1 Y.2 G) :
    IsCoherent B S hS X.1 X.2 (intersectionPushforward B S hS f φ) := by
  have qcoh : (intersectionPushforward B S hS f φ).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_intersectionPushforward B S hS f φ F_qcoh
      (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f quasiCompact quasiSeparated G
        G_coherent.toIsQuasicoherentOnSite)
      (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f quasiCompact quasiSeparated _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f F F_qcoh))
  have : Fact (HasEtaleLocalProperty B S hS Y.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨Y_noetherian⟩
  have := mono_intersectionPushforwardAdj B S hS f φ mono flat
  exact isCoherent_of_isCoherent_modulePullback B S hS f quasiCompact flat surjective
    X_noetherian _ qcoh
    (isCoherent_of_mono_of_isQuasicoherentOnSite B S hS Y.1 Y.2
      (intersectionPushforwardAdj B S hS f φ)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f _ qcoh) G_coherent)

end AlgebraicGeometry.Space

end
