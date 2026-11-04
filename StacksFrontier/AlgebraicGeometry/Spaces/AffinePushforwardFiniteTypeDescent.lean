module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDerivationExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Finite type descends along an affine direct image

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces and `𝒩` a quasi-coherent `𝒪_Y`-module.
Over an affine étale chart `V` of `X` the sections of `f_*𝒩` are the sections of `𝒩` over the
affine chart `V ×_X Y` of `Y`, the identification being semilinear over the pullback of regular
functions `𝒪_X(V) ⟶ 𝒪_Y(V ×_X Y)`.  So a finite generating family of `(f_*𝒩)(V)` over `𝒪_X(V)`
generates `𝒩(V ×_X Y)` over `𝒪_Y(V ×_X Y)`, and the charts `V ×_X Y` cover `Y`.  Hence `𝒩` is of
finite type as soon as `f_*𝒩` has finite sections over the affine charts of `X`, and on a locally
Noetherian `Y` it is coherent as soon as `f_*𝒩` is.

The application is to the right adjoint `π^!` of the direct image along a finite morphism `π`:
`π_*(π^!ℱ) ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` is coherent for a coherent `ℱ` on a locally Noetherian `X`
(Stacks 07UE), so `π^!ℱ` is coherent.  This is the coherence of the module
`π^*ℱ ⊗ ω_{Y/X}` used in the proof of [Stacks, Tag 0GUZ].

## Main results

* `AlgebraicGeometry.Space.moduleFinite_sections_of_surjective_modulePushforwardCounitApp`.
* `AlgebraicGeometry.Space.isFiniteType_of_isAffineHom_of_moduleFinite_modulePushforward`.
* `AlgebraicGeometry.Space.isCoherent_of_isAffineHom_of_isCoherent_modulePushforward`.
* `AlgebraicGeometry.Space.isCoherent_affinePushforwardRightAdjoint_obj`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Finite generation of sections passes along a surjective map of sections into a direct
image**: if the canonical map `(f_*𝒩)(V) ⟶ 𝒩(U)` of a chart diagram `U ⟶ V` over `f` is
surjective and `(f_*𝒩)(V)` is finite over `𝒪_X(V)`, then `𝒩(U)` is finite over `𝒪_Y(U)`.  The
map is semilinear over the pullback of regular functions, so the image of a generating family
generates. -/
theorem moduleFinite_sections_of_surjective_modulePushforwardCounitApp (f : Y ⟶ X)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hsurj : Function.Surjective (modulePushforwardCounitApp B S hS f N d))
    (hfin : Module.Finite (chartRing B S hS X.1 X.2 d.V)
      (((modulePushforward B S hS f).obj N).val.obj (op d.V))) :
    Module.Finite (chartRing B S hS Y.1 Y.2 d.U) (N.val.obj (op d.U)) := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (modulePushforwardCounitApp B S hS f N d), top_unique ?_⟩⟩
  rintro y -
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : x ∈ Submodule.span (chartRing B S hS X.1 X.2 d.V) (s : Set _) := by
    rw [hs]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => modulePushforwardCounitApp B S hS f N d x ∈
      Submodule.span (chartRing B S hS Y.1 Y.2 d.U)
        ((s.image (modulePushforwardCounitApp B S hS f N d) : Finset _) : Set _)) ?_ ?_ ?_ ?_ hx
  · intro z hz
    exact Submodule.subset_span (by simpa using ⟨z, hz, rfl⟩)
  · rw [modulePushforwardCounitApp_zero f N d]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [modulePushforwardCounitApp_add]
    exact Submodule.add_mem _ ha hb
  · intro r a _ ha
    rw [modulePushforwardCounitApp_smul]
    exact Submodule.smul_mem _ _ ha

/-- **A quasi-coherent module whose direct image along an affine morphism has finite sections over
the affine charts is of finite type.**

Over each affine chart `V` of `X`,
`AlgebraicGeometry.Space.exists_affine_chart_bijective_modulePushforwardCounitApp`
supplies an affine chart `W` of `Y` above `V` (the chart `V ×_X Y`) on which the sections of `𝒩`
are those of `f_*𝒩`, so they are finite by
`AlgebraicGeometry.Space.moduleFinite_sections_of_surjective_modulePushforwardCounitApp`.  These
charts cover `Y`: every chart of `Y` carrying an affine chart diagram over `f` maps to one of
them, and such charts cover (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`). -/
theorem isFiniteType_of_isAffineHom_of_moduleFinite_modulePushforward (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (hNcart : IsCartesianOnAffineCharts N)
    (hfin : ∀ V : SmallEtale B S hS X.1, IsAffine (chartScheme V) →
      Module.Finite (chartRing B S hS X.1 X.2 V)
        (((modulePushforward B S hS f).obj N).val.obj (op V))) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS Y.1 Y.2).J N.val := by
  choose W b hb hWa hbij hmax using
    fun V : {V : SmallEtale B S hS X.1 // IsAffine (chartScheme V)} =>
      exists_affine_chart_bijective_modulePushforwardCounitApp f hf V.1 V.2
  refine isFiniteType_of_coversTop_affine_moduleFinite B S hS Y.1 Y.2 N hNcart W hWa ?_
    fun V => moduleFinite_sections_of_surjective_modulePushforwardCounitApp B S hS f N
      ⟨W V, V.1, b V, hb V⟩ (hbij V N).2 (hfin V.1 V.2)
  intro U
  refine mem_topology_of_hasAffineChartDiagram B S hS f U _ fun W' a hW' => ?_
  let d := hW'.chartDiagram B S hS f
  exact ⟨⟨d.V, hW'.isAffine_V B S hS f⟩, hmax ⟨d.V, hW'.isAffine_V B S hS f⟩ d.U d.g d.comm⟩

/-- **A quasi-coherent module on a locally Noetherian algebraic space whose direct image along an
affine morphism is coherent is coherent.**  The direct image has finite sections over the affine
charts (`AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent`), so the module is of
finite type by
`AlgebraicGeometry.Space.isFiniteType_of_isAffineHom_of_moduleFinite_modulePushforward`, and
quasi-coherent plus finite type is coherent on a locally Noetherian space (Stacks 07UB). -/
theorem isCoherent_of_isAffineHom_of_isCoherent_modulePushforward (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (h : IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS f).obj N)) :
    IsCoherent B S hS Y.1 Y.2 N := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hY⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS Y.1 Y.2 N).2
    ⟨hN, isFiniteType_of_isAffineHom_of_moduleFinite_modulePushforward B S hS f hf N
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 N hN)
      fun V hV => moduleFinite_sections_of_isCoherent B S hS X.1 X.2 _ h hV⟩

/-- **`π^!ℱ` is coherent** for a finite morphism `π : Y ⟶ X` of locally Noetherian algebraic
spaces and a coherent `𝒪_X`-module `ℱ`.

`π_*𝒪_Y` is coherent by Stacks 07UH, hence of finite presentation, so `π^!ℱ` is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_affinePushforwardRightAdjoint_obj`) and
`π_*(π^!ℱ) ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` is coherent by Stacks 07UE; coherence then descends along the
affine morphism `π` by
`AlgebraicGeometry.Space.isCoherent_of_isAffineHom_of_isCoherent_modulePushforward`. -/
theorem isCoherent_affinePushforwardRightAdjoint_obj (π : Y ⟶ X) (hπ : IsFinite B S hS π.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    IsCoherent B S hS Y.1 Y.2 ((affinePushforwardRightAdjoint B S hS π).obj F) := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hY⟩
  have hA : IsCoherent B S hS X.1 X.2 (pushforwardStructureModule B S hS π) :=
    isCoherent_modulePushforward_of_isFinite' B S hS π hπ hX _
      (isCoherent_structureSheaf B S hS Y.1 Y.2)
  have hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite _ hA.toIsCoherentOnSite
  have hH : IsCoherent B S hS X.1 X.2
      (smallEtaleInternalHomSmall B S hS X.1 X.2 (pushforwardStructureModule B S hS π) F) :=
    isCoherent_smallEtaleInternalHomSmall B S hS X.1 X.2 _ _
  exact isCoherent_of_isAffineHom_of_isCoherent_modulePushforward B S hS π hπ.isAffineHom hY _
    (isQuasicoherentOnSite_affinePushforwardRightAdjoint_obj B S hS π hπ.isAffineHom hfp F
      hF.toIsQuasicoherentOnSite)
    ((isCoherent.{u, u} B S hS X.1 X.2).prop_of_iso
      (modulePushforward_affinePushforwardRightAdjointIso B S hS π hπ.isAffineHom hfp F
        hF.toIsQuasicoherentOnSite).symm hH)

end AlgebraicGeometry.Space

end
