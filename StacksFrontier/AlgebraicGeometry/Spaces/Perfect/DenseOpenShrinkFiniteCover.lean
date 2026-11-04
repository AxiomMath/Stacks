module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverEtaleOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpenLocallyFinite

/-!
# Shrinking a dense open under a finite scheme cover

Let `X` be a quasi-separated algebraic space over a scheme `S` whose point space has finitely
many irreducible components, let `f : h_T ⟶ X` be the finite and finitely presented cover of
Stacks 0GUN — finite étale over a quasi-compact dense open `U₀ ⊆ X` — and let `V ⊆ h_T` be the
dense open subspace produced by Stacks 0GTT.  **Then `U₀` can be shrunk to a quasi-compact open
subspace `U ⊆ U₀`, still with dense point set, whose inverse image along `f` is contained in
`V`.**

## Main results

* `AlgebraicGeometry.Space.genericPoints_subset_range_pointsMap_ι_of_dense`: the point set of an
  open subspace with dense point set contains every generic point of an irreducible component of
  the ambient point space, when there are finitely many such components.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_`
  `isIntegralHom`: the shrinking, for an integral morphism which is étale over the dense open
  being shrunk; the morphism is still étale over the shrunken open.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_`
  `isFiniteSchemeCover`: the same for a cover satisfying
  `AlgebraicGeometry.Space.IsFiniteSchemeCoverFiniteEtaleOverDenseOpen`.

## References

* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04Y9](https://stacks.math.columbia.edu/tag/04Y9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The point set of a dense open subspace contains every generic point**, provided the
ambient point space has finitely many irreducible components. -/
theorem genericPoints_subset_range_pointsMap_ι_of_dense
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) (hG : IsOpenSubspace B S hS G)
    (hfin : (irreducibleComponents (points B S hS F)).Finite)
    (hdense : Dense (Set.range (pointsMap B S hS G.toFunctor G.ι))) :
    genericPoints (points B S hS F) ⊆ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  have _ : Finite (irreducibleComponents (points B S hS F)) := hfin.to_subtype
  exact fun _ hx => TopologicalSpace.mem_of_mem_genericPoints_of_dense_of_locallyFinite
    (locallyFinite_of_finite _)
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2) hdense hx

/-- The open subspace cut out by a set of points lies in an open subspace whose point set
contains that set. -/
private theorem openSubspaceOfPoints_le_of_subset_range {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {H : Subfunctor F} (hH : IsOpenSubspace B S hS H) {W : Set (points B S hS F)}
    (hW : W ⊆ Set.range (pointsMap B S hS H.toFunctor H.ι)) :
    openSubspaceOfPoints B S hS F W ≤ H :=
  le_of_range_pointsMap_ι_subset B S hS hH (by rwa [range_pointsMap_ι_openSubspaceOfPoints])

/-- **Shrinking a dense open subspace under an integral morphism.**  Let `f : Y ⟶ X` be an integral
morphism of algebraic spaces over `S` with `X` quasi-separated, let `U₀ ⊆ X` be an open subspace
with dense point set over which `f` is étale, and let `V ⊆ Y` be an open subspace with dense
point set.  If the point spaces of `X` and of `Y` both have finitely many irreducible
components, then `U₀` contains a quasi-compact open subspace `U`, again with dense point set,
whose inverse image along `f` is contained in `V` and over which `f` is still étale. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_isIntegralHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hXcomp : (irreducibleComponents (points B S hS X)).Finite)
    (hYcomp : (irreducibleComponents (points B S hS Y)).Finite)
    (f : Y ⟶ X) (hf : IsIntegralHom B S hS f)
    (U₀ : Subfunctor X) (hU₀ : IsOpenSubspace B S hS U₀)
    (hU₀dense : Dense (Set.range (pointsMap B S hS U₀.toFunctor U₀.ι)))
    (hfet : IsEtale B S hS (pullback.fst U₀.ι f))
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι))) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧
      Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
      U ≤ U₀ ∧ U.preimage f ≤ V ∧ IsEtale B S hS (pullback.fst U.ι f) := by
  have hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY hXqs
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIntegralHom B S hS f hY hX hf))
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have _ : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have _ : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hXdec
  obtain ⟨hW₀open, hW₀gen, hW₀mem⟩ := exists_isOpen_genericPoints_subset_of_isIntegralHom
    B S hS B.contains_terminal hX hY hXqs hYqs f hf
    (Set.range (pointsMap B S hS U₀.toFunctor U₀.ι))
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS U₀.ι hU₀.2)
    (genericPoints_subset_range_pointsMap_ι_of_dense B S hS U₀ hU₀ hXcomp hU₀dense)
    (fun y hy => isEtaleAt_of_isEtale_pullback_fst B S hS hX hY U₀ hU₀ f hfet y hy)
    (Set.range (pointsMap B S hS V.toFunctor V.ι))
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2)
    (genericPoints_subset_range_pointsMap_ι_of_dense B S hS V hV hYcomp hVdense)
  set W₀ := Set.range (pointsMap B S hS U₀.toFunctor U₀.ι) ∩
    (pointsMap B S hS Y f '' (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ)ᶜ with hW₀def
  have hnbhd : ∀ η ∈ genericPoints (points B S hS X), ∃ K : Set (points B S hS X),
      IsOpen K ∧ IsCompact K ∧ η ∈ K ∧ K ⊆ W₀ := by
    intro η hη
    obtain ⟨K, ⟨hKopen, hKcompact, hηK⟩, hKsub⟩ :=
      (hasBasis_nhds_isOpen_isCompact B S hS X hX η).mem_iff.1 (hW₀open.mem_nhds (hW₀gen hη))
    exact ⟨K, hKopen, hKcompact, hηK, hKsub⟩
  choose! K hKopen hKcompact hKmem hKsub using hnbhd
  have hWsub : (⋃ η ∈ genericPoints (points B S hS X), K η) ⊆ W₀ := Set.iUnion₂_subset hKsub
  have hWdense : Dense (⋃ η ∈ genericPoints (points B S hS X), K η) := by
    refine dense_iff_closure_eq.2 (Set.univ_subset_iff.1 ?_)
    calc (Set.univ : Set (points B S hS X))
        = closure (genericPoints (points B S hS X)) :=
          (genericPoints.closure (α := points B S hS X)).symm
      _ ⊆ closure (⋃ η ∈ genericPoints (points B S hS X), K η) :=
          closure_mono fun η hη => Set.mem_biUnion hη (hKmem η hη)
  have hU : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS X (⋃ η ∈ genericPoints (points B S hS X), K η)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ (isOpen_biUnion hKopen)
  refine ⟨openSubspaceOfPoints B S hS X (⋃ η ∈ genericPoints (points B S hS X), K η), hU, ?_,
    ?_, ?_, ?_, ?_⟩
  · refine isQuasiCompactSpace_of_isCompact_range B S hS hX hU ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact (genericPoints.finite hXcomp).isCompact_biUnion hKcompact
  · rwa [range_pointsMap_ι_openSubspaceOfPoints]
  · exact openSubspaceOfPoints_le_of_subset_range B S hS hU₀ fun _ hx => (hWsub hx).1
  · rw [preimage_openSubspaceOfPoints']
    exact openSubspaceOfPoints_le_of_subset_range B S hS hV fun y hy => (hW₀mem y (hWsub hy)).1
  · refine isEtale_pullback_fst_of_forall_isEtaleAt B S hS hX hY _ hU f fun y hy => ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints] at hy
    exact (hW₀mem y (hWsub hy)).2

/-- **Shrinking a dense open subspace under a finite scheme cover.**  Let `X` be a
quasi-separated algebraic space over `S` whose point space has finitely many irreducible
components, let `f : h_T ⟶ X` together with `U₀ ⊆ X` be a cover as in clause (1) of Stacks 0GUN —
surjective, finite and of finite presentation, finite étale over the quasi-compact open `U₀` with
dense point set — and suppose the point space of `h_T` also has finitely many irreducible
components.  Then every open subspace `V ⊆ h_T` with dense point set receives the inverse image
of a quasi-compact open subspace `U ⊆ U₀` of `X` with dense point set, over which `f` is again
étale. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_isFiniteSchemeCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hXcomp : (irreducibleComponents (points B S hS X)).Finite)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (U₀ : Subfunctor X)
    (hcover : IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS T f U₀)
    (hTcomp : (irreducibleComponents (points B S hS (yoneda.obj T))).Finite)
    (V : Subfunctor (yoneda.obj T)) (hV : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι))) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧
      Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
      U ≤ U₀ ∧ U.preimage f ≤ V ∧ IsEtale B S hS (pullback.fst U.ι f) :=
  exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_isIntegralHom B S hS hX
    (isAlgebraicSpace_yoneda B S hS T) hXqs hXcomp hTcomp f
    (IsFinite.isIntegralHom B S hS hcover.2.1) U₀ hcover.2.2.2.1 hcover.2.2.2.2.2.1
    hcover.2.2.2.2.2.2.2 V hV hVdense

end AlgebraicGeometry.Space

end
