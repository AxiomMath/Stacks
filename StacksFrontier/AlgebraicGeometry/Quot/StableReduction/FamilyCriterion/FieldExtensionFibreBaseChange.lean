module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SubcurveGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree

/-!
# Stable fibre conditions are invariant under extension of the ground field

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, of genus at least two, without rational tails and without rational
bridges. Then for every field extension `K/k` and every cartesian square exhibiting `V` as
`X ×_k K`, the scheme `V` over `K` again has genus at least two, no rational tail and no rational
bridge.

The genus is invariant by [Stacks, Tag 0BY9]. For the two other conditions, `ω_X` is ample
([Stacks, Tag 0E3P]), hence so is its pullback `ω_V` ([Stacks, Tag 0E32]) along the affine
projection `V ⟶ X`. A curve with ample dualizing sheaf has no rational tail, on which `ω` would
have negative degree ([Stacks, Tag 0E63]), and no rational bridge, on which `ω` would have degree
zero ([Stacks, Tag 0E64]).

## Main results

* `forall_not_isRationalBridge_of_isAmple_of_isInvertible_dualizingSheafOverField`: a nodal curve
  with ample dualizing sheaf has no rational bridge.
* `hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_specMapAlgebraMap`: the fibre conditions
  of a stable curve survive extension of the ground field.

## References

* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A nodal curve with ample dualizing sheaf has no rational bridge.** Let `X` be a proper
scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities. If `ω_X`
is ample, then on a rational bridge `C` the degree of `ω_X|_C` is positive, `C` being a curve
mapping finitely onto its image; but it is zero ([Stacks, Tag 0E64]). -/
theorem forall_not_isRationalBridge_of_isAmple_of_isInvertible_dualizingSheafOverField
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))]
    (hample : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (C : X.IdealSheafData) : ¬ IsRationalBridge k X C := by
  intro hC
  have h0 := invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge
    hdim hnodal C hC
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  have := Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k
    (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have hne : ¬ (Set.range C.subschemeι.base).Subsingleton := by
    intro hsub
    have : Subsingleton C.subscheme :=
      ⟨fun x y => C.subschemeι.isClosedEmbedding.injective (hsub ⟨x, rfl⟩ ⟨y, rfl⟩)⟩
    have := topologicalKrullDim_nonpos_of_subsingleton (α := C.subscheme)
    rw [hCdim] at this
    exact absurd this (by decide)
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range k
    (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim C.subschemeι hne _ hample
  exact hpos.ne' h0

/-- At-worst-nodal singularities of a proper curve over `k` with `H⁰(X, 𝒪_X) = k` survive any
cartesian base change along `Spec K ⟶ Spec k`. -/
theorem hasAtWorstNodalSingularities_of_isPullback_specMapAlgebraMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    {g' : V ⟶ X} {f' : V ⟶ Spec (.of K)}
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    letI : V.Over (Spec (.of K)) := ⟨f'⟩
    Stacks.Curves.HasAtWorstNodalSingularities K V := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have hW := Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X
    (equidimensional_of_isIso_globalSections_of_dimension_one k f hdim) hdim hnodal
  have hWdim : topologicalKrullDim (pullback f gK : Scheme.{u}) = 1 :=
    (topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback f gK)).trans hdim
  have : LocallyOfFiniteType (pullback.snd f gK) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f gK) inferInstance
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso (pullback.snd f gK) f' hWdim
    h.isoPullback.hom (𝟙 _) (by rw [Spec.map_id, Category.comp_id, h.isoPullback_hom_snd]) hW

/-- **The fibre conditions of a stable curve survive extension of the ground field.** Let `X` be
a proper scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities, of genus at least two, without rational tails or rational bridges, and let
`V = X ×_k K` for a field extension `K/k`, presented by any cartesian square. Then `V` over `K`
has genus at least two (Tag 0BY9), is proper, and has no rational tail and no rational bridge:
its dualizing sheaf `ω_V ≅ pr^* ω_X` (Tag 0E32) is ample, `ω_X` being ample (Tag 0E3P) and the
projection `pr : V ⟶ X` affine. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_specMapAlgebraMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hX : HasGenusTwoNoRationalTailNoRationalBridge k f)
    {g' : V ⟶ X} {f' : V ⟶ Spec (.of K)}
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    HasGenusTwoNoRationalTailNoRationalBridge K f' := by
  obtain ⟨hg, htail, hXp, hbridge⟩ := hX
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : V.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper f' := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
  have : IsProper (V ↘ Spec (.of K)) := inferInstanceAs (IsProper f')
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop) :=
    isIso_globalSections_baseChange k K g' f' f h
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (V ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop))
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
  have hVdim : topologicalKrullDim V = 1 :=
    (topologicalKrullDim_baseChange k K g' f' f h).trans hdim
  have hVnodal : Stacks.Curves.HasAtWorstNodalSingularities K V :=
    hasAtWorstNodalSingularities_of_isPullback_specMapAlgebraMap k K f hdim hnodal h
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  have : ConnectedSpace V := connectedSpace_of_isIso_globalSections K f'
  obtain ⟨hωX, hωXample⟩ := isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X
    hdim hnodal htail hbridge hg
  have hωX' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) := hωX
  have hωV : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f') :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K V hVdim hVnodal
  let : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have : IsAffineHom g' := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace f'
  have hωVample : Scheme.Modules.IsAmple V (Stacks.Duality.dualizingSheafOverField f') :=
    Scheme.Modules.isAmple_of_iso (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h)
      (Scheme.Modules.isAmple_pullback_of_isAffineHom g' _ hωXample)
  have : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (V ↘ Spec (.of K))) := hωV
  refine ⟨(genus_baseChange k K g' f' f h).symm ▸ hg, fun C => ?_, inferInstance, fun C => ?_⟩
  · exact Stacks.Curves.forall_not_isRationalTail_of_pullback_iso_of_isAmple hVdim hVnodal (𝟙 V)
      _ hωVample ((Scheme.Modules.pullbackId V).app _) C
  · exact forall_not_isRationalBridge_of_isAmple_of_isInvertible_dualizingSheafOverField K V
      hVdim hVnodal hωVample C

end AlgebraicGeometry

end
