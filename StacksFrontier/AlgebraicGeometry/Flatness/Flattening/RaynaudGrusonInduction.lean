module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.PushforwardOnOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.IteratedCentreFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.RaynaudGrusonInductionStep
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# The Raynaud–Gruson induction

This file runs the induction of [Stacks, Tag 0815] on

  `d = max_{s ∈ S} dim Supp(ℱ_s)`,

and so proves the flatness assertion of that theorem for a module, from the conclusion of
[Stacks, Tag 0811] and nothing else. That conclusion is supplied, in the form the induction
consumes it, by `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/GenericFibreFreeBlowup0811.lean`, so the
flatness assertion holds with nothing granted.

The induction is on the predicate
`AlgebraicGeometry.ModuleFlatteningCentreBelow`, the flatness assertion for every datum whose
fibre supports have dimension below a given bound. The step is:

* **The base case.** If the bound is `0` then every fibre support is empty, so `ℱ` has empty
  support and is flat over the base
  (`AlgebraicGeometry.isFlatOver_of_topologicalKrullDim_supp_fiber_lt_zero`); the empty centre
  works.
* **Already flat.** More generally, whenever `ℱ` happens to be flat over all of `S` the empty
  centre works, by `AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver`.
* **The step.** Otherwise a flattening neighbourhood is produced at every point of `X`, and
  `exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_flatteningNeighborhoods`, the
  finiteness reduction over [Stacks, Tag 0814], assembles them into one centre on `S`. Off the
  support of `ℱ` no blowup is needed. At a point of the support, the elementary dévissage of
  [Stacks, Tag 057S] (`AlgebraicGeometry.exists_elementaryDevissage`) replaces the datum, étale
  locally, by a module on a *smooth affine* morphism `h : Y ⟶ V` with geometrically integral
  fibres of dimension `D.n`, and
  `AlgebraicGeometry.nonempty_flatteningNeighborhood_of_elementaryDevissage` reduces the
  flattening of `ℱ` near `x` to the flattening of that module. There [Stacks, Tag 0811] makes
  the strict transform finite locally free on an open surjecting onto the base, and
  `AlgebraicGeometry.hasFlatteningCentre_of_fiberFree` finishes with the inductive hypothesis at
  `D.n`, which is below the bound by `AlgebraicGeometry.ElementaryDevissage.dimension_lt`. The
  two centres — the one from [Stacks, Tag 0811] and the one from the inductive hypothesis —
  amalgamate into one by
  `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_successive`,
  whose [Stacks, Tag 0803] hypothesis is discharged by
  `AlgebraicGeometry.secondCentreFactorization`.

## Main definitions

* `AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup` is the conclusion of
  [Stacks, Tag 0811] in the form the induction consumes it.

## Main results

* `AlgebraicGeometry.moduleFlatteningCentreBelow`: every bound is reached — the induction.
* `AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup`: **the flatness assertion of
  [Stacks, Tag 0815] for a module**, from the conclusion of [Stacks, Tag 0811] in the form above.
  `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` supplies that form from the
  proved tag, so no hypothesis survives.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The conclusion of [Stacks, Tag 0811], in the form the induction of [Stacks, Tag 0815]
consumes it.** For a quasi-compact and quasi-separated base, an affine morphism of finite
presentation with geometrically integral fibres and a quasi-coherent module of finite type which
is of finite presentation and flat over a quasi-compact open `W` of the base, there is a centre
on the base, finitely presented and supported away from `W`, and an open of the base change on
which the strict transform of the module is finite locally free and which surjects onto the
blowup.

This is verbatim the conclusion of
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_free_surjective`, minus its
`Stacks.Blowup.IsAdmissibleBlowup` conjunct, which the two conditions on the centre already
imply. It is also the conclusion of [Stacks, Tag 0811] itself, which
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` proves under
exactly the source's hypotheses, and
`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` derives this statement from that
one with nothing granted.

The quasi-compactness and quasi-separatedness of the base are the hypotheses of
[Stacks, Tag 0811] itself. They cost the induction nothing: the only place the induction applies
this statement is `AlgebraicGeometry.hasFlatteningCentre_of_smoothChart`, whose base is affine
and therefore both. -/
def FinitePresentationHasGenericFibreFreeBlowup : Prop :=
  ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [IsAffineHom f]
    [Flat f] [GeometricallyIntegral f],
    AlgebraicGeometry.FinitePresentation f → ∀ (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (W : S.Opens), IsCompact (W : Set S) →
    ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj F).IsFinitePresentation →
    IsFlatOver (f ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj F) →
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (W : Set S) (I.support : Set S) ∧
      ∃ V : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens,
        (∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I), z ∈ V →
          ∃ (W : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens) (n : ℕ),
            z ∈ W ∧ W ≤ V ∧
            Nonempty ((Stacks.StrictTransform.sheaf f (blowUpToBase I)
              (exceptionalIdeal I) F).over W ≅
                SheafOfModules.free.{u} (ULift.{u} (Fin n)))) ∧
        Function.Surjective (V.ι ≫ pullback.snd f (blowUpToBase I)).base

/-- **The flattening input of the induction**, quantified over the data the induction of
[Stacks, Tag 0815] applies it to: for an affine, flat morphism of finite presentation with
geometrically integral fibres and a quasi-coherent module of finite type which is of finite
presentation and flat over a quasi-compact open `W` of the base, a centre on the base, finitely
presented and supported away from `W`, after whose blowup the strict transform is of finite
presentation and flat at the generic point of every fibre.

This is `AlgebraicGeometry.GenericFibreFlatteningBlowup`. It is more than
[Stacks, Tag 0811] concludes — that tag is proved outright, as
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibres0811.lean`, from the
reductions of Remark 38.30.1 ([Stacks, Tag 080Y]) and the affine engine [Stacks, Tag 0810] —
because it asks for global finite presentation of the strict transform and for flatness at
*every* generic point of a fibre of the blown-up projection, where that tag gives freeness on an
open surjecting onto the blowup. -/
def FinitePresentationHasGenericFibreFlatteningBlowup : Prop :=
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [Flat f] [GeometricallyIntegral f],
    AlgebraicGeometry.FinitePresentation f → ∀ (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (W : S.Opens), IsCompact (W : Set S) →
    ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj F).IsFinitePresentation →
    IsFlatOver (f ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj F) →
    GenericFibreFlatteningBlowup f F W

/-- **The conclusion of [Stacks, Tag 0811] from the flattening input.** This is
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_free_surjective`, quantified over the data
the induction of [Stacks, Tag 0815] applies it to; its `Stacks.Blowup.IsAdmissibleBlowup`
conjunct is dropped, being implied by the two conditions on the centre. -/
theorem finitePresentationHasGenericFibreFreeBlowup_of_genericFibreFlatteningBlowup
    (H : FinitePresentationHasGenericFibreFlatteningBlowup.{u}) :
    FinitePresentationHasGenericFibreFreeBlowup.{u} := by
  intro S X _ _ f _ _ _ hf F _ _ W hWc hfp hflat
  obtain ⟨I, hIfp, hIdisj, -, V, hVfree, hVsurj⟩ :=
    exists_isAdmissibleBlowup_opens_free_surjective f F W (H f hf F W hWc hfp hflat)
  exact ⟨I, hIfp, hIdisj, V, hVfree, hVsurj⟩

/-- **The flattening centre on the base of a smooth chart.** Let `h : Y ⟶ V` be an affine
morphism of affine schemes, smooth of relative dimension `n` with geometrically integral fibres,
and let `M` be a quasi-coherent module of finite type on `Y` which is of finite presentation and
flat over a quasi-compact open `W ⊆ V`. Granted [Stacks, Tag 0811] and the flattening theorem in
fibre-support dimension `< n`, `M` has a flattening centre avoiding `W`.

[Stacks, Tag 0811] supplies a centre `I` after which the strict transform is finite locally free
on an open surjecting onto the blowup; `AlgebraicGeometry.hasFlatteningCentre_of_fiberFree` then
flattens that strict transform, and the two centres amalgamate by
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_successive`. -/
theorem hasFlatteningCentre_of_smoothChart (H : FinitePresentationHasGenericFibreFreeBlowup.{u})
    {Y V : Scheme.{u}} [IsAffine V] [IsAffine Y] (h : Y ⟶ V) [IsAffineHom h]
    [LocallyOfFinitePresentation h] (n : ℕ) [SmoothOfRelativeDimension n h]
    [GeometricallyIntegral h] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (W : V.Opens) (hWc : IsCompact (W : Set V))
    (hMfp : ((Scheme.Modules.pullback (h ⁻¹ᵁ W).ι).obj M).IsFinitePresentation)
    (hMflat : IsFlatOver (h ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (h ⁻¹ᵁ W).ι).obj M))
    (ih : ModuleFlatteningCentreBelow.{u} n) :
    HasFlatteningCentre h M W := by
  have _ : Smooth h := SmoothOfRelativeDimension.smooth n h
  have _ : Flat h := inferInstance
  obtain ⟨I, hIfp, hIdisj, O, hOfree, hOsurj⟩ :=
    H h ⟨inferInstance, inferInstance, inferInstance⟩ M W hWc hMfp hMflat
  have _ : IsProper (blowUpToBase I) :=
    isProper_blowUpToBase_of_fg I ((finitePresentation_subschemeι_iff_isFiniteType I).mp hIfp)
  have _ : CompactSpace (blowUp I) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I)
  have _ : QuasiSeparatedSpace (blowUp I) :=
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase I)
  have _ : CompactSpace (Stacks.StrictTransform.baseChange h (blowUpToBase I)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h (blowUpToBase I))
  have _ : (Stacks.StrictTransform.sheaf h (blowUpToBase I)
      (exceptionalIdeal I) M).IsQuasicoherent := inferInstance
  have _ : (Stacks.StrictTransform.sheaf h (blowUpToBase I)
      (exceptionalIdeal I) M).IsFiniteType := isFiniteType_strictTransformSheaf h I M
  have _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hsq : IsPullback (pullback.fst h (blowUpToBase I)) (pullback.snd h (blowUpToBase I))
      h (blowUpToBase I) := IsPullback.of_hasPullback h (blowUpToBase I)
  have _ : SmoothOfRelativeDimension n (pullback.snd h (blowUpToBase I)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have _ : GeometricallyIntegral (pullback.snd h (blowUpToBase I)) := inferInstance
  have _ : IsAffineHom (pullback.snd h (blowUpToBase I)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have _ : LocallyOfFinitePresentation (pullback.snd h (blowUpToBase I)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  obtain ⟨J, hJfp, hJdisj, hJflat⟩ :=
    hasFlatteningCentre_of_fiberFree (pullback.snd h (blowUpToBase I)) n
      (Stacks.StrictTransform.sheaf h (blowUpToBase I) (exceptionalIdeal I) M)
      (blowUpToBase I ⁻¹ᵁ W) ((blowUpToBase I).isCompact_preimage hWc)
      (isFinitePresentation_strictTransformSheaf_on_admissible_open h I M W hIdisj hMfp)
      (isFlatOver_strictTransformSheaf_on_admissible_open h I M inferInstance W hIdisj hMflat)
      O hOfree hOsurj ih
  obtain ⟨K, hKfp, hKdisj, -, hKflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_successive
      secondCentreFactorization h M W I hIfp hIdisj J hJfp hJdisj hJflat
  exact ⟨K, hKfp, hKdisj, hKflat⟩

/-- **The induction of [Stacks, Tag 0815].** From the conclusion of [Stacks, Tag 0811] in the
shape above, the flatness assertion holds for every datum whose fibre supports have dimension
below any given bound. That shape is supplied with nothing granted by
`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup`. -/
theorem moduleFlatteningCentreBelow (H : FinitePresentationHasGenericFibreFreeBlowup.{u})
    (n : ℕ) : ModuleFlatteningCentreBelow.{u} n := by
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro X S f F _ _ _ _ _ _ U hU hFfp hFflat hn
  have hloc : ∀ x : X, Nonempty (FlatteningNeighborhood f F U x) := fun x ↦ by
    by_cases hx : x ∈ SheafOfModules.supp F
    swap
    · exact nonempty_flatteningNeighborhood_of_notMem_supp f F U x hx
    have hx' : f.asFiber x ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) := by
      simpa [Stacks.Modules.supp_pullback] using hx
    obtain ⟨D⟩ := exists_elementaryDevissage f F x hx'
    refine nonempty_flatteningNeighborhood_of_elementaryDevissage f F U x hx' D ?_
    have _ := D.quasicoherent_G
    have _ := D.finiteType_G
    have _ := D.finite_π
    have _ : IsAffine D.V.scheme := D.affine_V
    have _ : IsAffine D.Y := D.affine_Y
    have _ : SmoothOfRelativeDimension D.n D.h := D.smooth
    have _ : GeometricallyIntegral D.h := by
      rw [GeometricallyIntegral.eq_geometrically,
        geometrically_iff_forall_fiberToSpecResidueField]
      exact fun s ↦ (D.integral_fibers s).geometrically_isIntegral
    have _ : Smooth D.h := SmoothOfRelativeDimension.smooth D.n D.h
    have _ : ((Scheme.Modules.pushforward D.π).obj D.G).IsFiniteType :=
      (isFiniteType_iff_pushforward_isFiniteType D.π D.G).mp D.finiteType_G
    have _ : ((Scheme.Modules.pushforward D.π).obj D.G).IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff D.π _).2
        (Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent D.π D.G
          D.quasicoherent_G)
    have hopen : D.U.toBase ⁻¹ᵁ (f ⁻¹ᵁ U) = D.toBase ⁻¹ᵁ (D.V.toBase ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, D.commutes_base]
    have hpre : ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ (D.V.toBase ⁻¹ᵁ U)).ι).obj
        ((Scheme.Modules.pullback D.U.toBase).obj F)).IsFinitePresentation := by
      rw [← hopen]
      exact Stacks.Modules.isFinitePresentation_pullback_on_preimage D.U.toBase F (f ⁻¹ᵁ U) hFfp
    have _ : ((Scheme.Modules.pullback D.U.toBase).obj F).IsQuasicoherent :=
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        D.U.toBase.toLRSHom.toShHom F
        (inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F))
    have hQflat : ∀ y : D.U.scheme, D.toBase y ∈ (D.V.toBase ⁻¹ᵁ U : D.V.scheme.Opens) →
        IsFlatOverAt D.toBase.toLRSHom.toShHom ((Scheme.Modules.pullback D.U.toBase).obj F) y := by
      intro y hy
      have hyU : f (D.U.toBase y) ∈ U := by
        simpa only [← Scheme.Hom.comp_apply, D.commutes_base] using
          (show D.V.toBase (D.toBase y) ∈ U from hy)
      exact isFlatOverAt_pullback_of_etale_square f D.toBase D.U.toBase D.V.toBase F
        D.commutes_base y (isFlatOverAt_of_open_restriction f F U (D.U.toBase y) hyU hFflat)
    obtain ⟨K, hKfp, hKdisj, hKflat⟩ :=
      hasFlatteningCentre_of_smoothChart H D.h D.n
        ((Scheme.Modules.pushforward D.π).obj D.G) (D.V.toBase ⁻¹ᵁ U)
        (D.V.toBase.isCompact_preimage hU)
        (ElementaryDevissage.pushforward_isFinitePresentation_onOpen f F x hx' D
          (D.V.toBase ⁻¹ᵁ U) hpre)
        (ElementaryDevissage.pushforward_isFlatOver_onOpen f F x hx' D (D.V.toBase ⁻¹ᵁ U)
          (isFlatOver_restrict_of_flatOnPreimage D.toBase _ (D.V.toBase ⁻¹ᵁ U) hQflat))
        (ih D.n (ElementaryDevissage.dimension_lt f F x hx' D (hn (f x))))
    exact ⟨K, ⟨hKfp, hKdisj⟩, hKflat⟩
  obtain ⟨I, hIfp, hIdisj, -, hIflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_flatteningNeighborhoods
      f F U hU hloc
  exact ⟨I, hIfp, hIdisj, hIflat⟩

/-- **The flatness assertion of [Stacks, Tag 0815] for a module**, from the conclusion of
[Stacks, Tag 0811] in the shape the induction consumes it — which
`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` supplies with nothing granted.
Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be locally of finite presentation
with `X` quasi-compact, let `ℱ` be a quasi-coherent module of finite type on `X` and let
`U ⊆ S` be a quasi-compact open over which `ℱ` is of finite presentation and flat. Then `ℱ` has
a flattening centre avoiding `U`.

The induction variable exists by
`AlgebraicGeometry.exists_topologicalKrullDim_supp_fiber_lt`, and
`AlgebraicGeometry.moduleFlatteningCentreBelow` reaches it. -/
theorem hasFlatteningCentre_of_genericFibreFreeBlowup
    (H : FinitePresentationHasGenericFibreFreeBlowup.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X]
    [LocallyOfFinitePresentation f] [F.IsQuasicoherent] [F.IsFiniteType] (U : S.Opens)
    (hU : IsCompact (U : Set S))
    (hFfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hFflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)) :
    HasFlatteningCentre f F U := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_supp_fiber_lt f F
  exact moduleFlatteningCentreBelow H n f F U hU hFfp hFflat hn

end AlgebraicGeometry

end
