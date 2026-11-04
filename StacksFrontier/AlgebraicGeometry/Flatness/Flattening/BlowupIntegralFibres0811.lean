module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresRankDecomposition
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankStalkBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange

/-!
# Stacks 0811: flattening a module by a blowup, with geometrically integral fibres

Let `S` be a quasi-compact and quasi-separated scheme, `f : X ⟶ S` a morphism, `F` a
quasi-coherent `𝒪_X`-module and `U ⊆ S` a quasi-compact open. Assume

1. `f` is affine, of finite presentation, flat, with geometrically integral fibres;
2. `F` is of finite type;
3. `F` restricted to `X_U` is of finite presentation;
4. `F` is flat over `S` at every generic point of a fibre over a point of `U`.

Then there is a `U`-admissible blowup `S' ⟶ S` and an open `V ⊆ X_{S'}` such that the strict
transform of `F` is finitely locally free on `V` and `V ⟶ S'` is surjective.

## Main results

* `AlgebraicGeometry.exists_freeAtPointOfRank_of_isFlatOverAt_over_open`: hypothesis (4) upgraded
  by [Stacks, Tag 080Q] — at a generic point of a fibre over `U` the module is finite locally free
  of some finite rank on a neighbourhood.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective`:
  **[Stacks, Tag 0811]**.

## Implementation notes

The proof assembles the three pieces of the source. The hypotheses are bundled as
`AlgebraicGeometry.FlatteningSituation`, whose last field is hypothesis (4) in the form
[Stacks, Tag 080Q] upgrades it to over `U`; the rank function of the source is then the rank
occurring in that field, and only finitely many values occur because `U` is quasi-compact and
each value occupies an open of `U`
(`AlgebraicGeometry.FlatteningSituation.rankBase`). The reduction to a constant rank is
`AlgebraicGeometry.FlatteningSituation.isSolvable_of_hasRankIn` ([Stacks, Tag 080P] iterated), the
reduction of the constant-rank case to an affine base with principal boundary is
`AlgebraicGeometry.FlatteningSituation.isSolvable_of_constantRank` (the Cartier-divisor and
local-global observations of [Stacks, Tag 080Y]), and that case is
`AlgebraicGeometry.FlatteningSituation.isSolvable_of_affine_of_basicOpen`
([Stacks, Tag 0810]).

Hypothesis (4) is used through [Stacks, Tag 080Q] applied to the base change of `f` over `U`,
where the module *is* of finite presentation by hypothesis (3); the fibre-wise hypothesis of that
tag is automatic at a generic point of a geometrically integral fibre, because the local ring
there is the function field of the fibre.

"Finitely locally free on `V`" is spelled out: every point of `V` has an open neighbourhood inside
`V` on which the strict transform is isomorphic to a finite free module. The rank may differ
between neighbourhoods, which is what the conclusion of the source allows.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Hypothesis (4) of [Stacks, Tag 0811] upgraded by [Stacks, Tag 080Q].** For `f` of finite
presentation with geometrically integral fibres and `F` of finite presentation over the open `U`,
flatness of `F` over `S` at a generic point of a fibre over `U` makes `F` finite locally free of
some finite rank on a neighbourhood of that point.

[Stacks, Tag 080Q] is applied to the base change of `f` over `U`, where the module is of finite
presentation; its fibre-wise hypothesis is automatic at a generic point of a geometrically
integral fibre. -/
theorem exists_freeAtPointOfRank_of_isFlatOverAt_over_open {S X : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyIntegral f] (hf : AlgebraicGeometry.FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens)
    (hFU : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (x : X) (hxU : f.base x ∈ U) (hgen : f.base ⁻¹' {f.base x} ⊆ closure {x})
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ r : ℕ, FreeAtPointOfRank F x r := by
  have := hf.locallyOfFinitePresentation
  have := hf.quasiCompact
  have := hf.quasiSeparated
  have hpb := IsPullback.of_hasPullback f U.ι
  have : GeometricallyIntegral (pullback.snd f U.ι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb ‹GeometricallyIntegral f›
  have hFPg : AlgebraicGeometry.FinitePresentation (pullback.snd f U.ι) :=
    ⟨locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback hpb
        hf.locallyOfFinitePresentation,
      quasiCompact_isStableUnderBaseChange.of_isPullback hpb hf.quasiCompact,
      quasiSeparated_isStableUnderBaseChange.of_isPullback hpb hf.quasiSeparated⟩
  have hGfp : ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F).IsFinitePresentation := by
    have hp : ((Scheme.Modules.pullback (pullbackRestrictIsoRestrict f U).hom).obj
        (F.restrict (f ⁻¹ᵁ U).ι)).IsFinitePresentation :=
      Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ _
    exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      ((Scheme.Modules.pullback (pullbackRestrictIsoRestrict f U).hom).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app F) ≪≫
        (Scheme.Modules.pullbackComp (pullbackRestrictIsoRestrict f U).hom (f ⁻¹ᵁ U).ι).app F ≪≫
        (Scheme.Modules.pullbackCongr (pullbackRestrictIsoRestrict_hom_ι f U)).app F) hp
  set z : ↑(Limits.pullback f U.ι) := (pullbackRestrictIsoRestrict f U).inv.base ⟨x, hxU⟩
  have hzx : (pullback.fst f U.ι).base z = x :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ k.base ⟨x, hxU⟩)
      (pullbackRestrictIsoRestrict_inv_fst f U)
  have hflatz : IsFlatOverAt (pullback.snd f U.ι).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F) z := by
    let G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := F
    have hG : G.IsQuasicoherent := ‹F.IsQuasicoherent›
    exact modulePullback_isFlatOverAt hpb G z (by rwa [hzx])
  have hgenz : (pullback.snd f U.ι).base ⁻¹' {(pullback.snd f U.ι).base z} ⊆ closure {z} :=
    fibre_subset_closure_pullback_of_isOpenImmersion f U.ι z (by rwa [hzx])
  obtain ⟨V, hzV, n, ⟨iso⟩⟩ :=
    Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk
      (pullback.snd f U.ι) hFPg ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F) z hflatz
      (flat_fibre_stalk_of_fibre_subset_closure (pullback.snd f U.ι) _ z hgenz)
  refine ⟨n, ?_⟩
  simpa only [hzx] using freeAtPointOfRank_of_isOpenImmersion (pullback.fst f U.ι) F z n
    (freeAtPointOfRank_of_over_iso_free _ hzV n iso)

/-- **Stacks Project, Tag 0811.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism, let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a
quasi-compact open. Assume

1. `f` is affine, of finite presentation, flat, with geometrically integral fibres;
2. `F` is of finite type;
3. `F` restricted to `X_U` is of finite presentation;
4. `F` is flat over `S` at every generic point of a fibre over a point of `U`.

Then there is a `U`-admissible blowup of `S` — given by a centre `I` of finite presentation whose
support avoids `U` — and an open subscheme `V` of `X ×_S Bl_I(S)` such that

* **(a)** the strict transform of `F` along the blowup is free of finite rank on an open
  neighbourhood, inside `V`, of every point of `V`, that is, finitely locally free on `V`, and
* **(b)** `V` surjects onto `Bl_I(S)`.

The rank at the generic point of a fibre over `U` is made constant by iterating
[Stacks, Tag 080P]; the complement of `U` is made an effective Cartier divisor and then, locally
on the base, principal on an affine open, by the observations of [Stacks, Tag 080Y]; and that case
is [Stacks, Tag 0810]. -/
@[stacks 0811 "the full statement under hypotheses (1)-(4) of the source: a U-admissible blowup \
and an open of the base change on which the strict transform is finitely locally free and which \
surjects onto the blowup"]
theorem exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S)
    [IsAffineHom f] [Flat f] [GeometricallyIntegral f]
    (hf : AlgebraicGeometry.FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : S.Opens)
    (hU : IsCompact (U : Set S))
    (hFU : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (hflat : ∀ x : X, f.base x ∈ U → f.base ⁻¹' {f.base x} ⊆ closure {x} →
      IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      ∃ V : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens,
        (∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I), z ∈ V →
          ∃ (W : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens) (n : ℕ),
            z ∈ W ∧ W ≤ V ∧
            Nonempty ((Stacks.StrictTransform.sheaf f (blowUpToBase I)
              (exceptionalIdeal I) F).restrict W.ι ≅
                SheafOfModules.free.{u} (ULift.{u} (Fin n)))) ∧
        Function.Surjective (V.ι ≫ pullback.snd f (blowUpToBase I)).base := by
  classical
  -- The data of the source, with hypothesis (4) upgraded by tag 080Q.
  set D : FlatteningSituation.{u} :=
    { S := S, X := X, f := f, finitePresentation := hf, F := F, U := U, compact_U := hU
      finitePresentation_restrict := hFU
      free_at_generic := fun x hx hgen ↦
        exists_freeAtPointOfRank_of_isFlatOverAt_over_open f hf F U hFU x hx hgen
          (hflat x hx hgen) }
  -- Only finitely many ranks occur, because `U` is quasi-compact.
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, D.HasRankIn A := by
    have hcover : (U : Set S) ⊆ ⋃ a : ℕ, (D.rankBase a : Set S) := by
      intro u hu
      obtain ⟨x, hxu, hxgen⟩ := exists_fibre_dense_preimage f u
      obtain ⟨r, hr⟩ := D.free_at_generic x (by rwa [hxu]) (by rwa [hxu])
      refine Set.mem_iUnion.mpr ⟨r, ?_⟩
      rw [← hxu]
      exact (D.mem_rankBase_iff r x (by rwa [hxu])).mpr hr
    obtain ⟨A, hAsub⟩ := hU.elim_finite_subcover (fun a : ℕ ↦ (D.rankBase a : Set S))
      (fun a ↦ (D.rankBase a).2) hcover
    refine ⟨A, fun x hx hgen r hr ↦ ?_⟩
    obtain ⟨a, haA, hxa⟩ := Set.mem_iUnion₂.mp (hAsub hx)
    exact freeAtPointOfRank_unique F hr ((D.mem_rankBase_iff a x hgen).mp hxa) ▸ haA
  obtain ⟨I, hIfp, hIU, hP⟩ := FlatteningSituation.isSolvable_of_hasRankIn A.card D A le_rfl hA
  obtain ⟨-, V, hVfree, hVsurj⟩ :=
    (freeOnSurjectiveOpen_strictTransform_iff_sheaf f F I).mp hP
  refine ⟨I, hIfp, hIU, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase I)).mpr
    ⟨I, hIfp, hIU, Iso.refl _, Category.id_comp _⟩, V, fun z hz ↦ ?_, hVsurj⟩
  obtain ⟨n, hn⟩ := hVfree z hz
  obtain ⟨W, hzW, hWV, hiso⟩ := exists_restrict_iso_free_le_of_freeAtPointOfRank
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) z n V hz hn
  exact ⟨W, n, hzW, hWV, hiso⟩

end AlgebraicGeometry

end
