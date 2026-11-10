module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveSplitting
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LocalConstancy
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreConnectedness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UpperSemicontinuity
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Affine

/-!
# `Rᵠ f_* 𝐙/ℓ` for a family of curves: reduction to a Noetherian base

Let `f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most
one, and let `ℓ` be a prime. The first paragraph of the proof of [Stacks, Tag 0GKV] reduces the
constructibility of `Rᵠ f_* 𝐙/ℓ` to the case of a Noetherian base:

* constructibility is Zariski local on `S` ([Stacks, Tag 095F]), so `S` may be taken affine;
* an affine `S = Spec A` is the limit of the spectra `S_i` of the finitely generated
  `𝐙`-subalgebras of `A`, and `f` is the base change of a proper smooth `f_i : X_i ⟶ S_i`
  ([Stacks, Tag 01ZM], [Stacks, Tag 081F], [Stacks, Tag 0C0C]);
* the locus `U_i ⊆ S_i` where the fibres of `f_i` are geometrically connected (open by
  [Stacks, Tag 0E0N], the fibres of the smooth `f_i` being geometrically reduced) and of
  dimension at most one (open by [Stacks, Tag 0D4I]) contains the image of `S`, because both
  invariants of a fibre are unchanged by base change ([Stacks, Tag 055F], [Stacks, Tag 02FY]);
* the restriction of `f_i` over the Noetherian `U_i` is a family of the same kind, and proper
  base change ([Stacks, Tag 095T]) together with [Stacks, Tag 095G] transports the
  constructibility from `U_i` to `S`.

The spectra `S_i` are objects of the big étale site because the ring of `S_i` is a subring of
`A`, so its cardinality is bounded by the size of `S` ([Stacks, Tag 000R]).

## Main results

* `isConstructibleEtaleModule_rightDerivedConstantUnit_of_forall_isNoetherian`: the reduction of
  [Stacks, Tag 0GKV] to a Noetherian base.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 0E0N](https://stacks.math.columbia.edu/tag/0E0N)
* [Stacks Project, Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The stages of `AlgebraicGeometry.affineStageCone S` are no larger than `S`.** The ring of
a stage is a subring of `Γ(S, ⊤)`. -/
theorem size_specAdjoinFinsetDiagram_obj_lt {S : Scheme.{u}} [IsAffine S] {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hsl : κ.IsStrongPrelimit) (hS : S.size < κ)
    (j : (Finset Γ(S, ⊤))ᵒᵖ) : ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj j).size < κ := by
  refine Scheme.size_lt_of_isAffine_of_mk_le hκ hsl hS ?_
  rw [specAdjoinFinsetDiagram_obj, Cardinal.mk_congr
    (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.toEquiv]
  refine (Cardinal.mk_le_of_injective Subtype.val_injective).trans ?_
  rw [Scheme.size_of_isAffine S]
  exact (le_max_right _ _).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- An element of `WithBot ℕ∞` is at most `1` exactly when it is less than `2`. -/
theorem withBot_enat_le_one_iff_lt_two (x : WithBot ℕ∞) : x ≤ 1 ↔ x < 2 := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨fun _ => WithBot.bot_lt_coe _, fun _ => bot_le⟩
  | coe y =>
    rw [show (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl,
      show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
      WithBot.coe_lt_coe]
    induction y using ENat.recTopCoe with
    | top => exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    | coe n =>
      rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl,
        ENat.natCast_le_natCast, ENat.natCast_lt_natCast]
      omega

/-- **A proper smooth family of curves over an affine base comes from a Noetherian base.** Let
`f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most one,
`S` affine. Then `f` is the base change, along a morphism `j : S ⟶ T` of the big étale site, of a
proper smooth `h : Y ⟶ T` with geometrically connected fibres of dimension at most one over a
Noetherian `T`.

`T` is the open subscheme of a stage `S_i` of `AlgebraicGeometry.affineStageCone S` where the
fibres of the model `f_i` are geometrically connected ([Stacks, Tag 0E0N]) and of dimension at
most one ([Stacks, Tag 0D4I]). -/
theorem exists_isPullback_isNoetherian_curveFamily (B : BigEtaleSite.{u}) {X S : B.Scheme}
    [IsAffine S.obj] (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1) :
    ∃ (T Y : B.Scheme) (h : Y.obj ⟶ T.obj) (j : S ⟶ T) (g : X.obj ⟶ Y.obj),
      IsProper h ∧ Smooth h ∧ GeometricallyConnected h ∧
        (∀ t : T.obj, topologicalKrullDim (h.fiber t) ≤ 1) ∧ IsNoetherian T.obj ∧
        IsPullback g f h (B.inclusion.map j) := by
  obtain ⟨i, Y₀, h₀, q', hpr, hsm, hpb⟩ :=
    HodgeSpreadingOut.exists_isPullback_affineStageCone_properSmooth f
  let T₀ := (specAdjoinFinsetDiagram Γ(S.obj, ⊤)).obj i
  let q : S.obj ⟶ T₀ := (affineStageCone S.obj).π.app i
  have hT₀ : B.Contains T₀ :=
    size_specAdjoinFinsetDiagram_obj_lt B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit S.property i
  have : IsNoetherian T₀ := isNoetherian_specAdjoinFinsetDiagram_obj _ i
  -- the locus `V` of the fibres that are geometrically connected and of dimension at most one
  let V₀ : Set T₀ := {t | numGeometricConnectedComponents h₀ t = 1 ∧ h₀.fiberDimension t ≤ 1}
  have hV₀ : IsOpen V₀ := by
    have e : V₀ = numGeometricConnectedComponents h₀ ⁻¹' {1} ∩
        h₀.fiberDimension ⁻¹' Set.Iio 2 := by
      ext t
      exact and_congr Iff.rfl (withBot_enat_le_one_iff_lt_two _)
    rw [e]
    refine IsOpen.inter ?_ ?_
    · have := isLocallyConstant_numGeometricConnectedComponents h₀ (fun k _ _ s =>
        pullback_of_geometrically (geometricallyReduced_of_smooth h₀).geometrically_isReduced k s)
      exact this.isOpen_fiber 1
    · exact (upperSemicontinuous_iff_isOpen_preimage.mp
        (upperSemicontinuous_fiberDimension h₀)) 2
  let V : T₀.Opens := ⟨V₀, hV₀⟩
  have hrange : Set.range q ⊆ (V : Set T₀) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 := congrFun (numGeometricConnectedComponents_eq_of_isPullback h₀ f q' q hpb) s
      rw [Function.comp_apply] at h1
      rw [← h1, ← geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
      exact (GeometricallyConnected.iff_geometricallyConnected_fiber f).1 inferInstance s
    · exact (congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hpb) s).symm.trans_le (hdim s)
  -- the restricted family
  let qV : S.obj ⟶ V := IsOpenImmersion.lift V.ι q (by rwa [Scheme.Opens.range_ι])
  have hqV : qV ≫ V.ι = q := IsOpenImmersion.lift_fac _ _ _
  let h : pullback h₀ V.ι ⟶ V := pullback.snd h₀ V.ι
  have hV : B.Contains V := Scheme.size_lt_of_isOpenImmersion V.ι hT₀
  have hmemV : ∀ v : V, V.ι v ∈ V₀ := fun v => by
    change V.ι v ∈ (V : Set T₀)
    rw [← Scheme.Opens.range_ι]
    exact ⟨v, rfl⟩
  have hY₀ : B.Contains Y₀ := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact h₀ hT₀
  have hY : B.Contains (pullback h₀ V.ι) :=
    Scheme.size_lt_of_isOpenImmersion (pullback.fst h₀ V.ι) hY₀
  have hsqV : IsPullback (pullback.fst h₀ V.ι) h h₀ V.ι := IsPullback.of_hasPullback h₀ V.ι
  have hcond : q' ≫ h₀ = (f ≫ qV) ≫ V.ι := by rw [hpb.w, Category.assoc, hqV]
  have hpbV : IsPullback (pullback.lift q' (f ≫ qV) hcond) f h qV := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hsqV
    rw [pullback.lift_fst, hqV]
    exact hpb
  refine ⟨B.obj V hV, B.obj _ hY, h, ObjectProperty.homMk qV, pullback.lift q' (f ≫ qV) hcond,
    inferInstance, inferInstance, ?_, ?_, ?_, hpbV⟩
  · rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
    intro v
    refine ConnectedComponentSection.pullback_fiber_geometricallyConnected h₀ V.ι v ?_
    rw [geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
    exact (hmemV v).1
  · exact fun v =>
      (congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hsqV) v).trans_le (hmemV v).2
  · exact Stacks.Coherent.isNoetherian_of_isOpenImmersion V.ι

variable (B : BigEtaleSite.{u})

/-- **The affine case of the reduction.** -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_isAffine_of_forall_isNoetherian
    {X S : B.Scheme} [IsAffine S.obj] (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    (hN : ∀ (X' S' : B.Scheme) (f' : X'.obj ⟶ S'.obj) [IsProper f'] [Smooth f']
      [GeometricallyConnected f'], (∀ s : S'.obj, topologicalKrullDim (f'.fiber s) ≤ 1) →
      IsNoetherian S'.obj →
      IsBigSiteConstructibleEtaleModule B S' (ZMod ℓ) (rightDerivedConstantUnit f' q (ZMod ℓ))) :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) := by
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B (ZMod ℓ) f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B (ZMod ℓ)
  obtain ⟨T, Y, h, j, g, hpr, hsm, hgc, hdimT, hT, hpb⟩ :=
    exists_isPullback_isNoetherian_curveFamily B f hdim
  exact (isConstructibleEtaleModule_inverseImage_rightDerivedConstantUnit_iff B h ℓ q j g f
    hpb).1 (isConstructibleModuleSheaf_congr B (ZMod ℓ) S
      (etaleModulesToSmallEtalePullbackIso B (ZMod ℓ) j _).symm
      (isConstructibleModuleSheaf_pullback B (ZMod ℓ) j _ (hN Y T h hdimT hT)))

/-- **Reduction of [Stacks, Tag 0GKV] to a Noetherian base.** Let `f : X ⟶ S` be proper and
smooth with geometrically connected fibres of dimension at most one, and `ℓ` a prime. If
`Rᵠ f'_* 𝐙/ℓ` is constructible for every such family `f' : X' ⟶ S'` over a Noetherian base
`S'`, then `Rᵠ f_* 𝐙/ℓ` is constructible.

This is the first paragraph of the proof of [Stacks, Tag 0GKV]: constructibility is Zariski
local ([Stacks, Tag 095F]), and over an affine open the family is the base change of a family of
the same kind over a Noetherian base
(`Stacks.EtaleCohomology.exists_isPullback_isNoetherian_curveFamily`), along which proper base
change ([Stacks, Tag 095T]) and [Stacks, Tag 095G] transport constructibility. -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_forall_isNoetherian
    {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    (hN : ∀ (X' S' : B.Scheme) (f' : X'.obj ⟶ S'.obj) [IsProper f'] [Smooth f']
      [GeometricallyConnected f'], (∀ s : S'.obj, topologicalKrullDim (f'.fiber s) ≤ 1) →
      IsNoetherian S'.obj →
      IsBigSiteConstructibleEtaleModule B S' (ZMod ℓ) (rightDerivedConstantUnit f' q (ZMod ℓ))) :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) := by
  let U : S.obj.affineOpens → B.Scheme := fun k =>
    B.obj k.1 (Scheme.size_lt_of_isOpenImmersion k.1.ι S.property)
  let ι : ∀ k, U k ⟶ S := fun k => ObjectProperty.homMk k.1.ι
  refine isConstructibleModuleSheaf_of_openCover B (ZMod ℓ) S _ U ι
    (fun k => inferInstanceAs (IsOpenImmersion k.1.ι)) ?_ (fun k => ?_)
  · refine (Set.eq_univ_of_forall fun s => ?_).symm
    have hs : s ∈ (⨆ k : S.obj.affineOpens, (k : S.obj.Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
    exact Set.mem_iUnion.2 ⟨k, by
      change s ∈ Set.range k.1.ι
      rwa [Scheme.Opens.range_ι]⟩
  · have : IsAffine (U k).obj := k.2
    have hXk : B.Contains (pullback f k.1.ι) :=
      Scheme.size_lt_of_isOpenImmersion (pullback.fst f k.1.ι) X.property
    let fk : (B.obj _ hXk).obj ⟶ (U k).obj := pullback.snd f k.1.ι
    have hdimk : ∀ s, topologicalKrullDim (fk.fiber s) ≤ 1 := fun s => by
      exact_mod_cast topologicalKrullDim_fiber_pullbackSnd_le_of_isImmersion f k.1.ι
        (fun s => by exact_mod_cast hdim s) s
    exact isConstructibleModuleSheaf_pullback_rightDerivedConstantUnit B f ℓ q (ι k)
      (pullback.fst f k.1.ι) fk (IsPullback.of_hasPullback f k.1.ι)
      (isConstructibleEtaleModule_rightDerivedConstantUnit_of_isAffine_of_forall_isNoetherian B
        fk hdimk ℓ q hN)

end Stacks.EtaleCohomology

end
