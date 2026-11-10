module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductAffineTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductNoetherianAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterizationVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismFormalAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps

/-!
# Types of formal algebraic spaces stable under fibre products

Let `X ⟶ Y ⟵ Z` be morphisms of formal algebraic spaces. If `X` and `Z` are locally countably
indexed, locally countably indexed and classical, locally weakly adic, or locally adic\*, then so
is `X ×_Y Z`. If `X` and `Z` are locally Noetherian and `X_red ⟶ Y_red` is locally of finite
type, then `X ×_Y Z` is locally Noetherian.

These results are stated next to `StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes`
but kept in a module of their own, so that that module stays as it is on the base.

## Main definitions

* `AffineChartFibreProductStableRel`: The affine case of such a stability statement for a
  property of fppf sheaves, relative to the chart map.

## Main results

* `isLocallyCountablyIndexed_pullback_unconditional`: Fibre products of locally countably
  indexed formal algebraic spaces are locally countably indexed.
* `isLocallyCountablyIndexedAndClassical_pullback_unconditional`: Fibre products of locally
  countably indexed and classical formal algebraic spaces are locally countably indexed and
  classical.
* `isLocallyWeaklyAdic_pullback_unconditional`: Fibre products of locally weakly adic formal
  algebraic spaces are locally weakly adic.
* `isLocallyAdicStar_pullback_unconditional`: Fibre products of locally adic\* formal algebraic
  spaces are locally adic\*.
* `isLocallyNoetherian_pullback_unconditional`: `X ×_Y Z` is locally Noetherian when `X` and `Z`
  are and `X_red ⟶ Y_red` is locally of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine case of a clause of Stacks 0GBB for a property `P` of fppf sheaves, relative to
a property `Q` of the first morphism: the fibre product of two affine formal algebraic spaces
satisfying `P` over an affine formal algebraic space satisfies `P`, provided the morphism from
the first factor satisfies `Q`.

The relative form is what clause (5) needs. The source attaches its finite type condition to
the *specific* chart map — "if `X_red ⟶ Y_red` is locally of finite type, then
`(X_{ji})_red ⟶ (Y_j)_red` is locally of finite type" — so an affine case with no room to
receive that map cannot express it; at `P := IsNoetherian` the map-blind form
`AlgebraicGeometry.FormalSpace.AffineChartFibreProductStable` is in fact unsatisfiable,
`Spec K ×_{Spec k} Spec K` for `K/k` of infinite transcendence degree being a fibre product of
Noetherian affine formal algebraic spaces over an affine one whose presenting ring `K ⊗_k K` is
not Noetherian. Clauses (1) to (4) need nothing of the map, and for them the map-blind form is
available and is what is proved. -/
abbrev AffineChartFibreProductStableRel (P : FppfSheaf B S hS → Prop)
    (Q : ∀ {U V : FppfSheaf B S hS}, (U ⟶ V) → Prop) : Prop :=
  ∀ {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS W → Q t → P U → P W → P (pullback t s)

/-- The map-blind affine case of a clause of Stacks 0GBB implies the form relative to any
property of the chart map: the relative form has one hypothesis more and the same conclusion.
This is how the four clauses whose affine case needs nothing of the map feed the engine. -/
theorem affineChartFibreProductStableRel_of_mapBlind {P : FppfSheaf B S hS → Prop}
    (Q : ∀ {U V : FppfSheaf B S hS}, (U ⟶ V) → Prop)
    (h : AffineChartFibreProductStable B S hS P) :
    AffineChartFibreProductStableRel B S hS P Q :=
  fun t s hU hV hW _ hPU hPW ↦ h t s hU hV hW hPU hPW

/-- **The chart transfer of the finite type condition of clause (5) of Stacks 0GBB.** If
`X_red ⟶ Y_red` is locally of finite type then so is `(Uⱼᵢ)_red ⟶ (Vⱼ)_red` for every affine
representable étale chart `Vⱼ` of `Y` and every affine representable étale chart `Uⱼᵢ` of
`Vⱼ ×_Y X`. This is the source's own step, "if `X_red ⟶ Y_red` is locally of finite type, then
`(X_{ji})_red ⟶ (Y_j)_red` is locally of finite type", and it is what discharges the hypothesis
`hQ` of `AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_pullback` at
`Q := HasLocallyOfFiniteTypeReduction`.

The reduction of `Vⱼ ×_Y X` is `(Vⱼ)_red ×_{Y_red} X_red` by
`AlgebraicGeometry.FormalSpace.exists_isReduction_pullback_iso_of_isRepresentableEtale` — the
étale case of Stacks 0GB7 — and the morphism of reductions over the first projection is the base
change of `X_red ⟶ Y_red` along `(Vⱼ)_red ⟶ Y_red`, hence locally of finite type by
Stacks 0AQ5. The chart `Uⱼᵢ` is representable étale over `Vⱼ ×_Y X`, so its reduction is the
base change of that reduction along it by Stacks 0GB7 again, and the resulting morphism of
reductions is representable étale, hence locally of finite type by Stacks 0AJG. Stacks 0AQ4
composes the two. -/
theorem hasLocallyOfFiniteTypeReduction_chart {X Y V U : FppfSheaf B S hS} {f : X ⟶ Y}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (v : V ⟶ Y) (a : U ⟶ pullback v f) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hv : IsRepresentableEtale B S hS v) (ha : IsRepresentableEtale B S hS a)
    (hfin : HasLocallyOfFiniteTypeReduction B S hS f) :
    HasLocallyOfFiniteTypeReduction B S hS (a ≫ pullback.fst v f) := by
  obtain ⟨Xred, Yred, iX, iY, fred, hiX, hiY, hfred, hfredft⟩ := hfin
  obtain ⟨hW, hiW, hiV, pred, hpred, hpredsq⟩ :=
    exists_isReduction_pullback_iso_of_isRepresentableEtale B S hS hX hY
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) hiX hiY hfred hv
      (IsPullback.of_hasPullback v f)
  have hU : IsFormalAlgebraicSpace B S hS U :=
    isFormalAlgebraicSpace_of_isRepresentableEtale B S hS a hW ha
  have hiU : IsReduction B S hS U
      (pullback a (pullback.fst (pullback.snd v f) iX))
      (pullback.fst a (pullback.fst (pullback.snd v f) iX)) :=
    isReduction_pullback_reduction_of_smooth B S hS hU hW ha.1
      (hasPropertyULift_smooth_of_isRepresentableEtale B S hS ha) hiW
      (IsPullback.of_hasPullback _ _)
  refine ⟨_, _, pullback.fst a (pullback.fst (pullback.snd v f) iX), pullback.fst v iY,
    pullback.snd a (pullback.fst (pullback.snd v f) iX) ≫ pred, hiU, hiV, ?_,
    IsLocallyOfFiniteType.comp B S hS _ _
      (IsLocallyOfFiniteType.of_isPullback B S hS
        (IsPullback.of_hasPullback a (pullback.fst (pullback.snd v f) iX)).flip
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS a ha))
      (IsLocallyOfFiniteType.of_isPullback B S hS hpredsq hfredft)⟩
  calc (pullback.snd a (pullback.fst (pullback.snd v f) iX) ≫ pred) ≫ pullback.fst v iY
      = pullback.snd a (pullback.fst (pullback.snd v f) iX) ≫ pred ≫ pullback.fst v iY := by
        rw [Category.assoc]
    _ = (pullback.snd a (pullback.fst (pullback.snd v f) iX) ≫
          pullback.fst (pullback.snd v f) iX) ≫ pullback.fst v f := by
        rw [hpred, Category.assoc]
    _ = pullback.fst a (pullback.fst (pullback.snd v f) iX) ≫ a ≫ pullback.fst v f := by
        rw [← pullback.condition, Category.assoc]

/-- The common content of the five clauses of **Stacks 0GBB**: the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an atlas of `X ×_Y Z` as in Definition 0AIM all of whose members satisfy
`P`, so condition (1) of Stacks 0AKX for `P` at `X` and at `Z` gives condition (2) for
`X ×_Y Z`.

The property is asked of `X` and of `Z` in the shape the proof uses it, condition (1) of
Stacks 0AKX: the members of the atlases of `X` and of `Z` are not the charts the proof needs,
which are the charts of `Vⱼ ×_Y X` and of `Vⱼ ×_Y Z`. For a `P` to which Stacks 0AKX applies
the two conditions agree, and the five clauses below get condition (1) out of condition (2)
that way.

The affine case `hPaff` is relative to a property `Q` of the chart map, which `hQ` asserts of
every chart map `Uⱼᵢ ⟶ Vⱼ` of the cover the proof builds. That is where the finite type
condition of clause (5) enters; clauses (1) to (4) take `Q := fun _ ↦ True` and `hQ` trivial,
and supply `hPaff` from the map-blind
`AlgebraicGeometry.FormalSpace.AffineChartFibreProductStable` they prove, by
`AlgebraicGeometry.FormalSpace.affineChartFibreProductStableRel_of_mapBlind`. -/
theorem hasAffineEtaleAtlasWithProperty_pullback_of_chartPullbacks (P : FppfSheaf B S hS → Prop)
    (Q : ∀ {U V : FppfSheaf B S hS}, (U ⟶ V) → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hXchart : HasAffineEtaleChartProperty B S hS X P)
    (hZchart : HasAffineEtaleChartProperty B S hS Z P)
    (h0AJ3f : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (h0AJ3g : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hQ : ∀ (V U : FppfSheaf B S hS) (v : V ⟶ Y) (a : U ⟶ pullback v f),
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      IsAffineFormalAlgebraicSpace B S hS U → IsRepresentableEtale B S hS a →
      Q (a ≫ pullback.fst v f))
    (hPaff : AffineChartFibreProductStableRel B S hS P Q) :
    HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, J, V, v, hVaff, hVet, hVsurj⟩ := hY
  choose I U a hUaff hUet hUsurj using fun j ↦ (h0AJ3f (V j) (v j) (hVaff j) (hVet j)).2
  choose K W b hWaff hWet hWsurj using fun j ↦ (h0AJ3g (V j) (v j) (hVaff j) (hVet j)).2
  refine ⟨Σ j, I j × K j,
    fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ ?_, fun p ↦ ?_, ?_, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hVaff p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hVaff p.1))
      (hUaff p.1 p.2.1) (hWaff p.1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hVet p.1) (hUet p.1 p.2.1) (hWet p.1 p.2.2)
  · exact isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hVsurj a hUsurj b hWsurj
  · exact hPaff _ _ (hUaff p.1 p.2.1) (hVaff p.1) (hWaff p.1 p.2.2)
      (hQ (V p.1) (U p.1 p.2.1) (v p.1) (a p.1 p.2.1) (hVaff p.1) (hVet p.1)
        (hUaff p.1 p.2.1) (hUet p.1 p.2.1))
      (hXchart (U p.1 p.2.1) (a p.1 p.2.1 ≫ pullback.snd (v p.1) f) (hUaff p.1 p.2.1)
        (IsRepresentableEtale.comp B S hS (hUet p.1 p.2.1)
          (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVet p.1))))
      (hZchart (W p.1 p.2.2) (b p.1 p.2.2 ≫ pullback.snd (v p.1) g) (hWaff p.1 p.2.2)
        (IsRepresentableEtale.comp B S hS (hWet p.1 p.2.2)
          (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hVet p.1))))

/-- **The affine case of clause (1) of Stacks 0GBB.** It needs nothing of the chart map, so it
holds in the map-blind form; `affineChartFibreProductStableRel_of_mapBlind` puts it in the shape
the engine consumes. -/
theorem affineChartFibreProductStable_isCountablyIndexed :
    AffineChartFibreProductStable B S hS (IsCountablyIndexed B S hS) :=
  fun t s hU hV hW hPU hPW ↦
    isCountablyIndexed_pullback_affine B S hS t s hU hV hW hPU hPW

/-- **The affine case of clause (2) of Stacks 0GBB**, map-blind as in clause (1). -/
theorem affineChartFibreProductStable_isCountablyIndexedAndClassical :
    AffineChartFibreProductStable B S hS
      (fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T) :=
  fun t s hU hV hW hPU hPW ↦
    ⟨isCountablyIndexed_pullback_affine B S hS t s hU hV hW hPU.1 hPW.1,
      isClassical_pullback_affine B S hS t s hV hPU.1 hPW.1 hPU.2 hPW.2⟩

/-- **The affine case of clause (3) of Stacks 0GBB**, map-blind as in clause (1). -/
theorem affineChartFibreProductStable_isWeaklyAdic :
    AffineChartFibreProductStable B S hS (IsWeaklyAdic B S hS) :=
  fun t s _ hV _ hPU hPW ↦ isWeaklyAdic_pullback_affine B S hS t s hV hPU hPW

/-- **The affine case of clause (4) of Stacks 0GBB**, map-blind as in clause (1). -/
theorem affineChartFibreProductStable_isAdicStar :
    AffineChartFibreProductStable B S hS (IsAdicStar B S hS) :=
  fun t s _ hV _ hPU hPW ↦ isAdicStar_pullback_affine B S hS t s hV hPU hPW

/-- **The affine case of clause (5) of Stacks 0GBB**, in the shape the engine consumes. The
content is `AlgebraicGeometry.FormalSpace.isNoetherian_pullback_affine`; what this records is
that it fits the engine's relative affine input at `Q := HasLocallyOfFiniteTypeReduction`. This
clause is the one whose affine case cannot be map-blind: the map-blind form
`AlgebraicGeometry.FormalSpace.AffineChartFibreProductStable` is unsatisfiable at
`P := IsNoetherian`, for the reason given in the docstring of
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_pullback_unconditional`. -/
theorem affineChartFibreProductStable_isNoetherian :
    AffineChartFibreProductStableRel B S hS (IsNoetherian B S hS)
      (HasLocallyOfFiniteTypeReduction B S hS) :=
  fun t s hU hV hW ht hPU hPW ↦
    isNoetherian_pullback_affine B S hS t s hU hV hW ht hPU hPW

/-- The set-theoretic condition of **Stacks 0AIS** for a fibre product of formal algebraic
spaces: if `X`, `Y` and `Z` are formal algebraic spaces, then `X ×_Y Z` satisfies it.

All three have representable relative products by the representability assertion of
**Stacks 0AIP**, `hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`, and `X` and `Z`
satisfy the condition, it being a conjunct of their formality; so
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts` applies. -/
theorem satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z) :
    SatisfiesSetTheoreticCondition B S hS (pullback f g) :=
  satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS f g
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX)
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ) hX.1 hZ.1

/-- The engine `hasAffineEtaleAtlasWithProperty_pullback_of_chartPullbacks` with the formality of
the fibre product added and the étale chart pullbacks supplied by `X` and `Z` themselves. -/
private theorem isFormal_and_atlas_pullback (P : FppfSheaf B S hS → Prop)
    (Q : ∀ {U V : FppfSheaf B S hS}, (U ⟶ V) → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hXchart : HasAffineEtaleChartProperty B S hS X P)
    (hZchart : HasAffineEtaleChartProperty B S hS Z P)
    (hQ : ∀ (V U : FppfSheaf B S hS) (v : V ⟶ Y) (a : U ⟶ pullback v f),
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      IsAffineFormalAlgebraicSpace B S hS U → IsRepresentableEtale B S hS a →
      Q (a ≫ pullback.fst v f))
    (hPaff : AffineChartFibreProductStableRel B S hS P Q) :
    IsFormalAlgebraicSpace B S hS (pullback f g) ∧
      HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_chartPullbacks B S hS P Q f g hY
    hXchart hZchart
    (fun _V v _hV hv ↦ isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v f hX hv)
    (fun _V v _hV hv ↦ isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v g hZ hv)
    hQ hPaff
  ⟨isFormalAlgebraicSpace_of_hasAffineEtaleAtlasWithProperty B S hS
    (satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace' B S hS f g hX hY hZ) h, h⟩

/-- **Stacks 0GBB, clause (1).** If `X` and `Z` are locally countably indexed, then so is
`X ×_Y Z`. The hypotheses are exactly the source's. -/
@[stacks 0GBB "clause (1), locally countably indexed, in full under the source's hypotheses. The \
affine case (0AN3 with 0GB4) is `affineChartFibreProductStable_isCountablyIndexed`; the 0AIS \
set-theoretic condition for X ×_Y Z is \
`satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'`, from 0AIP; the 0AIM covering \
condition for the chart cover is `isLocallySurjective_sigmaDesc_chartPullbackMap`; Stacks 0AKX (2) \
implies (1) is `AlgebraicGeometry.FormalSpace.\
hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed`; and the étale \
case of \
Stacks 0AJ3 is `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`"]
theorem isLocallyCountablyIndexed_pullback_unconditional {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z) :
    IsLocallyCountablyIndexed B S hS (pullback f g) :=
  isFormal_and_atlas_pullback B S hS (IsCountablyIndexed B S hS) (fun _ ↦ True) f g hX.1 hY
    hZ.1
    ((hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed B S hS X
      hX.1).2 hX.2)
    ((hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed B S hS Z
      hZ.1).2 hZ.2)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (affineChartFibreProductStableRel_of_mapBlind B S hS (fun _ ↦ True)
      (affineChartFibreProductStable_isCountablyIndexed B S hS))

/-- **Stacks 0GBB, clause (2).** If `X` and `Z` are locally countably indexed and classical, then
so is `X ×_Y Z`. The hypotheses are exactly the source's. -/
@[stacks 0GBB "clause (2), locally countably indexed and classical, in full under the source's \
hypotheses. The affine case (0AN3 with 0GB4) is \
`affineChartFibreProductStable_isCountablyIndexedAndClassical`; the 0AIS set-theoretic condition \
for X ×_Y Z is `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'`, from 0AIP; \
the 0AIM covering condition for the chart cover is \
`isLocallySurjective_sigmaDesc_chartPullbackMap`; Stacks 0AKX (2) implies (1) is \
`hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexedAndClassical_unconditional`; and the \
étale case of Stacks 0AJ3 is `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`"]
theorem isLocallyCountablyIndexedAndClassical_pullback_unconditional {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyCountablyIndexedAndClassical B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexedAndClassical B S hS Z) :
    IsLocallyCountablyIndexedAndClassical B S hS (pullback f g) :=
  isFormal_and_atlas_pullback B S hS
    (fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T) (fun _ ↦ True) f g hX.1 hY hZ.1
    ((hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexedAndClassical_unconditional B S hS X
      hX.1).2 hX.2)
    ((hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexedAndClassical_unconditional B S hS Z
      hZ.1).2 hZ.2)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (affineChartFibreProductStableRel_of_mapBlind B S hS (fun _ ↦ True)
      (affineChartFibreProductStable_isCountablyIndexedAndClassical B S hS))

/-- **Stacks 0GBB, clause (3).** If `X` and `Z` are locally weakly adic, then so is `X ×_Y Z`. The
hypotheses are exactly the source's. -/
@[stacks 0GBB "clause (3), locally weakly adic, in full under the source's hypotheses. The affine \
case (0AN3 with 0GXJ) is `affineChartFibreProductStable_isWeaklyAdic`; the 0AIS set-theoretic \
condition for X ×_Y Z is `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'`, \
from 0AIP; the 0AIM covering condition for the chart cover is \
`isLocallySurjective_sigmaDesc_chartPullbackMap`; Stacks 0AKX (2) implies (1) is \
`hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic_unconditional`; and the étale case of Stacks \
0AJ3 is `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`"]
theorem isLocallyWeaklyAdic_pullback_unconditional {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y)
    (hX : IsLocallyWeaklyAdic B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyWeaklyAdic B S hS Z) :
    IsLocallyWeaklyAdic B S hS (pullback f g) :=
  isFormal_and_atlas_pullback B S hS (IsWeaklyAdic B S hS) (fun _ ↦ True) f g hX.1 hY hZ.1
    ((hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic_unconditional B S hS X
      hX.1).2 hX.2)
    ((hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic_unconditional B S hS Z
      hZ.1).2 hZ.2)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (affineChartFibreProductStableRel_of_mapBlind B S hS (fun _ ↦ True)
      (affineChartFibreProductStable_isWeaklyAdic B S hS))

/-- **Stacks 0GBB, clause (4).** If `X` and `Z` are locally adic\*, then so is `X ×_Y Z`. The
hypotheses are exactly the source's. -/
@[stacks 0GBB "clause (4), locally adic*, in full under the source's hypotheses. The affine case \
(0AN3 with 0GB4) is `affineChartFibreProductStable_isAdicStar`; the 0AIS set-theoretic condition \
for X ×_Y Z is `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'`, from 0AIP; \
the 0AIM covering condition for the chart cover is \
`isLocallySurjective_sigmaDesc_chartPullbackMap`; Stacks 0AKX (2) implies (1) is \
`hasAffineEtaleChartProperty_iff_atlas_isAdicStar_unconditional`; and the étale case of Stacks \
0AJ3 is `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`"]
theorem isLocallyAdicStar_pullback_unconditional {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z) :
    IsLocallyAdicStar B S hS (pullback f g) :=
  isFormal_and_atlas_pullback B S hS (IsAdicStar B S hS) (fun _ ↦ True) f g hX.1 hY hZ.1
    ((hasAffineEtaleChartProperty_iff_atlas_isAdicStar_unconditional B S hS X
      hX.1).2 hX.2)
    ((hasAffineEtaleChartProperty_iff_atlas_isAdicStar_unconditional B S hS Z
      hZ.1).2 hZ.2)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (affineChartFibreProductStableRel_of_mapBlind B S hS (fun _ ↦ True)
      (affineChartFibreProductStable_isAdicStar B S hS))

/-- **Stacks 0GBB, clause (5).** If `X` and `Z` are locally Noetherian and `X_red ⟶ Y_red` is
locally of finite type, then `X ×_Y Z` is locally Noetherian.

`hfin` is the source's own hypothesis on the reduction morphism, and the hypotheses are exactly
the source's.

The affine case is relative to the chart map,
`AlgebraicGeometry.FormalSpace.AffineChartFibreProductStableRel`: the map-blind
`AlgebraicGeometry.FormalSpace.AffineChartFibreProductStable`, which the other four clauses
prove, is *unsatisfiable* at `P := IsNoetherian`: it asserts that every fibre product of
Noetherian affine formal algebraic spaces over an affine formal algebraic space is Noetherian,
which is false in every big fppf site over a nonempty base. Take a point of `S` with residue field
`k` and `K = k(x₁, x₂, …)`; then `Spec k` and `Spec K` are affine objects of the site, hence affine
formal algebraic spaces by
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sheafifiedYoneda'`, and `Spec K` is
Noetherian — its presenting ring `K` is discrete, hence Noetherian, complete and adic with ideal of
definition `(0)`. The sheafified Yoneda embedding preserves fibre products on this subcanonical
site, so `Spec K ×_{Spec k} Spec K = Spec (K ⊗_k K)`, whose presenting ring is `K ⊗_k K`; that
ring is not Noetherian, and by
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_isPresentingRing` the presenting
ring is unique up to isomorphism of topological rings, so no Noetherian one presents it. A
registration of this clause on the map-blind affine case would be vacuously true.

The passage from the chart map to the morphism into the shrunk base of the affine case transports
nothing along the monomorphism of the shrink: reduction is not invariant along an arbitrary
monomorphism, `AlgebraicGeometry.FormalSpace.isReduction_completionSheaf` being a
counterexample. -/
@[stacks 0GBB "clause (5), locally Noetherian, in full under the source's hypotheses. The affine \
case (0AN3 with 0GB4) is `affineChartFibreProductStable_isNoetherian`, the affine case RELATIVE TO \
THE CHART MAP: the map-blind form is unsatisfiable at IsNoetherian -- it quantifies over all \
affine U, V, W with no condition on the maps, which is false for Spec K over Spec k with K/k of \
infinite transcendence degree, the presenting ring of the fibre product being the non-Noetherian K \
tensor K -- so a registration on it would have been vacuous. The docstring gives that witness. The \
source's finite type condition on the reductions, hfin, is carried to the chart maps by \
`hasLocallyOfFiniteTypeReduction_chart` and from there to `algebraMap C A` by the affine \
dictionary `chartPropertyIsFiniteTypeOnReductions`. The 0AIS set-theoretic condition for X ×_Y Z \
is `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace'`, from 0AIP; the 0AIM \
covering condition for the chart cover is `isLocallySurjective_sigmaDesc_chartPullbackMap`; Stacks \
0AKX (2) implies (1) is `hasAffineEtaleChartProperty_iff_atlas_isNoetherian_unconditional`; and \
the étale case of Stacks 0AJ3 is `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`"]
theorem isLocallyNoetherian_pullback_unconditional {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hfin : HasLocallyOfFiniteTypeReduction B S hS f) :
    IsLocallyNoetherian B S hS (pullback f g) :=
  isFormal_and_atlas_pullback B S hS (IsNoetherian B S hS)
    (HasLocallyOfFiniteTypeReduction B S hS) f g hX.1 hY hZ.1
    ((hasAffineEtaleChartProperty_iff_atlas_isNoetherian_unconditional B S hS X hX.1).2 hX.2)
    ((hasAffineEtaleChartProperty_iff_atlas_isNoetherian_unconditional B S hS Z hZ.1).2 hZ.2)
    (fun _V _U v a hVaff hv _hUaff ha ↦
      hasLocallyOfFiniteTypeReduction_chart B S hS hX.1 hY v a hVaff hv ha hfin)
    (affineChartFibreProductStable_isNoetherian B S hS)

end AlgebraicGeometry.FormalSpace

end
