module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.BaseLocality
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedSourcePasting
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.ExactResolution
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.MayerVietorisDevissage
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.ShiftCompatibility
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction

/-!
# Flat base change for the higher direct images of a quasi-compact quasi-separated morphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, let `G` be a
quasi-coherent `𝒪_{S'}`-module flat over `S` and let `F` be a quasi-coherent `𝒪_X`-module.  With
the two coefficient functors

`Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G` and `Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G`

this file proves [Stacks, Tag 0GN5]: the degreewise comparison

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

of `DegreewiseComparison.lean` is an isomorphism for every `i`.

## The route

Everything is reduced to the quasi-compact *separated* case of `BaseLocality.lean` by a
Mayer--Vietoris dévissage in `D⁺(𝒪_X)`.

*Reduction to a single morphism.*  `AffineInvertibility.lean` replaces the family of degreewise
comparisons by the single derived comparison `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` at `F[0]`, and
`BaseLocality.lean` makes that local on the base, so the base may be assumed affine.

*The dévissage.*  Choose a bounded below complex `K` of injective `𝒪_X`-modules with `Qh K ≅ F[0]`
(`ExactResolution.lean`).  The objects of `D⁺(𝒪_X)` at which the derived comparison is invertible
form a triangulated subcategory closed under isomorphisms (`ShiftCompatibility.lean`), and the
Mayer--Vietoris dévissage of `MayerVietorisDevissage.lean` says that such a subcategory contains
the image of `K` as soon as it contains the images of `j_{W,*} j_W^* K` for `W` running over `A`,
`B` and `A ∩ B`, for one cover of `X` by two opens.  Iterating over a finite cover by affine opens
reduces the statement to:

*The base case.*  For an open `W` of `X` whose inclusion is quasi-compact and whose composite
`W ⟶ S` is separated, the derived comparison is invertible at the image of `j_{W,*} j_W^* K`.  The
fibre-direction pasting law of `DerivedSourcePasting.lean` reduces that to two instances of the
quasi-compact separated case: one for `W ⟶ S`, which is separated by hypothesis and quasi-compact
because `f` is, and one for the inclusion `W ⟶ X` over the base `X`, which is separated because an
open immersion is a monomorphism.

*Why the cover can be iterated.*  The opens satisfying the two conditions of the base case are
closed under intersection — for the inclusion because it is a base change of another such
inclusion, for the composite because it factors through one — and the affine opens satisfy them
over an affine base.  So an induction over a finite affine cover, with the relative form of the
dévissage, reaches `⊤`; and at `⊤` the endofunctor "restrict and push forward again" is the
identity.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_isAffine_base`:
  the derived comparison is invertible at `F[0]` for a quasi-compact quasi-separated morphism to
  an affine base.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single`: the same over an
  arbitrary base.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app`:
  **[Stacks, Tag 0GN5]** — the degreewise comparison is invertible in every degree.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The direct image along an open immersion preserves injective objects -/

/-- **The direct image along the inclusion of an open subscheme preserves injective objects.**
Its left adjoint, restriction, is exact. -/
theorem preservesInjectiveObjects_modulePushforward_opensι {Y : Scheme.{u}} (V : Y.Opens) :
    (modulePushforward V.ι.toLRSHom.toShHom).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact (modulePushforward V.ι.toLRSHom.toShHom)
    (modulePullback V.ι.toLRSHom.toShHom)
    (modulePullbackPushforwardAdjunction V.ι.toLRSHom.toShHom)
    ⟨preservesFiniteLimits_modulePullback_opensι V,
      preservesFiniteColimits_modulePullback_opensι V⟩

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-! ### The opens the base case covers -/

/-- An open `W` of `X` is *adapted* to `f` when the inclusion of `W` is quasi-compact and the
composite `W ⟶ S` is separated.  These are the hypotheses the quasi-compact separated case of
`BaseLocality.lean` is applied under, once for `W ⟶ S` and once for `W ⟶ X`. -/
private def IsAdapted (f : X ⟶ S) (W : X.Opens) : Prop :=
  QuasiCompact W.ι ∧ IsSeparated (W.ι ≫ f)

/-- **An affine open is adapted** over an affine base: it is compact, so its inclusion composed
with `f` is quasi-compact, hence its inclusion is quasi-compact because `f` is quasi-separated;
and a morphism of affine schemes is separated. -/
private theorem isAdapted_of_isAffineOpen [IsAffine S] [QuasiCompact f] [QuasiSeparated f]
    (W : X.Opens) (hW : IsAffineOpen W) : IsAdapted f W := by
  have : IsAffine W.toScheme := hW
  have hc : QuasiCompact (W.ι ≫ f) := (quasiCompact_iff_compactSpace (W.ι ≫ f)).mpr inferInstance
  exact ⟨MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) W.ι f
    inferInstance hc, inferInstance⟩

/-- **The adapted opens are closed under intersection.**  The inclusion of `W ⊓ W'` into `W'` is a
base change of the inclusion of `W`, and `(W ⊓ W').ι` factors through `W.ι`. -/
private theorem IsAdapted.inf {W W' : X.Opens} (hW : IsAdapted f W) (hW' : IsAdapted f W') :
    IsAdapted f (W ⊓ W') := by
  obtain ⟨hWqc, hWsep⟩ := hW
  obtain ⟨hW'qc, hW'sep⟩ := hW'
  have : QuasiCompact (X.homOfLE (inf_le_right : W ⊓ W' ≤ W')) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
      (isPullback_opens_inf W W') hWqc
  have := hW'qc
  have := hWsep
  refine ⟨?_, ?_⟩
  · rw [← Scheme.homOfLE_ι X (inf_le_right : W ⊓ W' ≤ W')]
    infer_instance
  · rw [← Scheme.homOfLE_ι X (inf_le_left : W ⊓ W' ≤ W), Category.assoc]
    infer_instance

/-! ### The base case of the dévissage -/

/-- **The base case.**  For an open `W` adapted to `f`, the derived comparison of
[Stacks, Tag 0GN5] is invertible at the image of `j_{W,*} j_W^* K`.

The fibre-direction pasting law of `DerivedSourcePasting.lean` reduces this to the quasi-compact
separated case for `W ⟶ S` and for `W ⟶ X`, both at the restriction of `F` to `W`; the complex
`j_W^* K` is a bounded below complex of injectives resolving that restriction, restriction to an
open being exact and preserving injective objects. -/
private theorem isIso_derivedComparison_app_restrictPush (H : IsPullback g' f' f g)
    [QuasiCompact f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (e : DerivedCategory.Plus.Qh.obj K ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (W : X.Opens) (hW : IsAdapted f W) :
    IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback W.ι.toLRSHom.toShHom ⋙
        modulePushforward W.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) := by
  obtain ⟨hWqc, hWsep⟩ := hW
  have := hWqc
  have := hWsep
  let := preservesFiniteLimits_modulePullback_opensι W
  let := preservesFiniteColimits_modulePullback_opensι W
  have := preservesInjectiveObjects_modulePullback_opensι W
  have := preservesInjectiveObjects_modulePushforward_opensι W
  have := preservesInjectiveObjects_modulePushforward_opensι (g' ⁻¹ᵁ W)
  have : ((modulePullback W.ι.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ F
  have : ((modulePullback f'.toLRSHom.toShHom).obj G).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G
  have hGup := isFlatOver_pullbackCoefficients H G hG
  have hN : ∀ n : ℤ,
      Injective (((modulePullback W.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj
        K).obj.as.X n) := fun n => by
    have := hK n
    exact inferInstanceAs
      (Injective ((modulePullback W.ι.toLRSHom.toShHom).obj (K.obj.as.X n)))
  have eN := exactResolutionIso (modulePullback W.ι.toLRSHom.toShHom) K F e
  have Hup : IsPullback (g' ∣_ W) (g' ⁻¹ᵁ W).ι W.ι g' := isPullback_morphismRestrict g' W
  have Hrect := Hup.paste_vert H
  refine isIso_derivedComparison_app_pushforward H.w Hup.w Hrect.w G hG hGup _ hN ?_ ?_ <;>
    refine (CategoryTheory.NatTrans.isIso_app_iff_of_iso _ eN).mpr ?_
  · exact isIso_derivedComparison_app_single_of_isSeparated' Hrect G hG _
  · exact isIso_derivedComparison_app_single_of_isSeparated' Hup _ hGup _

/-! ### The induction over a finite cover -/

/-- One step of the dévissage, at the invertibility locus of the derived comparison: the
relative Mayer--Vietoris dévissage of `MayerVietorisDevissage.lean` with the object property
written out, so that the instances it needs are supplied rather than searched for. -/
private theorem isIso_derivedComparison_app_restrictPush_step (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) (A B : X.Opens)
    (hA : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback A.ι.toLRSHom.toShHom ⋙
        modulePushforward A.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))))
    (hB : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback B.ι.toLRSHom.toShHom ⋙
        modulePushforward B.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))))
    (hC : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback (A ⊓ B).ι.toLRSHom.toShHom ⋙
        modulePushforward (A ⊓ B).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))) :
    IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback (A ⊔ B).ι.toLRSHom.toShHom ⋙
        modulePushforward (A ⊔ B).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) :=
  @prop_of_sup X
    (fun E : DerivedCategory.Plus
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
      IsIso ((derivedComparison G H.w hG).app E))
    (isTriangulated_isIso_derivedComparison_app H.w G hG)
    (isClosedUnderIsomorphisms_isIso_derivedComparison_app H.w G hG) A B K hK hA hB hC

/-- Invertibility of the derived comparison at the image of `j_{W,*} j_W^* K` depends on `W`
only through its value.  Stated so that the lattice identities of the induction below are
discharged here, where the terms are small, rather than by rewriting inside the goal. -/
private theorem isIso_derivedComparison_app_restrictPush_congr (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {W W' : X.Opens} (hWW' : W = W')
    (hW : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback W.ι.toLRSHom.toShHom ⋙
        modulePushforward W.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))) :
    IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback W'.ι.toLRSHom.toShHom ⋙
        modulePushforward W'.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) := by
  subst hWW'
  exact hW

/-- The dévissage at `⊤`, at the invertibility locus of the derived comparison. -/
private theorem isIso_derivedComparison_app_of_top (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (h : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePullback (⊤ : X.Opens).ι.toLRSHom.toShHom ⋙
        modulePushforward
          (⊤ : X.Opens).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)))) :
    IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj K)) :=
  @prop_of_top X
    (fun E : DerivedCategory.Plus
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
      IsIso ((derivedComparison G H.w hG).app E))
    (isTriangulated_isIso_derivedComparison_app H.w G hG)
    (isClosedUnderIsomorphisms_isIso_derivedComparison_app H.w G hG) K h

/-- **The dévissage over a finite family of adapted opens.**  The derived comparison is invertible
at the image of `j_{W,*} j_W^* K` for `W` the union of a finite family of adapted opens and one
further adapted open; the relative Mayer--Vietoris dévissage supplies the induction step, the
intersection of the new open with the union being again such a union by distributivity. -/
private theorem isIso_derivedComparison_app_restrictPush_sup (H : IsPullback g' f' f g)
    [QuasiCompact f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (e : DerivedCategory.Plus.Qh.obj K ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    {ι : Type*} (t : Finset ι) :
    ∀ (V : ι → X.Opens), (∀ j ∈ t, IsAdapted f (V j)) → ∀ W₀ : X.Opens, IsAdapted f W₀ →
      IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj
        ((modulePullback (t.sup V ⊔ W₀).ι.toLRSHom.toShHom ⋙
          modulePushforward
            (t.sup V ⊔ W₀).ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) := by
  induction t using Finset.cons_induction with
  | empty =>
    intro V _ W₀ hW₀
    refine isIso_derivedComparison_app_restrictPush_congr H G hG K
      (W := W₀) (by rw [Finset.sup_empty, bot_sup_eq]) ?_
    exact isIso_derivedComparison_app_restrictPush H G hG F K hK e W₀ hW₀
  | cons a t ha hind =>
    intro V hV W₀ hW₀
    have haa : IsAdapted f (V a) := hV a (Finset.mem_cons_self a t)
    have hVt : ∀ j ∈ t, IsAdapted f (V j) := fun j hj => hV j (Finset.mem_cons_of_mem hj)
    have hsup : (t.sup V ⊔ W₀) ⊔ V a = (Finset.cons a t ha).sup V ⊔ W₀ := by
      rw [Finset.sup_cons, sup_comm (V a) (t.sup V), sup_right_comm]
    have hinf : t.sup (fun j => V a ⊓ V j) ⊔ (V a ⊓ W₀) = (t.sup V ⊔ W₀) ⊓ V a := by
      rw [inf_comm (t.sup V ⊔ W₀) (V a), inf_sup_left, Finset.sup_inf_distrib_left]
    refine isIso_derivedComparison_app_restrictPush_congr H G hG K hsup ?_
    refine isIso_derivedComparison_app_restrictPush_step H G hG K hK (t.sup V ⊔ W₀) (V a)
      (hind V hVt W₀ hW₀) (isIso_derivedComparison_app_restrictPush H G hG F K hK e _ haa) ?_
    refine isIso_derivedComparison_app_restrictPush_congr H G hG K hinf ?_
    exact hind (fun j => V a ⊓ V j) (fun j hj => haa.inf (hVt j hj)) (V a ⊓ W₀)
      (haa.inf hW₀)

/-! ### The affine base -/

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for a quasi-compact
quasi-separated morphism to an affine base.**  The Mayer--Vietoris dévissage over a finite cover
of `X` by affine opens, each of which is adapted to `f`. -/
theorem isIso_derivedComparison_app_single_of_isAffine_base (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_injectiveComplex_iso
    ((DerivedCategory.Plus.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
  have : CompactSpace ↥X := (quasiCompact_iff_compactSpace f).mp inferInstance
  -- a finite family of affine opens covering `X`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).2)
    (fun x _ => by
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by
          rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have htop : t.sup (fun U : X.affineOpens => (U : X.Opens)) ⊔ ⊥ = ⊤ := by
    rw [sup_bot_eq]
    refine top_le_iff.mp ?_
    intro x _
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact (Finset.le_sup (f := fun U : X.affineOpens => (U : X.Opens)) hUt) hxU
  refine @ObjectProperty.prop_of_iso _ _
    (fun E : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
      IsIso ((derivedComparison G H.w hG).app E))
    (isClosedUnderIsomorphisms_isIso_derivedComparison_app H.w G hG) _ _ e ?_
  refine isIso_derivedComparison_app_of_top H G hG K ?_
  refine isIso_derivedComparison_app_restrictPush_congr H G hG K htop ?_
  exact isIso_derivedComparison_app_restrictPush_sup H G hG F K hK e t _
    (fun U _ => isAdapted_of_isAffineOpen _ (U : X.affineOpens).2) ⊥
    (isAdapted_of_isAffineOpen _ (isAffineOpen_bot X))

/-! ### Tag 0GN5 -/

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for a quasi-compact
quasi-separated morphism over an arbitrary base.**  Invertibility of the derived comparison is
local on the base, and the restriction of `f` over an affine open is again quasi-compact and
quasi-separated. -/
theorem isIso_derivedComparison_app_single (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  refine isIso_derivedComparison_app_single_of_affineBases H G hG F ?_
  intro U V hU hV hUV e HV hGV
  have : IsAffine U.toScheme := hU
  have : ((modulePullback V.ι.toLRSHom.toShHom).obj G).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G
  have : ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ F
  exact isIso_derivedComparison_app_single_of_isAffine_base HV _ hGV _

/-- **[Stacks, Tag 0GN5].**  Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, let `G` be a
quasi-coherent `𝒪_{S'}`-module flat over `S` and let `F` be a quasi-coherent `𝒪_X`-module.  Then
the degreewise comparison

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

of the two coefficient functors `Φ : M ↦ g^*M ⊗ G` and `Ψ : F ↦ (g')^*F ⊗ (f')^*G` is an
isomorphism in every degree `i`. -/
@[stacks 0GN5]
theorem isIso_degreewiseComparison_app (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) :=
  isIso_degreewiseComparison_app_of_isIso H G hG F
    (isIso_derivedComparison_app_single H G hG F) i

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
