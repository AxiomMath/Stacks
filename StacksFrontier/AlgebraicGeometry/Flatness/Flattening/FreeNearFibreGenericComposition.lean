module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeNearFibreGeneric
public import StacksFrontier.AlgebraicGeometry.StrictTransform.RestrictOpen

/-!
# Freeness near the generic points of the fibres is stable under a second blowup

`AlgebraicGeometry.FreeNearFibreGeneric` is the property of an `𝒪_B`-module `G` over
`g : B ⟶ T` that `G` be free of finite rank on a neighbourhood of every point whose closure
contains its whole fibre. This file proves that the property *of the strict transform* is stable
under composing with a second blowup — the hypothesis "`P` is stable under strict transform" of
[Stacks, Remark 38.30.1] (tag 080Y), for the property `P` that the strict transform is free of
finite rank near the generic point of every fibre.

## Main results

* `AlgebraicGeometry.freeNear_strictTransformSheaf_of_over_iso_free`: a module free of finite
  rank on an open `W` of the base change has free strict transform on the inverse image of `W`.
  This is the geometric heart: on `W` the module is flat over the base
  (`AlgebraicGeometry.isFlatOverAt_of_over_iso_free`), so by [Stacks, Tag 080F] part (2) its
  strict transform in the second centre is its pullback.
* `AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf`: freeness near the generic points
  of the fibres is inherited by the strict transform along any blowup of the base.
* `AlgebraicGeometry.FreeNearFibreGeneric.transport`: the property transports along an
  isomorphism of the source, of the target and of the module.
* `AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf_comp_blowUp`: the main result —
  with the hypotheses of [Stacks, Tag 080I] on the third centre `K`, freeness near the generic
  points of the fibres for the strict transform in `I` gives it for the strict transform in `K`.
* `AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf_mul`: the case `K = I * J` of a
  second centre pulled back from the base, where both hypotheses of the main result are
  discharged unconditionally.

## Implementation notes

The three steps of the main proof are separated. The step on the second blowup alone,
`AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf`, has two halves. The topological
half is that the first projection of `(X ×_S Bl_I S) ×_{Bl_I S} Bl_J(Bl_I S)` carries a generic
point of a fibre to a generic point of a fibre: given a competitor `y` upstairs,
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` lifts it to the iterated base change
over the same point of `Bl_J(Bl_I S)`, where genericity applies, and continuity brings the
conclusion back down. The module half is
`AlgebraicGeometry.freeNear_strictTransformSheaf_of_over_iso_free`, which compares two
applications of `Stacks.StrictTransform.pullbackSheafBlowUpIso` over the open
`pr^{-1} W` of the iterated base change: one for the strict transform of `G` itself along
`pr_{Bl_I S}`, one for the strict transform of `G|_W` along `W ⟶ Bl_I S`, whose quotient map is
invertible by [Stacks, Tag 080F] part (2). The two base changes are identified by
`CategoryTheory.Limits.pullbackRightPullbackFstIso` together with
`AlgebraicGeometry.pullbackRestrictIsoRestrict`.

`AlgebraicGeometry.FreeNearFibreGeneric` is phrased with `SheafOfModules.over`, while every
pullback comparison available is phrased with `AlgebraicGeometry.Scheme.Modules.pullback`. The
two are matched in both directions by the private bridges below, built from
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso`; `restrictFunctor`
sits between them and is identified with `pullback` by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

Geometric integrality of `f` is *not* used: it is carried in the statements below only because
it is part of the setting of [Stacks, Tag 0811], where this stability is consumed. Flatness of
`f` is used, through the flatness of the projection of the base change, to turn freeness on `W`
into flatness over the base there.

## References

* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Bridges between `over`, `restrictFunctor` and `pullback` -/

/-- **The pullback of a free module is free on the same index type.** The site functor of a
morphism of schemes is final, so Mathlib's `CategoryTheory.SheafOfModules.pullbackObjFreeIso`
applies. -/
private def pullbackObjFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅
      SheafOfModules.free.{u} I := by
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom f)).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact SheafOfModules.pullbackObjFreeIso (Scheme.Hom.toRingCatSheafHom f) I

/-- A module whose pullback along an *isomorphism* is free of finite rank is itself free of that
rank: pull back again along the inverse. -/
private def isoFreeOfPullbackIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (N : Y.Modules)
    (I : Type u)
    (e : (Scheme.Modules.pullback f).obj N ≅ SheafOfModules.free.{u} I) :
    N ≅ SheafOfModules.free.{u} I :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app N).symm ≪≫
      ((Scheme.Modules.pullbackComp (inv f) f).app N).symm ≪≫
        (Scheme.Modules.pullback (inv f)).mapIso e ≪≫ pullbackObjFreeIso (inv f) I

/-- A trivialisation of the restriction of `M` along `V.ι` read as a trivialisation of `M.over V`.
This is the inverse passage to
`Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso`: the equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv` is fully faithful, so an isomorphism of the images
is the image of an isomorphism. -/
private def overIsoFreeOfRestrictIso {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (I : Type u)
    (e : M.restrict V.ι ≅ SheafOfModules.free.{u} I) :
    M.over V ≅ SheafOfModules.free.{u} I :=
  let F := Scheme.Modules.overEquiv (X := X) V
  have hdisc : Limits.PreservesColimitsOfShape (Discrete I) F.functor :=
    Limits.preservesColimitsOfShape_of_discrete F.functor
  have hunit : SheafOfModules.unit (V.toScheme).ringCatSheaf ≅
      F.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
  F.fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (X := X) V).app M ≪≫ e ≪≫ eFree)

/-- A trivialisation of the pullback of `M` along `V.ι` read as a trivialisation of `M.over V`. -/
private def overIsoFreeOfPullbackIso {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (I : Type u)
    (e : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.free.{u} I) :
    M.over V ≅ SheafOfModules.free.{u} I :=
  overIsoFreeOfRestrictIso M V I
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ e)

/-- A trivialisation of `M.over V` read as a trivialisation of the pullback of `M` along `V.ι`. -/
private def pullbackIsoFreeOfOverIso {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (I : Type u)
    (e : M.over V ≅ SheafOfModules.free.{u} I) :
    (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.free.{u} I :=
  ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫
    (Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso V I M e).symm ≪≫
      _root_.restrictFunctor_obj_free_iso V.ι I

/-- A module whose pullback along an open immersion `k` is free of finite rank is free of that
rank on the image open of `k`. -/
private def overOpensRangeIsoFree {X Y : Scheme.{u}} (M : Y.Modules) (k : X ⟶ Y)
    [IsOpenImmersion k] (I : Type u)
    (e : (Scheme.Modules.pullback k).obj M ≅ SheafOfModules.free.{u} I) :
    M.over k.opensRange ≅ SheafOfModules.free.{u} I :=
  overIsoFreeOfPullbackIso M k.opensRange I
    (isoFreeOfPullbackIsIso k.isoOpensRange.hom
      ((Scheme.Modules.pullback k.opensRange.ι).obj M) I
      ((Scheme.Modules.pullbackComp k.isoOpensRange.hom k.opensRange.ι).app M ≪≫
        (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_hom_ι k)).app M ≪≫ e))

/-- A quasi-coherent module isomorphic to a finite free module is flat over the base at every
point, as soon as the structure morphism is flat. This is
`AlgebraicGeometry.isFlatOverAt_of_over_iso_free` at the open `⊤`. -/
private theorem isFlatOverAt_of_iso_free {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (F : X.Modules)
    [F.IsQuasicoherent] (r : ℕ) (e : F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom F x :=
  isFlatOverAt_of_over_iso_free f F (show x ∈ (⊤ : X.Opens) from trivial) r
    (overIsoFreeOfPullbackIso F ⊤ _
      ((Scheme.Modules.pullback (⊤ : X.Opens).ι).mapIso e ≪≫ pullbackObjFreeIso _ _))

/-! ### The strict transform of a module free on an open of the base change -/

/-- **A module free of finite rank on an open of the base change has free strict transform
there.** Let `q : Y ⟶ T` be flat, let `J` be a centre on `T` and let the quasi-coherent module
`G` be isomorphic to a finite free module on the open `W` of `Y`. Then the strict transform of
`G` along the blowup of `T` in `J` is isomorphic to a free module of the same rank on the inverse
image of `W` in `Y ×_T Bl_J T`.

On `W` the module `G` is flat over `T` (`AlgebraicGeometry.isFlatOverAt_of_over_iso_free`), so
[Stacks, Tag 080F] part (2) makes the quotient map onto the strict transform of `G|_W` along
`W ⟶ T` invertible; `Stacks.StrictTransform.pullbackSheafBlowUpIso`, applied once on each side,
identifies that strict transform with the restriction of the strict transform of `G`. -/
theorem freeNear_strictTransformSheaf_of_over_iso_free {Y T : Scheme.{u}} (q : Y ⟶ T) [Flat q]
    (J : T.IdealSheafData) (G : Y.Modules) [G.IsQuasicoherent] (W : Y.Opens) (n : ℕ)
    (eW : G.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    Nonempty ((Stacks.StrictTransform.sheaf q (blowUpToBase J) (exceptionalIdeal J) G).over
        (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W) ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin n))) := by
  have hqcG : ((Scheme.Modules.pullback W.ι).obj G).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      W.ι.toLRSHom.toShHom G ‹G.IsQuasicoherent›
  have eG : (Scheme.Modules.pullback W.ι).obj G ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin n)) := pullbackIsoFreeOfOverIso G W _ eW
  have hπ : IsIso (Stacks.StrictTransform.π (W.ι ≫ q) (blowUpToBase J) (exceptionalIdeal J)
      ((Scheme.Modules.pullback W.ι).obj G)) :=
    isIso_strictTransformSheaf_quotient_of_flat_at_exceptional (W.ι ≫ q) J _
      fun x _ ↦ isFlatOverAt_of_iso_free (W.ι ≫ q) _ n eG x
  obtain ⟨j, hj, hjfst, hjsnd⟩ :
      ∃ j : (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).toScheme ⟶
          Limits.pullback (W.ι ≫ q) (blowUpToBase J), IsIso j ∧
        (j ≫ pullback.fst (W.ι ≫ q) (blowUpToBase J)) ≫ W.ι =
          (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι ≫ pullback.fst q (blowUpToBase J) ∧
        j ≫ pullback.snd (W.ι ≫ q) (blowUpToBase J) =
          (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι ≫ pullback.snd q (blowUpToBase J) := by
    refine ⟨(pullbackRestrictIsoRestrict (pullback.fst q (blowUpToBase J)) W).inv ≫
      (pullbackSymmetry (pullback.fst q (blowUpToBase J)) W.ι).hom ≫
      (pullbackRightPullbackFstIso q (blowUpToBase J) W.ι).hom, inferInstance, ?_, ?_⟩
    · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
        pullbackSymmetry_hom_comp_fst_assoc, ← pullback.condition,
        pullbackRestrictIsoRestrict_inv_fst_assoc]
    · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
        pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]
  have : IsIso j := hj
  have : IsOpenImmersion j := inferInstance
  have hset : (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι.base ⁻¹'
        Stacks.StrictTransform.exceptionalPreimage q (blowUpToBase J) (exceptionalIdeal J) =
      j.base ⁻¹' Stacks.StrictTransform.exceptionalPreimage (W.ι ≫ q) (blowUpToBase J)
        (exceptionalIdeal J) := by
    refine Set.ext fun x ↦ ?_
    have hx : (pullback.snd (W.ι ≫ q) (blowUpToBase J)).base (j.base x) =
        (pullback.snd q (blowUpToBase J)).base
          ((pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι.base x) :=
      congrArg (fun a ↦ a x) hjsnd
    change (pullback.snd q (blowUpToBase J)).base
        ((pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι.base x) ∈
          ((exceptionalIdeal J).support : Set (blowUp J)) ↔
      (pullback.snd (W.ι ≫ q) (blowUpToBase J)).base (j.base x) ∈
        ((exceptionalIdeal J).support : Set (blowUp J))
    rw [hx]
  have hmod : (Scheme.Modules.pullback
        ((pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι ≫ pullback.fst q (blowUpToBase J))).obj G ≅
      (Scheme.Modules.pullback (j ≫ pullback.fst (W.ι ≫ q) (blowUpToBase J))).obj
        ((Scheme.Modules.pullback W.ι).obj G) :=
    ((Scheme.Modules.pullbackComp (j ≫ pullback.fst (W.ι ≫ q) (blowUpToBase J)) W.ι).app G ≪≫
      (Scheme.Modules.pullbackCongr hjfst).app G).symm
  refine ⟨overIsoFreeOfPullbackIso _ _ _ ?_⟩
  refine Stacks.StrictTransform.pullbackSheafBlowUpIso q J G
    (pullback.fst q (blowUpToBase J) ⁻¹ᵁ W).ι ≪≫ ?_
  rw [hset]
  refine Stacks.SupportedQuotient.supportedSectionsCokernelIso _ hmod ≪≫ ?_
  refine (Stacks.StrictTransform.pullbackSheafBlowUpIso (W.ι ≫ q) J
    ((Scheme.Modules.pullback W.ι).obj G) j).symm ≪≫ ?_
  refine (Scheme.Modules.pullback j).mapIso (@asIso _ _ _ _ _ hπ).symm ≪≫ ?_
  refine (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.pullback (pullback.fst (W.ι ≫ q) (blowUpToBase J))).mapIso eG) ≪≫ ?_
  exact (Scheme.Modules.pullback j).mapIso (pullbackObjFreeIso _ _) ≪≫ pullbackObjFreeIso j _

/-! ### Freeness near the generic points of the fibres and one blowup -/

/-- **The first projection of an iterated base change carries generic points of fibres to
generic points of fibres.** If the fibre of `pr_{T'} : Y ×_T T' ⟶ T'` through `w` lies in the
closure of `w`, then the fibre of `q : Y ⟶ T` through the image of `w` lies in the closure of
that image.

A competitor `y` in the fibre of `q` has the same image in `T` as `pr_{T'} w`, so
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` lifts it to a point `v` of the base
change lying over `pr_{T'} w`; genericity gives `v ∈ closure {w}`, and continuity of the
projection gives `y ∈ closure {pr_Y w}`. -/
private theorem fibreGeneric_fst {Y T T' : Scheme.{u}} (q : Y ⟶ T) (c : T' ⟶ T)
    (w : Stacks.StrictTransform.baseChange q c)
    (hw : (pullback.snd q c).base ⁻¹' {(pullback.snd q c).base w} ⊆ closure {w}) :
    q.base ⁻¹' {q.base ((pullback.fst q c).base w)} ⊆
      closure {(pullback.fst q c).base w} := by
  intro y hy
  have hqy : q.base y = q.base ((pullback.fst q c).base w) := hy
  have hcond : q.base ((pullback.fst q c).base w) = c.base ((pullback.snd q c).base w) :=
    congrArg (fun a ↦ a w) (pullback.condition (f := q) (g := c))
  obtain ⟨v, hv₁, hv₂⟩ := Scheme.Pullback.exists_preimage_pullback y
    ((pullback.snd q c).base w) (hqy.trans hcond)
  rw [← hv₁]
  exact map_mem_closure (by fun_prop) (hw hv₂) (Set.mapsTo_singleton.2 rfl)

/-- **Freeness near the generic points of the fibres passes to the strict transform.** For `q`
flat and `G` quasi-coherent, if `G` is free of finite rank near the generic point of every fibre
of `q`, then the strict transform of `G` along the blowup of the base in any centre `J` is free
of finite rank near the generic point of every fibre of the projection to that blowup.

The two inputs are `AlgebraicGeometry.fibreGeneric_fst`, which produces the generic point of the
fibre of `q` downstairs, and
`AlgebraicGeometry.freeNear_strictTransformSheaf_of_over_iso_free`, which converts the
trivialisation found there into one upstairs. -/
theorem freeNearFibreGeneric_strictTransformSheaf {Y T : Scheme.{u}} (q : Y ⟶ T) [Flat q]
    (J : T.IdealSheafData) (G : Y.Modules) [G.IsQuasicoherent] (h : FreeNearFibreGeneric q G) :
    FreeNearFibreGeneric (pullback.snd q (blowUpToBase J))
      (Stacks.StrictTransform.sheaf q (blowUpToBase J) (exceptionalIdeal J) G) := by
  intro w hw
  obtain ⟨W, n, hW, ⟨eW⟩⟩ := h ((pullback.fst q (blowUpToBase J)).base w)
    (fibreGeneric_fst q (blowUpToBase J) w hw)
  exact ⟨pullback.fst q (blowUpToBase J) ⁻¹ᵁ W, n, hW,
    freeNear_strictTransformSheaf_of_over_iso_free q J G W n eW⟩

/-! ### Transport along isomorphisms -/

/-- **Freeness near the generic points of the fibres transports along isomorphisms** of the
source, of the target and of the module. The fibres correspond because the identification of the
targets is injective, the closures correspond because the identification of the sources is a
homeomorphism, and the witnessing open is carried over as the image open of the isomorphism. -/
theorem FreeNearFibreGeneric.transport {B B' T T' : Scheme.{u}} {p : B ⟶ T} {p' : B' ⟶ T'}
    (gB : B ≅ B') (gT : T ≅ T') (hcomm : gB.hom ≫ p' = p ≫ gT.hom) {M : B.Modules}
    {M' : B'.Modules} (eM : (Scheme.Modules.pullback gB.hom).obj M' ≅ M)
    (h : FreeNearFibreGeneric p M) : FreeNearFibreGeneric p' M' := by
  intro b' hb'
  have hinv : ∀ x : B', gB.hom.base (gB.inv.base x) = x :=
    fun x ↦ congrArg (fun a : B' ⟶ B' ↦ a x) gB.inv_hom_id
  have hinv' : ∀ x : B, gB.inv.base (gB.hom.base x) = x :=
    fun x ↦ congrArg (fun a : B ⟶ B ↦ a x) gB.hom_inv_id
  have ecomm : ∀ x : B, p'.base (gB.hom.base x) = gT.hom.base (p.base x) :=
    fun x ↦ congrArg (fun a : B ⟶ T' ↦ a x) hcomm
  have hgen : p.base ⁻¹' {p.base (gB.inv.base b')} ⊆ closure {gB.inv.base b'} := by
    intro y hy
    have hy' : p.base y = p.base (gB.inv.base b') := hy
    have h₁ : p'.base (gB.hom.base y) = p'.base b' := by
      rw [ecomm y, hy', ← ecomm (gB.inv.base b'), hinv b']
    have h₃ := map_mem_closure (f := gB.inv.base) (t := {gB.inv.base b'}) (by fun_prop)
      (hb' h₁) (Set.mapsTo_singleton.2 rfl)
    rwa [hinv' y] at h₃
  obtain ⟨W, n, hW, ⟨eW⟩⟩ := h (gB.inv.base b') hgen
  have hmem : b' ∈ (W.ι ≫ gB.hom).opensRange :=
    ⟨⟨gB.inv.base b', hW⟩, hinv b'⟩
  refine ⟨(W.ι ≫ gB.hom).opensRange, n, hmem,
    ⟨overOpensRangeIsoFree M' (W.ι ≫ gB.hom) _ ?_⟩⟩
  exact ((Scheme.Modules.pullbackComp W.ι gB.hom).app M').symm ≪≫
    (Scheme.Modules.pullback W.ι).mapIso eM ≪≫ pullbackIsoFreeOfOverIso M W _ eW

/-! ### Stability under composing with a second blowup -/

/-- **Freeness near the generic points of the fibres of the strict transform is stable under
composing with a second blowup.** This is the hypothesis "`P` is stable under strict transform"
of [Stacks, Remark 38.30.1] for the property `P` that the strict transform is free of finite rank
near the generic point of every fibre.

The hypotheses `hK` and `e` are exactly those of [Stacks, Tag 080I] part (1): the support of the
third centre `K` is the support of `I` together with the image of the support of `J`, and the
two-step blowup is identified with the blowup in `K` as an `S`-scheme. Granted them,
`Stacks.StrictTransform.strictTransformSheaf_comp_blowUp` identifies the strict transform in `K`
with the strict transform in `J` of the strict transform in `I`, and
`AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf` handles the latter. Geometric
integrality of `f` is not used; see the implementation notes. -/
theorem freeNearFibreGeneric_strictTransformSheaf_comp_blowUp {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [GeometricallyIntegral f] (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase K))
    (F : X.Modules) [F.IsQuasicoherent]
    (h : FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase I))
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase K))
      (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) := by
  have hqc : (Stacks.StrictTransform.sheaf f (blowUpToBase I)
      (exceptionalIdeal I) F).IsQuasicoherent := inferInstance
  have h₂ := freeNearFibreGeneric_strictTransformSheaf
    (pullback.snd f (blowUpToBase I)) J _ h
  obtain ⟨g, hg, hq, eQ, -⟩ :=
    Stacks.StrictTransform.strictTransformSheaf_comp_blowUp f I K J hK e F
  exact FreeNearFibreGeneric.transport g ((Over.forget S).mapIso e) hq eQ h₂

/-- **Enlarging the centre by a second centre pulled back from the base preserves freeness near
the generic points of the fibres of the strict transform.** This is the instance
`K = I * J` of `AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf_comp_blowUp`, whose
two hypotheses are discharged unconditionally by
`AlgebraicGeometry.supportSet_mul_eq_union_image_comap` and
`AlgebraicGeometry.blowUpMulIso`. -/
theorem freeNearFibreGeneric_strictTransformSheaf_mul {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [GeometricallyIntegral f] (I J : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (h : FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase I))
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase (I * J)))
      (Stacks.StrictTransform.sheaf f (blowUpToBase (I * J)) (exceptionalIdeal (I * J)) F) :=
  freeNearFibreGeneric_strictTransformSheaf_comp_blowUp f I (I * J)
    (J.comap (blowUpToBase I)) (supportSet_mul_eq_union_image_comap I J) (blowUpMulIso I J) F h

end AlgebraicGeometry

end
