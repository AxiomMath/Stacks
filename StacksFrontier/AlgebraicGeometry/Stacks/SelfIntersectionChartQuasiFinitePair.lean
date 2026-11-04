module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreQuasiFiniteAt
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartDoubleFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# The pair of legs of a charted self-intersection is quasi-finite (Stacks 0CPL)

Let `q : 𝒴₀ ⟶ Spec(k)` be a locally quasi-finite 1-morphism of algebraic stacks over `S` to a
field-valued point of the base, let `p : U ⟶ 𝒴₀` be a 1-morphism out of the algebraic stack
represented by a scheme `U` of the site, let `F` represent the apex of the canonical 2-fibre
product square `U ×_{𝒴₀} U` and let `c : h_R ⟶ F` be an étale chart of `F` by a scheme `R` of the
site. Write `a` and `b` for the two legs `AlgebraicGeometry.Stack.chartLeg` read as morphisms of
schemes `R ⟶ U`.

Then the *pair* `(a, b) : R ⟶ U ×_{Spec k} U` is a **locally quasi-finite** morphism of schemes,
and consequently the double fibre of `(a, b)` is discrete at every point of `R` whose image under
`b` is closed in `U` — which is the hypothesis `hiso` of
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`, the slicing step
of the chart construction of **Stacks 06MF**. This closes the input that
`StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartDoubleFibre` carried.

The pair factors as an étale chart followed by the comparison 1-morphism
`U ×_{𝒴₀} U ⟶ U ×_{Spec k} U`, which is locally quasi-finite by **Stacks 0CPL / 050H part (5)**:
it is a base change of the relative diagonal `Δ_{𝒴₀/Spec(k)}`, which is locally quasi-finite
because `q` is quasi-DM.

## Main results

* `AlgebraicGeometry.isIsolatedPoint_asFiber_of_isPullback`: the scheme-level conclusion of
  `StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartDoubleFibre`, with the fibre product
  `U ×_T U` presented by an arbitrary `CategoryTheory.IsPullback` square rather than by
  `CategoryTheory.Limits.pullback`.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProduct_sitePullback`: the apex of
  the canonical 2-fibre product of `p ≫ q` with itself is represented by the presheaf of the
  scheme-level fibre product `U ×_{Spec k} U`, read in the site.
* `AlgebraicGeometry.Stack.locallyQuasiFinite_pair_chartLeg`: the pair of the two legs is a
  locally quasi-finite — and locally of finite type — morphism of schemes into a fibre product
  `U ×_{Spec k} U`.
* `AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_chartLeg_twoFibreProductSquare`: the
  hypothesis `hiso` of **Stacks 06MF**, with nothing carried.
* `AlgebraicGeometry.isClosed_asFiber_of_isPullback_pair` and
  `AlgebraicGeometry.Stack.isClosed_asFiber_chartLeg_twoFibreProductSquare`: the point of the
  relation is closed in the fibre of the second leg, which is the input the quasi-finiteness
  conjunct of the slicing step of **Stacks 06MF** carries.

## Implementation notes

Three identifications are needed, and each is an existing construction read at this cospan.

The square of represented algebraic stacks over the scheme-level fibre product
`U ×_{Spec k} U` is a 2-fibre product of `(schemeStackMap m, schemeStackMap m)`, where `m` is the
morphism of the site underlying `p ≫ q`
(`AlgebraicGeometry.Stack.isTwoFibreProduct_sitePullbackStackSquare`). Its cospan is 2-isomorphic
to `(p ≫ q, p ≫ q)` by `AlgebraicGeometry.Stack.schemeStackMapIso`, and
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexFst` and `…_reindexSnd` move the square
across that 2-isomorphism without changing its apex or its projections. The comparison with the
*canonical* 2-fibre product is then an equivalence
(`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProductAlgebraicStacks`), which
`CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` and
`AlgebraicGeometry.Stack.representedChart` turn into the representation by `h_{U ×_{Spec k} U}`.

That the two projections of that representation really are the two projections of a fibre product
of *schemes* does not need to be checked by hand:
`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare` makes the morphisms of
representing presheaves a pullback square, the Yoneda embedding is fully faithful so reflects it
into the site, and `AlgebraicGeometry.BigFppfOver.toScheme` preserves it.

Finally the compatibility of `AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` with the two
projections — the equation that identifies the two components of the pair with the two
`AlgebraicGeometry.Stack.chartLeg` — holds by `rfl`: both sides are the same functor, as
`CategoryTheory.TwoFibreProductOver.mapBase_comp_fst` records one level down.

Local quasi-finiteness is transported from 1-morphisms to the morphism of representing presheaves
by `AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty` (**Stacks 04XC**) and
read on the étale chart by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` (**Stacks 03MJ**) at the property
`LocallyOfFiniteType ⊓ LocallyQuasiFinite`, which is étale local on the source and target.

No `@[stacks]` attribute is claimed: **Stacks 050H** part (5) is registered on
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM`, and this is a
step of **Stacks 06MF**.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

/-- The double fibre `b.fiberι (b r₀) ≫ a` of a quasi-finite pair is locally quasi-finite and
locally of finite type when `b r₀` is a closed point. -/
private theorem locallyQuasiFinite_fiberι_comp_of_isPullback_of_isClosed
    {R U T Wsch : Scheme.{u}} (m : U ⟶ T) [LocallyOfFiniteType m] (a b : R ⟶ U)
    {pr₁ pr₂ : Wsch ⟶ U} (hW : IsPullback pr₁ pr₂ m m)
    (e : R ⟶ Wsch) (he₁ : e ≫ pr₁ = a) (he₂ : e ≫ pr₂ = b)
    (helqf : LocallyQuasiFinite e) (helft : LocallyOfFiniteType e)
    (r₀ : R) (hclosed : IsClosed ({b r₀} : Set U)) :
    LocallyQuasiFinite (b.fiberι (b r₀) ≫ a) ∧ LocallyOfFiniteType (b.fiberι (b r₀) ≫ a) :=
  have _ : IsClosedImmersion (U.fromSpecResidueField (b r₀)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  locallyQuasiFinite_fiberι_comp_of_isPullback m a b hW e he₁ he₂ helqf helft (b r₀) inferInstance

/-- **A quasi-finite pair has discrete double fibres, at a recognised fibre product.** This is
`AlgebraicGeometry.isIsolatedPoint_asFiber_of_locallyQuasiFinite_pair` with the fibre product
`U ×_T U` given by an arbitrary `CategoryTheory.IsPullback` square and the pair given as a
morphism `e` into its apex, which is the form in which the stack-level construction produces
them. -/
theorem isIsolatedPoint_asFiber_of_isPullback
    {R U T Wsch : Scheme.{u}} (m : U ⟶ T) [LocallyOfFiniteType m] (a b : R ⟶ U)
    {pr₁ pr₂ : Wsch ⟶ U} (hW : IsPullback pr₁ pr₂ m m)
    (e : R ⟶ Wsch) (he₁ : e ≫ pr₁ = a) (he₂ : e ≫ pr₂ = b)
    (helqf : LocallyQuasiFinite e) (helft : LocallyOfFiniteType e)
    (r₀ : R) (hclosed : IsClosed ({b r₀} : Set U)) :
    IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀)) := by
  obtain ⟨hlqf, hlft⟩ := locallyQuasiFinite_fiberι_comp_of_isPullback_of_isClosed m a b hW e he₁
    he₂ helqf helft r₀ hclosed
  let := hlft
  exact ((quasiFiniteAt_tfae (b.fiberι (b r₀) ≫ a) (b.asFiber r₀)).out 1 2).mp
    ((forall_quasiFiniteAt_iff _).mpr ⟨hlft, hlqf⟩ _)

/-- **A point of a quasi-finite pair whose two images are closed points is closed in the fibre
of either leg.** This is
`Stacks.AlgebraicGeometry.isClosed_asFiber_of_locallyQuasiFinite_fiberι_comp` with the double
fibre's quasi-finiteness supplied, exactly as in
`AlgebraicGeometry.isIsolatedPoint_asFiber_of_isPullback`, by
`AlgebraicGeometry.locallyQuasiFinite_fiberι_comp_of_isPullback`.

This is the input that the quasi-finiteness conjunct of
`AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` — the slicing step of
**Stacks 06MF** — carries: the slice is quasi-finite over `U` along `b` at the sliced point as
soon as that point is closed in its fibre under `b`. -/
theorem isClosed_asFiber_of_isPullback_pair
    {R U T Wsch : Scheme.{u}} (m : U ⟶ T) [LocallyOfFiniteType m] (a b : R ⟶ U)
    {pr₁ pr₂ : Wsch ⟶ U} (hW : IsPullback pr₁ pr₂ m m)
    (e : R ⟶ Wsch) (he₁ : e ≫ pr₁ = a) (he₂ : e ≫ pr₂ = b)
    (helqf : LocallyQuasiFinite e) (helft : LocallyOfFiniteType e)
    (r₀ : R) (hclosedb : IsClosed ({b r₀} : Set U))
    (hcloseda : IsClosed ({a r₀} : Set U)) :
    IsClosed ({b.asFiber r₀} : Set (b.fiber (b r₀))) := by
  obtain ⟨hlqf, hlft⟩ := locallyQuasiFinite_fiberι_comp_of_isPullback_of_isClosed m a b hW e he₁
    he₂ helqf helft r₀ hclosedb
  exact Stacks.AlgebraicGeometry.isClosed_asFiber_of_locallyQuasiFinite_fiberι_comp a b r₀
    hlqf hlft hcloseda

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
  (q : 𝒴₀ ⟶ schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
  (U : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS U ⟶ 𝒴₀)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS p p).pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

/-- **The canonical 2-fibre product of `p ≫ q` with itself is represented by the scheme-level
fibre product.** The apex of `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` at
the cospan `(p ≫ q, p ≫ q)` is represented by the presheaf of
`AlgebraicGeometry.Stack.sitePullbackObj`, the fibre product of the underlying schemes read as an
object of the site.

The square of represented stacks over that object is a 2-fibre product of
`(schemeStackMap m, schemeStackMap m)` for `m` the morphism of the site underlying `p ≫ q`; both
legs are reindexed across `AlgebraicGeometry.Stack.schemeStackMapIso` to the cospan
`(p ≫ q, p ≫ q)`, the comparison with the canonical square is an equivalence, and
`CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` composed with
`AlgebraicGeometry.Stack.representedChart` is the representation. -/
theorem nonempty_equivalenceOver_twoFibreProduct_sitePullback :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS (p ≫ q) (p ≫ q)).val.val.p
      (presheafOfCategories (yoneda.obj (sitePullbackObj B S hS
        (siteMap B S hS (p ≫ q)) (siteMap B S hS (p ≫ q))) ⋙ typeToCat)).p) := by
  classical
  set m := siteMap B S hS (p ≫ q)
  let θ : schemeStackMap.{u, w} B S hS m ≅ p ≫ q := (schemeStackMapIso B S hS (p ≫ q)).symm
  let Wsq := ((schemeStackSquare.{u, w} B S hS
    (isPullback_sitePullback B S hS m m).w).reindexFst θ).reindexSnd θ
  have hWsq : Bicategory.IsTwoFibreProduct Wsq :=
    Bicategory.isTwoFibreProduct_reindexSnd θ (Bicategory.isTwoFibreProduct_reindexFst θ
      (isTwoFibreProduct_sitePullbackStackSquare.{u, w} B S hS m m))
  let a₀ : Bicategory.TwoCommSq.PreHom
      (AlgebraicStacks.twoFibreProductSquare B S hS (p ≫ q) (p ≫ q)) Wsq :=
    Quotient.out (hWsq.from _)
  exact (StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (AlgebraicStacks.twoFibreProductSquare B S hS (p ≫ q) (p ≫ q)).pt.val.property
    Wsq.pt.val.property
    (CatFiberedInGroupoids.homFunctor a₀.hom.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p a₀.hom.hom)
    (isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (p ≫ q) (p ≫ q))
      hWsq a₀)).map
    fun E => E.trans (representedChart B S hS _)

/-- **The pair of the two legs of a charted self-intersection is locally quasi-finite.** In the
setting of **Stacks 06MF** — `q : 𝒴₀ ⟶ Spec(k)` locally quasi-finite, `p : U ⟶ 𝒴₀` a 1-morphism
out of a represented algebraic stack, `F` representing the apex of the canonical 2-fibre product
square `U ×_{𝒴₀} U` and `c : h_R ⟶ F` an étale chart — there are a fibre product
`U ×_{Spec k} U` of schemes and a morphism `e : R ⟶ U ×_{Spec k} U` whose two components are the
two legs `AlgebraicGeometry.Stack.chartLeg`, and `e` is locally quasi-finite and locally of
finite type.

The comparison 1-morphism `U ×_{𝒴₀} U ⟶ U ×_{Spec k} U` is locally quasi-finite in the sense of
**Stacks 04XB** by **Stacks 050H** part (5), since `q` is quasi-DM; **Stacks 04XC** reads that on
the morphism of representing presheaves, composition with the étale chart keeps it, and
**Stacks 03MJ** reads the result on the morphism of schemes. The identification of the target
with a fibre product of schemes, and of the two components with the two legs, is explained in the
module's implementation notes. -/
theorem locallyQuasiFinite_pair_chartLeg
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    ∃ (Wsch : Scheme.{u}) (pr₁ pr₂ : Wsch ⟶ (BigFppfOver.toScheme B S hS).obj U)
      (_ : IsPullback pr₁ pr₂ ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q)))
        ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q))))
      (e : (BigFppfOver.toScheme B S hS).obj R ⟶ Wsch),
      e ≫ pr₁ = (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).fst) ∧
        e ≫ pr₂ = (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) ∧
        LocallyQuasiFinite e ∧ LocallyOfFiniteType e := by
  classical
  obtain ⟨eG⟩ := nonempty_equivalenceOver_twoFibreProduct_sitePullback B S hS k hk toBase q U p
  set W := sitePullbackObj B S hS (siteMap B S hS (p ≫ q)) (siteMap B S hS (p ≫ q))
  set 𝒵 := AlgebraicStacks.twoFibreProduct B S hS (p ≫ q) (p ≫ q)
  set Csq := AlgebraicStacks.twoFibreProductSquare B S hS (p ≫ q) (p ≫ q)
  set rmfst := representingMap B S hS 𝒵.val (schemeStack.{u, w} B S hS U).val
    (yoneda.obj W) (yoneda.obj U) eG (representedChart B S hS U) Csq.fst.hom with hrmfst
  set rmsnd := representingMap B S hS 𝒵.val (schemeStack.{u, w} B S hS U).val
    (yoneda.obj W) (yoneda.obj U) eG (representedChart B S hS U) Csq.snd.hom with hrmsnd
  have hpbpre : IsPullback rmfst rmsnd (yoneda.map (siteMap B S hS (p ≫ q)))
      (yoneda.map (siteMap B S hS (p ≫ q))) := by
    let _hfib : (twoFibreProductStructureFunctor B S hS (schemeStack.{u, w} B S hS U).val
        (schemeStack.{u, w} B S hS U).val
        (schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))).val
        (p ≫ q).hom (p ≫ q).hom).IsFibered :=
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (p ≫ q).hom (p ≫ q).hom).pt.property.isFibered
    rw [← representingMap_representedChart_eq_yoneda_map_siteMap B S hS (p ≫ q), hrmfst, hrmsnd]
    exact isPullback_representingMap_twoFibreProductSquare B S hS
      (schemeStack.{u, w} B S hS U).val (schemeStack.{u, w} B S hS U).val
      (schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))).val
      (yoneda.obj U) (yoneda.obj U)
      (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (representedChart B S hS U) (representedChart B S hS U)
      (representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (p ≫ q).hom (p ≫ q).hom (yoneda.obj W) eG
  have hpbsite : IsPullback (yoneda.preimage rmfst) (yoneda.preimage rmsnd)
      (siteMap B S hS (p ≫ q)) (siteMap B S hS (p ≫ q)) :=
    IsPullback.of_map_of_faithful yoneda
      (by rwa [yoneda.map_preimage, yoneda.map_preimage])
  set rmMB := representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS p p).pt.val
    𝒵.val F (yoneda.obj W) eF eG (AlgebraicStacks.mapBase B S hS p p q).hom with hrmMB
  have hbar : Space.IsLocallyQuasiFinite B S hS (c ≫ rmMB) :=
    Space.isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS R) hF
      (isAlgebraicSpace_yoneda B S hS W) c _
      (Space.isLocallyQuasiFinite_of_isEtale B S hS hF
        (Space.isEtale_of_presheaf_etale B S hS hc))
      (prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS
        (Space.locallyQuasiFiniteProperty B S hS)
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒴₀.val
          (schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))).val q.hom)
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS q)
        ((AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS q).mp hq.1)
        𝒵.val (AlgebraicStacks.mapCospan B S hS p p q).hom
        (AlgebraicStacks.mapBaseSquare B S hS p p q)
        (AlgebraicStacks.isTwoFibreProduct_mapBaseSquare B S hS p p q)
        F (yoneda.obj W) hF (isAlgebraicSpace_yoneda B S hS W) eF eG)
  have hprops : ((@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} :
      MorphismProperty Scheme.{u})) ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (c ≫ rmMB))) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      (P := (@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite
      (yoneda.preimage (c ≫ rmMB))).1
      (by rwa [yoneda.map_preimage])
  refine ⟨_, _, _, Functor.map_isPullback (BigFppfOver.toScheme B S hS) hpbsite,
    (BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ rmMB)), ?_, ?_,
    hprops.2, hprops.1⟩ <;>
  · rw [← Functor.map_comp]
    refine congrArg (BigFppfOver.toScheme B S hS).map (yoneda.map_injective ?_)
    rw [Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage, Category.assoc, hrmMB]
    simp only [hrmfst, hrmsnd]
    rw [← representingMap_comp B S hS F (yoneda.obj W) (yoneda.obj U) eF eG
      (representedChart B S hS U) (AlgebraicStacks.mapBase B S hS p p q).hom]
    exact (yoneda.map_preimage _).symm

/-- The morphism of schemes underlying `p ≫ q` is locally of finite type when `p` is smooth and
`q` is locally quasi-finite. -/
private theorem locallyOfFiniteType_map_siteMap_comp_of_isSmooth
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (hp : AlgebraicStacks.IsSmooth B S hS p) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q))) :=
  locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S hS (p ≫ q)
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS p q
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS p hp) hq.2.1)

/-- **The double fibre of a charted self-intersection is discrete at the identity point.** Let
`q : 𝒴₀ ⟶ Spec(k)` be a locally quasi-finite 1-morphism to a field-valued point of the base, let
`p : U ⟶ 𝒴₀` be a smooth 1-morphism out of the algebraic stack represented by a scheme `U` of the
site, let `F` represent the apex of the canonical 2-fibre product square `U ×_{𝒴₀} U` and let
`c : h_R ⟶ F` be an étale chart of `F` by a scheme `R` of the site. Write `a` and `b` for the two
legs `AlgebraicGeometry.Stack.chartLeg` read as morphisms of schemes `R ⟶ U`. Then every point
`r₀` of `R` whose image `b r₀` is closed in `U` — for instance the identity point of
`AlgebraicGeometry.Stack.exists_point_chartLeg_eq` over a closed point of `U` — is an isolated
point of the double fibre, the scheme-theoretic fibre over `a r₀` of
`b.fiber (b r₀) ⟶ R ⟶ U`.

This is the hypothesis `hiso` of
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`, the slicing step
of the chart construction of **Stacks 06MF**, with nothing carried: the pair of legs is locally
quasi-finite by `AlgebraicGeometry.Stack.locallyQuasiFinite_pair_chartLeg`, and smoothness of `p`
enters only to make `U ⟶ Spec(k)` locally of finite type, through **Stacks 06FT** and
`AlgebraicGeometry.Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType`. -/
theorem isIsolatedPoint_asFiber_chartLeg_twoFibreProductSquare
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (hp : AlgebraicStacks.IsSmooth B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
      (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsIsolatedPoint
      ((((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
            (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
            (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).fiberι
          ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
            (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
            (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀) ≫
        (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).fst)).asFiber
        (((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).asFiber r₀)) := by
  have := locallyOfFiniteType_map_siteMap_comp_of_isSmooth B S hS k hk toBase q U p hq hp
  obtain ⟨Wsch, pr₁, pr₂, hpb, e, he₁, he₂, helqf, helft⟩ :=
    locallyQuasiFinite_pair_chartLeg B S hS k hk toBase q U p F eF R c hq hF hc
  exact isIsolatedPoint_asFiber_of_isPullback
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q))) _ _ hpb e he₁ he₂ helqf helft
    r₀ hclosed

/-- **A point of a charted self-intersection whose two images are closed is closed in the fibre
of the second leg.** Same data as
`AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_chartLeg_twoFibreProductSquare`, with both
images of `r₀` in `U` assumed closed; the conclusion is the input the quasi-finiteness conjunct
of `AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` carries, so this is what makes
the quasi-finiteness datum of the chart of **Stacks 06MF** unconditional at the identity point,
where the two images coincide and are the closed point of **Stacks 06FX**. -/
theorem isClosed_asFiber_chartLeg_twoFibreProductSquare
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (hp : AlgebraicStacks.IsSmooth B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hclosedb : IsClosed ({(BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
      (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hcloseda : IsClosed ({(BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
      (twoFibreProductSquareAlgebraicStacks B S hS p p).fst) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsClosed ({((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).asFiber r₀} :
      Set (((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).fiber
        ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀))) := by
  have := locallyOfFiniteType_map_siteMap_comp_of_isSmooth B S hS k hk toBase q U p hq hp
  obtain ⟨Wsch, pr₁, pr₂, hpb, e, he₁, he₂, helqf, helft⟩ :=
    locallyQuasiFinite_pair_chartLeg B S hS k hk toBase q U p F eF R c hq hF hc
  exact isClosed_asFiber_of_isPullback_pair
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q))) _ _ hpb e he₁ he₂ helqf helft
    r₀ hclosedb hcloseda

end Stack

end AlgebraicGeometry

end
