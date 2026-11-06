module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RelationSlice
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverFieldPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartIdentityPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SitePullbackStackSquare

/-!
# The double fibre of a charted self-intersection is discrete at the identity point (Stacks 06MF)

Let `a, b : R ⟶ U` be the two legs `AlgebraicGeometry.Stack.chartLeg` of a charted
self-intersection `U ×_𝒴₀ U` of a smooth chart `p : U ⟶ 𝒴₀` of an algebraic stack which is
locally quasi-finite over a field-valued point `Spec(k) ⟶ S` of the base, and let `r₀` be the
identity point of `AlgebraicGeometry.Stack.exists_point_chartLeg_eq` over a point `u` of `U`
which is closed in `U`. The slicing step of **Stacks 06MF**
(`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`) asks for `r₀` to
be an **isolated point of the double fibre** — of the scheme-theoretic fibre over `a r₀` of
`b.fiber (b r₀) ⟶ R ⟶ U`. This file produces that hypothesis from one input: that the *pair*
`(a, b) : R ⟶ U ×_{Spec k} U` is a locally quasi-finite morphism of schemes.

The reduction is the whole content of the file, and it is purely scheme-theoretic. Write
`m : U ⟶ Spec(k)` for the structure morphism and `v : Spec κ(u) ⟶ U` for the residue-field point
of `U` at `u`. Then

* `b.fiber u` is the base change of the pair `(a, b)` along
  `U ×_{Spec k} Spec κ(u) ⟶ U ×_{Spec k} U`,
  so the morphism `b.fiber u ⟶ U ×_{Spec k} Spec κ(u)` it induces is locally quasi-finite; and
* `U ×_{Spec k} Spec κ(u) ⟶ U` is the base change of `v ≫ m`, which is locally quasi-finite
  because its source has one point.

Their composite is `b.fiberι u ≫ a`, so that morphism is locally quasi-finite, and
**Stacks 01TH** turns local quasi-finiteness at `r₀` into isolation of `r₀` in the double fibre.
The point `u` is used only through the closedness that makes `v` locally of finite type.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_of_subsingleton_source`: a morphism of schemes locally of
  finite type whose source has at most one point is locally quasi-finite.
* `AlgebraicGeometry.locallyQuasiFinite_fiberι_comp_of_isPullback`: the two base-change steps
  above, at an arbitrary fibre product `U ×_T U` recognised by
  `CategoryTheory.IsPullback`.
* `AlgebraicGeometry.isIsolatedPoint_asFiber_of_locallyQuasiFinite_pair`: the scheme-level
  statement — if `(a, b) : R ⟶ U ×_T U` is locally quasi-finite and `b r₀` is closed in `U`, then
  `r₀` is an isolated point of the double fibre.
* `AlgebraicGeometry.Stack.chartLeg_comp_siteMap_eq` and
  `AlgebraicGeometry.Stack.toScheme_chartLeg_comp_siteMap_eq`: the two legs of a charted
  self-intersection agree after composing with the morphism to the field-valued point, so that
  the pair `(a, b)` is defined.
* `AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_chartLeg`: the statement in the setting of
  **Stacks 06MF**, in the exact shape
  `AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth` consumes.

## Implementation notes

The scheme-level step is written with `CategoryTheory.IsPullback` squares rather than with
`CategoryTheory.Limits.pullback` and comparison isomorphisms: the base change of the pair along
`U ×_T Spec κ(u) ⟶ U ×_T U` is obtained from
`CategoryTheory.IsPullback.of_bot` applied to the fibre square
`AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField` of `b` and to the defining square
of `U ×_T Spec κ(u) = (U ×_T U) ×_U Spec κ(u)`, and no isomorphism of schemes is ever named.

Local quasi-finiteness of `v ≫ m` is free: `Spec κ(u)` has one point, so every fibre of a
morphism out of it is discrete, which is
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton` once the morphism is
known to be locally of finite type. That is where closedness of `u` enters, through
`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`; no Nullstellensatz is needed, and
the residue field is never compared with `k`.

That the two legs agree over `Spec(k)` is the square's own filler read through
**Stacks 04SW**: `AlgebraicGeometry.Stack.representingMap_congr_twoIso` turns the 2-isomorphism
`P.fst ≫ p ≫ q ≅ P.snd ≫ p ≫ q` into an equality of morphisms of representing presheaves,
and `AlgebraicGeometry.Stack.representingMap_representedChart_eq_yoneda_map_siteMap` reads that
equality through the Yoneda embedding, exactly as in
`AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint`.

Local quasi-finiteness of the pair `(a, b)` is a hypothesis here and is discharged in
`StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartQuasiFinitePair`, where it is
**Stacks 0CPL / 050H part (5)** for the comparison `U ×_{𝒴₀} U ⟶ U ×_{Spec k} U` —
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM` at
`f = g = p` and `h = q` — composed with the étale chart `c`.

No `@[stacks]` attribute is claimed: this is a step of **Stacks 06MF**, not a tag of its own.

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes out of a one-point scheme is locally quasi-finite.** For a morphism
locally of finite type, local quasi-finiteness is discreteness of every set-theoretic fibre
(**Stacks 01TH**), and a subset of a space with at most one point is discrete. -/
theorem locallyQuasiFinite_of_subsingleton_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton X] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro y
  rw [isDiscrete_iff_discreteTopology]
  infer_instance

/-- **The fibre of one leg, read along the other, is locally quasi-finite.** Let `a, b : R ⟶ U`
be two morphisms of schemes over `m : U ⟶ T`, assembled into a morphism `e : R ⟶ U ×_T U` to a
fibre product recognised by `hW`, and let `u` be a point of `U`. If `e` is locally quasi-finite
and locally of finite type, and the residue-field point `Spec κ(u) ⟶ U ⟶ T` is locally of finite
type, then `b.fiberι u ≫ a : b.fiber u ⟶ U` is locally quasi-finite and locally of finite type.

The morphism factors through `U ×_T Spec κ(u)`. The first factor is the base change of `e` along
`U ×_T Spec κ(u) ⟶ U ×_T U`, by `CategoryTheory.IsPullback.of_bot` applied to the fibre square of
`b` and to the defining square of `U ×_T Spec κ(u) = (U ×_T U) ×_U Spec κ(u)`; the second is the
base change of `Spec κ(u) ⟶ T` along `m`, by pasting those same two squares. -/
theorem locallyQuasiFinite_fiberι_comp_of_isPullback
    {R U T Wsch : Scheme.{u}} (m : U ⟶ T) (a b : R ⟶ U)
    {pr₁ pr₂ : Wsch ⟶ U} (hW : IsPullback pr₁ pr₂ m m)
    (e : R ⟶ Wsch) (he₁ : e ≫ pr₁ = a) (he₂ : e ≫ pr₂ = b)
    (helqf : LocallyQuasiFinite e) (helft : LocallyOfFiniteType e)
    (u : U) (hvlft : LocallyOfFiniteType (U.fromSpecResidueField u ≫ m)) :
    LocallyQuasiFinite (b.fiberι u ≫ a) ∧ LocallyOfFiniteType (b.fiberι u ≫ a) := by
  have hvlqf : LocallyQuasiFinite (U.fromSpecResidueField u ≫ m) := by
    have := hvlft
    exact locallyQuasiFinite_of_subsingleton_source _
  have hS2 : IsPullback (pullback.fst pr₂ (U.fromSpecResidueField u))
      (pullback.snd pr₂ (U.fromSpecResidueField u)) pr₂ (U.fromSpecResidueField u) :=
    IsPullback.of_hasPullback _ _
  have hZbig : IsPullback (pullback.snd pr₂ (U.fromSpecResidueField u))
      (pullback.fst pr₂ (U.fromSpecResidueField u) ≫ pr₁)
      (U.fromSpecResidueField u ≫ m) m := hS2.flip.paste_vert hW.flip
  have hfac : (b.fiberι u ≫ e) ≫ pr₂ =
      b.fiberToSpecResidueField u ≫ U.fromSpecResidueField u := by
    rw [Category.assoc, he₂]
    exact b.fiber_fac u
  have hδκ : pullback.lift (b.fiberι u ≫ e) (b.fiberToSpecResidueField u) hfac ≫
      pullback.fst pr₂ (U.fromSpecResidueField u) = b.fiberι u ≫ e := pullback.lift_fst _ _ _
  have hδz : pullback.lift (b.fiberι u ≫ e) (b.fiberToSpecResidueField u) hfac ≫
      pullback.snd pr₂ (U.fromSpecResidueField u) = b.fiberToSpecResidueField u :=
    pullback.lift_snd _ _ _
  have hTop : IsPullback (b.fiberι u)
      (pullback.lift (b.fiberι u ≫ e) (b.fiberToSpecResidueField u) hfac) e
      (pullback.fst pr₂ (U.fromSpecResidueField u)) := by
    refine IsPullback.of_bot ?_ hδκ.symm hS2
    rw [hδz, he₂]
    exact isPullback_fiberι_fiberToSpecResidueField b u
  have heq : b.fiberι u ≫ a =
      pullback.lift (b.fiberι u ≫ e) (b.fiberToSpecResidueField u) hfac ≫
        (pullback.fst pr₂ (U.fromSpecResidueField u) ≫ pr₁) := by
    rw [← Category.assoc, hδκ, Category.assoc, he₁]
  rw [heq]
  exact ⟨MorphismProperty.IsStableUnderComposition.comp_mem _ _
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hTop helqf)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hZbig hvlqf),
    MorphismProperty.IsStableUnderComposition.comp_mem _ _
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hTop helft)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hZbig hvlft)⟩

/-- **A quasi-finite pair has discrete double fibres.** Let `a, b : R ⟶ U` be two morphisms of
schemes which agree after composing with a morphism `m : U ⟶ T` locally of finite type, let `a`
be locally of finite type, and let the pair `(a, b) : R ⟶ U ×_T U` be locally quasi-finite. Then
for every point `r₀` of `R` whose image `b r₀` is closed in `U`, the point `r₀` is an isolated
point of the double fibre: of the scheme-theoretic fibre over `a r₀` of
`b.fiber (b r₀) ⟶ R ⟶ U`.

This is the hypothesis `hiso` of
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`.  Closedness of
`b r₀` is used only to make `Spec κ(b r₀) ⟶ U` a closed immersion, hence locally of finite type,
which is what
`AlgebraicGeometry.locallyQuasiFinite_fiberι_comp_of_isPullback` asks of the residue-field point;
**Stacks 01TH** then converts local quasi-finiteness at `r₀` into isolation in the fibre. -/
theorem isIsolatedPoint_asFiber_of_locallyQuasiFinite_pair
    {R U T : Scheme.{u}} (m : U ⟶ T) [LocallyOfFiniteType m]
    (a b : R ⟶ U) [LocallyOfFiniteType a] (hab : a ≫ m = b ≫ m)
    (hpair : LocallyQuasiFinite (pullback.lift a b hab : R ⟶ pullback m m))
    (r₀ : R) (hclosed : IsClosed ({b r₀} : Set U)) :
    IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀)) := by
  have he₁ : (pullback.lift a b hab : R ⟶ pullback m m) ≫ pullback.fst m m = a :=
    pullback.lift_fst _ _ _
  have he₂ : (pullback.lift a b hab : R ⟶ pullback m m) ≫ pullback.snd m m = b :=
    pullback.lift_snd _ _ _
  have helft : LocallyOfFiniteType (pullback.lift a b hab : R ⟶ pullback m m) := by
    refine LocallyOfFiniteType.of_comp (g := pullback.fst m m) ?_
    rw [he₁]
    infer_instance
  have _ : IsClosedImmersion (U.fromSpecResidueField (b r₀)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  have hvlft : LocallyOfFiniteType (U.fromSpecResidueField (b r₀) ≫ m) := inferInstance
  obtain ⟨hlqf, hlft⟩ := locallyQuasiFinite_fiberι_comp_of_isPullback m a b
    (IsPullback.of_hasPullback m m) (pullback.lift a b hab) he₁ he₂ hpair helft (b r₀) hvlft
  let := hlft
  exact ((quasiFiniteAt_tfae (b.fiberι (b r₀) ≫ a) (b.asFiber r₀)).out 1 2).mp
    ((forall_quasiFiniteAt_iff _).mpr ⟨hlft, hlqf⟩ _)

namespace Stack

universe w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
  (q : 𝒴₀ ⟶ schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
  (U : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS U ⟶ 𝒴₀)
  (P : Bicategory.TwoCommSq p p)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

/-- **The two legs of a charted self-intersection agree over the field-valued point.** For a
2-commutative square `P` over the cospan `(p, p)` with `p : U ⟶ 𝒴₀` and a chart `c : h_R ⟶ F` of
its apex, the two morphisms of the site `AlgebraicGeometry.Stack.chartLeg … P.fst` and
`… P.snd` become equal after composing with the morphism of the site underlying `p ≫ q`.

The square's filler gives a 2-isomorphism `P.fst ≫ p ≫ q ≅ P.snd ≫ p ≫ q`, which
`AlgebraicGeometry.Stack.representingMap_congr_twoIso` turns into an equality of morphisms of
representing presheaves;
`AlgebraicGeometry.Stack.representingMap_representedChart_eq_yoneda_map_siteMap`
identifies the morphism of representing presheaves of `p ≫ q` with the Yoneda image of
`AlgebraicGeometry.Stack.siteMap`, and the Yoneda embedding is faithful. -/
theorem chartLeg_comp_siteMap_eq :
    chartLeg B S hS U p P F eF R c P.fst ≫ siteMap B S hS (p ≫ q) =
      chartLeg B S hS U p P F eF R c P.snd ≫ siteMap B S hS (p ≫ q) := by
  refine yoneda.map_injective ?_
  have hiso : P.fst.hom ≫ (p ≫ q).hom ≅ P.snd.hom ≫ (p ≫ q).hom :=
    (Bicategory.associator P.fst.hom p.hom q.hom).symm ≪≫
      Bicategory.whiskerRightIso P.underlying.iso q.hom ≪≫
      Bicategory.associator P.snd.hom p.hom q.hom
  have hpre : ∀ leg : P.pt ⟶ schemeStack.{u, w} B S hS U,
      yoneda.map (chartLeg B S hS U p P F eF R c leg) =
        c ≫ representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F (yoneda.obj U)
          eF (representedChart B S hS U) leg.hom := fun leg => yoneda.map_preimage _
  rw [Functor.map_comp, Functor.map_comp, hpre, hpre,
    ← representingMap_representedChart_eq_yoneda_map_siteMap B S hS (p ≫ q),
    Category.assoc, Category.assoc, ← representingMap_comp, ← representingMap_comp]
  exact congrArg (fun z => c ≫ z) (representingMap_congr_twoIso B S hS F
    (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) eF
    (representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) hiso)

/-- **The two legs of a charted self-intersection agree over the field-valued point, as
morphisms of schemes.** This is `AlgebraicGeometry.Stack.chartLeg_comp_siteMap_eq` read through
the structure functor to schemes; it is the equation which makes the pair
`(a, b) : R ⟶ U ×_{Spec k} U` of underlying morphisms of schemes exist. -/
theorem toScheme_chartLeg_comp_siteMap_eq :
    (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.fst) ≫
        (BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q)) =
      (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) ≫
        (BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, chartLeg_comp_siteMap_eq B S hS k hk toBase q U p P
    F eF R c]

/-- **The double fibre of a charted self-intersection is discrete at the identity point.** Let
`q : 𝒴₀ ⟶ Spec(k)` be a locally quasi-finite 1-morphism to a field-valued point of the base, let
`p : U ⟶ 𝒴₀` be a smooth chart by a scheme `U` of the site, let `P` be a 2-fibre product square
over the cospan `(p, p)`, let `F` represent its apex and let `c : h_R ⟶ F` be an étale chart of
`F` by a scheme `R` of the site. Write `a` and `b` for the two legs
`AlgebraicGeometry.Stack.chartLeg` read as morphisms of schemes `R ⟶ U`. If the pair
`(a, b) : R ⟶ U ×_{Spec k} U` is locally quasi-finite, then every point `r₀` of `R` whose image
`b r₀` is closed in `U` — for instance the identity point of
`AlgebraicGeometry.Stack.exists_point_chartLeg_eq` over a closed point of `U` — is an isolated
point of the double fibre.

This is the hypothesis `hiso` of
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth`, in the setting of
the chart construction of **Stacks 06MF**. The content is
`AlgebraicGeometry.isIsolatedPoint_asFiber_of_locallyQuasiFinite_pair` at the structure morphism
`U ⟶ Spec(k)`, which is locally of finite type by **Stacks 06FT** and
`AlgebraicGeometry.Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType`,
and at the two legs, which are smooth —
hence locally of finite type — by `AlgebraicGeometry.Stack.smooth_chartLeg`. -/
theorem isIsolatedPoint_asFiber_chartLeg
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (hp : AlgebraicStacks.IsSmooth B S hS p)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hF : IsAlgebraicSpace B S hS F)
    (hcet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hpair : LocallyQuasiFinite (pullback.lift _ _
      (toScheme_chartLeg_comp_siteMap_eq B S hS k hk toBase q U p P F eF R c)))
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (chartLeg B S hS U p P F eF R c P.snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsIsolatedPoint
      ((((BigFppfOver.toScheme B S hS).map
            (chartLeg B S hS U p P F eF R c P.snd)).fiberι
          ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀) ≫
        (BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.fst)).asFiber
        (((BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.snd)).asFiber r₀)) := by
  obtain ⟨hsa, hsb⟩ := smooth_chartLeg B S hS U p P F eF R c hF hcet hp hP
  let := hsa
  let : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (siteMap B S hS (p ≫ q))) :=
    locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S hS (p ≫ q)
      (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS p q
        (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS p hp) hq.2.1)
  exact isIsolatedPoint_asFiber_of_locallyQuasiFinite_pair
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (p ≫ q)))
    _ _ (toScheme_chartLeg_comp_siteMap_eq B S hS k hk toBase q U p P F eF R c) hpair r₀ hclosed

end Stack

end AlgebraicGeometry

end
