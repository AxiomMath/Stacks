module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare

/-!
# Locality on the base for the fpqc topology transferred from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**). **Stacks 03MJ** turns
`P` into the property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of
algebraic spaces over `S`. This module shows that if `P` is in addition stable under composition
and base change, implied by étaleness, and local on the base for the fpqc topology of *schemes*,
then the associated property of morphisms of algebraic spaces is local on the base for the fpqc
topology of **Stacks 03YH**; and it reads off from that the entry of the list of **Stacks 042A**:
unramifiedness of morphisms of algebraic spaces is fpqc local on the base.

The argument is the source's. Preservation under base change is **Stacks 0AMM**. For descent,
the criterion is first reduced, by condition (4) of **Stacks 03MM**, to base changes along
morphisms from *affine* schemes of the site; the refinement clause of the fpqc covering
condition of **Stacks 03MQ** then replaces the given covering, over such an affine base `T`, by
a finite affine fpqc covering family of `T` refining it. Over `T` the statement becomes a
statement about schemes: a surjective étale atlas `h_U ⟶ X` of the source determines a morphism
`U ⟶ T` of the site, each base change of which along a member of the refining family is, by
**Stacks 03MJ**, the scheme morphism of an étale chart square of the corresponding base change
of the morphism of algebraic spaces. So `U ⟶ T` has `P` after base change along an fpqc covering
of `T`, hence has `P`; and one surjective étale chart square suffices by **Stacks 03MJ** again.

## Main results

* `AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_schemes`: the transfer.

## Implementation notes

`isLocalAtTarget_fpqc_of_schemes` is **deliberately not tagged**. The Stacks tag for the
transfer itself is 06EN, which asserts it for all five topologies of Stacks 03YH at once, in the
same shape as Stacks 06ER does for locality on the source; only the fpqc case is proved here.
Stacks 042A, on the other hand, is exactly the fpqc case at unramifiedness, and it is tagged on
`AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` of
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget`, the instance this transfer
is applied at.

The two sides of Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the ambient category, which for algebraic spaces is the
fibre product of **Stacks 02X2** only up to the canonical isomorphism of pullbacks; the
chart conditions, on the other hand, are conditions on the *presheaf* fibre product.
`holdsOnEveryEtaleChart_pullback_fst_hom` below is that comparison, made once.

`holdsOnEveryEtaleChart_of_affineFpqcPresieve` is the only place where locality on the base for
schemes is used, and the only place where the covering family has to be affine: it is applied to
the refining family produced by the fpqc condition, whose members are affine objects of the site
by construction.

## References

* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 042A](https://stacks.math.columbia.edu/tag/042A)
* [Stacks Project, Tag 06EN](https://stacks.math.columbia.edu/tag/06EN)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty Scheme.{u})

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_fpqcTarget :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_fpqcTarget
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_fpqcTarget B S hS).has_limit _

/-! ### Comparing the two fibre products -/

/-- A property respecting isomorphisms holds for `pullback.snd` iff it holds for the second
projection of any other pullback square on the same cospan. -/
private theorem pullback_snd_iff_of_isPullback {C : Type*} [Category C] (Q : MorphismProperty C)
    [Q.RespectsIso] {W X Y Z : C} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (sq : IsPullback fst snd f g) : Q (pullback.snd f g) ↔ Q snd := by
  rw [← sq.isoPullback_hom_snd]
  exact (Q.cancel_left_of_respectsIso _ _).symm

/-- The chart condition of Stacks 03MJ for the base change of `f` along `g`, read on the
*presheaf* fibre product, follows from the same condition on the base change formed in the
category of algebraic spaces: the two are pullbacks of the same cospan, so they differ by an
isomorphism, and the chart condition respects isomorphisms. -/
private theorem holdsOnEveryEtaleChart_pullback_fst_hom {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : HoldsOnEveryEtaleChart B S hS P (pullback.snd f g).hom) :
    HoldsOnEveryEtaleChart B S hS P (pullback.fst g.hom f.hom) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ k => HoldsOnEveryEtaleChart B S hS P k.hom
  let _ : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  exact (pullback_snd_iff_of_isPullback Q
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g f).flip).mp h

/-! ### The chart square cut out by a base change of the target -/

/-- A base change over a *scheme* base, read on one étale chart of the source.

Let `f : X ⟶ h_V` be a morphism of algebraic spaces over `S` whose target is representable, let
`p : h_U ⟶ X` be an étale chart of the source, and let `h : U ⟶ V` be the morphism of the site
underlying `p ≫ f`. If the chart condition holds for the base change of `f` along a morphism
`k : V' ⟶ V` of the site, then `P` holds for the base change of the scheme morphism underlying
`h` along the one underlying `k`: the pullback `U ×_V V'` is a chart of the base change of `X`,
étale over it because étaleness of charts is stable under base change, so the pair consisting of
that chart and the identity of `h_{V'}` is a commuting square of étale charts of the base
change. -/
private theorem prop_pullbackSnd_of_chart {X : AlgebraicSpaces B S hS}
    {U V V' : BigFppfOver B S hS} (f : X ⟶ schemeSpace V) (p : yoneda.obj U ⟶ X.obj)
    (hpEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (h : U ⟶ V) (hh : yoneda.map h = p ≫ f.hom) (k : V' ⟶ V)
    [P.IsStableUnderBaseChange]
    (hf : HoldsOnEveryEtaleChart B S hS P (pullback.snd f (schemeSpaceMap k)).hom) :
    P (pullback.snd ((BigFppfOver.toScheme B S hS).map h)
      ((BigFppfOver.toScheme B S hS).map k)) := by
  let q := BigFppfOver.toScheme B S hS
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) q
  let _ : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  let W := pullback h k
  let r : W ⟶ U := pullback.fst h k
  let s : W ⟶ V' := pullback.snd h k
  let g' : schemeSpace V' ⟶ schemeSpace V := schemeSpaceMap k
  have sqh := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g')
  let pp : yoneda.obj W ⟶ (pullback f g').obj :=
    sqh.lift (yoneda.map r ≫ p) (yoneda.map s) (by
      change yoneda.map r ≫ (p ≫ f.hom) = yoneda.map s ≫ yoneda.map k
      rw [← hh]
      change yoneda.map r ≫ yoneda.map h = yoneda.map s ≫ yoneda.map k
      simpa only [Functor.map_comp] using
        congrArg yoneda.map (pullback.condition : r ≫ h = s ≫ k))
  have sqW : IsPullback (yoneda.map s) (yoneda.map r) (yoneda.map k) (yoneda.map h) :=
    ((IsPullback.of_hasPullback h k).map yoneda).flip
  have pp_fst : pp ≫ (pullback.fst f g').hom = yoneda.map r ≫ p := sqh.lift_fst _ _ _
  have pp_snd : pp ≫ (pullback.snd f g').hom = yoneda.map s := sqh.lift_snd _ _ _
  have outer : IsPullback (pp ≫ (pullback.snd f g').hom) (yoneda.map r) g'.hom (p ≫ f.hom) := by
    rw [pp_snd, ← hh]
    exact sqW
  have sqAtlas : IsPullback pp (yoneda.map r) (pullback.fst f g').hom p :=
    outer.of_right pp_fst sqh.flip
  have hppEtale : E.presheaf pp :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := E.presheaf) sqAtlas.flip hpEtale
  have hW : P (q.map s) := hf W V' pp (𝟙 _) s hppEtale (presheaf_etale_id B S hS V')
    ((Category.comp_id (yoneda.map s)).trans pp_snd.symm)
  exact (pullback_snd_iff_of_isPullback P ((IsPullback.of_hasPullback h k).map q)).mpr hW

/-! ### Descent over an affine base -/

/-- Descent of the chart condition over an affine base, along an affine fpqc covering presieve.

The source is given a surjective étale atlas, which over a representable target determines a
morphism `U ⟶ T` of the site. Its base change along each member of the presieve has `P` by
`AlgebraicGeometry.Space.prop_pullbackSnd_of_chart`, so `U ⟶ T` itself has `P` because `P` is
local on the base for the fpqc topology of schemes; and the atlas together with the identity of
`h_T` is a surjective étale chart square, which suffices by [Stacks Project, Tag 03MJ]. -/
private theorem holdsOnEveryEtaleChart_of_affineFpqcPresieve
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (T : BigAffineFppf B S hS) (R : Presieve T)
    (hR : R.map (BigAffineFppf.toScheme B S hS) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T))
    (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace ((BigAffineFppf.inclusion B S hS).obj T))
    (hf : ∀ {T' : BigAffineFppf B S hS} (g : T' ⟶ T), R g →
      HoldsOnEveryEtaleChart B S hS P
        (pullback.snd f (schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map g))).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := X.property.exists_atlas
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let q := BigFppfOver.toScheme B S hS
  let h : U ⟶ V := yoneda.preimage (p ≫ f.hom)
  have hh : yoneda.map h = p ≫ f.hom := yoneda.map_preimage _
  have hscheme : P (q.map h) := by
    refine (inferInstance : P.IsLocalAtTarget Scheme.fpqcPrecoverage).of_forall_pullbackSnd
      (f := q.map h) hR ?_
    rintro W j _ @⟨T', g, hg⟩
    exact prop_pullbackSnd_of_chart B S hS P f p hpEtale h hh
      ((BigAffineFppf.inclusion B S hS).map g) (hf g hg)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP X.property
    (schemeSpace V).property f.hom).mpr ⟨U, V, p, 𝟙 _, h, hpEtale,
      presheaf_etale_id B S hS V, hpSurj, (Category.comp_id (yoneda.map h)).trans hh, hscheme⟩

/-! ### The transfer, and Stacks 042A -/

/-- Locality on the base for the fpqc topology, transferred from schemes to algebraic spaces.
If a property `P` of morphisms of schemes is étale local on the source and target, stable under
composition and base change, implied by étaleness, and local on the base for the fpqc topology
of schemes, then the associated property of morphisms of algebraic spaces over `S` of
Stacks 03MJ is local on the base for the fpqc topology of Stacks 03YH.

Deliberately untagged: the Stacks tag for the transfer is 06EN, which asserts it for all five
topologies of Stacks 03YH at once, and only the fpqc case is proved here. -/
theorem isLocalAtTarget_fpqc_of_schemes (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ f => HoldsOnEveryEtaleChart B S hS P f.hom
  let _ : Q.IsStableUnderBaseChange :=
    holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP
  refine { precomp := (inferInstance : Q.RespectsIso).precomp
           postcomp := (inferInstance : Q.RespectsIso).postcomp
           pullbackSnd := ?_
           of_forall_pullbackSnd := ?_ }
  · exact fun _ _ hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q)
      (IsPullback.of_hasPullback _ _) hf
  · intro Y X f R hR hall
    obtain ⟨I, Yi, gi, rfl, _, _, hfpqc⟩ := hR
    change IsFpqcCovering B S hS (fun i => (gi i).hom) at hfpqc
    refine holdsOnEveryEtaleChart_of_affine_baseChange B S hS P hP inferInstance hPetale
      X.property Y.property f.hom ?_
    intro Z g hZaff
    let Zaff : BigAffineFppf B S hS := ⟨Z, hZaff⟩
    let gZ : schemeSpace Z ⟶ Y := ObjectProperty.homMk g
    obtain ⟨W, hWfinite, hWcover, href⟩ := hfpqc.2 Zaff g
    refine holdsOnEveryEtaleChart_pullback_fst_hom B S hS P f gZ ?_
    refine holdsOnEveryEtaleChart_of_affineFpqcPresieve B S hS P hP Zaff W.presieve₀ hWcover
      (pullback f gZ) (pullback.snd f gZ) ?_
    rintro T' k ⟨j⟩
    obtain ⟨i, a, ha⟩ := href j
    let a' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (W.X j)) ⟶ Yi i :=
      ObjectProperty.homMk a
    let k' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (W.X j)) ⟶ schemeSpace Z :=
      schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map (W.f j))
    have hcomm : a' ≫ gi i = k' ≫ gZ := ObjectProperty.hom_ext _ ha
    exact MorphismProperty.pullbackSnd_of_comm Q f (gi i) gZ a' k' hcomm
      (hall (g := gi i) (Presieve.ofArrows.mk i))

end AlgebraicGeometry.Space

end
