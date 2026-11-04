module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Regular immersions of algebraic spaces

For a representable morphism of algebraic spaces over a scheme `S` and a property of scheme
morphisms which is étale local on the target, the property of the base change of the
morphism to every étale scheme chart of the target is equivalent to its property for the
base change to one surjective étale chart, and, when the source and target are
representable, to the property of the scheme morphism they represent. A representable
morphism of algebraic spaces is then a *Koszul-regular*, an *`H₁`-regular* or a
*quasi-regular* immersion when its base changes to étale scheme charts of the target are
immersions of schemes with the corresponding regularity property.

## Main definitions

* `AlgebraicGeometry.Space.IsKoszulRegularImmersion` is Koszul-regularity: **Stacks
  06BN**, part (1).
* `AlgebraicGeometry.Space.IsH1RegularImmersion` is `H₁`-regularity: **Stacks 06BN**, part
  (2).
* `AlgebraicGeometry.Space.IsQuasiRegularImmersion` is quasi-regularity: **Stacks 06BN**,
  part (3).

## Main results

* `AlgebraicGeometry.Space.property_on_all_etale_charts_iff_exists_atlas`: for an étale
  local property, all étale charts may be replaced by one surjective étale chart:
  **Stacks 06BM**.
* `AlgebraicGeometry.Space.property_on_all_etale_charts_iff_of_schemes`: for representable
  source and target the same condition is the property of the represented scheme morphism:
  **Stacks 06BM**.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_forall_etale_chart`: for a property
  étale local on the source and target, the condition on the represented base changes to the
  étale charts of the target implies the every-chart condition of Stacks 03MJ.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isQuasiRegularImmersion`:
  **Stacks 09RY**, condition (1) in the direction out of quasi-regularity: a quasi-regular
  immersion of algebraic spaces is locally of finite presentation.

## Implementation notes

An étale chart of a presheaf is encoded by its Yoneda morphism, and its étaleness and
surjectivity are the representable morphism properties induced from schemes along
`AlgebraicGeometry.BigFppfOver.toScheme`, exactly as in the atlas field of
`AlgebraicGeometry.IsAlgebraicSpace`. The represented fibre product of `f` with a chart `q`
and its projection to the chart are the canonical choices `hf.pullback q` and `hf.snd q`
supplied by `CategoryTheory.Functor.relativelyRepresentable`; the statement is independent
of that choice up to unique isomorphism, which is what the comparison isomorphisms in the
proofs provide. In the representable case the scheme morphism is obtained from the
canonical Yoneda representations of the source and the target.

The implication from one surjective chart to all charts is étale locality at the target:
over a chart `q'` the base change of `f` is covered, after pulling back along the
surjective étale `q`, by the base change over `q`, and the property transfers along the
singleton étale covering so obtained. The transfer along a single, not necessarily
surjective, étale morphism uses the covering of the target by that morphism together with
its identity, which is a covering in `AlgebraicGeometry.Scheme.etalePrecoverage` because
the identity is surjective; `CategoryTheory.MorphismProperty.IsLocalAtTarget.pullbackSnd`
then gives the property of the base change.

Each of the three regularity predicates is condition (1) of Stacks 06BM for the
corresponding scheme property of Stacks 063J. The scheme-level predicates
`Stacks.AlgebraicGeometry.RegularIdealSheaf.*` take the immersion hypothesis as an instance
argument, so the existence of that hypothesis is part of the chart condition rather than a
separate conjunct: an immersion of schemes with a Koszul-regular, `H₁`-regular or
quasi-regular defining ideal sheaf is exactly what Stacks 063J asks of each base change.

None of the three imposes algebraicity of the source or target; as with the conditions of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that is imposed by clients, exactly as
in the source definition. Representability of the morphism, on the other hand, is part of
the source definition and so is part of each predicate.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 06BM](https://stacks.math.columbia.edu/tag/06BM)
* [Stacks Project, Tag 06BN](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Tag 09RQ](https://stacks.math.columbia.edu/tag/09RQ)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 09RY](https://stacks.math.columbia.edu/tag/09RY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Two pullbacks of the same morphism along the same chart, with the second leg a Yoneda
image, give a property `P` of scheme morphisms to the legs simultaneously. -/
private theorem property_map_iff_of_isPullback_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {D A A' : BigFppfOver B S hS}
    {q : yoneda.obj D ⟶ Y} {x : yoneda.obj A ⟶ X} {x' : yoneda.obj A' ⟶ X}
    {b : A ⟶ D} {b' : A' ⟶ D} (h : IsPullback x (yoneda.map b) f q)
    (h' : IsPullback x' (yoneda.map b') f q) :
    P ((BigFppfOver.toScheme B S hS).map b) ↔ P ((BigFppfOver.toScheme B S hS).map b') := by
  let eW := h.isoPullback.trans h'.isoPullback.symm
  have heW : eW.hom ≫ yoneda.map b' = yoneda.map b := by
    simp only [eW, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      h'.isoPullback_inv_snd, h.isoPullback_hom_snd]
  let e := yoneda.preimageIso eW
  have he : e.hom ≫ b' = b := by
    apply yoneda.map_injective
    simpa [e] using heW
  let eSch := Functor.mapIso (BigFppfOver.toScheme B S hS) e
  have heSch : eSch.hom ≫ (BigFppfOver.toScheme B S hS).map b' =
      (BigFppfOver.toScheme B S hS).map b := by
    simpa [eSch, Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map he
  simpa only [heSch] using
    P.cancel_left_of_respectsIso eSch.hom ((BigFppfOver.toScheme B S hS).map b')

/-- **Stacks 06BM, the equivalence of conditions (1) and (2).** For a property `P` of
scheme morphisms which is étale local on the target and a representable morphism `f` of
algebraic spaces over `S`, the projection of the represented fibre product has `P` over
every étale scheme chart of the target if and only if it has `P` over some surjective étale
chart. -/
@[stacks 06BM "equivalence of all charts and one surjective chart"]
theorem property_on_all_etale_charts_iff_exists_atlas (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    (∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      P ((BigFppfOver.toScheme B S hS).map (hf.snd q))) ↔
    (∃ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      P ((BigFppfOver.toScheme B S hS).map (hf.snd q))) := by
  have : HasLimitsOfShape WalkingCospan B.Schemes := inferInstance
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  constructor
  · intro hall
    obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
    exact ⟨V, q, hqSurj, hqEtale, hall V q hqEtale⟩
  · rintro ⟨V, q, hqSurj, hqEtale, hP⟩ V' q' hq'Etale
    have hqRep : yoneda.relativelyRepresentable q := hqEtale.1
    let t := hqRep.snd q'
    let s := yoneda.preimage (hqRep.fst q')
    have hT : IsPullback (yoneda.map s) (yoneda.map t) q q' := by
      simpa [s] using hqRep.isPullback q'
    let toSch := BigFppfOver.toScheme B S hS
    have hsEtSch : Etale (toSch.map s) := hq'Etale.2 q (yoneda.map t) s hT.flip
    have htEtSch : Etale (toSch.map t) := hqEtale.2 q' (yoneda.map s) t hT
    let p := toSch.map (hf.snd q)
    let p' := toSch.map (hf.snd q')
    let sSch := toSch.map s
    let tSch := toSch.map t
    have htSurj : Surjective tSch := hqSurj.2 q' (yoneda.map s) t hT
    have hEtaleBaseChange : ∀ {W Z T : Scheme.{u}} (p₀ : W ⟶ Z) (g₀ : T ⟶ Z),
        P p₀ → Etale g₀ → P (pullback.snd p₀ g₀) := by
      intro W Z T p₀ g₀ hp₀ hg₀
      have hmem : Presieve.ofArrows (fun b : Bool ↦ bif b then T else Z)
          (fun b ↦ match b with | true => g₀ | false => 𝟙 Z) ∈
            Scheme.etalePrecoverage.coverings Z := by
        rw [Scheme.etalePrecoverage]
        refine (Scheme.ofArrows_mem_precoverage_iff (@Etale)).2 ⟨fun x ↦ ⟨false, x, rfl⟩, ?_⟩
        rintro (_ | _)
        · exact inferInstanceAs (Etale (𝟙 Z))
        · exact hg₀
      exact MorphismProperty.IsLocalAtTarget.pullbackSnd hmem ⟨true⟩ hp₀
    have hBase : P (pullback.snd p sSch) := hEtaleBaseChange p sSch hP hsEtSch
    let a := pullback.fst (hf.snd q) s
    let b := pullback.snd (hf.snd q) s
    let a' := pullback.fst (hf.snd q') t
    let b' := pullback.snd (hf.snd q') t
    have hW : IsPullback (yoneda.map a) (yoneda.map b)
        (yoneda.map (hf.snd q)) (yoneda.map s) :=
      Functor.map_isPullback yoneda (IsPullback.of_hasPullback (hf.snd q) s)
    have hW' : IsPullback (yoneda.map a') (yoneda.map b')
        (yoneda.map (hf.snd q')) (yoneda.map t) :=
      Functor.map_isPullback yoneda (IsPullback.of_hasPullback (hf.snd q') t)
    have hWSch : IsPullback (toSch.map a) (toSch.map b) p sSch :=
      Functor.map_isPullback toSch (IsPullback.of_hasPullback (hf.snd q) s)
    have hW'Sch : IsPullback (toSch.map a') (toSch.map b') p' tSch :=
      Functor.map_isPullback toSch (IsPullback.of_hasPullback (hf.snd q') t)
    have hOuter := hW.paste_horiz (hf.isPullback q)
    have hOuter' : IsPullback
        (yoneda.map a' ≫ hf.fst q') (yoneda.map b') f (yoneda.map s ≫ q) := by
      simpa only [← hT.w] using hW'.paste_horiz (hf.isPullback q')
    have hPb : P (toSch.map b) := by
      simpa only [hWSch.isoPullback_hom_snd] using
        (P.cancel_left_of_respectsIso hWSch.isoPullback.hom _).mpr hBase
    have hPb' : P (toSch.map b') :=
      (property_map_iff_of_isPullback_yoneda B S hS P hOuter hOuter').mp hPb
    have hCanon : P (pullback.snd p' tSch) := by
      apply (P.cancel_left_of_respectsIso hW'Sch.isoPullback.hom _).mp
      simpa only [hW'Sch.isoPullback_hom_snd] using hPb'
    have hCover : Presieve.singleton tSch ∈ Scheme.etalePrecoverage.coverings _ := by
      rw [Scheme.etalePrecoverage]
      exact (Scheme.singleton_mem_precoverage_iff (@Etale) tSch).2
        ⟨htSurj.surj, htEtSch⟩
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hCover ?_
    rintro _ _ _ ⟨⟩
    exact hCanon

/-- **Stacks 06BM, the comparison with the scheme-theoretic property.** When the source and
target of a representable morphism of algebraic spaces over `S` are representable, the
condition of Stacks 06BM on all étale charts holds exactly when the morphism of schemes
they represent has the property. -/
@[stacks 06BM "comparison when both spaces are schemes"]
theorem property_on_all_etale_charts_iff_of_schemes (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [X.IsRepresentable] [Y.IsRepresentable]
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    (∀ (W : BigFppfOver B S hS) (q : yoneda.obj W ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      P ((BigFppfOver.toScheme B S hS).map (hf.snd q))) ↔
    P ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (X.reprW.hom ≫ f ≫ Y.reprW.inv))) := by
  let toSch := BigFppfOver.toScheme B S hS
  let q0 := Y.reprW.hom
  let g := yoneda.preimage (X.reprW.hom ≫ f ≫ Y.reprW.inv)
  have : IsIso q0 := inferInstance
  have hiso (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative] [Q.RespectsIso] :
      (MorphismProperty.inverseImage Q toSch).presheaf q0 := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda q0, ?_⟩
    intro A D g fst snd h
    have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    exact Q.of_isIso (toSch.map snd)
  have hq0Etale := hiso (@Etale.{u} : MorphismProperty Scheme.{u})
  have hq0Surj := hiso (@Surjective.{u} : MorphismProperty Scheme.{u})
  have hX : IsAlgebraicSpace B S hS X :=
    (isAlgebraicSpace_yoneda B S hS X.reprX).of_iso X.reprW
  have hY : IsAlgebraicSpace B S hS Y :=
    (isAlgebraicSpace_yoneda B S hS Y.reprX).of_iso Y.reprW
  have hChartIff := property_on_all_etale_charts_iff_exists_atlas B S hS P hX hY f hf
  have hComm : yoneda.map g ≫ q0 = X.reprW.hom ≫ f := by
    simp [g, q0, Category.assoc]
  have hFq := hf.isPullback q0
  have hSquare : IsPullback X.reprW.hom (yoneda.map g) f q0 :=
    IsPullback.of_horiz_isIso ⟨hComm.symm⟩
  have hChart : P (toSch.map (hf.snd q0)) ↔ P (toSch.map g) :=
    property_map_iff_of_isPullback_yoneda B S hS P hFq hSquare
  exact ⟨fun hall ↦ hChart.mp (hall Y.reprX q0 hq0Etale),
    fun hP ↦ hChartIff.mpr ⟨Y.reprX, q0, hq0Surj, hq0Etale, hChart.mpr hP⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06BN, part (1).** A representable morphism of algebraic spaces over `S` is a
*Koszul-regular immersion* when its base change to every étale scheme chart of the target
is a Koszul-regular immersion of schemes. -/
@[stacks 06BN "part (1): Koszul-regular immersion"]
abbrev IsKoszulRegularImmersion (i : X ⟶ Y) : Prop :=
  ∃ hi : yoneda.relativelyRepresentable i,
    ∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      ∃ hj : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)),
        @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion _ _
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)) hj

/-- **Stacks 06BN, part (2).** A representable morphism of algebraic spaces over `S` is an
*`H₁`-regular immersion* when its base change to every étale scheme chart of the target is
an `H₁`-regular immersion of schemes. -/
@[stacks 06BN "part (2): H₁-regular immersion"]
abbrev IsH1RegularImmersion (i : X ⟶ Y) : Prop :=
  ∃ hi : yoneda.relativelyRepresentable i,
    ∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      ∃ hj : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)),
        @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsH1RegularImmersion _ _
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)) hj

/-- **Stacks 06BN, part (3).** A representable morphism of algebraic spaces over `S` is a
*quasi-regular immersion* when its base change to every étale scheme chart of the target is
a quasi-regular immersion of schemes. -/
@[stacks 06BN "part (3): quasi-regular immersion"]
abbrev IsQuasiRegularImmersion (i : X ⟶ Y) : Prop :=
  ∃ hi : yoneda.relativelyRepresentable i,
    ∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      ∃ hj : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)),
        @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion _ _
          ((BigFppfOver.toScheme B S hS).map (hi.snd q)) hj

/-! ### Local finite presentation of a quasi-regular immersion -/

/-- **The target-chart condition implies the every-chart condition of Stacks 03MJ.** Let `P`
be a property of scheme morphisms which is étale local on the source and target and let
`i : Z ⟶ X` be a representable morphism of algebraic spaces over `S` whose represented base
change to every étale scheme chart of the target has `P`. Then the scheme morphism underlying
every commuting square of étale charts of `i` has `P`.

A surjective étale chart `b` of the target lifts to the surjective étale chart `i` pulls back
from it, because being a surjective étale chart is stable under base change; the resulting
square over the given base change is the one surjective square of Stacks 03MJ, condition
(2). -/
theorem holdsOnEveryEtaleChart_of_forall_etale_chart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i)
    (hall : ∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      P ((BigFppfOver.toScheme B S hS).map (hi.snd q))) :
    HoldsOnEveryEtaleChart B S hS P i := by
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hZ hX i).mpr ?_
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hX.exists_atlas
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let Sur : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have hfst (Q : MorphismProperty (BigFppfOver B S hS)) (hQ : Q.presheaf b) :
      Q.presheaf (hi.fst b) := by
    have : MorphismProperty.IsStableUnderBaseChange Q.presheaf :=
      MorphismProperty.relative_isStableUnderBaseChange Q
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hi.isPullback b).flip hQ
  exact ⟨hi.pullback b, V, hi.fst b, b, hi.snd b, hfst E hbEtale, hbEtale, hfst Sur hbSurj,
    (hi.isPullback b).w.symm, hall V b hbEtale⟩

open Stacks.AlgebraicGeometry.RegularIdealSheaf
  (locallyOfFinitePresentation_of_isQuasiRegularImmersion)

/-- **Stacks 09RY, condition (1) in the direction out of quasi-regularity.** A quasi-regular
immersion of algebraic spaces over `S` is locally of finite presentation.

Each represented base change of `i` to an étale scheme chart of the target is a quasi-regular
immersion of schemes, hence locally of finite presentation by the case of schemes
[Stacks, Tag 063M]; local finite presentation is étale local on the source and target
[Stacks, Tag 04R3], so those chart conditions are the local finite presentation of `i`. -/
@[stacks 09RY "the direction out of quasi-regularity, condition (1) only: a quasi-regular \
immersion of algebraic spaces is locally of finite presentation.  Conditions (2) and (3) and \
the converse are not transported, because the case of schemes, Tag 063M, is itself carried \
only as conditions (1) and (2) out of quasi-regularity"]
theorem isLocallyOfFinitePresentation_of_isQuasiRegularImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (_hIm : IsImmersion B S hS i) (h : IsQuasiRegularImmersion B S hS i) :
    IsLocallyOfFinitePresentation B S hS i := by
  obtain ⟨hi, hcharts⟩ := h
  refine holdsOnEveryEtaleChart_of_forall_etale_chart B S hS _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hZ hX i hi ?_
  intro V q hq
  obtain ⟨hj, hqr⟩ := hcharts V q hq
  have := hj
  exact locallyOfFinitePresentation_of_isQuasiRegularImmersion _ hqr

end AlgebraicGeometry.Space

end
