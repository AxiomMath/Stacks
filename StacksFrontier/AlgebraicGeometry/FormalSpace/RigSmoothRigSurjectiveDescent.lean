module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange
import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
import StacksFrontier.RingTheory.Rig.RigEtaleIsLocal
import StacksFrontier.RingTheory.Rig.RigSmoothStability

/-!
# Descent of rig-smoothness and rig-étaleness along a rig-surjective morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GH6** says that if
`g` is locally of finite type, `f` is rig-smooth (resp. rig-étale) and rig-surjective, and
`g ∘ f` is rig-smooth (resp. rig-étale), then `g` is rig-smooth (resp. rig-étale). Both cases
are proved here, as
`AlgebraicGeometry.FormalSpace.isRigSmooth_of_comp_of_isRigSurjective` and
`AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isRigSurjective`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasRigSurjectiveChartDescent`: the chart-level core of the
  source's proof for a property of arrows of `WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isRepresentableEtale`:
  condition (1) of Stacks 0ANG is inherited by a precomposition with a representable étale
  morphism.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_of_comp_of_isRigSurjective`: **Stacks 0GH6**, the
  rig-smooth case.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isRigSurjective`: **Stacks 0GH6**, the
  rig-étale case, granted the locality of rig-étaleness;
  `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isRigSurjective'` is the form with that
  hypothesis discharged, and carries the tag.

## Implementation notes

The reduction carried out here is the first half of the source's proof. Both conclusions are
chart conditions: by conditions (1) and (2) of Stacks 0GCQ, resp. 0GCZ, rig-smoothness, resp.
rig-étaleness, of `g` is the assertion that the property `P` of arrows of `WAdm^{Noeth}` holds
on the morphism `t : V ⟶ W` of every affine étale chart square

```
V ⟶ W
↓     ↓
Y ⟶ Z
```

over `g`. Fix such a square, with charts `a : V ⟶ Y` and `b : W ⟶ Z`. The data the source
assembles at this point is produced from the three hypotheses as follows.

* `t` is locally of finite type: `a ≫ g = t ≫ b` is locally of finite type because `a` is
  representable étale and `g` is locally of finite type (hypothesis (1)), and `b` has an affine
  formal algebraic space as its source, so Stacks 0AQ6 cancels it.
* `X ×_Y V ⟶ V` is rig-surjective: it is the base change of `f` along `a`, and `a` is locally
  of finite type, so Stacks 0AQS applies to the rig-surjectivity in hypothesis (2).
* `X ×_Y V ⟶ V` has `P` on every affine étale diagram over it: `a` is adic, so this is the
  base-change transfer of Remark 0GBG applied to hypothesis (2).
* `X ×_Y V ⟶ W` has `P` on every affine étale diagram over it: that morphism is
  `X ×_Y V ⟶ X ⟶ Z`, whose first factor is representable étale, so this follows from
  hypothesis (3) by
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isRepresentableEtale`,
  proved below.

What remains is the source's argument proper — the choice of a prime of the chart ring `B` of
`V` away from the ideal of definition, the complete discrete valuation ring dominating `B/𝔮`
supplied by Stacks 00PH, the lift of `Spf R ⟶ V` through `X ×_Y V` and through a chart
`Spf A` of it, the flatness of `B_𝔮 ⟶ A_𝔭` coming from rig-smoothness, and faithfully flat
descent of the conclusion from `𝔭` to `𝔮`. None of this is available in the library: it needs
localization of the completed naive cotangent complex at a prime and the exact sequences of
Stacks 09D9 and 0GAC in that localized form, which
`StacksFrontier.RingTheory.Restricted.RigSmoothCriteria` does not provide. It is therefore carried
as the hypothesis `AlgebraicGeometry.FormalSpace.HasRigSurjectiveChartDescent`, which is a
statement about one chart square equipped with a rig-surjective cover of its source chart and
not a restatement of either conclusion: it says nothing about `f`, `g` or `Y`, and it takes the
cover as data.

The hypotheses `hetaleAdic` and `hetaleFiniteType` are the assertions that a representable étale
morphism of fppf sheaves is adic (Stacks 0AQ3) and locally of finite type (Stacks 0AJG read
through Definition 0AM4). Neither is in this library, which has no implication from
`AlgebraicGeometry.Space.IsEtaleULift` to `AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift`
and no étale case of Stacks 0AQ3; both are quantified over all representable étale morphisms.

Definition 0AQQ presupposes its morphism to be locally of finite type, so hypothesis (2) is
read as including that `f` is locally of finite type; it appears as the separate hypothesis
`hfft`, which Stacks 0AQS consumes.

The locally Noetherian hypotheses on `X`, `Y` and `Z` are omitted, as they are in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange`: the class of rings over which
the chart conditions quantify already provides adicness and Noetherianity of every chart ring.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AJG](https://stacks.math.columbia.edu/tag/0AJG)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ6](https://stacks.math.columbia.edu/tag/0AQ6)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GCP](https://stacks.math.columbia.edu/tag/0GCP)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Condition (1) of Stacks 0ANG for a property `P` of arrows of `WAdm^{Noeth}` is inherited by
a precomposition with a representable étale morphism: an affine étale chart of the source of
`c ≫ h` becomes, after composition with `c`, an affine étale chart of the source of `h`, over
the same chart of the target and with the same chart morphism. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_of_isRepresentableEtale
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    {X' X Y : FppfSheaf B S hS} (c : X' ⟶ X) (h : X ⟶ Y)
    (hc : IsRepresentableEtale B S hS c)
    (hh : HasPropertyOnEveryAffineEtaleDiagram B S hS C P h) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P (c ≫ h) := by
  intro U V a b t hU hV ha hb hcomm
  exact hh U V (a ≫ c) b t hU hV (IsRepresentableEtale.comp B S hS ha hc) hb
    (by rw [Category.assoc]; exact hcomm)

/-- The chart-level core of the proof of **Stacks 0GH6** for a property `P` of arrows of
`WAdm^{Noeth}`. Given a morphism `t : V ⟶ W` of affine formal algebraic spaces which is locally
of finite type, a representable étale morphism `b : W ⟶ Z`, and a rig-surjective morphism
`p : X' ⟶ V` such that `P` holds on every affine étale diagram over `p` and over `p ≫ t ≫ b`,
the property `P` holds on the continuous homomorphism realizing `t` for every presentation of
`V` and `W` as formal spectra.

This is the part of the source's proof which argues at the level of the chart rings: it chooses
a prime of the chart ring of `V` away from the ideal of definition, dominates its quotient by a
complete discrete valuation ring, lifts the resulting point through `p` and through a chart of
`X'`, and descends the conclusion by faithful flatness. It speaks only about the chart square
and the given cover `p`. -/
abbrev HasRigSurjectiveChartDescent
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) :
    Prop :=
  ∀ {X' V W Z : FppfSheaf B S hS} (p : X' ⟶ V) (t : V ⟶ W) (b : W ⟶ Z),
    IsAffineFormalAlgebraicSpace B S hS V → IsAffineFormalAlgebraicSpace B S hS W →
    IsRepresentableEtale B S hS b → IsLocallyOfFiniteType B S hS t →
    IsRigSurjective B S hS p →
    HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P p →
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (p ≫ t ≫ b) →
        HasPropertyOnAffineChartMap B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P t

/-- The chart data the source's argument consumes, assembled from the hypotheses of Stacks
0GH6 at one affine étale chart square over `g`. The four conclusions are, in order: the chart
morphism `t` is locally of finite type; the base change `X ×_Y V ⟶ V` of `f` along the chart
`a : V ⟶ Y` is rig-surjective; it has `P` on every affine étale diagram over it; and so does
its composite with `t ≫ b`, which is its composite with `g ∘ f` through the projection to
`X`. -/
private theorem chartData
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbase : TopologicalRing.IsStableUnderBaseChangeBy.{u} P
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ))
    (htransfer : TransfersBaseChangeOnAffineEtaleDiagrams B S hS)
    (hetaleAdic : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS w)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    {X Y Z V W : FppfSheaf B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {a : V ⟶ Y} {b : W ⟶ Z} {t : V ⟶ W}
    (hgft : IsLocallyOfFiniteType B S hS g) (hfft : IsLocallyOfFiniteType B S hS f)
    (hfs : IsRigSurjective B S hS f)
    (hfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hgfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g))
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (ha : IsRepresentableEtale B S hS a) (hcomm : a ≫ g = t ≫ b) :
    IsLocallyOfFiniteType B S hS t ∧ IsRigSurjective B S hS (pullback.snd f a) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f a) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P
        (pullback.snd f a ≫ t ≫ b) := by
  have haft : IsLocallyOfFiniteType B S hS a := hetaleFiniteType a ha
  have htb : IsLocallyOfFiniteType B S hS (t ≫ b) := by
    rw [← hcomm]
    exact IsLocallyOfFiniteType.comp B S hS a g haft hgft
  have hsq : IsPullback (pullback.snd f a) (pullback.fst f a) a f :=
    (IsPullback.of_hasPullback f a).flip
  have hfstetale : IsRepresentableEtale B S hS (pullback.fst f a) :=
    isRepresentableEtale_of_isPullback B S hS hsq ha
  have heq : pullback.snd f a ≫ t ≫ b = pullback.fst f a ≫ f ≫ g :=
    calc pullback.snd f a ≫ t ≫ b
        = pullback.snd f a ≫ a ≫ g := by rw [hcomm]
      _ = (pullback.snd f a ≫ a) ≫ g := (Category.assoc _ _ _).symm
      _ = (pullback.fst f a ≫ f) ≫ g := by rw [pullback.condition]
      _ = pullback.fst f a ≫ f ≫ g := Category.assoc _ _ _
  refine ⟨IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t b hW htb,
    (IsRigSurjective.of_isPullback B S hS hsq hfft haft hfs).2,
    htransfer _ _ hbase f a hfP (hetaleAdic a ha), ?_⟩
  rw [heq]
  exact hasPropertyOnEveryAffineEtaleDiagram_comp_of_isRepresentableEtale B S hS _ P
    (pullback.fst f a) (f ≫ g) hfstetale hgfP


/-- The shared argument of the two cases of Stacks 0GH6: at one affine étale chart square over
`g`, the hypotheses produce the chart data the source's argument consumes, namely that the chart
morphism `t` is locally of finite type and that the base change `X ×_Y V ⟶ V` of `f` along the
chart `a : V ⟶ Y` is rig-surjective, has `P` on every affine étale diagram over it, and so does
its composite with `t ≫ b`, which is its composite with `g ∘ f` through the projection to `X`.
The chart-level descent `hdescent` then gives `P` on every affine étale diagram over `g`. -/
private theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isRigSurjective
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbase : TopologicalRing.IsStableUnderBaseChangeBy.{u} P
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ))
    (htransfer : TransfersBaseChangeOnAffineEtaleDiagrams B S hS)
    (hetaleAdic : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS w)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    (hdescent : HasRigSurjectiveChartDescent B S hS P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgft : IsLocallyOfFiniteType B S hS g) (hfft : IsLocallyOfFiniteType B S hS f)
    (hfs : IsRigSurjective B S hS f)
    (hfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hgfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g)) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g := by
  intro V W a b t hV hW ha hb hcomm
  have haft : IsLocallyOfFiniteType B S hS a := hetaleFiniteType a ha
  have htb : IsLocallyOfFiniteType B S hS (t ≫ b) := by
    rw [← hcomm]
    exact IsLocallyOfFiniteType.comp B S hS a g haft hgft
  have hsq : IsPullback (pullback.snd f a) (pullback.fst f a) a f :=
    (IsPullback.of_hasPullback f a).flip
  have hfstetale : IsRepresentableEtale B S hS (pullback.fst f a) :=
    isRepresentableEtale_of_isPullback B S hS hsq ha
  have heq : pullback.snd f a ≫ t ≫ b = pullback.fst f a ≫ f ≫ g :=
    calc pullback.snd f a ≫ t ≫ b
        = pullback.snd f a ≫ a ≫ g := by rw [hcomm]
      _ = (pullback.snd f a ≫ a) ≫ g := (Category.assoc _ _ _).symm
      _ = (pullback.fst f a ≫ f) ≫ g := by rw [pullback.condition]
      _ = pullback.fst f a ≫ f ≫ g := Category.assoc _ _ _
  exact hdescent (pullback.snd f a) t b hV hW hb
    (IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t b hW htb)
    (IsRigSurjective.of_isPullback B S hS hsq hfft haft hfs).2
    (htransfer _ _ hbase f a hfP (hetaleAdic a ha))
    (heq ▸ hasPropertyOnEveryAffineEtaleDiagram_comp_of_isRepresentableEtale B S hS _ P
      (pullback.fst f a) (f ≫ g) hfstetale hgfP)

/-- **Stacks 0GH6**, the rig-smooth case, carrying four hypotheses. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of formal algebraic spaces over `S`. If `g` is locally of finite type,
`f` is rig-smooth and rig-surjective, and `f ≫ g` is rig-smooth, then `g` is rig-smooth.

Rig-smoothness of `g` is tested on affine étale chart squares over it, by conditions (1) and
(2) of Stacks 0GCQ. At such a square the three hypotheses produce exactly the data the source's
argument consumes: the chart morphism `t` is locally of finite type, the base change
`X ×_Y V ⟶ V` of `f` along the chart of `Y` is rig-surjective and rig-smooth on charts, and its
composite with `t ≫ b` — that is, its composite with `g ∘ f` through the projection to `X` — is
rig-smooth on charts.

The hypotheses carried are `hlocal`, which is Stacks 0GCK; `htransfer`, the transfer of Remark
0GBG to formal algebraic spaces; `hetaleAdic` and `hetaleFiniteType`, that a representable étale
morphism is adic and locally of finite type; and `hdescent`, the chart-level argument of the
source. Local finiteness of type of `f`, which Definition 0AQQ presupposes, is the hypothesis
`hfft`. -/
@[stacks 0GH6 "the rig-smooth case, assuming Stacks 0GCK (hlocal), the transfer of Remark 0GBG \
to formal algebraic spaces (htransfer), that a representable étale morphism is adic and locally \
of finite type (hetaleAdic, hetaleFiniteType), and the chart-level argument of the source's \
proof (hdescent)"]
theorem isRigSmooth_of_comp_of_isRigSurjective
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigSmoothArrow φ))
    (htransfer : TransfersBaseChangeOnAffineEtaleDiagrams B S hS)
    (hetaleAdic : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS w)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    (hdescent : HasRigSurjectiveChartDescent B S hS
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigSmoothArrow φ))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgft : IsLocallyOfFiniteType B S hS g) (hfft : IsLocallyOfFiniteType B S hS f)
    (hf : IsRigSmooth B S hS f) (hfs : IsRigSurjective B S hS f)
    (hgf : IsRigSmooth B S hS (f ≫ g)) :
    IsRigSmooth B S hS g := by
  refine (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mpr ?_
  exact hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isRigSurjective B S hS _
    (TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic hlocal)
    htransfer hetaleAdic hetaleFiniteType hdescent f g hgft hfft hfs
    ((isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
    ((isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hgf)

/-- **Stacks 0GH6**, the rig-étale case, carrying four hypotheses. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of formal algebraic spaces over `S`. If `g` is locally of finite type,
`f` is rig-étale and rig-surjective, and `f ≫ g` is rig-étale, then `g` is rig-étale.

The proof is the proof of the rig-smooth case with rig-smoothness of arrows of `WAdm^{Noeth}`
replaced by rig-étaleness throughout: conditions (1) and (2) of Stacks 0GCZ replace those of
Stacks 0GCQ, and Stacks 0GCW replaces Stacks 0GCL as the base-change input. The hypotheses are
the same four, with `hlocal` now Stacks 0AQL. -/
@[stacks 0GH6 "the rig-étale case, assuming Stacks 0AQL (hlocal), the transfer of Remark 0GBG \
to formal algebraic spaces (htransfer), that a representable étale morphism is adic and locally \
of finite type (hetaleAdic, hetaleFiniteType), and the chart-level argument of the source's \
proof (hdescent)"]
theorem isRigEtale_of_comp_of_isRigSurjective
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    (htransfer : TransfersBaseChangeOnAffineEtaleDiagrams B S hS)
    (hetaleAdic : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS w)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    (hdescent : HasRigSurjectiveChartDescent B S hS
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgft : IsLocallyOfFiniteType B S hS g) (hfft : IsLocallyOfFiniteType B S hS f)
    (hf : IsRigEtale B S hS f) (hfs : IsRigSurjective B S hS f)
    (hgf : IsRigEtale B S hS (f ≫ g)) :
    IsRigEtale B S hS g := by
  refine (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mpr ?_
  exact hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isRigSurjective B S hS _
    (TopologicalRing.rigEtale_isStableUnderBaseChangeByAdic hlocal)
    htransfer hetaleAdic hetaleFiniteType hdescent f g hgft hfft hfs
    ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
    ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hgf)

/-- **Stacks 0GH6**, the rig-étale case, carrying three hypotheses. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of formal algebraic spaces over `S`. If `g` is locally of finite type,
`f` is rig-étale and rig-surjective, and `f ≫ g` is rig-étale, then `g` is rig-étale.

This is `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isRigSurjective` with its
hypothesis `hlocal` discharged: the locality of rig-étaleness is Stacks 0AQL,
`Rig.rigEtale_propertyIsLocalNoetherian`, which this library proves. The transfer of
Remark 0GBG, the two facts about representable étale morphisms and the chart-level descent
remain inputs. -/
theorem isRigEtale_of_comp_of_isRigSurjective'
    (htransfer : TransfersBaseChangeOnAffineEtaleDiagrams B S hS)
    (hetaleAdic : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS w)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    (hdescent : HasRigSurjectiveChartDescent B S hS
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgft : IsLocallyOfFiniteType B S hS g) (hfft : IsLocallyOfFiniteType B S hS f)
    (hf : IsRigEtale B S hS f) (hfs : IsRigSurjective B S hS f)
    (hgf : IsRigEtale B S hS (f ≫ g)) :
    IsRigEtale B S hS g :=
  isRigEtale_of_comp_of_isRigSurjective B S hS Rig.rigEtale_propertyIsLocalNoetherian
    htransfer hetaleAdic hetaleFiniteType hdescent f g hgft hfft hf hfs hgf

end AlgebraicGeometry.FormalSpace

end
