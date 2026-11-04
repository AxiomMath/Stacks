module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# Immersions into a space smooth over the target of a local complete intersection morphism

Let `f : X ⟶ Y` be a local complete intersection morphism of algebraic spaces over a scheme `S`,
let `P` be an algebraic space smooth over `Y`, let `U ⟶ X` be an étale morphism of algebraic
spaces and let `i : U ⟶ P` be an immersion of algebraic spaces over `Y`. Then `i` is a
Koszul-regular immersion of algebraic spaces. This is **Stacks 06C5**, the algebraic-spaces form
of Stacks 069G.

## Main results

* `AlgebraicGeometry.Space.isKoszulRegularImmersion_of_isLocalCompleteIntersection`:
  **Stacks 06C5**.
* `AlgebraicGeometry.koszulRegularCompSmooth`: the Koszul case of Stacks 0693, in the packaged
  form that Stacks 069G takes as a hypothesis.
* `isKoszulRegularImmersion_of_pullback_snd_of_etale_surjective`, in the namespace
  `Stacks.AlgebraicGeometry.RegularIdealSheaf`: Koszul-regularity of an immersion of schemes
  descends along a surjective étale base change.

## Implementation notes

Koszul-regularity of a representable morphism of algebraic spaces, Stacks 06BN part (1), is a
condition on the represented base change of the morphism over *every* étale scheme chart of the
target, so the proof fixes such a chart `q : V ⟶ P` and must show that the base change
`t : U ×_P V ⟶ V` is a Koszul-regular immersion of schemes. The source argues instead on one
surjective chart, which is equivalent by Stacks 06BM; that equivalence needs Koszul-regularity to
be étale local on the target, which is the descent step below, so nothing is gained by it and the
every-chart form is discharged directly.

The scheme morphism `t` is an immersion, but `V ⟶ P ⟶ Y` is only smooth, not étale, so `t` does
not itself sit in a commuting square of étale charts of `f`. An étale atlas `Y₀ ⟶ Y` is
therefore pulled back along `V ⟶ Y`, giving `C = V ×_Y Y₀` with `C ⟶ V` surjective étale and
`C ⟶ Y₀` smooth — the chart condition of Stacks 03ZC for the smooth `P ⟶ Y` applied to the étale
chart `C ⟶ V ⟶ P` of `P`. Over `R = (U ×_P V) ×_V C` the chart condition of Stacks 06C4 for `f`,
applied to the étale chart `R ⟶ U ×_P V ⟶ U ⟶ X` of `X` and to the atlas of `Y`, makes
`R ⟶ Y₀` a local complete intersection morphism of schemes, and `R ⟶ C` is an immersion over
`Y₀` into a scheme smooth over `Y₀`. Stacks 069G therefore applies to the open `⊤ ⊆ R` and makes
`R ⟶ C` Koszul-regular; the conclusion for `t` is the descent along the surjective étale
`C ⟶ V`.

That descent is Stacks 0694 for the Koszul-regular clause, which this development has only for a
*quasi-compact* immersion, that qualifier coming from the affine criteria its proof rests on. The
qualifier is removed here by running the descent on the canonical closed factor
`U ×_P V ⟶ (closure of the image)`, a closed immersion and hence quasi-compact: Stacks 067S
removes from the target the open immersion by which the two base changes differ, the fpqc
locality of Stacks 0694 descends the closed factor along the surjective étale cover of the open,
and the Koszul case of Stacks 0693 puts the open immersion back. That Koszul case, which Stacks
069G takes as the explicit hypothesis `AlgebraicGeometry.KoszulRegularCompSmooth`, is available
in this development as
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth`, so the
hypothesis is discharged here rather than propagated.

## References

* [Stacks Project, Lemma 76.48.2 (06C5)](https://stacks.math.columbia.edu/tag/06C5)
* [Stacks Project, Lemma 37.62.3 (069G)](https://stacks.math.columbia.edu/tag/069G)
* [Stacks Project, Definition 76.44.2 (06BN)](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Definition 76.48.1 (06C4)](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Lemma 31.23.12 (0693)](https://stacks.math.columbia.edu/tag/0693)
* [Stacks Project, Lemma 31.23.9 (067S)](https://stacks.math.columbia.edu/tag/067S)
* [Stacks Project, Lemma 35.26.1 (0694)](https://stacks.math.columbia.edu/tag/0694)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Koszul-regularity transports along an equality of immersions. The instance argument of
`IsKoszulRegularImmersion` makes the corresponding rewrite fail on the motive. -/
private theorem isKoszulRegularImmersion_congr {Z X : Scheme.{u}} {i j : Z ⟶ X}
    [_root_.AlgebraicGeometry.IsImmersion i] [_root_.AlgebraicGeometry.IsImmersion j] (h : i = j)
    (hi : IsKoszulRegularImmersion i) : IsKoszulRegularImmersion j := by
  subst h; exact hi

/-- Koszul-regularity of an immersion `f` transports along an isomorphism precomposition equal
to another immersion `g`. -/
private theorem isKoszulRegularImmersion_of_iso_hom_comp_eq {A B X : Scheme.{u}} (e : A ≅ B)
    {f : B ⟶ X} {g : A ⟶ X} [_root_.AlgebraicGeometry.IsImmersion f]
    [_root_.AlgebraicGeometry.IsImmersion g] (h : e.hom ≫ f = g)
    (hf : IsKoszulRegularImmersion f) : IsKoszulRegularImmersion g :=
  isKoszulRegularImmersion_congr h (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_iso_hom_comp
    e f hf)

/-- **Koszul-regularity of an immersion of schemes descends along a surjective étale base
change.** This is the Koszul-regular clause of Stacks 0694 for an étale covering by a single
morphism, with no quasi-compactness hypothesis on the immersion. -/
theorem isKoszulRegularImmersion_of_pullback_snd_of_etale_surjective {Z X X' : Scheme.{u}}
    (i : Z ⟶ X) (g : X' ⟶ X) [_root_.AlgebraicGeometry.IsImmersion i] [Etale g] [Surjective g]
    (h : IsKoszulRegularImmersion (pullback.snd i g)) : IsKoszulRegularImmersion i := by
  have hiV : i.liftCoborder ≫ i.coborderRange.ι = i := Scheme.Hom.liftCoborder_ι i
  -- The two base changes differ by the open immersion `(i.coborderRange) ×_X X' ⟶ X'`.
  have hcomp : (pullbackRightPullbackFstIso i.coborderRange.ι g i.liftCoborder ≪≫
        pullback.congrHom hiV rfl).hom ≫ pullback.snd i g =
      pullback.snd i.liftCoborder (pullback.fst i.coborderRange.ι g) ≫
        pullback.snd i.coborderRange.ι g := by
    simp [pullback.map, pullback.lift_snd]
  have hreg : IsKoszulRegularImmersion
      (pullback.snd i.liftCoborder (pullback.fst i.coborderRange.ι g)) :=
    isKoszulRegularImmersion_of_comp_of_smooth _ (pullback.snd i.coborderRange.ι g)
      (isKoszulRegularImmersion_of_iso_hom_comp_eq _ hcomp h)
  -- The closed factor of `i` is quasi-compact, so Stacks 0694 descends it.
  let Q : MorphismProperty Scheme.{u} :=
    (fun _ _ j => ∃ hj : _root_.AlgebraicGeometry.IsImmersion j,
      @IsKoszulRegularImmersion _ _ j hj) ⊓ (@QuasiCompact : MorphismProperty Scheme.{u})
  have hQfpqc : Q.IsLocalAtTarget Scheme.fpqcPrecoverage :=
    isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc
  have hQetale : Q.IsLocalAtTarget Scheme.etalePrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.etalePrecoverage_le_fpqcPrecoverage
  have hCover : Presieve.singleton (pullback.fst i.coborderRange.ι g) ∈
      Scheme.etalePrecoverage.coverings i.coborderRange.toScheme := by
    rw [Scheme.etalePrecoverage]
    exact (Scheme.singleton_mem_precoverage_iff (@Etale) _).2
      ⟨(inferInstance : Surjective (pullback.fst i.coborderRange.ι g)).surj, inferInstance⟩
  have hQ : Q i.liftCoborder := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := Q) hCover
    intro W' g' _ hg'
    cases hg'
    exact ⟨⟨inferInstance, hreg⟩, inferInstance⟩
  obtain ⟨⟨_, hiVreg⟩, -⟩ := hQ
  -- Putting the open immersion back is the Koszul case of Stacks 0693.
  exact isKoszulRegularImmersion_congr hiV
    (isKoszulRegularImmersion_comp_of_smooth i.liftCoborder i.coborderRange.ι hiVreg)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- **The Koszul case of Stacks 0693.** A Koszul-regular immersion of schemes followed by a
smooth morphism of its target is Koszul-regular as soon as the composite is an immersion. -/
@[sga "6 VIII 1.3" "converse direction"]
public theorem koszulRegularCompSmooth : KoszulRegularCompSmooth.{u} := by
  intro Y X T a p _ _ _ ha
  exact isKoszulRegularImmersion_comp_of_smooth a p ha

/-- **Stacks 069G on a chart, followed by the descent of Stacks 0694.** Let `t` be an immersion of
schemes whose base change `k` along a surjective étale `u` composes with a smooth `v` to a local
complete intersection morphism `w`. Then `t` is a Koszul-regular immersion. -/
private theorem isKoszulRegularImmersion_of_isPullback_of_isLocalCompleteIntersectionMorphism
    {R C V Z Y₀ : Scheme.{u}} {r : R ⟶ Z} {k : R ⟶ C} {t : Z ⟶ V} {u : C ⟶ V} {v : C ⟶ Y₀}
    {w : R ⟶ Y₀} [_root_.AlgebraicGeometry.IsImmersion t] [Etale u] [Surjective u] [Smooth v]
    (hpb : IsPullback r k t u) (hw : w = k ≫ v)
    (hLCI : IsLocalCompleteIntersectionMorphism w) : IsKoszulRegularImmersion t := by
  have : _root_.AlgebraicGeometry.IsImmersion k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have htriangle : (⊤ : R.Opens).ι ≫ w = ((⊤ : R.Opens).ι ≫ k) ≫ v := by
    simp [hw, Category.assoc]
  have hkTop := isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism
    koszulRegularCompSmooth w v ⊤ ((⊤ : R.Opens).ι ≫ k) hLCI htriangle
  have htop : (Scheme.topIso R).symm.hom ≫ (⊤ : R.Opens).ι ≫ k = k := by simp
  have hkScheme := isKoszulRegularImmersion_of_iso_hom_comp_eq _ htop hkTop
  have hkCanonical := isKoszulRegularImmersion_of_iso_hom_comp_eq _ hpb.isoPullback_inv_snd hkScheme
  exact isKoszulRegularImmersion_of_pullback_snd_of_etale_surjective t u hkCanonical

namespace Space

/-- The étale morphism property pulled back along the functor taking an object of the big fppf
site to its scheme is stable under composition, étaleness of scheme morphisms being so. -/
private theorem etale_inverseImage_isStableUnderComposition (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  ⟨fun x y hx hy => by
    show Etale ((BigFppfOver.toScheme B S hS).map (x ≫ y))
    rw [Functor.map_comp]
    have : Etale ((BigFppfOver.toScheme B S hS).map x) := hx
    have : Etale ((BigFppfOver.toScheme B S hS).map y) := hy
    infer_instance⟩

/-- The étale morphism property pulled back along the functor taking an object of the big fppf
site to its scheme is stable under base change, étaleness of scheme morphisms being so. -/
private theorem etale_inverseImage_isStableUnderBaseChange (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun sq => MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u})
    (sq.map (BigFppfOver.toScheme B S hS))⟩

/-- A morphism of the big fppf site whose underlying scheme morphism is étale is étale as a
morphism of representable presheaves, étaleness of scheme morphisms being stable under base
change. -/
private theorem etalePresheaf_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A C : BigFppfOver B S hS} (g : A ⟶ C)
    (hg : Etale ((BigFppfOver.toScheme B S hS).map g)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g) := by
  have : HasLimitsOfShape WalkingCospan B.Schemes := inferInstance
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have := etale_inverseImage_isStableUnderBaseChange B S hS
  exact MorphismProperty.relative_map hg

/-- The commuting square of étale charts of a morphism `f : X ⟶ Y`: if `b` is an atlas of `Y`
pulled back to `v : C ⟶ Y₀` along `q ≫ p`, if `R` is the fibre product of `t` and `u`, and if `s`
is the base change of `i` along `q`, then the chart `R ⟶ C ⟶ Y₀` of the atlas agrees with the
chart `R ⟶ Z ⟶ U ⟶ X` of `X` followed by `f`. -/
private theorem chart_comp_atlas_comm {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    (G : 𝒞 ⥤ 𝒟) {Y₀ C V Z R : 𝒞} {X Y U P : 𝒟} {b : G.obj Y₀ ⟶ Y} {v : C ⟶ Y₀} {u : C ⟶ V}
    {q : G.obj V ⟶ P} {p : P ⟶ Y} {s : G.obj Z ⟶ U} {i : U ⟶ P} {t : Z ⟶ V} {r : R ⟶ Z}
    {k : R ⟶ C} {a : U ⟶ X} {f : X ⟶ Y} (hAtlasSquare : G.map v ≫ b = G.map u ≫ q ≫ p)
    (hRpbw : G.map r ≫ G.map t = G.map k ≫ G.map u) (hPullw : s ≫ i = G.map t ≫ q)
    (hcomm : a ≫ f = i ≫ p) : G.map (k ≫ v) ≫ b = ((G.map r ≫ s) ≫ a) ≫ f :=
  calc G.map (k ≫ v) ≫ b = G.map k ≫ G.map v ≫ b := by
        simp [Category.assoc]
    _ = G.map k ≫ G.map u ≫ q ≫ p := by rw [hAtlasSquare]
    _ = G.map r ≫ G.map t ≫ q ≫ p := by
        simpa only [Category.assoc] using congrArg (fun x => x ≫ q ≫ p) hRpbw.symm
    _ = G.map r ≫ s ≫ i ≫ p := by
        have hw : s ≫ i = G.map t ≫ q := hPullw
        simpa only [Category.assoc] using
          congrArg (fun x => G.map r ≫ x ≫ p) hw.symm
    _ = G.map r ≫ s ≫ a ≫ f := by rw [← hcomm]
    _ = ((G.map r ≫ s) ≫ a) ≫ f := by simp [Category.assoc]

/-- **Stacks 06C5.** Let `f : X ⟶ Y` be a local complete intersection morphism of algebraic
spaces over `S`, let `p : P ⟶ Y` be smooth, let `a : U ⟶ X` be étale and let `i : U ⟶ P` be an
immersion over `Y`. Then `i` is a Koszul-regular immersion of algebraic spaces. -/
@[stacks 06C5]
theorem isKoszulRegularImmersion_of_isLocalCompleteIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y U P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hU : IsAlgebraicSpace B S hS U) (_hP : IsAlgebraicSpace B S hS P)
    (f : X ⟶ Y) (a : U ⟶ X) (i : U ⟶ P) (p : P ⟶ Y)
    (hf : IsLocalCompleteIntersection B S hS f) (ha : IsEtale B S hS a)
    (hi : IsImmersion B S hS i) (hp : IsSmooth B S hS p) (hcomm : a ≫ f = i ≫ p) :
    IsKoszulRegularImmersion B S hS i := by
  have : HasLimitsOfShape WalkingCospan B.Schemes := inferInstance
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨hrep, himm⟩ := hi
  refine ⟨hrep, ?_⟩
  intro V q hq
  let T := BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have hEcomp : E.IsStableUnderComposition := etale_inverseImage_isStableUnderComposition B S hS
  have hEbc : E.IsStableUnderBaseChange := etale_inverseImage_isStableUnderBaseChange B S hS
  have : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  have : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  -- The base change of `i` over the chart `q` of `P`.
  let t := hrep.snd q
  let s := hrep.fst q
  have hPull := hrep.isPullback q
  have himmT : _root_.AlgebraicGeometry.IsImmersion (T.map t) := himm q s t hPull
  refine ⟨himmT, ?_⟩
  -- An étale atlas of `Y`, pulled back along `V ⟶ P ⟶ Y`.
  obtain ⟨Y₀, b, hbSurj, hb⟩ := hY.exists_atlas
  let hYrep : yoneda.relativelyRepresentable b := hb.1
  let C := hYrep.pullback (q ≫ p)
  let v := hYrep.fst' (q ≫ p)
  let u := hYrep.snd (q ≫ p)
  have hu : Etale (T.map u) := hb.2 (q ≫ p) (yoneda.map v) u (hYrep.isPullback' (q ≫ p))
  have huSurj : Surjective (T.map u) :=
    hbSurj.2 (q ≫ p) (yoneda.map v) u (hYrep.isPullback' (q ≫ p))
  -- The chart `R` of the source of `i` lying over the atlas of `Y`.
  let R := Limits.pullback t u
  let r := Limits.pullback.fst t u
  let k := Limits.pullback.snd t u
  have hRpb : IsPullback (yoneda.map r) (yoneda.map k) (yoneda.map t) (yoneda.map u) :=
    (IsPullback.of_hasPullback t u).map yoneda
  have hRpbT : IsPullback (T.map r) (T.map k) (T.map t) (T.map u) :=
    (IsPullback.of_hasPullback t u).map T
  have hr : Etale (T.map r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hRpbT.flip hu
  have hsE : E.presheaf s :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hPull.flip hq
  have hRchart : E.presheaf (yoneda.map r ≫ s) :=
    E.presheaf.comp_mem _ _ (etalePresheaf_yoneda_map B S hS r hr) hsE
  have hRchartX : E.presheaf ((yoneda.map r ≫ s) ≫ a) := ha R (yoneda.map r ≫ s) hRchart
  have hCchart : E.presheaf (yoneda.map u ≫ q) :=
    E.presheaf.comp_mem _ _ (etalePresheaf_yoneda_map B S hS u hu) hq
  have hAtlasSquare : yoneda.map v ≫ b = yoneda.map u ≫ q ≫ p :=
    (hYrep.isPullback' (q ≫ p)).w
  have hvSmooth : Smooth (T.map v) := hp C Y₀ (yoneda.map u ≫ q) b v hCchart hb hAtlasSquare
  -- The square of étale charts of `f` through `R` and the atlas of `Y`.
  have hLCIcomm := chart_comp_atlas_comm yoneda hAtlasSquare hRpb.w hPull.w hcomm
  have hLCI : IsLocalCompleteIntersectionMorphism (T.map (k ≫ v)) :=
    hf R Y₀ ((yoneda.map r ≫ s) ≫ a) b (k ≫ v) hRchartX hb hLCIcomm
  -- Stacks 069G over the chart `Y₀` of `Y`, then descent along the surjective étale `C ⟶ V`.
  exact isKoszulRegularImmersion_of_isPullback_of_isLocalCompleteIntersectionMorphism hRpbT
    (T.map_comp k v) hLCI

end Space

end AlgebraicGeometry

end
