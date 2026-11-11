module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare
public import StacksFrontier.RingTheory.Smooth.FaithfullyFlatDescent

/-!
# Formal smoothness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. Formal smoothness of a morphism of
algebraic spaces over `S` is the infinitesimal lifting property
`AlgebraicGeometry.Space.FormallySmooth` of **Stacks 049S**, part (1), and **Stacks 06CS** asserts
that it is local on the target for the fpqc topology of **Stacks 03YH**.

The ascent half is base change, **Stacks 049U**. For the descent half the test objects of the
lifting property are affine objects of the site, so a lifting problem for `f : X ⟶ Y` is a lifting
problem for the base change of `f` along a scheme-valued point of `Y` with affine source; over
such a point the fpqc condition of **Stacks 03MQ** supplies a finite family of affine objects
which covers it and refines the given covering, and the base changes of `f` along the members of
that family are formally smooth. On an étale scheme chart of the source this makes the chart
morphism affine-locally formally smooth — condition (3) of **Stacks 0D0F** — over each member of
the family, and affine-local formal smoothness descends along the family, because formal
smoothness of ring maps descends along faithfully flat ring maps (**Stacks 06CM**).

## Main definitions

* `AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent` is the implication (3) ⟹ (1) of
  **Stacks 061K** with condition (3) read on affine opens: a morphism of algebraic spaces with
  one surjective étale chart square whose scheme morphism is affine-locally formally smooth is
  formally smooth.

## Main results

* `AlgebraicGeometry.Space.formallySmoothAffineLocally_isLocalAtTarget_fpqc`: affine-local formal
  smoothness of morphisms of *schemes* is local on the base for the fpqc topology, from
  **Stacks 06CM**.
* `AlgebraicGeometry.Space.formallySmooth_iff_affine_pullback`: formal smoothness of a morphism
  of algebraic spaces over `S` is detected by its base changes along the scheme-valued points of
  the target whose source is an affine object of the site.
* `AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc_of_chartDescent`: fpqc locality
  on the base of formal smoothness, from an instance of
  `AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent`, and its instance form
  `AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc`.

## Implementation notes

The class `AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent` isolates the one input the
argument below needs beyond fpqc descent of affine-local formal smoothness of schemes: the
converse implication of [Stacks Project, Tag 061K], with condition (3) read on affine opens. It
holds for every big fppf site and every base scheme, by
`AlgebraicGeometry.Space.formallySmoothEtaleChartDescent` of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/FpqcLocalAtTarget.lean`, which deduces it
from [Stacks Project, Tag 061K], `AlgebraicGeometry.Space.formallySmooth_tfae_etaleCharts`; that
file also states [Stacks Project, Tag 06CS] itself, as
`AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc'`. The forward implication of
Tag 061K, in the same affine-open reading, is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothAffineLocally`.

The source reduces Tag 06CS to Tag 061K in both directions together with the scheme-level fpqc
locality of formal smoothness; reading condition (3) of Tag 0D0F in place of the infinitesimal
lifting property of a scheme morphism lets the scheme-level step be fpqc descent of affine-local
formal smoothness, which is [Stacks Project, Tag 06CM] on affine opens.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049U](https://stacks.math.columbia.edu/tag/049U)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
* [Stacks Project, Tag 06CM](https://stacks.math.columbia.edu/tag/06CM)
* [Stacks Project, Tag 06CS](https://stacks.math.columbia.edu/tag/06CS)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Faithfully flat descent of affine-local formal smoothness -/

/-- **Stacks 06CM** in the shape `CategoryTheory.MorphismProperty.DescendsAlong` asks for: formal
smoothness of a ring map is implied by formal smoothness of its base change along a faithfully
flat ring map. -/
theorem formallySmooth_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.FormallySmooth RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.FormallySmooth.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [RingHom.formallySmooth_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact (Algebra.FormallySmooth.iff_tensorProduct_of_faithfullyFlat R T S).mpr h'

/-- Affine-local formal smoothness of morphisms of schemes is stable under base change, formal
smoothness of ring maps being so. -/
private instance formallySmoothAffineLocally_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Smooth.FormallySmoothAffineLocally.{u}) :=
  HasRingHomProperty.isStableUnderBaseChange
    (P := @Stacks.Smooth.FormallySmoothAffineLocally.{u})
    RingHom.FormallySmooth.isStableUnderBaseChange

/-- Affine-local formal smoothness of morphisms of schemes descends along surjective flat
quasi-compact morphisms, by **Stacks 06CM** on sections over affine opens. -/
instance formallySmoothAffineLocally_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Stacks.Smooth.FormallySmoothAffineLocally.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat formallySmooth_codescendsAlong_faithfullyFlat

/-- Affine-local formal smoothness of morphisms of schemes — condition (3) of
[Stacks Project, Tag 0D0F] — is local on the base for the fpqc topology.

The three hypotheses of the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` are
Zariski locality on the target and stability under flat base change, both of which come from the
affine-local description by a ring-map property, and descent along surjective flat quasi-compact
morphisms, which is **Stacks 06CM**. -/
theorem formallySmoothAffineLocally_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Stacks.Smooth.FormallySmoothAffineLocally.{u})
      Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@Stacks.Smooth.FormallySmoothAffineLocally.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @Stacks.Smooth.FormallySmoothAffineLocally.{u})
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Stacks.Smooth.FormallySmoothAffineLocally.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-! ### Reduction of the lifting property to affine test objects -/

/-- **Stacks 049U** read as a test criterion: formal smoothness of a morphism of algebraic spaces
over `S` is equivalent to formal smoothness of all of its base changes along the scheme-valued
points of its target whose source is an affine object of the site.

Each such base change is formally smooth when `f` is, by Stacks 049U. Conversely a lifting
problem for `f` along a square-zero closed immersion `i : T ⟶ T'` of affine objects is a lifting
problem for the base change of `f` along the point of the target classified by the given section
over `T'`: the section over `T` and the morphism `i` make up a point of the fibre product over
`T`, and the identity of `T'` is the point of `T'` it has to lift over. -/
@[ega "IV 17.1.3" "(iii), special case"]
theorem formallySmooth_iff_affine_pullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    formallySmoothProperty B S hS f ↔
      ∀ (T : BigAffineFppf B S hS)
        (g : schemeSpace ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
        formallySmoothProperty B S hS (pullback.snd f g) := by
  constructor
  · intro hf T g
    exact MorphismProperty.pullback_snd (P := formallySmoothProperty B S hS) f g hf
  · intro hf T T' hT hT' i hi x y hxy
    let Taff : BigAffineFppf B S hS := ⟨T', hT'⟩
    let T₁ := (BigAffineFppf.inclusion B S hS).obj Taff
    let iAff : T ⟶ T₁ := i
    let b : yoneda.obj T₁ ⟶ Y.obj := yonedaEquiv.symm y
    let g : schemeSpace T₁ ⟶ Y := ObjectProperty.homMk b
    have hcompat : yoneda.map iAff ≫ b = yonedaEquiv.symm x ≫ f.hom := by
      apply yonedaEquiv.injective
      simpa [b, yonedaEquiv_apply] using hxy.symm
    let sqh := (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)).flip
    let xmap : yoneda.obj T ⟶ (pullback f g).obj :=
      sqh.lift (yoneda.map iAff) (yonedaEquiv.symm x) hcompat
    have xmap_snd : xmap ≫ (pullback.snd f g).hom = yoneda.map iAff := sqh.lift_fst _ _ _
    have xmap_fst : xmap ≫ (pullback.fst f g).hom = yonedaEquiv.symm x := sqh.lift_snd _ _ _
    let xP := yonedaEquiv xmap
    let yP : (schemeSpace T₁).obj.obj (Opposite.op T₁) := 𝟙 T₁
    have hxyP : (pullback.snd f g).hom.app (Opposite.op T) xP =
        (schemeSpace T₁).obj.map iAff.op yP := by
      change yonedaEquiv (xmap ≫ (pullback.snd f g).hom) = iAff
      rw [xmap_snd]
      rfl
    obtain ⟨z, hz⟩ := (hf Taff g) T T' hT hT' i hi xP yP hxyP
    let z' := (pullback.fst f g).hom.app (Opposite.op T') z
    refine ⟨z', ?_, ?_⟩
    · calc
        X.obj.map i.op z' = (pullback.fst f g).hom.app (Opposite.op T)
            ((pullback f g).obj.map i.op z) :=
          (NatTrans.naturality_apply (pullback.fst f g).hom i.op z).symm
        _ = (pullback.fst f g).hom.app (Opposite.op T) xP := congrArg _ hz.1
        _ = x := by
          change yonedaEquiv (xmap ≫ (pullback.fst f g).hom) = x
          rw [xmap_fst, Equiv.apply_symm_apply]
    · have hc := congrArg
        (fun k : (pullback f g).obj ⟶ Y.obj => k.app (Opposite.op T') z) sqh.w
      have hc' : f.hom.app (Opposite.op T') z' =
          g.hom.app (Opposite.op T') ((pullback.snd f g).hom.app (Opposite.op T') z) := by
        simpa only [z', NatTrans.comp_app, ConcreteCategory.comp_apply] using hc.symm
      rw [hz.2] at hc'
      have hgy : g.hom.app (Opposite.op T') yP = y := by
        change b.app (Opposite.op T') (𝟙 T₁) = y
        simp [b, show (𝟙 T₁).op = 𝟙 (Opposite.op T₁) from rfl]
      exact hc'.trans hgy

/-! ### The chart morphism of a base change -/

/-- The identity of a representable presheaf is étale in the sense of the relative property
`MorphismProperty.presheaf`. -/
private theorem presheaf_id_etale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) := by
  refine presheaf_id_of_iso B S hS _ ?_ V
  intro A C e he
  have : IsIso e := he
  exact (inferInstance : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map e))

/-- The scheme morphism of an étale chart square of `f : X ⟶ V` base changed along `k : V' ⟶ V`
is affine-locally formally smooth as soon as that base change of `f` is formally smooth.

The chart of the source of the base change is the fibre product of the given chart with it, which
is again étale, and the square it makes up with the identity chart of `V'` is a square of étale
charts of the base change; the forward implication of Tag 061K in its affine-open reading applies
to it. -/
private theorem formallySmoothAffineLocally_chartBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : AlgebraicSpaces B S hS} {U V V' : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace V) (p : yoneda.obj U ⟶ X.obj)
    (hpEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (h : U ⟶ V) (hh : yoneda.map h = p ≫ f.hom) (k : V' ⟶ V)
    (hf : FormallySmooth (pullback.snd f (schemeSpaceMap k)).hom) :
    Stacks.Smooth.FormallySmoothAffineLocally
      (pullback.snd ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map k)) := by
  let q := BigFppfOver.toScheme B S hS
  let W := pullback h k
  let r : W ⟶ U := pullback.fst h k
  let s : W ⟶ V' := pullback.snd h k
  let g' := schemeSpaceMap (B := B) (S := S) (hS := hS) k
  let X' := pullback f g'
  have sq : IsPullback (pullback.fst f g') (pullback.snd f g') f g' :=
    IsPullback.of_hasPullback f g'
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  let pp : yoneda.obj W ⟶ X'.obj :=
    sqh.lift (yoneda.map r ≫ p) (yoneda.map s) (by
      change yoneda.map r ≫ (p ≫ f.hom) = yoneda.map s ≫ yoneda.map k
      rw [← hh]
      change yoneda.map r ≫ yoneda.map h = yoneda.map s ≫ yoneda.map k
      dsimp [r, s, W]
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
  have hEbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) q).IsStableUnderBaseChange :=
    ⟨by
      intro A C C' D a c a' c' sqq hc
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})) (sqq.map q) hc⟩
  have hEbc' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      q).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hppEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) q).presheaf pp :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) q).presheaf)
      sqAtlas.flip hpEtale
  have hW : Stacks.Smooth.FormallySmoothAffineLocally (q.map s) :=
    holdsOnEveryEtaleChart_formallySmoothAffineLocally (B := B) (S := S) (hS := hS) hf
      W V' pp (𝟙 _) s hppEtale (presheaf_id_etale B S hS V')
      (by
        simp only [schemeSpace, Category.comp_id]
        exact pp_snd.symm)
  have sqScheme : IsPullback (q.map r) (q.map s) (q.map h) (q.map k) :=
    (IsPullback.of_hasPullback h k).map q
  have sqCanonical : IsPullback (pullback.fst (q.map h) (q.map k))
      (pullback.snd (q.map h) (q.map k)) (q.map h) (q.map k) :=
    IsPullback.of_hasPullback (q.map h) (q.map k)
  let e := sqCanonical.isoIsPullback _ _ sqScheme
  have he : e.hom ≫ q.map s = pullback.snd (q.map h) (q.map k) :=
    sqCanonical.isoIsPullback_hom_snd _ _ sqScheme
  have heP : Stacks.Smooth.FormallySmoothAffineLocally (e.hom ≫ q.map s) :=
    ((@Stacks.Smooth.FormallySmoothAffineLocally.{u}).cancel_left_of_respectsIso
      e.hom (q.map s)).mpr hW
  exact he ▸ @heP

/-! ### Stacks 061K, condition (3) implies condition (1) -/

/-- **The implication (3) ⟹ (1) of [Stacks Project, Tag 061K], with condition (3) read on affine
opens.** A morphism of algebraic spaces over `S` which admits one commuting square of étale
scheme charts whose chart of the source is surjective and whose underlying scheme morphism is
affine-locally formally smooth is formally smooth.

It holds for every big fppf site and every base scheme, by
`AlgebraicGeometry.Space.formallySmoothEtaleChartDescent`, a consequence of
`AlgebraicGeometry.Space.formallySmooth_tfae_etaleCharts`. The converse implication, in the same
reading, is `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally`. -/
class FormallySmoothEtaleChartDescent (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop where
  /-- Formal smoothness from one surjective étale chart square carrying affine-local formal
  smoothness. -/
  formallySmooth_of_holdsOnSurjectiveEtaleChart :
    ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
      HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothAffineLocally.{u}) f →
      FormallySmooth f

/-! ### Descent over an affine object of the site -/

/-- Formal smoothness of a morphism of algebraic spaces over `S` whose target is an affine object
of the site descends along an fpqc presieve of affine objects.

A surjective étale chart of the source turns the assertion into affine-local formal smoothness of
a morphism of schemes, which is fpqc local on the base; the base changes it needs are supplied by
`AlgebraicGeometry.Space.formallySmoothAffineLocally_chartBaseChange`. -/
private theorem formallySmooth_of_affineFpqcPresieve (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hchart : FormallySmoothEtaleChartDescent B S hS)
    (T : BigAffineFppf B S hS) (R : Presieve T)
    (hR : R.map (BigAffineFppf.toScheme B S hS) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T))
    (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace ((BigAffineFppf.inclusion B S hS).obj T))
    (hf : ∀ {T' : BigAffineFppf B S hS} (g : T' ⟶ T), R g →
      FormallySmooth (pullback.snd f
        (schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map g))).hom) :
    FormallySmooth f.hom := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := X.property.exists_atlas
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let q := BigFppfOver.toScheme B S hS
  let h : U ⟶ V := yoneda.preimage (p ≫ f.hom)
  have hh : yoneda.map h = p ≫ f.hom := yoneda.map_preimage _
  have hscheme : Stacks.Smooth.FormallySmoothAffineLocally (q.map h) := by
    apply (formallySmoothAffineLocally_isLocalAtTarget_fpqc.{u}).of_forall_pullbackSnd
      (f := q.map h) hR
    intro W j hj hmem
    rcases hmem with ⟨hg⟩
    rename_i T' g
    exact formallySmoothAffineLocally_chartBaseChange B S hS f p hpEtale h hh
      ((BigAffineFppf.inclusion B S hS).map g) (hf g hg)
  refine hchart.formallySmooth_of_holdsOnSurjectiveEtaleChart f.hom X.property
    (schemeSpace V).property ⟨U, V, p, 𝟙 _, h, hpEtale, ?_, hpSurj, ?_, hscheme⟩
  · exact presheaf_id_etale B S hS V
  · simpa only [schemeSpace, Category.comp_id] using hh

/-! ### Stacks 06CS -/

/-- Formal smoothness of morphisms of algebraic spaces over `S` is local on the base for the fpqc
topology of Stacks 03YH, given the implication (3) ⟹ (1) of Stacks 061K in the form
`AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent`. That class always holds
(`AlgebraicGeometry.Space.formallySmoothEtaleChartDescent`), and Stacks 06CS itself is
`AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc'`.

The ascent half is Stacks 049U. For the descent half, a lifting problem for `f : X ⟶ Y` is one
for the base change of `f` along a point of `Y` with affine source
(`AlgebraicGeometry.Space.formallySmooth_iff_affine_pullback`); over such a point the fpqc
condition of Stacks 03MQ supplies a finite family of affine objects covering it and refining the
given covering, and `AlgebraicGeometry.Space.formallySmooth_of_affineFpqcPresieve` descends along
that family. -/
theorem formallySmooth_isLocalAtTarget_fpqc_of_chartDescent (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (hchart : FormallySmoothEtaleChartDescent B S hS) :
    (formallySmoothProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := formallySmoothProperty B S hS)
    (K := Topology.precoverage.{u, v} .fpqc B S hS) ?_
  intro X Y f R hR
  constructor
  · intro hf U g _ _
    exact MorphismProperty.pullback_snd (P := formallySmoothProperty B S hS) f g hf
  · intro hlocal
    obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
    obtain ⟨hY, hYi, hfpqc⟩ := hcover
    apply (formallySmooth_iff_affine_pullback B S hS f).2
    intro T gT
    obtain ⟨W, hfinite, hWcover, href⟩ := hfpqc.2 T gT.hom
    apply formallySmooth_of_affineFpqcPresieve B S hS hchart T W.presieve₀ hWcover
      (pullback f gT) (pullback.snd f gT)
    intro T' k hk
    rcases hk with ⟨j⟩
    obtain ⟨i, a, ha⟩ := href j
    let a' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (W.X j)) ⟶ Yi i :=
      ObjectProperty.homMk a
    let k' := schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map (W.f j))
    have hcomm : a' ≫ gi i = k' ≫ gT := by
      apply ObjectProperty.hom_ext
      exact ha
    exact MorphismProperty.pullbackSnd_of_comm (formallySmoothProperty B S hS) f (gi i) gT a' k'
      hcomm (hlocal (g := gi i) (Presieve.ofArrows.mk i))

/-- Formal smoothness of morphisms of algebraic spaces over `S` is local on the base for the fpqc
topology of Stacks 03YH, as an instance found through
`AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent`; that class always holds
(`AlgebraicGeometry.Space.formallySmoothEtaleChartDescent`). Stacks 06CS is
`AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc'`. -/
instance formallySmooth_isLocalAtTarget_fpqc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [hchart : FormallySmoothEtaleChartDescent B S hS] :
    (formallySmoothProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  formallySmooth_isLocalAtTarget_fpqc_of_chartDescent.{u, v} B S hS hchart

end AlgebraicGeometry.Space

end
