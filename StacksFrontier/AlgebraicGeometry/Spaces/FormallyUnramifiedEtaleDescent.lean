module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.CoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending formal unramifiedness along a surjective étale transformation

Let `p : F ⟶ G` and `q : G ⟶ H` be transformations of set-valued functors on the big fppf
site of `S` with `p` representable, surjective and étale. If the composite `p ≫ q` is formally
unramified in the sense of [Stacks Project, Tag 049S], then so is `q`. This is the descent
direction of [Stacks Project, Tag 04CY], its part (5), proved here for a middle functor which
is an algebraic space and by a route of this library's own rather than the source's.

Part (5) of that tag is an erratum: the tag states it for arbitrary set-valued functors and in
that generality it is false, and its corrected statement asks the middle functor to be
separated for the étale topology. The corrected statement is
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated`, which carries the tag as
that corrected part. An algebraic space is separated for the étale topology, so the statement
proved here is a special case of that one — reached, as the implementation notes explain, through
a hypothesis of a different kind.

With it the three conditions of [Stacks Project, Tag 04G8] become equivalent unconditionally,
and the equivalence of conditions (1) and (3) of [Stacks Project, Tag 04GA] follows.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_factorization_of_isOpenImmersion`: a morphism of the big
  fppf site over `S` whose image lies in the image of an open immersion of the site factors
  through it.
* `AlgebraicGeometry.Space.eq_of_formallyUnramified_comp` is the content of the descent: two
  sections of the middle functor over the thickened test object which agree on the test object
  and after `q` are equal.
* `AlgebraicGeometry.Space.formallyUnramified_of_formallyUnramified_comp` is the corrected
  part (5) of [Stacks Project, Tag 04CY] for a middle functor which is an algebraic space.
* `AlgebraicGeometry.Space.formallyUnramified_of_surjectiveEtaleChart` is the implication
  (3) ⟹ (1) of [Stacks Project, Tag 04G8], which together with the two implications already
  proved in `StacksFrontier/AlgebraicGeometry/Spaces/FormallyUnramifiedEtaleCharts.lean` makes all
  three conditions of that tag equivalent.
* `AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified` is
  the equivalence of conditions (1) and (3) of [Stacks Project, Tag 04GA].

## Implementation notes

*Why the route of the source is not taken.* Stacks proves part (5) by lifting the étale scheme
`W = F ×_G T` over the thickening by topological invariance of the étale site, Étale Morphisms,
Theorem 039R, and then lifting the two dotted arrows to `W'` using formal étaleness of the chart,
Tag 04AL (2). Neither of those is available in this development. The route taken instead needs
only formal unramifiedness of the composite and the stability of thickenings under base change.

*The route.* Let `i : T ⟶ T'` be a square-zero closed immersion of affine objects of the site
and let `ζ₁, ζ₂ : h_{T'} ⟶ G` be two sections agreeing after restriction along `i` and after `q`.
Representability of `p` turns `ζ₁` into an object `P` of the site with `a : P ⟶ T'` surjective
étale and a map `α : h_P ⟶ F` over `ζ₁`, and turns `ζ₂` pulled back to `P` into a second such
object `Q` with `r : Q ⟶ P` surjective étale and `α' : h_Q ⟶ F` over `ζ₂`. Over the closed fibre
`V = P ×_{T'} T` the two sections of `G` agree, so `α` restricted to `V` is also a point of `F`
over `ζ₂`, and therefore factors through `Q`: there is `s : V ⟶ Q` over `V ⟶ P`. That `s`, read
into the closed fibre `Q ×_{T'} T`, is a *section* of the base change of `r`, hence an étale
split monomorphism, hence an open immersion by
`AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`. Its image is an open of the closed fibre of
`Q`, and the closed fibre of `Q` is homeomorphic to `Q` because a square-zero closed immersion is
a thickening, so that image is cut out by an open `Q₀` of `Q`. On every affine open of `Q` inside
`Q₀` the two composites `h_{A} ⟶ F` given by `α` and by `α'` solve the same lifting problem for
`p ≫ q` across the base change of `i`, which is again a square-zero closed immersion by
[Stacks Project, Tag 09ZU], so they agree; pushing them down along `p` makes `ζ₁` and `ζ₂` agree
over `A`. Finally `Q₀ ⟶ T'` is surjective, because the section was defined over all of
`V = P ×_{T'} T` and `V ⟶ T` is surjective, so finitely many such affine opens already cover
`T'`; they form an fpqc covering presieve and the two sections agree.

*The algebraicity hypothesis, and what the source statement omits.* Tag 04CY is stated for
arbitrary set-valued functors, but its proof of part (5) ends by identifying two sections of `G`
which agree after pullback along an étale covering. That is a separatedness property of `G` which
the statement does not assume, and the proof above has exactly the same final step. In that
generality the assertion is false:
`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp` exhibits a
representable surjective étale `a` whose composite `a ≫ b` is formally étale while `b` is not
even formally unramified. The corrected statement, the one the source's own argument supports,
asks `G` to be separated for the étale topology and is
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated`.

The hypothesis here is `IsAlgebraicSpace B S hS G`, which is what the consumer in Tag 04G8 has
anyway, and which gives that separatedness: an algebraic space is an fppf sheaf, hence a sheaf
for the étale topology over `S` by
`AlgebraicGeometry.Space.isSheaf_etaleTopologyOver_of_isSheaf`. So this statement is a special
case of the corrected part (5), which is registered on that result; the registration here
names the algebraic-space case.

The route below, however, consumes separatedness for the *fpqc* topology, through
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`, and that lemma uses only
`IsAlgebraicSpace.diagonal_representable` — neither the sheaf condition nor the atlas. So this
argument gives part (5) for every presheaf with representable diagonal, and would be stated
that way if `isSeparatedFor_fpqc` were. How that condition compares with separatedness for the
étale topology is a question this module leaves open: the fpqc covering families it builds are
finite families of affines over an affine base, and refining an arbitrary étale covering to one
of those is not done here.

*Where the base change of the thickening is used.* Twice: for the closed immersion
`Q ×_{T'} T ⟶ Q`, whose being a thickening makes it a homeomorphism and so transports the open
from the closed fibre to `Q`, and for `A ×_{T'} T ⟶ A` on each affine open `A`, which is the
thickening that formal unramifiedness of `p ≫ q` is tested against. Both are
`Stacks.Thickenings.isFirstOrderThickening_of_isPullback`.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of the site factors through an open immersion containing its image.** If
`f : Y ⟶ X` is a morphism of the big fppf site over `S` whose underlying morphism of schemes is
an open immersion, and `g : Z ⟶ X` is a morphism whose range is contained in the range of `f`,
then `g` factors through `f`.

The factorization of the underlying schemes is `AlgebraicGeometry.IsOpenImmersion.lift`; it is a
morphism of the site because `AlgebraicGeometry.BigFppfSite.inclusion` is full and because the
structure morphism of `Z` factors as the lift followed by that of `Y`. -/
theorem exists_factorization_of_isOpenImmersion {X Y Z : BigFppfOver B S hS}
    (f : Y ⟶ X) (hf : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map f)) (g : Z ⟶ X)
    (hg : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map f)) :
    ∃ h : Z ⟶ Y, h ≫ f = g := by
  have := hf
  refine ⟨Over.homMk (ObjectProperty.homMk (_root_.AlgebraicGeometry.IsOpenImmersion.lift
    ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g) hg)) ?_, ?_⟩
  · have hwf : (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map X.hom =
        B.inclusion.map Y.hom := by rw [← Over.w f]; rfl
    have hwg : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map X.hom =
        B.inclusion.map Z.hom := by rw [← Over.w g]; rfl
    refine B.inclusion.map_injective ?_
    change (_root_.AlgebraicGeometry.IsOpenImmersion.lift
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g) hg) ≫
      B.inclusion.map Y.hom = B.inclusion.map Z.hom
    rw [← hwf, ← Category.assoc, _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac]
    exact hwg
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp]
    exact _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hg

/-- **The content of the descent direction of [Stacks Project, Tag 04CY].** Let `p : F ⟶ G` be
representable, surjective and étale, let `q : G ⟶ H`, let `G` be an algebraic space over `S` and
let `p ≫ q` be formally unramified. Then two sections of `G` over the larger member of a
square-zero closed immersion of affine objects of the site which agree after restriction along it
and after `q` are equal.

This is the whole geometric content of part (5) of the tag; see the implementation notes of this
file for the construction. -/
theorem eq_of_formallyUnramified_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⟶ G) (q : G ⟶ H) (hG : IsAlgebraicSpace B S hS G)
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpq : FormallyUnramified (p ≫ q))
    {T T' : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    (ζ₁ ζ₂ : yoneda.obj T' ⟶ G)
    (h1 : yoneda.map i ≫ ζ₁ = yoneda.map i ≫ ζ₂) (h2 : ζ₁ ≫ q = ζ₂ ≫ q) :
    ζ₁ = ζ₂ := by
  have hrep : yoneda.relativelyRepresentable p := hpe.1
  set P : BigFppfOver B S hS := hrep.pullback ζ₁ with hP
  set a : P ⟶ T' := hrep.snd ζ₁ with ha
  set α : yoneda.obj P ⟶ F := hrep.fst ζ₁ with hα
  have hPpb : IsPullback α (yoneda.map a) p ζ₁ := hrep.isPullback ζ₁
  set Q : BigFppfOver B S hS := hrep.pullback (yoneda.map a ≫ ζ₂) with hQ
  set r : Q ⟶ P := hrep.snd (yoneda.map a ≫ ζ₂) with hr
  set α' : yoneda.obj Q ⟶ F := hrep.fst (yoneda.map a ≫ ζ₂) with hα'
  have hQpb : IsPullback α' (yoneda.map r) p (yoneda.map a ≫ ζ₂) :=
    hrep.isPullback (yoneda.map a ≫ ζ₂)
  have haS : Surjective ((BigFppfOver.toScheme B S hS).map a) := hps.2 ζ₁ α a hPpb
  have haE : Etale ((BigFppfOver.toScheme B S hS).map a) := hpe.2 ζ₁ α a hPpb
  have hrE : Etale ((BigFppfOver.toScheme B S hS).map r) :=
    hpe.2 (yoneda.map a ≫ ζ₂) α' r hQpb
  -- the closed fibres
  set V : BigFppfOver B S hS := pullback a i with hV
  set QT : BigFppfOver B S hS := pullback (r ≫ a) i with hQT
  have hw : (pullback.fst (r ≫ a) i ≫ r) ≫ a = pullback.snd (r ≫ a) i ≫ i := by
    rw [Category.assoc, pullback.condition]
  set ρ : QT ⟶ V := pullback.lift (pullback.fst (r ≫ a) i ≫ r) (pullback.snd (r ≫ a) i) hw
    with hρ
  set γ : yoneda.obj V ⟶ F := yoneda.map (pullback.fst a i) ≫ α with hγ
  have hγp : γ ≫ p = yoneda.map (pullback.fst a i) ≫ (yoneda.map a ≫ ζ₂) := by
    rw [hγ, Category.assoc, hPpb.w, ← Category.assoc, ← Functor.map_comp,
      pullback.condition, Functor.map_comp, Category.assoc, h1, ← Category.assoc,
      ← Functor.map_comp, ← pullback.condition, Functor.map_comp, Category.assoc]
  set s : V ⟶ Q := hrep.lift γ (pullback.fst a i) hγp with hs
  have hsr : s ≫ r = pullback.fst a i := hrep.lift_snd _ _ _
  have hsα : yoneda.map s ≫ α' = γ := hrep.lift_fst _ _ _
  have hse : s ≫ (r ≫ a) = pullback.snd a i ≫ i := by
    rw [← Category.assoc, hsr, pullback.condition]
  set σ : V ⟶ QT := pullback.lift s (pullback.snd a i) hse with hσ
  have hσj : σ ≫ pullback.fst (r ≫ a) i = s := pullback.lift_fst _ _ _
  have hσc : σ ≫ pullback.snd (r ≫ a) i = pullback.snd a i := pullback.lift_snd _ _ _
  have hρsnd : ρ ≫ pullback.snd a i = pullback.snd (r ≫ a) i := pullback.lift_snd _ _ _
  have hρfst : ρ ≫ pullback.fst a i = pullback.fst (r ≫ a) i ≫ r := pullback.lift_fst _ _ _
  have hsection : σ ≫ ρ = 𝟙 V := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρfst, ← Category.assoc, hσj, hsr, Category.id_comp]
    · rw [Category.assoc, hρsnd, hσc, Category.id_comp]
  -- `σ` is an open immersion
  have hρpb : IsPullback (pullback.fst (r ≫ a) i) ρ r (pullback.fst a i) := by
    refine IsPullback.of_bot ?_ hρfst.symm (IsPullback.of_hasPullback a i)
    rw [hρsnd]
    exact IsPullback.of_hasPullback (r ≫ a) i
  have hρE : Etale ((BigFppfOver.toScheme B S hS).map ρ) :=
    MorphismProperty.of_isPullback (P := @Etale.{u})
      (hρpb.map (BigFppfOver.toScheme B S hS)) hrE
  have hσρ : (BigFppfOver.toScheme B S hS).map σ ≫ (BigFppfOver.toScheme B S hS).map ρ =
      𝟙 _ := by
    rw [← Functor.map_comp, hsection, CategoryTheory.Functor.map_id]
  have hσE : Etale ((BigFppfOver.toScheme B S hS).map σ) := by
    refine MorphismProperty.of_postcomp (W := @Etale.{u}) (W' := @Etale.{u}) _ _ hρE ?_
    rw [hσρ]
    exact (inferInstance : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj V)))
  have hσsplit : IsSplitMono ((BigFppfOver.toScheme B S hS).map σ) :=
    IsSplitMono.mk' ⟨(BigFppfOver.toScheme B S hS).map ρ, hσρ⟩
  have hσmono : Mono ((BigFppfOver.toScheme B S hS).map σ) := inferInstance
  have _ := hσE
  have hσoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ) :=
    _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono _
  -- the thickening `j : QT ⟶ Q` is a homeomorphism, so the image of `σ` is an open of `Q`
  have hpb : ∀ {X : BigFppfOver B S hS} (g : X ⟶ T'),
      IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst g i))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd g i))
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map i) :=
    fun g => (IsPullback.of_hasPullback g i).map (BigFppfOver.toScheme B S hS)
  have hjfo : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)) :=
    Stacks.Thickenings.isFirstOrderThickening_of_isPullback (hpb (r ≫ a)) hi
  have hjci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)) := hjfo.1
  have hjhomeo : IsHomeomorph
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨((BigFppfOver.toScheme B S hS).map
        (pullback.fst (r ≫ a) i)).isClosedEmbedding.isEmbedding, hjfo.isThickening.2⟩
  set Ω : ((BigFppfOver.toScheme B S hS).obj QT).Opens :=
    ((BigFppfOver.toScheme B S hS).map σ).opensRange with hΩ
  set Q₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens :=
    ⟨((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base '' (Ω : Set _),
      hjhomeo.isOpenMap _ Ω.isOpen⟩ with hQ₀
  -- on an affine open of `Q` inside `Q₀` the two sections agree
  have hkey : ∀ A : ((BigFppfOver.toScheme B S hS).obj Q).Opens, IsAffineOpen A → A ≤ Q₀ →
      ∃ (A' : BigFppfOver B S hS) (kA : A' ⟶ Q),
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map kA) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map kA) = (A : Set _) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj A') ∧
        yoneda.map (kA ≫ r ≫ a) ≫ ζ₁ = yoneda.map (kA ≫ r ≫ a) ≫ ζ₂ := by
    intro A hA hAQ₀
    obtain ⟨A', kA, hkAoi, hkArange, -⟩ := exists_restrict_bigFppfOver Q A
    have hAs : IsAffine ((A : Scheme.{u})) := hA
    have hor : ((BigFppfOver.toScheme B S hS).map kA).opensRange = A :=
      TopologicalSpace.Opens.ext hkArange
    have hranA : IsAffine
        (((BigFppfOver.toScheme B S hS).map kA).opensRange : Scheme.{u}) := by
      rw [hor]; exact hAs
    have hA'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj A') :=
      have := hkAoi
      _root_.AlgebraicGeometry.IsAffine.of_isIso
        ((BigFppfOver.toScheme B S hS).map kA).isoOpensRange.hom
    refine ⟨A', kA, hkAoi, hkArange, hA'aff, ?_⟩
    -- the base change of the thickening to `A'`
    have hjApb := hpb (kA ≫ r ≫ a)
    have hATaff : IsAffine
        ((BigFppfOver.toScheme B S hS).obj (pullback (kA ≫ r ≫ a) i)) :=
      have := hT
      have := hT'
      _root_.AlgebraicGeometry.IsAffine.of_isIso hjApb.isoPullback.hom
    have hjAsq : IsSquareZeroClosedImmersion B S hS (pullback.fst (kA ≫ r ≫ a) i) :=
      Stacks.Thickenings.isFirstOrderThickening_of_isPullback hjApb hi
    -- the comparison `m : A' ×_{T'} T ⟶ QT`
    have hme : (pullback.fst (kA ≫ r ≫ a) i ≫ kA) ≫ (r ≫ a) =
        pullback.snd (kA ≫ r ≫ a) i ≫ i :=
      (Category.assoc _ _ _).trans pullback.condition
    set m : pullback (kA ≫ r ≫ a) i ⟶ QT :=
      pullback.lift (pullback.fst (kA ≫ r ≫ a) i ≫ kA) (pullback.snd (kA ≫ r ≫ a) i) hme
      with hm
    have hmj : m ≫ pullback.fst (r ≫ a) i = pullback.fst (kA ≫ r ≫ a) i ≫ kA :=
      pullback.lift_fst _ _ _
    -- the range of `m` lies in the range of `σ`
    have hmran : Set.range ((BigFppfOver.toScheme B S hS).map m) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map σ) := by
      rintro z ⟨w, rfl⟩
      have hjz : ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base
          (((BigFppfOver.toScheme B S hS).map m).base w) ∈ (Q₀ : Set _) := by
        have hcomp : ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base
            (((BigFppfOver.toScheme B S hS).map m).base w) =
            ((BigFppfOver.toScheme B S hS).map kA).base
              (((BigFppfOver.toScheme B S hS).map (pullback.fst (kA ≫ r ≫ a) i)).base w) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
            ← Functor.map_comp, hmj]
        rw [hcomp]
        have hmem : ((BigFppfOver.toScheme B S hS).map kA).base
            (((BigFppfOver.toScheme B S hS).map (pullback.fst (kA ≫ r ≫ a) i)).base w) ∈
            Set.range ((BigFppfOver.toScheme B S hS).map kA) := Set.mem_range_self _
        rw [hkArange] at hmem
        exact hAQ₀ hmem
      obtain ⟨ω, hω, hjω⟩ := hjz
      have : ((BigFppfOver.toScheme B S hS).map m).base w = ω :=
        (hjhomeo.injective hjω).symm
      rw [this]
      exact hω
    obtain ⟨n, hn⟩ := exists_factorization_of_isOpenImmersion σ hσoi m hmran
    -- the two sections of `F` over `A'`
    have hmρ : m ≫ ρ = n := by
      rw [← hn, Category.assoc, hsection, Category.comp_id]
    have e1 : pullback.fst (kA ≫ r ≫ a) i ≫ kA ≫ r = n ≫ pullback.fst a i := by
      rw [← Category.assoc (pullback.fst _ i) kA r, ← hmj, Category.assoc, ← hρfst,
        ← Category.assoc m ρ, hmρ]
    have e2 : pullback.fst (kA ≫ r ≫ a) i ≫ kA = n ≫ s := by
      rw [← hmj, ← hn, Category.assoc, hσj]
    have hβ₁p : (yoneda.map (kA ≫ r) ≫ α) ≫ p = yoneda.map (kA ≫ r ≫ a) ≫ ζ₁ := by
      rw [Category.assoc, hPpb.w, ← Category.assoc (yoneda.map (kA ≫ r)) (yoneda.map a) ζ₁,
        ← Functor.map_comp, Category.assoc]
    have hβ₂p : (yoneda.map kA ≫ α') ≫ p = yoneda.map (kA ≫ r ≫ a) ≫ ζ₂ := by
      rw [Category.assoc, hQpb.w,
        ← Category.assoc (yoneda.map kA) (yoneda.map r) (yoneda.map a ≫ ζ₂),
        ← Functor.map_comp, ← Category.assoc (yoneda.map (kA ≫ r)) (yoneda.map a) ζ₂,
        ← Functor.map_comp, Category.assoc]
    have hL : yoneda.map (pullback.fst (kA ≫ r ≫ a) i) ≫ (yoneda.map (kA ≫ r) ≫ α) =
        yoneda.map n ≫ γ := by
      rw [← Category.assoc (yoneda.map (pullback.fst (kA ≫ r ≫ a) i)) (yoneda.map (kA ≫ r)) α,
        ← Functor.map_comp, e1, Functor.map_comp, Category.assoc, hγ]
    have hR : yoneda.map (pullback.fst (kA ≫ r ≫ a) i) ≫ (yoneda.map kA ≫ α') =
        yoneda.map n ≫ γ := by
      rw [← Category.assoc (yoneda.map (pullback.fst (kA ≫ r ≫ a) i)) (yoneda.map kA) α',
        ← Functor.map_comp, e2, Functor.map_comp, Category.assoc, hsα]
    have hrestrict : yoneda.map (pullback.fst (kA ≫ r ≫ a) i) ≫ (yoneda.map (kA ≫ r) ≫ α) =
        yoneda.map (pullback.fst (kA ≫ r ≫ a) i) ≫ (yoneda.map kA ≫ α') := by
      rw [hL, hR]
    -- apply formal unramifiedness of the composite
    have hβ : yoneda.map (kA ≫ r) ≫ α = yoneda.map kA ≫ α' := by
      have hcomp : (yoneda.map (kA ≫ r) ≫ α) ≫ (p ≫ q) = (yoneda.map kA ≫ α') ≫ (p ≫ q) := by
        rw [← Category.assoc (yoneda.map (kA ≫ r) ≫ α) p q, hβ₁p,
          ← Category.assoc (yoneda.map kA ≫ α') p q, hβ₂p, Category.assoc, Category.assoc, h2]
      have key := hpq (pullback (kA ≫ r ≫ a) i) A' hATaff hA'aff
        (pullback.fst (kA ≫ r ≫ a) i) hjAsq
        (F.map (pullback.fst (kA ≫ r ≫ a) i).op (yonedaEquiv (yoneda.map (kA ≫ r) ≫ α)))
        ((p ≫ q).app (op A') (yonedaEquiv (yoneda.map (kA ≫ r) ≫ α)))
        (NatTrans.naturality_apply (p ≫ q) (pullback.fst (kA ≫ r ≫ a) i).op
          (yonedaEquiv (yoneda.map (kA ≫ r) ≫ α)))
        (yonedaEquiv (yoneda.map (kA ≫ r) ≫ α)) (yonedaEquiv (yoneda.map kA ≫ α'))
        ⟨rfl, rfl⟩ ⟨?_, ?_⟩
      · exact yonedaEquiv.injective key
      · rw [yonedaEquiv_naturality, yonedaEquiv_naturality, hrestrict]
      · rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, hcomp]
    rw [← hβ₁p, ← hβ₂p, hβ]
  -- every point of `T'` is hit by an affine open of `Q` inside `Q₀`
  have hifo : Stacks.Thickenings.IsFirstOrderThickening
    ((BigFppfOver.toScheme B S hS).map i) := hi
  have hraE : Etale ((BigFppfOver.toScheme B S hS).map (r ≫ a)) := by
    rw [Functor.map_comp]
    have := hrE
    have := haE
    infer_instance
  have hdS : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd a i)) :=
    MorphismProperty.of_isPullback (P := @Surjective.{u}) (hpb a) haS
  have hestep : σ ≫ pullback.fst (r ≫ a) i ≫ (r ≫ a) = pullback.snd a i ≫ i := by
    rw [pullback.condition, ← Category.assoc, hσc]
  have hcover : ∀ t' : (BigFppfOver.toScheme B S hS).obj T',
      ∃ (A' : BigFppfOver B S hS) (w : A' ⟶ T'),
        IsAffine ((BigFppfOver.toScheme B S hS).obj A') ∧
        Etale ((BigFppfOver.toScheme B S hS).map w) ∧
        t' ∈ Set.range ((BigFppfOver.toScheme B S hS).map w) ∧
        yoneda.map w ≫ ζ₁ = yoneda.map w ≫ ζ₂ := by
    intro t'
    obtain ⟨t, ht⟩ := hifo.isThickening.2 t'
    obtain ⟨v, hv⟩ := hdS.1 t
    have hx₀ : ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base
        (((BigFppfOver.toScheme B S hS).map σ).base v) ∈ Q₀ :=
      ⟨((BigFppfOver.toScheme B S hS).map σ).base v, ⟨v, rfl⟩, rfl⟩
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAQ₀⟩ :=
      ((BigFppfOver.toScheme B S hS).obj Q).isBasis_affineOpens.exists_subset_of_mem_open
        hx₀ Q₀.isOpen
    obtain ⟨A', kA, hkAoi, hkArange, hA'aff, heq⟩ := hkey A hA hAQ₀
    refine ⟨A', kA ≫ r ≫ a, hA'aff, ?_, ?_, heq⟩
    · have := hkAoi
      have : Etale ((BigFppfOver.toScheme B S hS).map kA) := inferInstance
      rw [Functor.map_comp]
      have := hraE
      infer_instance
    · obtain ⟨z, hz⟩ : ∃ z, ((BigFppfOver.toScheme B S hS).map kA).base z =
          ((BigFppfOver.toScheme B S hS).map (pullback.fst (r ≫ a) i)).base
            (((BigFppfOver.toScheme B S hS).map σ).base v) := by
        rw [← Set.mem_range, hkArange]
        exact hxA
      refine ⟨z, ?_⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply,
        ← Functor.map_comp, ← Scheme.Hom.comp_apply, ← Functor.map_comp, hestep,
        Functor.map_comp, Scheme.Hom.comp_apply, hv, ht]
  classical
  choose A' w hA'aff hwE hwmem hweq using hcover
  have hwopen : ∀ t' : (BigFppfOver.toScheme B S hS).obj T',
      IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (w t'))) := by
    intro t'
    have := hwE t'
    have : UniversallyOpen ((BigFppfOver.toScheme B S hS).map (w t')) :=
      UniversallyOpen.of_flat _
    exact ((BigFppfOver.toScheme B S hS).map (w t')).isOpenMap.isOpen_range
  have hcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj T') :=
    have := hT'
    inferInstance
  obtain ⟨tt, htt⟩ := isCompact_univ.elim_finite_subcover
    (fun t' : (BigFppfOver.toScheme B S hS).obj T' =>
      Set.range ((BigFppfOver.toScheme B S hS).map (w t'))) hwopen
    fun t' _ => Set.mem_iUnion.2 ⟨t', hwmem t'⟩
  have hidxcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T', ∃ k : Fin tt.card,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (w (tt.equivFin.symm k).1)) := by
    intro x
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (htt (Set.mem_univ x))
    refine ⟨tt.equivFin ⟨z, hz⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hxz
  have hRmem : Presieve.ofArrows (fun k : Fin tt.card => A' (tt.equivFin.symm k).1)
      (fun k => w (tt.equivFin.symm k).1) ∈
      Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) T' := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine Scheme.ofArrows_mem_fpqcPrecoverage_of_finite hT' _ _
      (fun k => hA'aff _) (fun k => ?_) hidxcov
    have := hwE (tt.equivFin.symm k).1
    infer_instance
  refine yonedaEquiv.injective ((hG.isSeparatedFor_fpqc hRmem).ext ?_)
  rintro Z f ⟨k⟩
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, hweq]

/-- Let `p : F ⟶ G` be a representable, surjective and étale transformation of set-valued
functors on the big fppf site of `S`, let `q : G ⟶ H` and let `G` be an algebraic space over `S`.
If `p ≫ q` is formally unramified in the sense of [Stacks Project, Tag 049S], then so is `q`.

The corrected part (5) asks `G` to be separated for the étale topology, and an algebraic space
is (see the implementation notes of this file), so this is a special case of
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated`, which carries the
corrected part (5). This proof uses a hypothesis of a different kind — separatedness for the
fpqc topology, which follows from the representable diagonal alone. The composition direction
is `AlgebraicGeometry.Space.formallyUnramified_comp_of_etale`. -/
@[stacks 04CY "part (5), for a middle functor which is an algebraic space"]
theorem formallyUnramified_of_formallyUnramified_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (q : G ⟶ H)
    (hG : IsAlgebraicSpace B S hS G)
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpq : FormallyUnramified (p ≫ q)) :
    FormallyUnramified q := by
  intro T T' hT hT' i hi x y _hxy z₁ z₂ hz₁ hz₂
  have h1 : yoneda.map i ≫ yonedaEquiv.symm z₁ = yoneda.map i ≫ yonedaEquiv.symm z₂ := by
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, hz₁.1, hz₂.1]
  have h2 : yonedaEquiv.symm z₁ ≫ q = yonedaEquiv.symm z₂ ≫ q := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hz₁.2, hz₂.2]
  exact yonedaEquiv.symm.injective
    (eq_of_formallyUnramified_comp p q hG hps hpe hpq hT hT' i hi _ _ h1 h2)

/-- **Stacks 04G8, condition (3) implies condition (1).** If a morphism `f` out of an algebraic
space over `S` has one commuting square of surjective étale scheme charts whose chart morphism is
formally unramified as a morphism of schemes, then `f` is formally unramified in the sense of
[Stacks Project, Tag 049S].

The composite of the chart of the source with `f` is formally unramified by
`AlgebraicGeometry.Space.formallyUnramified_chart_comp`, and
`AlgebraicGeometry.Space.formallyUnramified_of_formallyUnramified_comp` descends that along the
chart. Together with `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified` and
`AlgebraicGeometry.Space.exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart` it makes all
three conditions of the tag equivalent. -/
@[stacks 04G8 "condition (3) implies condition (1)"]
theorem formallyUnramified_of_surjectiveEtaleChart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hex : ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (h : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      yoneda.map h ≫ b = a ≫ f ∧
      _root_.AlgebraicGeometry.FormallyUnramified
        ((BigFppfOver.toScheme B S hS).map h)) :
    FormallyUnramified f := by
  obtain ⟨U, V, a, b, h, haEtale, hbEtale, haSurj, -, hdiag, hh⟩ := hex
  exact formallyUnramified_of_formallyUnramified_comp B S hS a f hX haSurj haEtale
    (formallyUnramified_chart_comp B S hS f a b h hbEtale hdiag hh)

/-- **Conditions (1) and (3) of Stacks 04GA.** A morphism of algebraic spaces over `S` is
unramified if and only if it is locally of finite type and formally unramified in the sense of
[Stacks Project, Tag 049S].

`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts`
splits unramifiedness into local finite type and formal unramifiedness *of the étale charts*; the
passage from that chart condition to formal unramifiedness of `f` itself is the equivalence of
conditions (1) and (2) of [Stacks Project, Tag 04G8], whose remaining implication is
`AlgebraicGeometry.Space.formallyUnramified_of_surjectiveEtaleChart`.

This is the equivalence of conditions (1) and (3) of [Stacks Project, Tag 04GA]; the whole
tag, with condition (2), is `AlgebraicGeometry.Space.isUnramified_tfae_sheafOfDifferentials` in
`StacksFrontier/AlgebraicGeometry/Spaces/UnramifiedSheafOfDifferentials.lean`, which imports this
module. -/
@[ega "IV 17.4.2" "a) ⇔ e)"]
theorem isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsUnramified B S hS f ↔ (IsLocallyOfFiniteType B S hS f ∧ FormallyUnramified f) := by
  rw [isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts B S hS f]
  refine and_congr_right fun _ => ⟨fun hall => ?_, holdsOnEveryEtaleChart_of_formallyUnramified
    B S hS f⟩
  exact formallyUnramified_of_surjectiveEtaleChart B S hS hX f
    (exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart B S hS hX hY f hall)

end AlgebraicGeometry.Space

end
