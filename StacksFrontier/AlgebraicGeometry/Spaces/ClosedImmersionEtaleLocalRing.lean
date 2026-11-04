module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal

/-!
# The germ map of a closed immersion of algebraic spaces is surjective

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `X`. This file proves that the canonical homomorphism of étale local rings
`𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` of Stacks 04NG is surjective.

The proof is the one the source gives for a closed immersion of schemes, transported to the
étale site. Both étale local rings are filtered colimits of rings of regular functions on
pointed étale scheme charts, so an element of `𝒪_{X, x̄}` is the germ of a regular function `a`
on some pointed chart `N` of `X`; and surjectivity amounts to being able to choose that chart
so that `a` is pulled back from a chart of `Y`. Two cofinality statements do that:

* base changes along `f` of étale charts of `Y` are cover dense among étale charts of `X`
  (Stacks 04E5, part (1)), so `N` is refined by a *pointed* base-changed chart `X ×_Y V`; and
* affine étale charts are cover dense among all étale charts (Stacks 04JS), so `V` may be
  refined to a pointed chart whose scheme is affine.

With `V` affine the projection `X ×_Y V → V` is a closed immersion of schemes with affine
target, so it is surjective on global regular functions; hence `a`, restricted to
`X ×_Y V`, is pulled back from `V`, and its germ is the image of a germ at `f(x̄)`.

## Main results

* `AlgebraicGeometry.Space.exists_hom_of_isCoverDense`: a cover-dense family of étale charts
  is cofinal among the small étale neighbourhoods of a geometric point. This is where the
  point of the small étale site of Stacks 04K0 is used: a covering sieve of a chart has a
  member through which the geometric point lifts.
* `AlgebraicGeometry.Space.surjective_snd_appTop_of_isClosedImmersion`: for a closed immersion
  and an étale chart of the target whose scheme is affine, the projection of the base-changed
  chart is surjective on global regular functions.
* `AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`: the statement
  above.

## Implementation notes

The cofinality lemma is stated for an arbitrary cover-dense functor into the small étale site
rather than twice over for the two families used, because the two uses differ only in the
functor: both consist of lifting the geometric point through a member of the covering sieve
produced by cover density and then pushing it forward into the cover-dense object through
which that member factors.

Pointedness of the base-changed chart is not constructed by hand: it is read off the bijection
`AlgebraicGeometry.Space.smallBaseChangeFiberMap_bijective` between the lifts of `x̄` into
`X ×_Y V` and the lifts of `f(x̄)` into `V`, and the compatibility of that bijection with a
morphism `V' ⟶ V` of charts of `Y` is the naturality of
`AlgebraicGeometry.Space.smallBaseChangeFiberMap` together with its injectivity.

The conclusion is surjectivity of `AlgebraicGeometry.Space.etaleLocalRingMap`, the
homomorphism characterised by Stacks 04NG as the unique one compatible with the germ maps in
every commuting diagram of pointed étale charts; the diagram used here is the base-change
square, whose commutativity is the defining square of the representability of `f`.

No tag is claimed. The source does not state this surjectivity as a numbered result: it is
used inside the proof of Stacks 0EE3 and, for schemes, is one of the two defining fields of
`AlgebraicGeometry.IsClosedImmersion`.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-- **A cover-dense family of charts is cofinal among the small étale neighbourhoods.** Let
`G` be a functor into the small étale site of an algebraic space `F` which is cover dense for
the small étale topology, and let `N` be a small étale neighbourhood of a geometric point `x̄`
of `F`. Then some object in the image of `G` carries a lift of `x̄` and a morphism to the
chart of `N` carrying that lift to the chosen one.

Cover density makes the sieve of morphisms factoring through the image of `G` a covering sieve
of the chart of `N`; the point of the small étale site of Stacks 04K0 lifts `x̄` through a
member of that sieve, and pushing the lift forward along the factorisation lands it in the
image of `G`. -/
theorem exists_hom_of_isCoverDense {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : Type w} [Category.{v} A]
    (G : A ⥤ SmallEtale B S hS F) [G.IsCoverDense (SmallEtale.topology B S hS F)]
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    (N : SmallEtaleNeighborhood x) :
    ∃ (a : A) (p : GeometricFiber B S hS F x (G.obj a)) (g : G.obj a ⟶ N.chart),
      p.1 ≫ (SmallEtale.toOver B S hS F).map g = N.point := by
  obtain ⟨W, g, hg, q, hq⟩ := (etaleSitePoint B S hS F x hF).jointly_surjective _
    (G.is_cover_of_isCoverDense (SmallEtale.topology B S hS F) N.chart)
    ⟨N.point, N.point_comp⟩
  obtain ⟨⟨a, l, m, hfac⟩⟩ := hg
  refine ⟨a, (geometricFiber B S hS F x).map l q, m, ?_⟩
  rw [← hfac, Functor.map_comp_apply] at hq
  exact congrArg Subtype.val hq

/-- **A closed immersion is surjective on regular functions over an affine chart.** For a
closed immersion `f : X ⟶ Y` of algebraic spaces and an étale chart `V` of `Y` whose scheme is
affine, the cartesian projection `X ×_Y V → V` is surjective on global regular functions.

The projection is a closed immersion of schemes because `f` is a closed immersion of algebraic
spaces, and a closed immersion with affine target is surjective on global sections
(`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`). -/
theorem surjective_snd_appTop_of_isClosedImmersion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    Function.Surjective
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom)).appTop := by
  have := hV
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom)) := hf.property_snd V.1.hom
  exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom))).2

/-- **The germ map of a closed immersion of algebraic spaces is surjective.** Let
`f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `X`. Then the canonical homomorphism of étale local rings
`𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` of Stacks 04NG is surjective.

Every element of `𝒪_{X, x̄}` is the germ of a regular function on a pointed étale chart
(`AlgebraicGeometry.Space.spaceGerms_isColimit`). Base-changed charts are cofinal among
pointed étale charts of `X` by cover density, Stacks 04E5, part (1), and affine charts are
cofinal among pointed étale charts of `Y` by Stacks 04JS, so the chart may be taken to be
`X ×_Y V` with `V` affine; over such a `V` the projection is surjective on regular functions,
so the function is a pullback and its germ is the image of a germ at `f(x̄)`. -/
theorem surjective_etaleLocalRingMap_of_isClosedImmersion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1) :
    Function.Surjective (etaleLocalRingMap X.2 f.hom x) := by
  have hbc : (smallBaseChange B S hS f hf.rep).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    smallBaseChange_isCoverDense_of_isClosedImmersion B S hS f hf
  have haff : (AffineEtale.inclusion B S hS Y.1).IsCoverDense
      (SmallEtale.topology B S hS Y.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2.isCoverDense'
  intro r
  -- Write `r` as the germ of a regular function on a pointed étale chart `N` of `X`.
  obtain ⟨N, a, hNa⟩ := (spaceGerms_isColimit X.2).ι_jointly_surjective r
  -- Refine `N` by a pointed base-changed chart `X ×_Y Vc`.
  obtain ⟨Vc, p, g, hg⟩ :=
    exists_hom_of_isCoverDense (smallBaseChange B S hS f hf.rep) X.2 x N.unop
  -- The lift of `x̄` to `X ×_Y Vc` makes `Vc` a pointed chart of `Y`.
  set qV : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) Vc :=
    (smallBaseChangeFiberMap B S hS f hf.rep x).app Vc p with hqV
  set V : SmallEtaleNeighborhood (geometricPointMap f.hom x) := ⟨Vc, qV.1, qV.2⟩ with hV
  -- Refine `V` by a pointed chart whose scheme is affine.
  obtain ⟨A₀, q, k, hk⟩ :=
    exists_hom_of_isCoverDense (AffineEtale.inclusion B S hS Y.1) Y.2
      (geometricPointMap f.hom x) V
  set V' : SmallEtaleNeighborhood (geometricPointMap f.hom x) :=
    ⟨(AffineEtale.inclusion B S hS Y.1).obj A₀, q.1, q.2⟩ with hV'
  -- The lift of `x̄` to `X ×_Y V'`, read off the bijection on lifts.
  obtain ⟨p', hp'q⟩ :=
    (smallBaseChangeFiberMap_bijective B S hS f hf.rep x V'.chart).2 q
  have hsnd : p'.1 ≫ hf.rep.snd V'.chart.1.hom = q.1 := congrArg Subtype.val hp'q
  -- The base-changed chart of `V'` refines the base-changed chart of `V`, compatibly with the
  -- lifts of `x̄`: the two lifts agree because their images under the bijection on lifts do.
  have hmapk : (geometricFiber B S hS X.1 x).map
      ((smallBaseChange B S hS f hf.rep).map k) p' = p := by
    refine (smallBaseChangeFiberMap_bijective B S hS f hf.rep x Vc).1 ?_
    have hnat := congrArg (fun φ => φ p')
      ((smallBaseChangeFiberMap B S hS f hf.rep x).naturality k)
    refine Eq.trans hnat ?_
    change (geometricFiber B S hS Y.1 (geometricPointMap f.hom x)).map k
      ((smallBaseChangeFiberMap B S hS f hf.rep x).app V'.chart p') = _
    rw [hp'q]
    exact Subtype.ext hk
  -- Assemble the refinement `X ×_Y V' ⟶ N` of pointed charts.
  set U' : SmallEtaleNeighborhood x :=
    ⟨(smallBaseChange B S hS f hf.rep).obj V'.chart, p'.1, p'.2⟩ with hU'
  have hpoint : U'.point ≫ (SmallEtale.toOver B S hS X.1).map
      ((smallBaseChange B S hS f hf.rep).map k ≫ g) = N.unop.point := by
    rw [Functor.map_comp, ← Category.assoc]
    exact Eq.trans (congrArg (fun z => z ≫ (SmallEtale.toOver B S hS X.1).map g)
      (congrArg Subtype.val hmapk)) hg
  set m : U' ⟶ N.unop := ⟨(smallBaseChange B S hS f hf.rep).map k ≫ g, hpoint⟩ with hm
  -- The regular function `a`, restricted to `X ×_Y V'`, is pulled back from `V'`.
  obtain ⟨b, hb⟩ := surjective_snd_appTop_of_isClosedImmersion B S hS f hf V'.chart
    (AffineEtale.isAffine_toScheme B S hS Y.1 A₀)
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map m.hom)).op).hom a)
  have hb' : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hf.rep.snd V'.chart.1.hom)).op).hom b =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m.hom)).op).hom a := by
    rw [Scheme.Γ_map_op]
    exact hb
  -- Its germ is the image of the germ of `b`.
  refine ⟨etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (Opposite.op V') b, ?_⟩
  have hsq := etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x U' V'
    (hf.rep.snd V'.chart.1.hom) (hf.rep.w V'.chart.1.hom) hsnd
  have hval := congrArg (fun φ => φ b) hsq
  refine Eq.trans hval.symm ?_
  change etaleLocalRingGerm B S hS X.1 x (Opposite.op U')
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hf.rep.snd V'.chart.1.hom)).op).hom b) = r
  rw [hb']
  exact Eq.trans (congrArg (fun φ => φ a)
    (etaleLocalRingGerm_comp_map (B := B) (S := S) (hS := hS) m)) hNa

end AlgebraicGeometry.Space

end
