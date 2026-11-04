module

public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Legs

/-!
# The two-chart compatibility of the relative twists, in the vocabulary of Tag 01MY's legs

This file restates the two-chart compatibility
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq` of Tag 01NR's chart identifications
over a nested pair of affine opens of the base with Tag 01NO's comparison map written as Tag 01MY's
comparison map `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt` for the restriction
`Γ(V, A) ⟶ Γ(U, A)`, read at the legs `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` and
`𝟙 (Proj Γ(U, A))`, and then reads it at an arbitrary pair of legs.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_eq_comp₅`: the comparison map at given legs,
  written out, at the level of variables.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.projInclusionTwistMap_eq_twistMapAt`: **Tag 01NO's
  comparison map on the `n`-th twist is Tag 01MY's comparison map for the restriction, read at the
  legs of Tag 01NO**, followed by the identification of the inverse image along the identity.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.projInclusionTwistIso_hom_eq_twistMapAt`: the same for
  the underlying morphism of Tag 01NO's canonical isomorphism.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq_twistMapAt` and
  `chartTwistIso_hom_eq_twistMapAt'`: **the two-chart compatibility of Tag 01NR's chart
  identifications, with Tag 01NO's comparison map replaced by the comparison map of Tag 01MY read
  at legs**, in two bracketings.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_nested`: **the two-chart
  compatibility read at an arbitrary pair of legs.**

## Implementation notes

The two spellings of the comparison map of the restriction are definitionally equal, but
identifying the two composites at a concrete pair of affine opens is beyond the kernel's
deterministic budget (see `StacksFrontier/AlgebraicGeometry/ProjInclusionTwist/Legs.lean`).

The transport to arbitrary legs,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.three_comp_leg_nested_proj`, is taken in the form indexed by
the two graded rings. The version abstracting over the projective spectra as schemes makes the
kernel unfold `AlgebraicGeometry.Proj` once for each sheaf of modules it abstracts over, and at a
concrete pair of affine opens it exceeds the deterministic budget although elaboration succeeds.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjInclusionTwist

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

universe u

/-! ### The comparison map at given legs, written out -/

section Legs

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂]
  [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01MY's comparison map read at given legs, written out as its five factors**,
right-associated, at the level of variables. -/
public theorem twistMapAt_eq_comp₅ (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i) :
    twistMapAt 𝒜 ℬ φ n q hd hi =
      (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n) :=
  rfl

end Legs

/-! ### Tag 01NO's comparison map as a comparison map at legs -/

variable {S : Scheme.{u}}

/-- **Tag 01NO's comparison map on the `n`-th twist is Tag 01MY's comparison map for the
restriction `Γ(V, A) ⟶ Γ(U, A)`, read at the legs
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` and `𝟙 (Proj Γ(U, A))`**, followed by the
identification of the inverse image along the identity.

The legs are presented by
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionTopSection`, the identification of
`Proj Γ(U, A)` with the open domain of the restriction, which is everything by Tag 01NO. -/
public theorem projInclusionTwistMap_eq_twistMapAt (A : SheafGradedAlgebra S) (U V : S.Opens)
    (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    ProjInclusionTwist.projInclusionTwistMap A U V h hU hV n =
      twistMapAt (A.grading V) (A.grading U) (A.res h) n
          (projInclusionTopSection A U V h hU hV)
          (projInclusionTopSection_comp_mapHom A U V h hU hV)
          (projInclusionTopSection_ι A U V h hU hV) ≫
        (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :=
  (ProjInclusionTwist.projInclusionTwistMap_eq_mapHom A U V h hU hV n).trans
    (comp_congr (twistMapAt_eq_comp₅ (A.grading V) (A.grading U) (A.res h) n
      (projInclusionTopSection A U V h hU hV)
      (projInclusionTopSection_comp_mapHom A U V h hU hV)
      (projInclusionTopSection_ι A U V h hU hV)).symm rfl)

/-- **The underlying morphism of Tag 01NO's canonical isomorphism on the `n`-th twist is Tag
01MY's comparison map for the restriction, read at the legs of Tag 01NO.** -/
public theorem projInclusionTwistIso_hom_eq_twistMapAt (A : SheafGradedAlgebra S) (U V : S.Opens)
    (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    (ProjInclusionTwist.projInclusionTwistIso A U V h hU hV n).hom =
      twistMapAt (A.grading V) (A.grading U) (A.res h) n
          (projInclusionTopSection A U V h hU hV)
          (projInclusionTopSection_comp_mapHom A U V h hU hV)
          (projInclusionTopSection_ι A U V h hU hV) ≫
        (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :=
  (ProjInclusionTwist.projInclusionTwistIso_hom A U V h hU hV n).trans
    (projInclusionTwistMap_eq_twistMapAt A U V h hU hV n)

/-- **The chart identification of Tag 01NR over the smaller of a nested pair of affine opens of
the base is the one over the larger, pulled back along the chart transition and followed by Tag
01MY's comparison map for the restriction, read at the legs of Tag 01NO.** -/
public theorem chartTwistIso_hom_eq_twistMapAt (A : SheafGradedAlgebra S) (n : ℤ)
    (T U : S.affineOpens) (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) :
    (Scheme.Modules.pullbackCongr
            ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2
              U.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp
            (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            ((relativeProj A).chart (U.1 : S.Opens) U.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback
            (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)).map
            (chartTwistIso A n U).hom ≫
        (twistMapAt (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n
            (projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            (projInclusionTopSection_comp_mapHom A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            (projInclusionTopSection_ι A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2) ≫
          (Scheme.Modules.pullbackId
              (AlgebraicGeometry.Proj (A.grading (T.1 : S.Opens)))).hom.app
            (twistingSheaf (A.grading (T.1 : S.Opens)) n)) =
      (chartTwistIso A n T).hom :=
  (comp_congr rfl (comp_congr rfl (comp_congr rfl
      (projInclusionTwistIso_hom_eq_twistMapAt A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2
        n).symm))).trans
    (chartTwistIso_hom_eq A n T U h)

/-! ### The nested compatibility of the chart identification at arbitrary legs -/

/-- **The two-chart compatibility of Tag 01NR's chart identifications, bracketed as the
transported chart identification over `U` followed by Tag 01MY's comparison map for the
restriction.** This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq_twistMapAt`
reassociated. -/
public theorem chartTwistIso_hom_eq_twistMapAt' (A : SheafGradedAlgebra S) (n : ℤ)
    (T U : S.affineOpens) (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) :
    ((Scheme.Modules.pullbackCongr
              ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2
                U.2)).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullbackComp
              (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
              ((relativeProj A).chart (U.1 : S.Opens) U.2)).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullback
              (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)).map
            (chartTwistIso A n U).hom) ≫
        (twistMapAt (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n
            (projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            (projInclusionTopSection_comp_mapHom A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            (projInclusionTopSection_ι A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2) ≫
          (Scheme.Modules.pullbackId
              (AlgebraicGeometry.Proj (A.grading (T.1 : S.Opens)))).hom.app
            (twistingSheaf (A.grading (T.1 : S.Opens)) n)) =
      (chartTwistIso A n T).hom :=
  (comp₃_comp _ _ _ _).trans (chartTwistIso_hom_eq_twistMapAt A n T U h)

/-- **The nested compatibility of Tag 01NR's chart identification, read at arbitrary legs.** Let
`T ⊆ U` be affine opens of the base, let `k` be a morphism of schemes, let `d'` be a leg into
`Proj Γ(T, A)` and `d` a leg into `Proj Γ(U, A)` whose composites with the two charts are `c'` and
`c` with `k ≫ c = c'`, and let `p` be a morphism into the domain of definition of the restriction
`Γ(U, A) ⟶ Γ(T, A)` presenting `k ≫ d` and `d'`. Then the chart identification over `T`,
transported to `d'`, is the chart identification over `U` transported to `d`, pulled back along
`k`, followed by Tag 01MY's comparison map for the restriction read at `p`. -/
public theorem chartTwistIso_hom_nested (A : SheafGradedAlgebra S) (n : ℤ) (T U : S.affineOpens)
    (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) {Z' Z : Scheme.{u}} (k : Z' ⟶ Z)
    {d : Z ⟶ AlgebraicGeometry.Proj (A.grading (U.1 : S.Opens))}
    {c : Z ⟶ (relativeProj A).scheme}
    (hc : d ≫ (relativeProj A).chart (U.1 : S.Opens) U.2 = c)
    {d' : Z' ⟶ AlgebraicGeometry.Proj (A.grading (T.1 : S.Opens))}
    {c' : Z' ⟶ (relativeProj A).scheme}
    (hc' : d' ≫ (relativeProj A).chart (T.1 : S.Opens) T.2 = c') (hkc : k ≫ c = c')
    (p : Z' ⟶ (mapDomain (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens))
      (A.res h)).toScheme)
    (hp : p = d' ≫ projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (hpd : p ≫ mapHom (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) =
      k ≫ d)
    (hpi : p ≫ (mapDomain (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens))
      (A.res h)).ι = d') :
    (Scheme.Modules.pullbackCongr hc').inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp d'
            ((relativeProj A).chart (T.1 : S.Opens) T.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback d').map (chartTwistIso A n T).hom =
      (Scheme.Modules.pullbackCongr hkc).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp k c).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist A n) ≫
            (Scheme.Modules.pullbackComp d
                ((relativeProj A).chart (U.1 : S.Opens) U.2)).inv.app (relativeTwist A n) ≫
            (Scheme.Modules.pullback d).map (chartTwistIso A n U).hom) ≫
        (Scheme.Modules.pullbackComp k d).hom.app
          (twistingSheaf (A.grading (U.1 : S.Opens)) n) ≫
        twistMapAt (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n p hpd
          hpi :=
  three_comp_leg_nested_proj (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n
    ((relativeProj A).chart (T.1 : S.Opens) T.2) ((relativeProj A).chart (U.1 : S.Opens) U.2)
    (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (projInclusionTopSection_comp_mapHom A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (projInclusionTopSection_ι A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (chartTwistIso A n T).hom (chartTwistIso A n U).hom
    (twistMap (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n)
    k hc hc' hkc p hp hpd hpi
    (twistMapAt (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n
      (projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
      (projInclusionTopSection_comp_mapHom A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
      (projInclusionTopSection_ι A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2))
    (twistMapAt_eq_comp₅ (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n
      (projInclusionTopSection A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
      (projInclusionTopSection_comp_mapHom A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
      (projInclusionTopSection_ι A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2))
    (twistMapAt (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n p hpd hpi)
    (twistMapAt_eq_comp₅ (A.grading (U.1 : S.Opens)) (A.grading (T.1 : S.Opens)) (A.res h) n p
      hpd hpi)
    (chartTwistIso_hom_eq_twistMapAt' A n T U h)

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
