module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleNeighborhoodBaseChangeSystem

/-!
# The étale neighbourhood base change system as a Mayer--Vietoris reduction

Let `B` be a big étale site containing a scheme `S`, let `s` be a geometric point of `S` and let
`f : X ⟶ S` be a morphism of schemes. The base changes `X ×_S V` of `f` to the *affine* étale
neighbourhoods of `s` form a diagram of schemes over `X` whose limit is
`X ×_S Spec(𝒪^{sh}_{S,s})`, by `AlgebraicGeometry.isLimitStrictHenselizationBaseChangeAffineCone`.
This file feeds that system to the Mayer--Vietoris reduction of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/QcqsReduction.lean`.

The index category of the étale neighbourhoods of a geometric point is **cofiltered** and not a
directed preorder, which is what stops the colimit stack of [Stacks, Tag 03Q6] from applying to
it. The reduction of `QcqsReduction` is indexed by an *arbitrary* category with exact colimits of
abelian groups, so it does apply, and this file records that: the system, the vertex, the legs,
the comparison morphism, and the two conclusions of the reduction, all at the cofiltered index of
the affine étale neighbourhoods of `s`.

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhoodIndex` — the opposite of the small cofiltered category of
  affine étale neighbourhoods of `s`, i.e. the shape the colimit is taken over.
* `AlgebraicGeometry.etaleNeighborhoodBaseChangeOverDiagram` — the base changes `X ×_S V`, as a
  diagram of schemes over `X` indexed as the reduction wants it.
* `AlgebraicGeometry.etaleNeighborhoodBaseChangeOverCone` — the limit cone
  `X ×_S Spec(𝒪^{sh}_{S,s})`, in the category of schemes over `X`.
* `AlgebraicGeometry.etaleNeighborhoodComparison` — **the comparison morphism**
  `colim_V H^n(X ×_S V ⊇ preimage of U, 𝓕) ⟶ H^n(X ×_S Spec(𝒪^{sh}_{S,s}) ⊇ preimage of U, 𝓕)`
  of an open `U` of `X`.

## Main results

* `AlgebraicGeometry.hasExactColimitsOfShape_etaleNeighborhoodIndex` — abelian groups have exact
  colimits of this shape: the index is small and filtered, so this is `AB5OfSize`.
* `AlgebraicGeometry.isIso_etaleNeighborhoodComparison_sup` — **the Mayer--Vietoris step** at this
  index, with no hypothesis beyond the three smaller opens.
* `AlgebraicGeometry.isIso_etaleNeighborhoodComparison_top` — **the reduction to affine opens** of
  `X`, for `X` quasi-compact and quasi-separated.
* `AlgebraicGeometry.isIso_etaleNeighborhoodComparison_top_of_qcqs` — the same with the hypothesis
  [Stacks, Tag 03Q9] makes, `f` quasi-compact and quasi-separated over an affine base.

Both of the last two take the affine-open invertibility as a hypothesis, which is a genuine
hypothesis and not a gap; see "What this file does not do".

## Implementation notes

The reduction is indexed so that the levels sit over `Iᵒᵖ` and the colimit is taken over `I`;
the neighbourhood category `(geometricPointFiber B S hS s).Elements` is the *level* index, so `I`
is its opposite and the diagram is reindexed by `CategoryTheory.unopUnop`. Restricting to the
affine neighbourhoods along the initial inclusion
`AlgebraicGeometry.etaleNeighborhoodAffineInclusion` makes the index a `SmallCategory` in the
universe of the schemes, which is what `AB5OfSize` needs; the inclusion is initial, so no
generality is lost in the limit, and the levels become quasi-compact and quasi-separated as soon
as `f` is, by `AlgebraicGeometry.quasiCompact_etaleNeighborhoodBaseChange_fst` and its companion.

Every level of the system is étale over `X`, being the base change along `f` of the étale
structure morphism of a neighbourhood; Mathlib's base-change instance for `Etale` gives this. The
limit is not: `Spec(𝒪^{sh}_{S,s})` is not étale over `S`, which is why the right hand side of
[Stacks, Tag 03Q9] is not a value of a presheaf on the small étale site of `X`.

### What this file does not do

The coefficients of `QcqsReduction` are an abelian sheaf on the big étale site of *all* schemes,
whereas [Stacks, Tag 03Q9] takes an abelian sheaf on the small étale site of `X`; the two are
bridged by the big étale site *over* `X`, on which that sheaf does have an inverse image, and the
Mayer--Vietoris squares of preimages of opens are built in this repository only on the site of all
schemes. Nothing here asserts anything about an abelian sheaf on the small étale site of `X`, and
nothing here is about [Stacks, Tag 03Q9]'s conclusion.

The affine-open invertibility that `isIso_etaleNeighborhoodComparison_top` and its companion
consume is an input of those statements, and it is **not** [Stacks, Tag 03Q6] for a system of
affine schemes: with `𝓕` an arbitrary abelian sheaf on the big étale site of all schemes it is
false, the degree-zero comparison being `colim_V 𝓕(g_V⁻¹U) ⟶ 𝓕(g⁻¹U)` and a product of copies of
the structure sheaf refuting it. Tag 03Q6 takes the inverse images of a single sheaf on `X`, which
is a condition the site of all schemes cannot express. The implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/QcqsReduction.lean` give the counterexample
and say what Tag 03Q6 at its own hypotheses needs instead.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology.BigEtale

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  {X : Scheme.{u}} (f : X ⟶ S)

/-! ### The index -/

/-- The shape the colimit over the étale neighbourhoods of `s` is taken over: the opposite of the
small cofiltered category of affine étale neighbourhoods. It is small and filtered. -/
abbrev EtaleNeighborhoodIndex : Type u := (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ

/-- Abelian groups have exact colimits of the shape of the étale neighbourhoods of `s`: the index
is a small filtered category, so this is `AB5OfSize` for `AddCommGrpCat`. -/
instance hasExactColimitsOfShape_etaleNeighborhoodIndex :
    HasExactColimitsOfShape (EtaleNeighborhoodIndex B S hS s) AddCommGrpCat.{u + 1} :=
  letI : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} := AB5OfSize_of_univLE AddCommGrpCat.{u + 1}
  AB5OfSize.ofShape (EtaleNeighborhoodIndex B S hS s)

/-! ### The system and its limit, over `X` -/

/-- The base changes `X ×_S V` to the affine étale neighbourhoods of `s`, as a diagram of schemes
over `X` indexed by the opposite of `EtaleNeighborhoodIndex`. -/
abbrev etaleNeighborhoodBaseChangeOverDiagram :
    (EtaleNeighborhoodIndex B S hS s)ᵒᵖ ⥤ Over X :=
  unopUnop _ ⋙ etaleNeighborhoodAffineInclusion B S hS s ⋙
    etaleNeighborhoodOverDiagram B S hS s ⋙ Over.pullback f

/-- The cone `X ×_S Spec(𝒪^{sh}_{S,s})` over the system, in the category of schemes over `X`. -/
abbrev etaleNeighborhoodBaseChangeOverCone :
    Cone (etaleNeighborhoodBaseChangeOverDiagram B S hS s f) :=
  (((Over.pullback f).mapCone (strictHenselizationOverCone B S hS s)).whisker
    (etaleNeighborhoodAffineInclusion B S hS s)).whisker
      (unopUnop (etaleNeighborhoodAffineIndex B S hS s))

/-- The leg of the limit cone at a level. -/
abbrev etaleNeighborhoodBaseChangeLeg (i : (EtaleNeighborhoodIndex B S hS s)ᵒᵖ) :
    (etaleNeighborhoodBaseChangeOverCone B S hS s f).pt ⟶
      (etaleNeighborhoodBaseChangeOverDiagram B S hS s f).obj i :=
  (etaleNeighborhoodBaseChangeOverCone B S hS s f).π.app i

/-- A leg followed by a transition is a leg. -/
theorem etaleNeighborhoodBaseChangeLeg_comp
    ⦃i j : (EtaleNeighborhoodIndex B S hS s)ᵒᵖ⦄ (a : i ⟶ j) :
    etaleNeighborhoodBaseChangeLeg B S hS s f i ≫
        (etaleNeighborhoodBaseChangeOverDiagram B S hS s f).map a =
      etaleNeighborhoodBaseChangeLeg B S hS s f j :=
  (etaleNeighborhoodBaseChangeOverCone B S hS s f).w a

/-! ### The comparison morphism and the reduction -/

variable (𝓕 : Sheaf topology.{u} AddCommGrpCat.{u + 1})

/-- **The comparison morphism** `colim_V H^n(g_V⁻¹U, 𝓕) ⟶ H^n(g⁻¹U, 𝓕)` attached to an open `U`
of `X`, at the cofiltered index of the affine étale neighbourhoods of `s`. -/
abbrev etaleNeighborhoodComparison (U : X.Opens) (n : ℕ) :
    colimit (Stacks.EtaleCohomology.QcqsReduction.openDiagram
        (etaleNeighborhoodBaseChangeOverDiagram B S hS s f) 𝓕 U n) ⟶
      Sheaf.H'.{u + 1} 𝓕 n
        (preimageToSite (etaleNeighborhoodBaseChangeOverCone B S hS s f).pt.hom |>.obj U) :=
  Stacks.EtaleCohomology.QcqsReduction.comparison
    (etaleNeighborhoodBaseChangeOverDiagram B S hS s f)
    (etaleNeighborhoodBaseChangeOverCone B S hS s f).pt
    (etaleNeighborhoodBaseChangeLeg B S hS s f)
    (etaleNeighborhoodBaseChangeLeg_comp B S hS s f) 𝓕 U n

/-- **The Mayer--Vietoris step at the cofiltered index of the étale neighbourhoods of `s`.** If
the comparison is invertible over `U`, over `V` and over `U ⊓ V` in every degree, then it is
invertible over `U ⊔ V` in every degree. There is no hypothesis beyond the three smaller opens. -/
theorem isIso_etaleNeighborhoodComparison_sup (U V : X.Opens)
    (hU : ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 U n))
    (hV : ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 V n))
    (hUV : ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 (U ⊓ V) n)) :
    ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 (U ⊔ V) n) :=
  Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_sup _ _ _
    (etaleNeighborhoodBaseChangeLeg_comp B S hS s f) 𝓕 U V hU hV hUV

/-- **The reduction to the affine opens of `X`** at the cofiltered index of the étale
neighbourhoods of `s`: for a quasi-compact quasi-separated `X`, invertibility of the comparison
over every affine open of `X` in every degree gives invertibility over `X` itself. -/
theorem isIso_etaleNeighborhoodComparison_top [QuasiSeparatedSpace X] [CompactSpace X]
    (haffine : ∀ U : X.Opens, IsAffineOpen U →
      ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 U n)) :
    ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 ⊤ n) :=
  Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_top _ _ _
    (etaleNeighborhoodBaseChangeLeg_comp B S hS s f) 𝓕 haffine

/-- **The reduction to the affine opens of `X` for a quasi-compact quasi-separated `f` over an
affine base.** This is the shape in which [Stacks, Tag 03Q9] reduces to the affine opens of `X`:
the hypothesis on `f` is the one that tag makes, and no quasi-compactness of `X` is assumed — it
follows from that of `f` and affineness of `S`. -/
theorem isIso_etaleNeighborhoodComparison_top_of_qcqs [IsAffine S] [QuasiCompact f]
    [QuasiSeparated f]
    (haffine : ∀ U : X.Opens, IsAffineOpen U →
      ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 U n)) :
    ∀ n : ℕ, IsIso (etaleNeighborhoodComparison B S hS s f 𝓕 ⊤ n) :=
  Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_top_of_qcqs_over_affine _ _ _
    (etaleNeighborhoodBaseChangeLeg_comp B S hS s f) 𝓕 f haffine

end AlgebraicGeometry

end
