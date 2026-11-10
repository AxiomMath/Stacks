module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TriangleReduction
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenUniversalSkeleton

/-!
# The whole of Lemma 01O1 from one comparison with the universal quadruple

`...RelativeProjTwistChartBridge.tag01O1_of_triangleCommutes` carries the whole of [Stacks, Tag
01O1] on the single hypothesis
`...RelativeProjTwistChartBridge.TriangleCommutes`, and
`...RelativeProjTwistChartBridge.triangleCommutes_of_gradedIso` of
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TriangleReduction` shows that
hypothesis follows from *any* isomorphism of sheaves of graded algebras carrying the tag's second
leg to the quadruple's `ψ`. This file composes the two with the representation of `F_d` by the
relative degree-`d` open, and so reduces the tag to a single comparison that mentions neither `θ`
nor the triangle.

## What the obligation becomes

Let `Qu` be *a* universal quadruple on `U_d` — a quadruple over the structure morphism of `U_d`
whose class `...RelativeProjQcohSheaf.Fd.homDegreeOpen` sends to the identity of `U_d`. Such a
`Qu` exists unconditionally, because `homDegreeOpen` is a bijection
(`...RelativeProjQcohSheaf.Fd.degreeOpenEquiv`, residue (i) of [Stacks, Tag 01NY] over an
arbitrary base); `exists_universalQuadruple_degreeOpen` below records that, and nothing about it
needs the charts.

Then `...RelativeProjQcohSheaf.Fd.pullback_eq_of_homDegreeOpen_eq_id` says the given quadruple is
*strictly equivalent* to the pullback of `Qu` along the morphism `r` the tag attaches to it, so
the tag's `θ` exists on the Laurent algebra of `r^*ℒ_univ` with the triangle for `Qu`'s own `ψ`.
What is left is to move it to the tag's own source `r^*(⨁_n 𝒪(nd))`, and that is one comparison:

`c₀ : r^*(⨁_{n ∈ ℤ} 𝒪(nd)) ≅ ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n}`

carrying `...RelativeProjTwists.TwistData.psiLegVeronese` to
`...RelativeProjQcohSheaf.Quadruple.universalLeg`. `tag01O1_of_universalComparison` is the tag on
that comparison alone.

**That comparison is the chart-wise identification of the glued twists of [Stacks, Tag 01NR] with
the absolute universal family of [Stacks, Tag 01N9].** It is carried out, at `T` itself rather
than on `U_d`, in
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleChart`,
and the whole tag is `...RelativeProjTwistChartBridge.tag01O1`. Its two named halves are
`...RelativeProjTwists.TwistData.psiTransposeNat_chart` and
`...ProjClassifyingPullback.classifyingHom_universalVeroneseSections`; see the module docstring of
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTriangle` for the full account
of
what is owed. The point of this file is that *nothing else* is owed: no degree-one datum, no
recognition comparison, no induction on the degree, no unit law and no surjectivity — those were
all consequences of the comparison, and the three previous statements of the obligation that
listed them separately are subsumed here.

## Main results

* `...RelativeProjQcohSheaf.Fd.exists_universalQuadruple_degreeOpen`: **a universal quadruple on
  the relative degree-`d` open exists**, with no hypothesis beyond `d ≥ 1` — the preimage of the
  identity under the bijection of residue (i) of [Stacks, Tag 01NY].
* `...RelativeProjTwistChartBridge.tag01O1_of_universalComparison`: **the whole of [Stacks, Tag
  01O1] at the tag's own morphism and the tag's own second leg, on one comparison of the source
  with the Laurent algebra of the pullback of a universal quadruple's invertible module.**

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### A universal quadruple on the relative degree-`d` open -/

/-- **A universal quadruple on the relative degree-`d` open exists**, over an arbitrary base and
with no hypothesis beyond `d ≥ 1`: a quadruple over the structure morphism of `U_d` whose class
`...RelativeProjQcohSheaf.Fd.homDegreeOpen` sends to the identity of `U_d`.

No choice is being smuggled in beyond the one `homDegreeOpen` already is: the map is surjective
(`...RelativeProjQcohSheaf.Fd.homDegreeOpen_surjective`, residue (i) of [Stacks, Tag 01NY] over
an arbitrary base), so the identity has a preimage, and the recorded morphism of that preimage is
the structure morphism of `U_d` because `homDegreeOpen` is a correspondence over the base
(`...Fd.homDegreeOpen_comp_toBase`).

The content of [Stacks, Tag 01O1] is *not* the existence of this quadruple but its
identification with the glued twists of [Stacks, Tag 01NR]; see the module docstring. -/
public theorem Fd.exists_universalQuadruple_degreeOpen {S : Scheme.{u}} (A : SheafGradedAlgebra S)
    (P : RelativeProjData A) {k : ℕ} (hk : 0 < k) :
    ∃ Qu : Quadruple (Fd.degreeOpenHom A P k) (situationAlgebra A) (k : ℤ),
      Fd.homDegreeOpen A P hk (Fd.mk (Fd.degreeOpenHom A P k) Qu) =
        CategoryStruct.id (P.degreeOpen k).toScheme := by
  obtain ⟨ξ, hξ⟩ := Fd.homDegreeOpen_surjective A P hk (P.degreeOpen k).toScheme
    (CategoryStruct.id _)
  have hfst : ξ.1 = Fd.degreeOpenHom A P k := by
    refine (Fd.homDegreeOpen_comp_toBase A P hk ξ).symm.trans ?_
    rw [hξ]
    exact Category.id_comp _
  obtain ⟨Qu, hQu⟩ := Fd.exists_rep_of_fst ξ hfst
  exact ⟨Qu, (congrArg (Fd.homDegreeOpen A P hk) hQu).trans hξ⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {d : ℕ} {f : T ⟶ S}

/-- Two transports along mutually inverse equalities of objects cancel. Stated as a lemma rather
than left to `simp` because the context it is used in mentions `...RelativeProjQcohSheaf.Fd`,
whose unfolding to a sigma type makes the goal ill-typed at the transparency `rw` elaborates
patterns at. -/
private theorem eqToHom_eqToHom_comp {C : Type*} [Category C] {X Y Z : C}
    (h1 : X = Y) (h2 : Y = X) (g : X ⟶ Z) :
    eqToHom h1 ≫ eqToHom h2 ≫ g = g := by
  cases h1
  simp

/-! ### The tag on one comparison of the source -/

/-- **[Stacks, Tag 01O1], at the tag's own morphism and the tag's own second leg, on one
comparison of the source.**

In Situation 01NN, for a quadruple `(f : T → S, d, ℒ, ψ)` of Section 01NS with `d ≥ 1`, let
`r = r_{d, ℒ, ψ}` be `...RelativeProjTwistChartBridge.thetaMorphism`, let `Qu` be a universal
quadruple on the relative degree-`d` open (one exists, by
`...RelativeProjQcohSheaf.Fd.exists_universalQuadruple_degreeOpen`), and suppose given an
isomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras

`c₀ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n}`

carrying the tag's second leg `...RelativeProjTwists.TwistData.psiLegVeronese` to the pullback of
`Qu`'s own `ψ`. Then

1. `r` is a morphism over `S`;
2. there is an isomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras
   `θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`;
3. `ψ_univ ≫ θ = ψ` in every integer degree; and
4. `θ` is the unique homomorphism of sheaves of graded algebras with that property.

Nothing else is assumed. The universality of `Qu` turns the quadruple into the pullback of `Qu`
along `r` up to strict equivalence
(`...RelativeProjQcohSheaf.Fd.pullback_eq_of_homDegreeOpen_eq_id`), which gives `θ` on the Laurent
algebra of `r^*ℒ_univ`; `c₀` moves it to the tag's own source; and
`...RelativeProjTwistChartBridge.triangleCommutes_of_gradedIso` supplies the degree-one datum and
the recognition comparison that `...RelativeProjTwistChartBridge.TriangleCommutes` asks for, so
none of those has to be exhibited.

**This declaration carries no tag attribute**, because `c₀` is a hypothesis that Tag 01O1 does not
have. It is the chart-wise identification of the glued twists of [Stacks, Tag 01NR] with the
absolute universal family of [Stacks, Tag 01N9]; the tag itself, with no such hypothesis, is
`...RelativeProjTwistChartBridge.tag01O1`. -/
public theorem tag01O1_of_universalComparison (D : TwistData A) (hd : 0 < d)
    (P : Quadruple f (situationAlgebra A) (d : ℤ))
    (Qu : Quadruple (Fd.degreeOpenHom A (relativeProj A) d) (situationAlgebra A) (d : ℤ))
    (hQu : Fd.homDegreeOpen A (relativeProj A) hd
        (Fd.mk (Fd.degreeOpenHom A (relativeProj A) d) Qu) =
      CategoryStruct.id ((relativeProj A).degreeOpen d).toScheme)
    (c₀ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ≅
      laurent ((Qu.pullback (Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f P))).L))
    (hc₀ : ∀ n : ℤ,
      D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P) (d : ℤ) n ≫
          c₀.hom.app n =
        Qu.universalLeg
          (Fd.homDegreeOpen_comp_toBase A (relativeProj A) hd (Fd.mk f P)) n) :
    thetaMorphism hd P ≫ (relativeProj A).toBase = f ∧
      ∃ θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ≅ laurent P.L,
        (∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ θ.hom.app n = P.twisting.app n) ∧
          ∃! Θ : pullbackTwistVeronese D (d : ℤ) (thetaMorphism hd P) ⟶ laurent P.L,
            ∀ n : ℤ, D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P)
              (d : ℤ) n ≫ Θ.app n = P.twisting.app n := by
  obtain ⟨hf, γ, hγ⟩ := Fd.exists_laurentIso_of_mk_eq
    (Qu.pullback (Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f P))) P
    (Fd.pullback_eq_of_homDegreeOpen_eq_id A (relativeProj A) hd
      (Fd.mk (Fd.degreeOpenHom A (relativeProj A) d) Qu) hQu (Fd.mk f P))
  have hθ : ∀ n : ℤ, Qu.universalLeg
      (Fd.homDegreeOpen_comp_toBase A (relativeProj A) hd (Fd.mk f P)) n ≫ γ.hom.app n =
      P.twisting.app n := by
    intro n
    rw [Quadruple.universalLeg, Category.assoc, hγ n]
    exact eqToHom_eqToHom_comp _ _ _
  refine tag01O1_of_triangleCommutes D hd P
    (triangleCommutes_of_gradedIso D (thetaMorphism hd P) P
      (thetaMorphism_mem_degreeOpen hd P) (thetaMorphism_comp_toBase hd P) (c₀ ≪≫ γ) ?_)
  intro n
  change D.psiLegVeronese (thetaMorphism hd P) (thetaMorphism_comp_toBase hd P) (d : ℤ) n ≫
    c₀.hom.app n ≫ γ.hom.app n = P.twisting.app n
  rw [← Category.assoc, hc₀ n]
  exact hθ n

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
