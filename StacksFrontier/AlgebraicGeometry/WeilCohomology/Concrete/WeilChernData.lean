module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Weil cohomology theories, III: data (D0), (D1), (D2') satisfying (A1)–(A7)

Section 45.14 of the Stacks Project (Tag 0FID) fixes a field `k`, a field `F` of characteristic
zero, and data (D0), (D1), (D2') — `Stacks.WeilCohomology.FirstChernClassData` — satisfying the
axioms (A1)–(A7). Most statements of the section ("Assume given data (D0), (D1), and (D2')
satisfying axioms (A1) -- (A7)") are about such data. This file bundles them as
`Stacks.WeilCohomology.WeilChernData`, each axiom being the predicate that states it:

* (A1)–(A4): `FirstChernClassData.CoproductAxiom`, `PullbackAxiom`, `ProjectiveBundleAxiom`,
  `DivisorAxiom`;
* (A5) and (A7): `FirstChernClassData.KunnethAxiom` and `FirstChernClassData.BlowupAxiom`;
* (A6): `FirstChernClassData.TraceAxiomFor` for the cycle class map `γ` of Tag 0FIF, which is
  `FirstChernClassData.cycleClassOf`, the cycle class map `codimensionCycleClass` of the
  cohomological Chern character `ch^H` of Tag 0FIE (`FirstChernClassData.chernCharacterOf`, the
  rule of Tag 0FIE, unique under (A1)–(A4)).

The two further axioms (A8) and (A9) of the section are assumed only by some statements, so they
are predicates on the bundle rather than fields: (A8) is `WeilChernData.GlobalSections`
(`FirstChernClassData.GlobalSectionsAxiom`), (A9) is `WeilChernData.DivisorTrace`
(`FirstChernClassData.DivisorTraceAxiomFor`).

The data of Section 0FHA these define is `WeilChernData.toWeilData`: `γ` read in
`H^{2i}(X)(i)`, and `∫_X = λ`, the map of (A6), unique by Remark 0FIK.

## Axiom (A9)

(A9) reads: for `X` nonempty, smooth projective, equidimensional of dimension `d`, and
`i : Y ⟶ X` a nonempty effective Cartier divisor smooth over `k`,
`λ_Y(i^*a) = λ_X(a ∪ c₁^H(𝒪_X(Y)))` for `a ∈ H^{2d-2}(X)(d-1)`, `λ_X` and `λ_Y` being as in (A6).
In `FirstChernClassData.DivisorTraceAxiomFor` the dimension of `X` is written `d + 1` and `Y` is
assumed nonempty and equidimensional of dimension `d`, which a nonempty effective Cartier divisor
of `X` smooth over `k` is (and a nonempty `X` of dimension `0` has no nonempty effective Cartier
divisor); "`λ_X` as in (A6)" is any linear map `λ_X` normalised as in (A6), which under
(A1)–(A7) is the unique one (Remark 0FIK). The twist `H^{2d}(X)(d) = H^{2d}(X) ⊗ F(d)` is read
through the canonical coordinate of the line `F(1)`, as in `FirstChernClassData.untwistTrace`:
both sides are linear in the class and `F(d)` is a line, so this is the same condition.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.chernCharacterOf`: `ch^H` of Tag 0FIE.
* `Stacks.WeilCohomology.FirstChernClassData.cycleClassOf`: `γ` of Tag 0FIF.
* `Stacks.WeilCohomology.FirstChernClassData.DivisorTraceAxiomFor`: axiom (A9).
* `Stacks.WeilCohomology.WeilChernData`: data (D0), (D1), (D2') satisfying (A1)–(A7).
* `Stacks.WeilCohomology.WeilChernData.toWeilData`: the data (D0)–(D3) of Section 0FHA they
  define.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔇 : FirstChernClassData k F)

/-- **The cohomological Chern character `ch^H` of Tag 0FIE** of data satisfying (A1)–(A4): the
rule with the properties of Tag 0FIE, which is unique
(`FirstChernClassData.existsUnique_isCohomologicalChernCharacter`). -/
def chernCharacterOf (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
        ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  (𝔇.existsUnique_isCohomologicalChernCharacter hA1 hA2 hA3 hA4).exists.choose

/-- `FirstChernClassData.chernCharacterOf` has the properties of Tag 0FIE. -/
theorem isCohomologicalChernCharacter_chernCharacterOf (hA1 : 𝔇.CoproductAxiom)
    (hA2 : 𝔇.PullbackAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    𝔇.IsCohomologicalChernCharacter (𝔇.chernCharacterOf hA1 hA2 hA3 hA4) :=
  (𝔇.existsUnique_isCohomologicalChernCharacter hA1 hA2 hA3 hA4).exists.choose_spec

/-- `ch^H` is the only rule with the properties of Tag 0FIE. -/
theorem eq_chernCharacterOf (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
        ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) : ch = 𝔇.chernCharacterOf hA1 hA2 hA3 hA4 :=
  (𝔇.existsUnique_isCohomologicalChernCharacter hA1 hA2 hA3 hA4).unique h
    (𝔇.isCohomologicalChernCharacter_chernCharacterOf hA1 hA2 hA3 hA4)

/-- **The cycle class map `γ : CH^i(X) ⟶ H^{2i}(X)(i)` of Tag 0FIF** of data satisfying
(A1)–(A4), with values in `H^*(X)(i)`: the cycle class map `codimensionCycleClass` of the
cohomological Chern character `ch^H` of Tag 0FIE. -/
abbrev cycleClassOf (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ) :
    codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i :=
  (𝔇.isCohomologicalChernCharacter_chernCharacterOf hA1 hA2 hA3 hA4).codimensionCycleClass X i

/-- **Axiom (A9)** for a family `γ` of cycle class maps: let `X` be nonempty, smooth projective
and equidimensional of dimension `d + 1`, and `i : Y ⟶ X` the inclusion of an effective Cartier
divisor `D`, with `Y` nonempty, smooth projective and equidimensional of dimension `d`. For
`λ_X`, `λ_Y` as in axiom (A6) and `a ∈ H^{2d}(X)(d)` we have
`λ_Y(i^*a) = λ_X(a ∪ c₁^H(𝒪_X(D)))`. The twists are read through the canonical coordinate of
`F(1)` (`FirstChernClassData.untwistTrace`), see the module documentation. -/
def DivisorTraceAxiomFor (hA5 : 𝔇.KunnethAxiom)
    (γ : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ),
      codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i) : Prop :=
  ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ),
    IsNonemptyEquidimensional X (d + 1) → IsNonemptyEquidimensional Y d → ∀ (i : Y ⟶ X)
    (D : ((SmoothProjectiveScheme.toScheme k).obj X).IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (e : (SmoothProjectiveScheme.toScheme k).obj Y ≅ D.subscheme),
    e.hom ≫ D.subschemeι = (SmoothProjectiveScheme.toScheme k).map i →
    ∀ (lamX : tateTwist F 𝔇.tate (𝔇.grade X (2 * ((d + 1 : ℕ) : ℤ))) (d + 1 : ℕ) →ₗ[F] F)
      (lamY : tateTwist F 𝔇.tate (𝔇.grade Y (2 * (d : ℤ))) d →ₗ[F] F),
      𝔇.traceContract hA5 X (d + 1) lamX (γ (prod X X) (d + 1) (diagonalClass X (d + 1))) = 1 →
      𝔇.traceContract hA5 Y d lamY (γ (prod Y Y) d (diagonalClass Y d)) = 1 →
      ∀ a : 𝔇.H X, a ∈ 𝔇.grade X (2 * (d : ℤ)) →
        𝔇.untwistTrace Y d lamY (𝔇.pull i a) =
          𝔇.untwistTrace X (d + 1) lamX (a * 𝔇.κ X 1 (𝔇.c₁ X (haveI := hD;
            picardClassOf _ (Stacks.Divisors.divisorSheaf D)
              (Stacks.Divisors.isInvertible_divisorSheaf D))))

end FirstChernClassData

variable (k : Type u) [Field k] (F : Type w) [Field F] [CharZero F]

/-- **Data (D0), (D1), (D2') satisfying axioms (A1)–(A7)** of Section 45.14 (Tag 0FID), over
the category of smooth projective schemes over `k`. Axiom (A6) is stated for the cycle class map
`γ` of Tag 0FIF (`FirstChernClassData.cycleClassOf`), which (A1)–(A4) determine. -/
structure WeilChernData extends FirstChernClassData k F where
  /-- (A1) `H^*` is compatible with finite coproducts. -/
  coproduct : toFirstChernClassData.CoproductAxiom
  /-- (A2) `c₁^H` is compatible with pullbacks. -/
  pullback : toFirstChernClassData.PullbackAxiom
  /-- (A3) The projective bundle formula. -/
  projectiveBundle : toFirstChernClassData.ProjectiveBundleAxiom
  /-- (A4) `a ∪ c₁^H(𝒪_X(Y)) = 0` when `a` restricts to zero on the divisor `Y`. -/
  divisor : toFirstChernClassData.DivisorAxiom
  /-- (A5) `H^*` is compatible with finite products. -/
  kunneth : toFirstChernClassData.KunnethAxiom
  /-- (A6) Existence of a trace map `λ` with `(id ⊗ λ) γ([Δ]) = 1`. -/
  trace : toFirstChernClassData.TraceAxiomFor kunneth
    (toFirstChernClassData.cycleClassOf coproduct pullback projectiveBundle divisor)
  /-- (A7) Pullback along the blowing up in a smooth centre is injective. -/
  blowup : toFirstChernClassData.BlowupAxiom

namespace WeilChernData

variable {k F} (𝔚 : WeilChernData k F)

/-- The cohomological Chern character `ch^H` of Tag 0FIE. -/
abbrev chernCharacter :
    ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
        ∀ n : ℕ, tateTwist F 𝔚.tate (𝔚.H X) n :=
  𝔚.chernCharacterOf 𝔚.coproduct 𝔚.pullback 𝔚.projectiveBundle 𝔚.divisor

/-- `WeilChernData.chernCharacter` has the properties of Tag 0FIE. -/
theorem isCohomologicalChernCharacter :
    𝔚.IsCohomologicalChernCharacter 𝔚.chernCharacter :=
  𝔚.isCohomologicalChernCharacter_chernCharacterOf 𝔚.coproduct 𝔚.pullback 𝔚.projectiveBundle
    𝔚.divisor

/-- The cycle class map `γ : CH^i(X) ⟶ H^{2i}(X)(i)` of Tag 0FIF, with values in `H^*(X)(i)`. -/
abbrev γ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ) :
    codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔚.tate (𝔚.H X) i :=
  𝔚.cycleClassOf 𝔚.coproduct 𝔚.pullback 𝔚.projectiveBundle 𝔚.divisor X i

/-- **The data (D0)–(D3) of Section 0FHA** defined by `𝔚`: `F(1)`, `H^*`, the cycle class map
`γ` of Tag 0FIF read in `H^{2i}(X)(i)`, and the trace map `∫_X = λ` of axiom (A6). -/
abbrev toWeilData : WeilData k F :=
  𝔚.isCohomologicalChernCharacter.toWeilData 𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace

/-- **Axiom (A8)** for `𝔚`: `H^0(Spec(Γ(X, 𝒪_X))) ⟶ H^0(X)` is an isomorphism. -/
abbrev GlobalSections : Prop :=
  𝔚.GlobalSectionsAxiom

/-- **Axiom (A9)** for `𝔚`: `λ_Y(i^*a) = λ_X(a ∪ c₁^H(𝒪_X(Y)))` for a divisor `i : Y ⟶ X`. -/
abbrev DivisorTrace : Prop :=
  𝔚.DivisorTraceAxiomFor 𝔚.kunneth 𝔚.γ

end WeilChernData

end Stacks.WeilCohomology

end
