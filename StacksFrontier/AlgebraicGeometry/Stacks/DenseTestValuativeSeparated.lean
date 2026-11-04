module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianValuativeCriterionSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated

/-!
# The dense-test valuative criterion for separatedness (Stacks 0E95)

Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally
Noetherian, `f` locally of finite type and quasi-separated, `h` of finite type and the image of
`|h| : |𝒰| → |𝒳|` dense in `|𝒳|`. **Stacks 0E95** says that `f` is separated as soon as, for every
2-commutative diagram

```
Spec K --u--> 𝒰 --h--> 𝒳
  |                     |
  j                     f
  v                     v
Spec A -------y-------> 𝒴
```

with `A` a discrete valuation ring with fraction field `K`, the category of dotted arrows
`Spec A ⟶ 𝒳` is either empty or a setoid with exactly one isomorphism class.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.DenseTestUniqueness`: the hypothesis of
  **Stacks 0E95**.
* `AlgebraicGeometry.Stack.ValuativeCriterion.denseTestUniqueness_relativeDiagonal`: the
  hypothesis passes from `f` to its relative diagonal `Δ_f` (the last paragraph of the proof).
* `AlgebraicGeometry.Stack.ValuativeCriterion.denseTestExistence_relativeDiagonal`:
  every discrete valuative square through `h` for `Δ_f` has a dotted arrow, with no extension of
  the valuation ring (the first paragraph of the proof, by Stacks 0E8L).
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSeparated_of_denseTest_of_isSeparated_relativeDiagonal`:
  the first paragraph of the proof, when `Δ_f` is separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_denseTestUniqueness`:
  **Stacks 0E95**.

## Implementation notes

The source's diagram is encoded as a valuative square for `f`
(`AlgebraicGeometry.Stack.ValuativeSquare`, at the canonical spectra of the valuation ring and of
its fraction field) whose generic point `x` *is* a composite `u ≫ h`; the 2-morphism
`γ : y ∘ j ⟶ f ∘ (h ∘ u)` is the square's filler. As in Stacks 0E80 the clause "either empty or a
setoid with exactly one isomorphism class" is the conjunction of the setoid property with the
statement that any two dotted arrows are isomorphic.

Separatedness of `f` (Stacks 04YW) is properness of `Δ_f` in the relative sense of Stacks 04XB.
Stacks 0CQM is used only for 1-morphisms representable by algebraic spaces (it is applied to
`Δ_f` and to `Δ_{Δ_f}`), in the form
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isProper_of_denseTestExistence_of_isRepresentableByAlgebraicSpaces`.
It gives properness of `Δ_f` in the sense of Stacks 0CL5 (separated, finite type,
universally closed as a 1-morphism of algebraic stacks); since `Δ_f` is representable by
algebraic spaces (Stacks 04XS part (1)), the three conjuncts transfer to the 04XB sense by
Stacks 04YS (separatedness), Stacks 050T and Stacks 04XS part (2) (finite type) and Stacks 0512
(universal closedness).

The general case: `Δ_f` is separated by the first case applied to `Δ_f` itself, whose own relative
diagonal is separated because `Δ_f` is representable by algebraic spaces (Stacks 04YQ part (4),
read in the sense of Stacks 04YW by Stacks 04YS); `Δ_f` is quasi-separated in the sense of
Stacks 04YW because `f` is quasi-separated (Stacks 04YZ part (2)); and the hypothesis of the lemma
passes from `f` to `Δ_f` by Stacks 0E8L.

## References

* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 0CLC](https://stacks.math.columbia.edu/tag/0CLC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace ValuativeCriterion

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The hypothesis of Stacks 0E95.** For every valuative square for `f` whose valuation ring
is a discrete valuation ring and whose generic point is a composite `u ≫ h` through `h`, the
category of dotted arrows is either empty or a setoid with exactly one isomorphism class. -/
abbrev DenseTestUniqueness (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : ValuativeSquare B S hS f, IsDiscreteValuationRing q.R →
    (∃ u : schemeFibredCategory B S hS
        (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ 𝒰.1,
      q.x = u ≫ h.hom) →
      IsSetoidCategory (CategoryTheory.DottedArrow q.x q.j f.hom q.y q.γ) ∧
        ∀ a b : CategoryTheory.DottedArrow q.x q.j f.hom q.y q.γ, Nonempty (a ≅ b)

/-- For a discrete valuative square through `h` for `Δ_f`, the two dotted arrows of the associated
square of `f` (Stacks 0E8L part (1)) have a subsingleton set of morphisms, and are isomorphic. -/
private theorem subsingleton_and_nonempty_iso_diagonalDottedArrow {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hu : DenseTestUniqueness B S hS h f)
    (Q : ValuativeSquare B S hS (AlgebraicStacks.relativeDiagonal B S hS f))
    (hq : IsDiscreteValuationRing Q.R)
    (hx : ∃ u : schemeFibredCategory B S hS
        (siteObject B S hS Q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap Q.R Q.K)) ≫ Q.base)) ⟶ 𝒰.1,
      Q.x = u ≫ h.hom) :
    Subsingleton (diagonalDottedArrowFst B S hS (ValuativeSquare.toValuativeDiagram B S hS Q) ⟶
      diagonalDottedArrowSnd B S hS (ValuativeSquare.toValuativeDiagram B S hS Q)) ∧
    Nonempty (diagonalDottedArrowFst B S hS (ValuativeSquare.toValuativeDiagram B S hS Q) ≅
      diagonalDottedArrowSnd B S hS (ValuativeSquare.toValuativeDiagram B S hS Q)) := by
  let D := ValuativeSquare.toValuativeDiagram B S hS Q
  let q' : ValuativeSquare B S hS f :=
    { Q with
      y := (Q.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom
      γ := diagonalWitness B S hS D }
  have := hu q' hq hx
  exact ⟨this.1.subsingleton_hom _ _, this.2 _ _⟩

/-- **The hypothesis of Stacks 0E95 passes to the relative diagonal.** This is the last
paragraph of the proof of Stacks 0E95: the category of dotted arrows of a valuative square for
`Δ_f` is a setoid by Stacks 0E8L part (2) (`Δ_f` is representable by algebraic spaces, compare
Stacks 0CLC), and its isomorphism classes are the morphisms between two dotted arrows of a
valuative square for `f` with the same generic point (Stacks 0E8L part (2) again); those form a
subsingleton because the dotted-arrow category of that square is a setoid. The square for `f`
has the same valuation ring and the same generic point, so it is again a square through `h`. -/
theorem denseTestUniqueness_relativeDiagonal {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hu : DenseTestUniqueness B S hS h f) :
    DenseTestUniqueness B S hS h (AlgebraicStacks.relativeDiagonal B S hS f) := by
  intro q hq hx
  let D := ValuativeSquare.toValuativeDiagram B S hS q
  refine ⟨isSetoidCategory_dottedArrow_relativeDiagonal B S hS D, fun a b => ?_⟩
  have hthin := (subsingleton_and_nonempty_iso_diagonalDottedArrow B S hS hu q hq hx).1
  have heq : (diagonalDottedArrowClassesEquiv B S hS D) (Quotient.mk _ a)
      = (diagonalDottedArrowClassesEquiv B S hS D) (Quotient.mk _ b) :=
    hthin.allEq _ _
  exact Quotient.exact ((diagonalDottedArrowClassesEquiv B S hS D).injective heq)

/-- **A discrete valuative square through `h` for the relative diagonal has a dotted arrow**, as
soon as `f` satisfies the hypothesis of Stacks 0E95; no extension of the valuation ring is
needed. This is the first paragraph of the proof of Stacks 0E95: by Stacks 0E8L part (1) the
square produces two dotted arrows for a square of `f` with the same generic point, which is a
composite through `h`; the hypothesis makes them isomorphic, and Stacks 0E8L part (2) turns that
isomorphism into a dotted arrow for the square of `Δ_f`.

The square is a valuative square for the composite `h ≫ Δ_f`, read as a square for `Δ_f` by
`AlgebraicGeometry.Stack.ValuativeSquare.compRight`, and the dominating extension is the identity
of its valuation ring. -/
theorem denseTestExistence_relativeDiagonal {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hu : DenseTestUniqueness B S hS h f) :
    DenseTestExistence B S hS h (AlgebraicStacks.relativeDiagonal B S hS f) := by
  intro q hq
  let Q := ValuativeSquare.compRight B S hS q
  have hfrac : (algebraMap Q.R Q.K).comp (RingHom.id Q.R)
      = (RingHom.id Q.K).comp (algebraMap Q.R Q.K) := by
    rw [RingHom.comp_id, RingHom.id_comp]
  let e := dominatingExtensionOfRingMaps B Q Q.R Q.K (RingHom.id Q.R) (RingHom.id Q.K)
    (isLocalHom_id Q.R) hfrac Q.ring_mem Q.field_mem
  refine ⟨e, ?_⟩
  let Qe := ValuativeSquare.ofDominatingExtension B S hS Q e
  let D := ValuativeSquare.toValuativeDiagram B S hS Qe
  obtain ⟨m⟩ := (subsingleton_and_nonempty_iso_diagonalDottedArrow B S hS hu Qe hq
    ⟨e.k ≫ q.x, rfl⟩).2
  obtain ⟨d, _⟩ := Quotient.exists_rep
    ((diagonalDottedArrowClassesEquiv B S hS D).symm m.hom)
  exact ⟨d⟩

end ValuativeCriterion

namespace AlgebraicStacks

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The relative diagonal is locally of finite type** in the sense of Stacks 06FS, for an
arbitrary 1-morphism of algebraic stacks. Part (2) of Stacks 04XS gives the relative property of
Section 04XB, which Stacks 06FM equates with the smooth-diagram test of Stacks 06FS for the
representable `Δ_f`. -/
theorem isLocallyOfFiniteType_relativeDiagonal_algebraicStacks (f : 𝒳 ⟶ 𝒴) :
    IsLocallyOfFiniteType B S hS (AlgebraicStacks.relativeDiagonal B S hS f) := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
    (fun _ _ g => Space.IsLocallyOfFiniteType B S hS g)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳.property (twoFibreProduct B S hS f f).property (AlgebraicStacks.relativeDiagonal B S hS f).hom
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f).2

/-- **Properness of the relative diagonal in the sense of Stacks 0CL5 is properness in the sense
of Section 04XB**, that is, separatedness of `f`, once `Δ_f` is quasi-compact. `Δ_f` is
representable by algebraic spaces (Stacks 04XS part (1)); separatedness transfers by
Stacks 04YS, universal closedness by Stacks 0512, and local finiteness of type holds by Stacks
04XS part (2). -/
theorem isSeparated_of_isProper_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hqc : Stack.IsQuasiCompactMorphism B S hS (AlgebraicStacks.relativeDiagonal B S hS f))
    (hP : IsProper B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    IsSeparated B S hS f := by
  have hrep := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hsep : Stack.IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS f).hom :=
    ((Stack.isSeparated_relativeDiagonal_tfae B S hS (AlgebraicStacks.relativeDiagonal B S hS f)
      hrep).out 1 3).mpr hP.1
  have hUC : Stack.UniversallyClosed B S hS (AlgebraicStacks.relativeDiagonal B S hS f).hom :=
    (Stack.representable_universallyClosed_iff_closedMap_baseChange B S hS
      (AlgebraicStacks.relativeDiagonal B S hS f) hrep).mpr hP.2.2
  have hqc' := (Stack.isQuasiCompactMorphism_relativeDiagonal_iff B S hS f).mp hqc
  have hlft := (Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f).2
  intro U y hy F hF he
  exact ⟨hsep U y hy F hF he, ⟨hlft U y hy F hF he, hqc' U y hy F hF he⟩, hUC U y hy F hF he⟩

/-- The 2-fibre product `𝒳 ×_𝒴 𝒳` is locally Noetherian when `𝒴` is and `f` is locally of
finite type (Stacks 06R6, twice). -/
theorem isLocallyNoetherian_twoFibreProduct_of_isLocallyOfFiniteType (f : 𝒳 ⟶ 𝒴)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (twoFibreProduct B S hS f f) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (twoFibreProductSquare B S hS f f).fst
    (isLocallyOfFiniteType_baseChange B S hS f f (twoFibreProductSquare B S hS f f)
      (isTwoFibreProduct_twoFibreProductSquare B S hS f f) hft)
    (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hft hY)

/-- **Stacks 0E95, first paragraph of the proof: the case of a separated relative diagonal.**

Stacks 0CQM applies to `h` and `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`, which is representable by algebraic
spaces (Stacks 04XS part (1)): the target is locally Noetherian (Stacks
06R6, twice), `Δ_f` is separated by assumption and of finite type, and its valuative hypothesis
holds outright by Stacks 0E8L
(`AlgebraicGeometry.Stack.ValuativeCriterion.denseTestExistence_relativeDiagonal`).
So `Δ_f` is proper, which is separatedness of `f`. -/
theorem isSeparated_of_denseTest_of_isSeparated_relativeDiagonal
    (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hΔft : IsFiniteType B S hS (AlgebraicStacks.relativeDiagonal B S hS f))
    (hh : IsFiniteType B S hS h)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val;
      Dense (Set.range (Stack.pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property
        h.hom.hom)))
    (hΔsep : IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS f))
    (hu : ValuativeCriterion.DenseTestUniqueness B S hS h f) :
    IsSeparated B S hS f :=
  isSeparated_of_isProper_relativeDiagonal B S hS f hΔft.2
    (isProper_of_denseTestExistence_of_isRepresentableByAlgebraicSpaces B S hS
      (AlgebraicStacks.relativeDiagonal B S hS f) h
      (isLocallyNoetherian_twoFibreProduct_of_isLocallyOfFiniteType B S hS f hY hft)
      hΔft hh hΔsep hdense
      (ValuativeCriterion.denseTestExistence_relativeDiagonal B S hS hu)
      (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f))

/-- **Stacks 0E95.** Let
`f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally
Noetherian, `f` locally of finite type and quasi-separated, `h` of finite type and the image of
`|h|` dense in `|𝒳|`. If every discrete valuative square for `f` through `h` has a category of
dotted arrows which is either empty or a setoid with exactly one isomorphism class, then `f` is
separated.

`Δ_f` is separated by the first case applied to `Δ_f` and `h`: the relative diagonal of `Δ_f` is
separated because `Δ_f` is representable by algebraic spaces (Stacks 04YQ part (4), read in the
sense of Stacks 04YW by Stacks 04YS), `Δ_{Δ_f}` is quasi-compact because `Δ_f` is
quasi-separated (Stacks 04YZ part (2) and Stacks 050T), and the hypothesis passes from `f` to
`Δ_f` by Stacks 0E8L. Then the first case applies to `f` and `h`. -/
@[stacks 0E95]
theorem isSeparated_of_denseTestUniqueness
    (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hh : IsFiniteType B S hS h)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val;
      Dense (Set.range (Stack.pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property
        h.hom.hom)))
    (hu : ValuativeCriterion.DenseTestUniqueness B S hS h f) :
    IsSeparated B S hS f := by
  let g := AlgebraicStacks.relativeDiagonal B S hS f
  have hgrep : Stack.IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  -- `Δ_f` is of finite type
  have hΔft : IsFiniteType B S hS g :=
    ⟨isLocallyOfFiniteType_relativeDiagonal_algebraicStacks B S hS f,
      (Stack.isQuasiCompactMorphism_relativeDiagonal_iff B S hS f).mpr hqs.1⟩
  -- `Δ_{Δ_f}` is of finite type, `Δ_f` being quasi-separated
  have hΔΔft : IsFiniteType B S hS (AlgebraicStacks.relativeDiagonal B S hS g) :=
    ⟨isLocallyOfFiniteType_relativeDiagonal_algebraicStacks B S hS g,
      (Stack.isQuasiCompactMorphism_relativeDiagonal_iff B S hS g).mpr
        ((Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS g hgrep).mpr
          hqs.2)⟩
  -- `Δ_{Δ_f}` is separated, `Δ_f` being representable by algebraic spaces
  have hΔΔsep : IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS g) :=
    ((Stack.isSeparated_relativeDiagonal_tfae B S hS (AlgebraicStacks.relativeDiagonal B S hS g)
      (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS g)).out
        1 3).mp
      (Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS g hgrep).2
  -- the first case for `Δ_f`, then for `f`
  have hΔsep : IsSeparated B S hS g :=
    isSeparated_of_denseTest_of_isSeparated_relativeDiagonal B S hS g h
      (isLocallyNoetherian_twoFibreProduct_of_isLocallyOfFiniteType B S hS f hY hft)
      hΔft.1 hΔΔft hh hdense hΔΔsep
      (ValuativeCriterion.denseTestUniqueness_relativeDiagonal B S hS hu)
  exact isSeparated_of_denseTest_of_isSeparated_relativeDiagonal B S hS f h hY hft
    hΔft hh hdense hΔsep hu

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
