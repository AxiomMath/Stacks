module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianUniversallyClosedCounterexample

/-!
# Stacks 0H1Y, corrected

Let `f : X ⟶ Y` be a morphism of finite type of algebraic spaces over a scheme `S`, with `Y`
locally Noetherian. Stacks 0H1Y (Lemma 70.21.4) claims that the following five conditions are
equivalent:

1. `f` is universally closed;
2. `f` satisfies the existence part of the valuative criterion;
3. there are a scheme `V` and a surjective étale morphism `V ⟶ Y` such that
   `|𝐀ⁿ × X ×_Y V| ⟶ |𝐀ⁿ × V|` is closed for all `n ≥ 0`;
4. every valuative square for `f` over a discrete valuation ring `A` with fraction field `K`
   acquires a dotted arrow after a finite separable extension `K'/K` and passage to a discrete
   valuation ring `A' ⊆ K'` dominating `A`;
5. every valuative square for `f` over a discrete valuation ring `A` with fraction field `K`
   acquires a dotted arrow after a field extension `K'/K` and passage to a valuation ring
   `A' ⊆ K'` dominating `A`.

## The correction

As stated, with no condition on `f` beyond finite type, the lemma is false: the implication
(1) ⇒ (2) fails. The witness is the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ` of the quotient of the
affine line by the integer translations. It is of finite type over the Noetherian scheme
`Spec ℚ` and universally closed (Stacks 03IV), but the `ℚ((t))`-point `1/t` extends to no
valuation ring dominating `ℚ[[t]]`, which is the failure recorded in the introduction of Stacks
section 03K9; this morphism is not decent. The negation of the source statement is
`AlgebraicGeometry.Space.not_forall_universallyClosed_tfae_of_isLocallyNoetherian`.

The wrong step is the first sentence of the source's proof, which cites Stacks 0CM9
(Lemma 70.20.2) and Stacks 03KA (Lemma 67.42.1) for the equivalence of (1), (2) and (3).
Stacks 0CM9 gives (1) ⇔ (3) for `f` quasi-compact, but Stacks 03KA only gives (2) ⇒ (1) for `f`
quasi-compact; the converse (1) ⇒ (2) is Stacks 0A3X (Lemma 67.42.2) for `f` quasi-separated
and Stacks 03M6 (Lemma 68.17.11) for `f` quasi-compact and decent. The rest of the source's proof
is correct and uses no separation hypothesis.

The corrected statement therefore has two halves:

* without any further hypothesis, (2) ⇒ (4) ⇒ (5) ⇒ (1) ⇔ (3), so in particular (2) ⇒ (1);
* if moreover `f` is decent (for instance quasi-separated, Stacks 03M5), all five conditions
  are equivalent.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_implications_of_isLocallyNoetherian`: **Stacks
  0H1Y**, the implications (2) ⇒ (4) ⇒ (5) ⇒ (1) ⇔ (3), with no decency hypothesis.
* `AlgebraicGeometry.Space.universallyClosed_implications_and_tfae_of_isLocallyNoetherian`:
  **Stacks 0H1Y**, the full corrected statement: those implications, and the equivalence of the
  five conditions when `f` is decent, which is
  `AlgebraicGeometry.Space.universallyClosed_tfae_of_isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0H1Y](https://stacks.math.columbia.edu/tag/0H1Y)
* [Stacks Project, Tag 03IV](https://stacks.math.columbia.edu/tag/03IV)
* [Stacks Project, Tag 03K9](https://stacks.math.columbia.edu/tag/03K9)
* [Stacks Project, Tag 03KA](https://stacks.math.columbia.edu/tag/03KA)
* [Stacks Project, Tag 03M6](https://stacks.math.columbia.edu/tag/03M6)
* [Stacks Project, Tag 0A3X](https://stacks.math.columbia.edu/tag/0A3X)
* [Stacks Project, Tag 0CM9](https://stacks.math.columbia.edu/tag/0CM9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0H1Y, the implications that hold without decency.** Let `f : X ⟶ Y` be a morphism of
finite type of algebraic spaces over `S`, with `Y` locally Noetherian. Number the conditions of
Stacks 0H1Y as follows:

1. `f` is universally closed;
2. `f` satisfies the existence part of the valuative criterion;
3. there are an object `V` of the site and a surjective étale morphism `V ⟶ Y` such that for
   every `n` the base change of `f` to affine `n`-space over `V` is closed;
4. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after a finite separable extension of the fraction field and passage to a
   dominating discrete valuation ring;
5. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after an extension of the fraction field and passage to a dominating valuation
   ring.

Then (2) ⇒ (4), (4) ⇒ (5), (5) ⇒ (1) and (1) ⇔ (3); in particular (2) ⇒ (1).

**Correction.** The source asserts that the five conditions are equivalent under these
hypotheses alone, which is false: (1) ⇒ (2) fails for the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ`,
which is of finite type and universally closed (Stacks 03IV) but does not satisfy the existence
part of the valuative criterion (Stacks section 03K9); see
`not_forall_universallyClosed_tfae_of_isLocallyNoetherian`. The source's proof derives
(1) ⇔ (2) from Stacks 03KA, which only gives (2) ⇒ (1). Every other implication of the source
holds as stated, and they are the ones asserted here. The equivalence of all five conditions
for `f` decent is `universallyClosed_implications_and_tfae_of_isLocallyNoetherian`.

The proof follows the source: (1) ⇔ (3) is Stacks 0CM9 (`f` is quasi-compact, being of finite
type), (2) ⇒ (4) is Stacks 03KH with Krull–Akizuki (Stacks 00PG), (4) ⇒ (5) is immediate, and
(5) ⇒ (1) reduces to closedness over a Noetherian affine base by Stacks 0CMC. -/
@[stacks 0H1Y, ega "II 7.3.8" "(b) ⇒ (a)"]
theorem universallyClosed_implications_of_isLocallyNoetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X_alg : IsAlgebraicSpace B S hS X) (Y_alg : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (ft : IsFiniteType B S hS f)
    (noeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    (ValuativeCriterion.Existence f →
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift) ∧
      ((∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift) →
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift) ∧
      ((∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift) →
        UniversallyClosed B S hS f) ∧
      (UniversallyClosed B S hS f ↔
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f)) :=
  ⟨discreteFiniteSeparableExistence_of_valuativeCriterion_existence B S hS X_alg Y_alg f,
    fun h q hq ↦ (h q hq).imp fun _ he ↦ he.2.2,
    universallyClosed_of_discreteExistence B S hS X_alg Y_alg f ft noeth,
    (universallyClosed_tfae_of_isQuasiCompact B S hS X_alg Y_alg f ft.2).out 1 3⟩

/-- **Stacks 0H1Y, corrected.** Let `f : X ⟶ Y` be a morphism of finite type of algebraic spaces
over `S`, with `Y` locally Noetherian, and number the conditions of Stacks 0H1Y as in
`universallyClosed_implications_of_isLocallyNoetherian`:

1. `f` is universally closed;
2. `f` satisfies the existence part of the valuative criterion;
3. there are an object `V` of the site and a surjective étale morphism `V ⟶ Y` such that for
   every `n` the base change of `f` to affine `n`-space over `V` is closed;
4. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after a finite separable extension of the fraction field and passage to a
   dominating discrete valuation ring;
5. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after an extension of the fraction field and passage to a dominating valuation
   ring.

Then (2) ⇒ (4) ⇒ (5) ⇒ (1) ⇔ (3), and if `f` is decent (for instance quasi-separated) the five
conditions are equivalent.

**Correction.** The source asserts the equivalence of the five conditions with no hypothesis on
`f` beyond finite type. That is false, by
`not_forall_universallyClosed_tfae_of_isLocallyNoetherian`: the structure morphism
`𝔸¹_ℚ/ℤ ⟶ Spec ℚ` of the quotient of the affine line by the integer translations is of finite
type over a Noetherian scheme and universally closed (Stacks 03IV), but the `ℚ((t))`-point `1/t`
extends to no valuation ring dominating `ℚ[[t]]`, so (1) holds and (2) fails; that morphism is
not decent. The faulty step is the source's appeal to Stacks 03KA for (1) ⇔ (2): Stacks 03KA
only gives (2) ⇒ (1), and the converse needs decency (Stacks 03M6, `f` being quasi-compact as it
is of finite type) or quasi-separatedness (Stacks 0A3X). So decency is assumed exactly for the
full equivalence, which is `universallyClosed_tfae_of_isLocallyNoetherian`, and the remaining
implications are stated without it, as in
`universallyClosed_implications_of_isLocallyNoetherian`. -/
@[stacks 0H1Y]
theorem universallyClosed_implications_and_tfae_of_isLocallyNoetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X_alg : IsAlgebraicSpace B S hS X) (Y_alg : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (ft : IsFiniteType B S hS f)
    (noeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    ((ValuativeCriterion.Existence f →
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift) ∧
      ((∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift) →
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift) ∧
      ((∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift) →
        UniversallyClosed B S hS f) ∧
      (UniversallyClosed B S hS f ↔
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f))) ∧
    (IsDecent B S hS f →
      List.TFAE
        [UniversallyClosed B S hS f,
          ValuativeCriterion.Existence f,
          ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
            IsSurjective B S hS g ∧ IsEtale B S hS g ∧
              ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
                IsAffineSpaceOver B S hS V W n a ∧
                  IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f),
          ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
            ∃ e : q.DominatingExtension,
              IsDiscreteValuationRing e.square.R ∧
                (letI := e.fieldMap.toAlgebra
                 Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
                Nonempty e.square.Lift,
          ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
            ∃ e : q.DominatingExtension, Nonempty e.square.Lift]) :=
  ⟨universallyClosed_implications_of_isLocallyNoetherian B S hS X_alg Y_alg f ft noeth,
    fun decent ↦ universallyClosed_tfae_of_isLocallyNoetherian B S hS X_alg Y_alg f decent ft noeth⟩

end AlgebraicGeometry.Space

end
