module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonFullyFaithfulStack
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# `Complexes_{X/B}` at a pushout along a thickening (Stacks 0DLK, reduced)

Stacks 0DLK asserts, in Situation 0DLE, that for a pushout `Y' = Y ⨿_Z Z'` of schemes over `S`
along a finite order thickening `Z ⟶ Z'` and an affine morphism `Z ⟶ Y`, the functor on fibre
categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}`
is an equivalence. Its proof has two halves:

* **full faithfulness**: the isomorphism sheaves of `Complexes_{X/B}` are algebraic spaces
  (Stacks 0DLG), and an algebraic space takes such a pushout to a fibre product of sets
  (Stacks 07SY, or 07WN);
* **essential surjectivity**: a triple `(E_Y, E_{Z'}, α)` is glued by Stacks 0DL7 along the
  pushout `X_{Y'} = X_Y ⨿_{X_Z} X_{Z'}` of Stacks 07W3, and the glued object is `Y'`-perfect by
  Stacks 0DL4.

This file proves the first half outright from Stacks 0DLG, and deduces from the equivalence at
every such square the two forms in which Artin's criterion consumes Stacks 0DLK: condition (RS*)
of Stacks 07Y8, and hence condition (RS) of Stacks 07WP, which is the hypothesis `h0DLK` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.

Nothing here is registered: Stacks 0DLG is not yet proved here, and the essential
surjectivity half is a hypothesis.

## Main results

* `Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_finiteOrder`:
  condition (RS*) holds as soon as the comparison functor is an equivalence at every pushout
  along a finite order thickening and an affine morphism — the squares of Stacks 0DLK.
* `AlgebraicGeometry.Space.ComplexesSituation.fullyFaithful_complexesFiberSquareComparison`:
  the full faithfulness half of Stacks 0DLK, from Stacks 0DLG.
* `Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_essSurj`:
  Stacks 0DLK, from Stacks 0DLG and the essential surjectivity half.
* `AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor_of_essSurj` and
  `AlgebraicGeometry.Space.ComplexesSituation.satisfiesRS_complexesFunctor_of_essSurj`: the two
  consequences of Stacks 0DLK used by Artin's criterion, from the same two inputs.

## Implementation notes

The fibre categories and the restriction functors are those of
`CategoryTheory.Functor.chosenPullbacks` for the projection
`AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor`, and the functor of the source is
`Deformation.Artin.fiberSquareComparison`, exactly as in conditions (RS) and (RS*). The
fibred-in-groupoids witness is a hypothesis `hfib`, as in
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`; it is Stacks
0DLF, and `CategoryTheory.Functor.IsFibered` being a `Prop`, the results do not depend on it.

## References

* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w

namespace Deformation.Artin

/-- **Condition (RS*) from the equivalence at the squares of Stacks 0DLK.** Let `p` be a category
fibred in groupoids over the big fppf site of `S`. Suppose that for every commutative square
`i ≫ a = f ≫ b` of the site whose image in schemes is a pushout along the *finite order*
thickening `i` and the affine morphism `f`, the comparison
`Deformation.Artin.fiberSquareComparison` is an equivalence. Then `p` satisfies condition (RS*)
of Stacks 07Y8.

The squares (RS*) quantifies over have affine corners and a first order thickening, which is of
finite order, and a morphism of affine schemes is affine; this is
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine`. -/
theorem satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_finiteOrder
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒜 : Type v} [Category.{w} 𝒜] (p : 𝒜 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hcomp :
      letI : p.IsFibered := hp.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
        (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
        Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (fiberSquareComparison p (Functor.chosenPullbacks p) f i b a w.symm).IsEquivalence) :
    SatisfiesRSStar B S hS p hp :=
  satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine B S hS p hp
    fun i f a b w hX _hX' hY _hY' hfirst hpush =>
      have := hX
      have := hY
      hcomp i f a b w ⟨hfirst.1, 1, hfirst.2⟩ inferInstance hpush

end Deformation.Artin

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- **Stacks 0DLK, the full faithfulness half.** In Situation 0DLE, let `i ≫ a = f ≫ b` be a
commutative square of the site whose image in schemes is a pushout `Y' = Y ⨿_Z Z'` along the
thickening `i : Z ⟶ Z'` and the affine morphism `f : Z ⟶ Y`. Granted Stacks 0DLG (`h0DLG`: the
diagonal of `Complexes_{X/B}` is representable by algebraic spaces), the functor
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is fully
faithful.

This is the source's argument: `Isom(ξ₁, ξ₂)` is an algebraic space over `Y'`, and an algebraic
space takes the pushout to a fibre product of sets (Stacks 07SY); it is
`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal`. Only a
thickening is needed here, not one of finite order. -/
def fullyFaithful_complexesFiberSquareComparison (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (complexesFunctor D).IsFibered := hfib.isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).FullyFaithful :=
  letI : (complexesFunctor D).IsFibered := hfib.isFibered
  Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS
    (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib) h0DLG i f a b w hi hpush

/-- **Stacks 0DLK, from Stacks 0DLG and the essential surjectivity half.** In Situation 0DLE, let
`i ≫ a = f ≫ b` be a commutative square of the site whose image in schemes is a pushout
`Y' = Y ⨿_Z Z'` along the finite order thickening `i : Z ⟶ Z'` and the affine morphism
`f : Z ⟶ Y`. Then the functor
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence, granted

* `h0DLG`: Stacks 0DLG, the diagonal of `Complexes_{X/B}` is representable by algebraic spaces,
  which gives full faithfulness
  (`AlgebraicGeometry.Space.ComplexesSituation.fullyFaithful_complexesFiberSquareComparison`);
* `hES`: the functor is essentially surjective at the square, the second half of the source's
  proof (Stacks 07W3, 0DL7 and 0DL4). -/
theorem isEquivalence_complexesFiberSquareComparison_of_essSurj (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (hES : letI : (complexesFunctor D).IsFibered := hfib.isFibered
      (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
        (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).EssSurj) :
    letI : (complexesFunctor D).IsFibered := hfib.isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).IsEquivalence :=
  let : (complexesFunctor D).IsFibered := hfib.isFibered
  have hFF := fullyFaithful_complexesFiberSquareComparison D hfib h0DLG i f a b w
    hi.isThickening hpush
  have := hFF.full
  have := hFF.faithful
  { }

/-- **Condition (RS*) for `Complexes_{X/B}`, from Stacks 0DLG and the essential surjectivity
half of Stacks 0DLK.** In Situation 0DLE, granted Stacks 0DLG (`h0DLG`) and essential
surjectivity of the comparison functor at every pushout along a finite order thickening and an
affine morphism (`hES`), the category `Complexes_{X/B}` satisfies condition (RS*) of Stacks
07Y8. The equivalence at each such square is
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_essSurj`, and (RS*) is
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_finiteOrder`. -/
theorem satisfiesRSStar_complexesFunctor_of_essSurj (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    (hES : letI : (complexesFunctor D).IsFibered := hfib.isFibered
      ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
        (w : i ≫ a = f ≫ b),
        Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
            (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).EssSurj) :
    Deformation.Artin.SatisfiesRSStar B S hS (complexesFunctor D) hfib :=
  Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_finiteOrder
    B S hS (complexesFunctor D) hfib fun i f a b w hi hf hpush =>
      have := hf
      isEquivalence_complexesFiberSquareComparison_of_essSurj D hfib h0DLG i f a b w hi hpush
        (hES i f a b w hi hf hpush)

/-- **Condition (RS) for `Complexes_{X/B}`, from Stacks 0DLG and the essential surjectivity half
of Stacks 0DLK**: the hypothesis `h0DLK` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`, in exactly that
shape. It is condition (RS*)
(`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor_of_essSurj`)
followed by the implication (RS*) ⟹ (RS) of Stacks 0CXN, observation (4)
(`Deformation.Artin.satisfiesRS_of_satisfiesRSStar`). -/
theorem satisfiesRS_complexesFunctor_of_essSurj (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    (hES : letI : (complexesFunctor D).IsFibered := hfib.isFibered
      ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
        (w : i ≫ a = f ≫ b),
        Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
            (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).EssSurj) :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D) hfib :=
  Deformation.Artin.satisfiesRS_of_satisfiesRSStar B S hS (complexesFunctor D) hfib
    (satisfiesRSStar_complexesFunctor_of_essSurj D hfib h0DLG hES)

end AlgebraicGeometry.Space.ComplexesSituation

end
