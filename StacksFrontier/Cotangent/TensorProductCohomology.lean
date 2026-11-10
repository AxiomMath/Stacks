module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Cotangent.TensorProduct

/-!
# Cohomology of the object `E` of the tensor-product nine diagram

Let `R` be a ring and let `A` and `B` be `R`-algebras. Tag 09D9 produces an object `E` of
`D(A ⊗_R B)` in the upper right corner of the diagram

```
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}      ⟶ E
            ‖                     ↑                ↑
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}      ⟶ L_{A ⊗_R B/A}
                                  ↑                ↑
                      L_{B/R} ⊗^L_B (A ⊗_R B) ═ L_{B/R} ⊗^L_B (A ⊗_R B)
```

This file records what the cohomology of such an `E` is forced to be by the nine diagram alone,
namely that it vanishes in degrees `≥ 1`.

## Main results

* `CommAlgCat.isZero_homology_cotangentComplexDerived`: the cotangent complex, read in the
  derived category, has no cohomology in positive degrees.
* `CommAlgCat.isZero_homology_cotangentComplexDerivedBaseChange_of_nine_diagram`: in the
  situation of Tag 09D9, `L_{B/R} ⊗^L_B (A ⊗_R B)` has no cohomology in degrees `≥ 2`. This is
  read off the middle column of the diagram; no property of the derived base change itself is
  used.
* `CommAlgCat.isZero_homology_of_tensorProduct_nine_diagram`: `H^i(E) = 0` for `i ≥ 1`.

## Relation to Tag 09DB, and what is missing

Tag 09DB asserts more, namely

```
H^i(E) = 0                 if i ≥ -1
H^i(E) = Tor_1^R(A, B)     if i = -2
```

Neither of those two assertions is proved here, and no `@[stacks 09DB]` attribute is placed. The
reason is structural rather than a matter of effort, and it is worth recording.

The right column of the diagram exhibits `E` as a cone on a morphism
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`, and the long exact sequence then gives

`H^0(E) = coker H^0(that morphism)`,

so that `H^0(E) = 0` is exactly the surjectivity of that map on `H^0`. The content of Tag 09DB is
therefore a statement about *which* morphism the middle column is: it is the comparison map of
the base-change square along `R → A`, and the source's proof identifies it, through Lemma 09CG
and Remark 09D7, with the base change of Lichtenbaum–Schlessinger complexes, where the degree
`-1` and degree `0` maps are isomorphisms and the degree `-2` map has cokernel `Tor_1^R(A, B)`.

Tag 09D9, as this library states it, takes the two fundamental triangles as parameters and
leaves their morphisms arbitrary: its host file `StacksFrontier/Cotangent/TensorProduct.lean` sits
upstream of the proof of Proposition 08QX and so cannot name the display's own morphisms — see
the implementation note there. A cone on an arbitrary morphism between those objects does not
have the cohomology of Tag 09DB: the
abstract data of two distinguished triangles on the given objects does not determine the images
of `H^0` of the two left-hand maps inside `H^0(L_{A ⊗_R B/R})`, and `H^0(E) = 0` says precisely
that those two images together span. What survives the loss of the identification of the
morphisms is the vanishing in degrees `≥ 1` proved below, which uses only that the cotangent
complex has no cohomology in positive degrees.

Landing Tag 09DB therefore needs two inputs beyond this file: the nine diagram restated on the
display's own morphisms `CommAlgCat.fundamentalMor₁` and `CommAlgCat.fundamentalMor₂`, which
Proposition 08QX (`CommAlgCat.productFundamentalTriangle_distinguished`) puts in the two
triangles, and the base-change computation of Lichtenbaum–Schlessinger complexes (Remark 09D7 on
top of
`StacksFrontier/Cotangent/LichtenbaumSchlessingerComparison.lean`), whose degree `-2` cokernel is
the `Tor_1^R(A, B)` of the source.

## References

* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped TensorProduct

universe u v w w₁ w₂

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- The cotangent complex is concentrated in nonpositive cohomological degrees. -/
theorem isStrictlyLE_cotangentComplex (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    (cotangentComplex A B).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro m hm
  exact cotangentComplex_isZero_pos A B m hm

/-- The cotangent complex `L_{B/A}`, read as an object of `D(B)`, has no cohomology in positive
degrees. -/
theorem isZero_homology_cotangentComplexDerived (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) [HasDerivedCategory.{w} (ModuleCat.{max u v} B)] (i : ℤ)
    (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj
      (cotangentComplexDerived A B)) := by
  have := isStrictlyLE_cotangentComplex.{u, v} A B
  exact DerivedCategory.isZero_of_isLE _ 0 i hi

variable (R : Type u) [CommRing R] (A B : Type (max u v)) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

section

variable {R A B}
  {v : cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
    cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
  {q : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
    cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B))}
  {d₂ : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}

/-- In the situation of Tag 09D9, the derived base change `L_{B/R} ⊗^L_B (A ⊗_R B)` has no
cohomology in degrees `≥ 2`.

This is read off the middle column of the nine diagram: in the long exact sequence of that
triangle the two neighbours of `H^j(L_{B/R} ⊗^L_B (A ⊗_R B))` are `H^{j-1}(L_{A ⊗_R B/B})` and
`H^j(L_{A ⊗_R B/R})`, both of which vanish for `j ≥ 2` because a cotangent complex has no
cohomology in positive degrees. No property of the derived base change itself is used. -/
theorem isZero_homology_cotangentComplexDerivedBaseChange_of_nine_diagram
    (h₂ : Triangle.mk v q d₂ ∈ distTriang _) (j : ℤ) (hj : 2 ≤ j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (A ⊗[R] B)) j).obj
      (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))) := by
  have hleft : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (A ⊗[R] B)) (j - 1)).obj
      (cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)))) :=
    isZero_homology_cotangentComplexDerived.{max u v, max u v} B
      (CommAlgCat.of B (A ⊗[R] B)) (j - 1) (by omega)
  have hright : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (A ⊗[R] B)) j).obj
      (cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)))) :=
    isZero_homology_cotangentComplexDerived.{u, v} R
      (CommAlgCat.of R (A ⊗[R] B)) j (by omega)
  exact (DerivedCategory.HomologySequence.exact₁ _ h₂ (j - 1) j (by omega)).isZero_of_both_isZero
    hleft hright

end

section

variable {R A B}
  {p : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
    cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B))}
  {v : cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
    cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
  {q : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
    cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B))}
  {d₂ : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
  {E : DerivedCategory (ModuleCat.{max u v} (A ⊗[R] B))}
  {b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E}
  {e₂ : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}

/-- The cohomology of the object `E` of the nine diagram of Tag 09D9 vanishes in degrees `≥ 1`.

Only the middle column `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/B}` and the right
column `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A} ⟶ E` of the diagram are used, together with the
vanishing of the cohomology of a cotangent complex in positive degrees.

This is weaker than Tag 09DB, which asserts the vanishing in all degrees `≥ -1`; see the module
documentation for why the extra two degrees are not available from the nine diagram alone. -/
@[stacks 09DB "the vanishing in degrees i ≥ 1 only, which is the exact ceiling of what the \
nine diagram of Tag 09D9 determines in this library. The source asserts it for i ≥ -1 and \
identifies H^{-2}(E) with Tor_1^R(A, B); neither is a consequence of the 09D9 conclusion as \
formalized here, because exists_tensorProduct_nine_diagram leaves the morphisms of the two \
fundamental triangles arbitrary -- its host file sits upstream of the proof of Tag 08QX and so \
cannot name the display's own map L_{A ⊗ B/R} ⟶ L_{A ⊗ B/A} -- and two distinguished triangles \
on the given objects do not pin those maps down to anything that fixes their homology. \
At i = 0 the long exact sequence leaves coker H^0(v ≫ p), which the abstract \
data does not force to vanish"]
theorem isZero_homology_of_tensorProduct_nine_diagram
    (h₂ : Triangle.mk v q d₂ ∈ distTriang _)
    (hE₂ : Triangle.mk (v ≫ p) b e₂ ∈ distTriang _) (i : ℤ) (hi : 1 ≤ i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (A ⊗[R] B)) i).obj E) := by
  have hleft : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (A ⊗[R] B)) i).obj
      (cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)))) :=
    isZero_homology_cotangentComplexDerived.{max u v, max u v} A
      (CommAlgCat.of A (A ⊗[R] B)) i (by omega)
  have hright :=
    isZero_homology_cotangentComplexDerivedBaseChange_of_nine_diagram (A := A) h₂ (i + 1) (by omega)
  exact (DerivedCategory.HomologySequence.exact₃ _ hE₂ i (i + 1) (by omega)).isZero_of_both_isZero
    hleft hright

end

end CommAlgCat

end
