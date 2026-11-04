module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.NaiveComparison
public import StacksFrontier.Cotangent.NaiveComparisonExplicitArrow

/-!
# The explicit comparison with the naive cotangent complex, as a map of complexes

Let `P•` be the standard resolution of a commutative `A`-algebra `B`, let `P₀ = A[B]` be its
degree-zero term and let `I = ker(P₀ → B)`. Tag 08UP displays the diagram

```
L_{B/A}    ⋯ ⟶ Ω[P₂⁄A] ⊗[P₂] B ⟶ Ω[P₁⁄A] ⊗[P₁] B ⟶ Ω[P₀⁄A] ⊗[P₀] B
                      |                 |                 |
NL_{B/A}   ⋯ ⟶       0        ⟶      I/I²       ⟶ Ω[P₀⁄A] ⊗[P₀] B
```

whose only nonzero downward arrow above degree zero is `d f ⊗ b ↦ (d₀ f - d₁ f) b`, and concludes
"Hence a map of complexes". `StacksFrontier/Cotangent/NaiveComparisonExplicitArrow.lean` builds that
arrow and proves the two commuting squares; this file assembles them into the map of complexes
itself.

## Main definitions

* `CommAlgCat.faceAsTermMap`: a face `Pₙ₊₁ → Pₙ` read as a map of the base-changed differentials,
  i.e. `Algebra.Extension.CotangentSpace.map` transported onto `CommAlgCat.cotangentTerm`.
* `CommAlgCat.comparisonDegreeZero` and `CommAlgCat.comparisonDegreeNegOne`: the two nonzero
  components of the comparison, in cohomological degrees `0` and `-1`.
* `CommAlgCat.comparisonComponent`: the component in an arbitrary degree, zero outside `0`
  and `-1`.
* `CommAlgCat.explicitNaiveComparison`: **the map of complexes** `L_{B/A} ⟶ NL_{B/A}`, with
  `NL_{B/A}` the two-term complex `Algebra.Extension.naiveComplex` of the presentation
  `P₀ → B`.

## Main results

* `CommAlgCat.objD_zero_eq` and `CommAlgCat.objD_one_eq`: the differentials of `L_{B/A}` out of
  simplicial degrees `1` and `2` are `d₀ - d₁` and `d₀ - d₁ + d₂`.
* `CommAlgCat.core_lower` and `CommAlgCat.core_upper`: the two squares of the diagram, restated
  with those differentials; they are the two conditions `explicitNaiveComparison` needs.
* `CommAlgCat.isIso_comparisonDegreeZero`: in degree zero the comparison is an isomorphism —
  the source's "the same object on both rows, joined by the identity".
* `CommAlgCat.comparisonComponent_eq_zero`: the components outside degrees `0` and `-1` vanish,
  which is the bottom row's `0` above degree one.

## Implementation notes

The bottom row is `Algebra.Extension.naiveComplex` of `CommAlgCat.standardResolutionExtension A B
0`, the presentation `P₀ → B`. That is the source's own bottom row: it writes `I/I²` and
`Ω[P₀⁄A] ⊗[P₀] B` for `I = Ker(A[B] → B)` after recalling `P₀ = A[B]`, and
`CommAlgCat.standardResolution_obj_mvPolynomial` is that identification in this library.

Both squares are proved by category algebra from the two tagged lemmas of
`StacksFrontier/Cotangent/NaiveComparisonExplicitArrow.lean`, not elementwise: the cotangent space
of `standardResolutionExtension A B n` is `CommAlgCat.cotangentTerm A B (op ⦋n⦌)` by
`CommAlgCat.cotangentTerm_eq_cotangentSpace`, which holds by `rfl`, so the transport is an
`eqToHom` and `CommAlgCat.faceAsTermMap_comp_eqToHom` moves it past a face.

### The verification Tag 08UP omits

Tag 08UP ends "We omit the verification that this is the same as the map of Lemma 92.11.3", that
is, that `explicitNaiveComparison` induces an inverse of the canonical comparison map
`c : NL_{B/A} → τ_{≥ -1} L_{B/A}` of Tag 08RB.  That clause is not carried in this file; it is
`Stacks.Cotangent.explicitNaiveComparison_comp_comparison` and
`Stacks.Cotangent.explicitNaiveComparison_comp_comparisonAtNaive` of
`StacksFrontier/Cotangent/NaiveComparisonAgreement.lean`, in the form of the single equation

`Q(explicitNaiveComparison) ≫ c = (truncGEπ (-1)).app (Q (cotangentComplex A B))`

in `D(B)`.  The map `c` is the map of Tag 08R9 at the object `P₀ → B`,
`Stacks.Cotangent.comparison` of `StacksFrontier/Cotangent/NaiveComparisonMap.lean`, whose value at
the library's second spelling of that object is `Stacks.Cotangent.comparisonAtNaive`; and
`Stacks.Cotangent.comparison_eq_comparisonOfHom` of
`StacksFrontier/Cotangent/NaiveComparisonIndependence.lean` lets it be computed at the identity
morphism `P₀ ⟶ P₀` rather than at the morphism a `Classical.choice` of presentation produces,
which is what that proof does.

What the equation adds to the library is the *identification of the two maps*.  That `c` is an
isomorphism on cohomology in degree `-1` is separately
`Stacks.Cotangent.isIso_homologyMap_evalCone_conormalExtension` of
`StacksFrontier/Cotangent/NaiveComparisonQuasiIso.lean`; Tag 08RB's own assertion that `c` is a
quasi-isomorphism is still not proved, and in degree `0` the two maps are inverse already, by
`CommAlgCat.isIso_comparisonDegreeZero` and `CommAlgCat.cotangentComplexHomologyZeroIsoNaive`.

**The route the agreement file takes.**  Writing `f` for `CommAlgCat.explicitNaiveComparison`, `e`
for `Stacks.Cotangent.evalCone` at `A[B] → B` along the identity of `A[B]` and `ι` for
`Stacks.Cotangent.cotangentConeInr`, the naturality of `truncGEπ` and the definition of
`Stacks.Cotangent.truncGEConeIso` as `asIso` of `τ_{≥ -1}` of `Q ι` reduce the equation to the
vanishing, after `τ_{≥ -1}`, of the difference `g := f ≫ e - ι`, a map `L_{B/A} ⟶ cone(d)` in
`D(B)`.  That difference vanishes in cohomological degree `0` — both maps are the identity of
`Ω[P₀⁄A] ⊗[P₀] B` there — so it factors through the brutal quotient
`CochainComplex.brutalTrunc (cotangentComplex A B) 0`, which lies in `D^{≤ -1}(B)`; the target
`τ_{≥ -1} cone(d)` lies in `D^{≥ -1}(B)`; and a map of `D(B)` from an object of `D^{≤ n}` to an
object of `D^{≥ n}` killed by `Hⁿ` is zero, which is
`DerivedCategory.eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero` of
`StacksFrontier/Algebra/Homology/DerivedCategory/HomEqualDegree.lean`.

What is left is one computation with elements.  Every `ω` of `Ω[P₁⁄A] ⊗[P₁] B` is
`d₁ y + (δ₀ - δ₁ + δ₂) ξ` (`Stacks.Cotangent.exists_hub_decomposition`, which rests on the
naturality of `Algebra.Extension.toKaehler` in the extension and on
`Algebra.Extension.exact_cotangentComplex_toKaehler`), and Mathlib's cone differential
`(y, ξ) ↦ (-(δ₀ - δ₁) y, d₁ y + (δ₀ - δ₁ + δ₂) ξ)` carries `(-y, -ξ)` to the value of `g` at `ω`,
because the arrow `d f ⊗ b ↦ (d₀ f - d₁ f) b` agrees with `δ₀ - δ₁` on the image of `d₁`
(`Algebra.Extension.Cotangent.map_sub_map`) and annihilates `δ₀ - δ₁ + δ₂`
(`CommAlgCat.core_upper`).

**There is no chain homotopy, so `H^{-1}` cannot be bypassed.** `CommAlgCat.standardResolutionVar`
is a function, not a ring map — it is the chosen section `σ` of an extension — so it is not a
morphism of extensions, and the standard resolution has an extra degeneracy only when `B` is a
polynomial algebra (`CommAlgCat.nonempty_standardResolutionExtraDegeneracyLast`).  The
decomposition of `ω` above therefore needs a choice and is not linear in `ω`: the difference
`f ≫ e - ι` is not null-homotopic, and the argument has to pass through `H^{-1}`.

**Where the two spellings of `NL_{B/A}` meet.** `CommAlgCat.explicitNaiveComparison` lands in
`Algebra.Extension.naiveComplex (CommAlgCat.standardResolutionExtension A B 0)`, while
`Stacks.Cotangent.comparisonAtNaive` starts at
`Algebra.Extension.naiveComplex (Stacks.Cotangent.conormalExtension A B (op ⦋0⦌))`.  Those two
extensions have the same ring and the same augmentation, but different sections: the iterated
variables of `CommAlgCat.standardResolutionSection` against a `Classical.choice` of a preimage.
The section is *not* invisible to Mathlib's `Algebra.Extension`:
`Algebra.Extension.Cotangent.module` is defined through `σ`, so the two conormal modules are
different objects of `ModuleCat ↥B`, carrying the same underlying group with two scalar actions
that agree only up to `σ(r) - σ'(r) ∈ ker`.  The two complexes are therefore not equal; the
identity of `A[B]`, read as a morphism of extensions both ways
(`Stacks.Cotangent.toConormalExtension` and `Stacks.Cotangent.ofConormalExtension`), induces the
isomorphism `Stacks.Cotangent.naiveSpellingIso` between them, and that is the identification the
second form of the equation inserts.  All the identifications involved are made in an arbitrary
simplicial degree, as `Stacks.Cotangent.cotangentTermIsoCotangentSpace` does for the other pair of
spellings; at the single object `⦋0⦌` the unifier would be asked to evaluate the standard
resolution at a simplex.

## References

* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial TensorProduct AlgebraicTopology

universe u v

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The cotangent space of the presentation `Pₙ → B` is the `n`-th term of the cotangent
simplicial module: both are `B ⊗[Pₙ] Ω[Pₙ⁄A]`. -/
theorem cotangentTerm_eq_cotangentSpace (n : ℕ) :
    cotangentTerm A B (op ⦋n⦌) =
      ModuleCat.of ↥B (standardResolutionExtension A B n).CotangentSpace := rfl

/-- The `i`th face `Pₙ₊₁ → Pₙ`, read as a map `Ω[Pₙ₊₁⁄A] ⊗ B → Ω[Pₙ⁄A] ⊗ B` of the terms of the
cotangent simplicial module. -/
noncomputable def faceAsTermMap (n : ℕ) (i : Fin (n + 2)) :
    cotangentTerm A B (op ⦋n + 1⦌) ⟶ cotangentTerm A B (op ⦋n⦌) :=
  eqToHom (cotangentTerm_eq_cotangentSpace A B (n + 1)) ≫
    ModuleCat.ofHom
      (Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B n i)) ≫
    eqToHom (cotangentTerm_eq_cotangentSpace A B n).symm

/-- `faceAsTermMap` is the simplicial map of the cotangent simplicial module at that face. -/
theorem faceAsTermMap_eq (n : ℕ) (i : Fin (n + 2)) :
    faceAsTermMap A B n i = cotangentMap A B (SimplexCategory.δ i).op :=
  cotangentTerm_hom_ext A B (op ⦋n + 1⦌) _ _ fun p => by
    rw [cotangentMap_D]
    show Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B n i)
        ((1 : ↥B) ⊗ₜ KaehlerDifferential.D A _ p) = _
    have h := Algebra.Extension.CotangentSpace.map_tmul
      (standardResolutionExtensionFace A B n i) (1 : ↥B) p
    rw [map_one] at h
    exact h

/-- The differential of `L_{B/A}` out of simplicial degree `n + 1` is the alternating sum of the
faces. -/
private theorem objD_eq_sum (n : ℕ) :
    AlternatingFaceMapComplex.objD (cotangentSimplicialModule A B).object n =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceAsTermMap A B n i := by
  simp_rw [faceAsTermMap_eq]
  rfl

/-- The differential of `L_{B/A}` out of simplicial degree one is `d₀ - d₁`. -/
theorem objD_zero_eq :
    AlternatingFaceMapComplex.objD (cotangentSimplicialModule A B).object 0 =
      faceAsTermMap A B 0 0 - faceAsTermMap A B 0 1 := by
  rw [objD_eq_sum, Fin.sum_univ_two]
  simp [sub_eq_add_neg]
  abel

/-- The differential of `L_{B/A}` out of simplicial degree two is `d₀ - d₁ + d₂`. -/
theorem objD_one_eq :
    AlternatingFaceMapComplex.objD (cotangentSimplicialModule A B).object 1 =
      faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2 := by
  rw [objD_eq_sum, Fin.sum_univ_three]
  simp [sub_eq_add_neg]
  abel

/-! ### The components -/

/-- The degree-zero component of the comparison: the two rows of the diagram have the same term
`Ω[P₀⁄A] ⊗[P₀] B` there, and this is the identity between them. -/
noncomputable def comparisonDegreeZero :
    (cotangentComplex A B).X 0 ⟶
      (Algebra.Extension.naiveComplex (standardResolutionExtension A B 0)).X 0 :=
  (cotangentComplex_degreeIso A B 0).hom ≫
    eqToHom (cotangentTerm_eq_cotangentSpace A B 0) ≫
    (Algebra.Extension.naiveComplexXZeroIso (standardResolutionExtension A B 0)).inv

/-- The degree `-1` component of the comparison: the explicit downward arrow
`d f ⊗ b ↦ (d₀ f - d₁ f) b` of `CommAlgCat.naiveCotangentComparison`. -/
noncomputable def comparisonDegreeNegOne :
    (cotangentComplex A B).X (-1) ⟶
      (Algebra.Extension.naiveComplex (standardResolutionExtension A B 0)).X (-1) :=
  (cotangentComplex_degreeIso A B 1).hom ≫
    eqToHom (cotangentTerm_eq_cotangentSpace A B 1) ≫
    ModuleCat.ofHom (naiveCotangentComparison A B) ≫
    (Algebra.Extension.naiveComplexXNegOneIso (standardResolutionExtension A B 0)).inv

/-- Moving the transport of `CommAlgCat.cotangentTerm_eq_cotangentSpace` past a face. -/
theorem faceAsTermMap_comp_eqToHom (n : ℕ) (i : Fin (n + 2)) :
    faceAsTermMap A B n i ≫ eqToHom (cotangentTerm_eq_cotangentSpace A B n) =
      eqToHom (cotangentTerm_eq_cotangentSpace A B (n + 1)) ≫
        ModuleCat.ofHom
          (Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B n i)) := by
  rw [faceAsTermMap, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

private theorem ofHom_sub {M N : Type (max u v)} [AddCommGroup M] [Module ↥B M]
    [AddCommGroup N] [Module ↥B N] (f g : M →ₗ[↥B] N) :
    ModuleCat.ofHom (f - g) = ModuleCat.ofHom f - ModuleCat.ofHom g := rfl

/-- **The lower square of the diagram of Tag 08UP**, in the form the map of complexes needs:
the explicit arrow followed by the differential `I/I² → Ω[P₀⁄A] ⊗[P₀] B` of the naive cotangent
complex is `d₀ - d₁`, the differential of `L_{B/A}` out of simplicial degree one. -/
@[reassoc]
theorem core_lower :
    eqToHom (cotangentTerm_eq_cotangentSpace A B 1) ≫
        ModuleCat.ofHom (naiveCotangentComparison A B) ≫
        ModuleCat.ofHom (standardResolutionExtension A B 0).cotangentComplex =
      (faceAsTermMap A B 0 0 - faceAsTermMap A B 0 1) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B 0) := by
  rw [Preadditive.sub_comp, faceAsTermMap_comp_eqToHom, faceAsTermMap_comp_eqToHom,
    ← Preadditive.comp_sub, ← ModuleCat.ofHom_comp, ← ofHom_sub,
    naiveCotangentComparison_cotangentComplex]

/-- **The upper square of the diagram of Tag 08UP**, in the form the map of complexes needs:
the explicit arrow annihilates `d₀ - d₁ + d₂`, the differential of `L_{B/A}` out of simplicial
degree two, because the bottom row is zero there. -/
@[reassoc]
theorem core_upper :
    (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B 1) ≫
        ModuleCat.ofHom (naiveCotangentComparison A B) = 0 := by
  rw [Preadditive.add_comp, Preadditive.sub_comp, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, faceAsTermMap_comp_eqToHom, faceAsTermMap_comp_eqToHom,
    faceAsTermMap_comp_eqToHom, Category.assoc, Category.assoc, Category.assoc,
    ← Preadditive.comp_sub, ← Preadditive.comp_add, ← ModuleCat.ofHom_comp,
    ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, ← ofHom_sub, ← ModuleCat.ofHom_add,
    ← LinearMap.comp_sub, ← LinearMap.comp_add, naiveCotangentComparison_faceSum,
    ModuleCat.ofHom_zero, Limits.comp_zero]

/-! ### The map of complexes -/

/-- The differential of `L_{B/A}` from cohomological degree `-1` to `0`, as `d₀ - d₁`. -/
theorem cotangentComplex_d_negOne_zero :
    (cotangentComplex A B).d (-1) 0 =
      (cotangentComplex_degreeIso A B 1).hom ≫
        (faceAsTermMap A B 0 0 - faceAsTermMap A B 0 1) ≫
        (cotangentComplex_degreeIso A B 0).inv := by
  refine (cotangentComplex_d A B 0).trans ?_
  rw [objD_zero_eq]
  rfl

/-- The differential of `L_{B/A}` from cohomological degree `-2` to `-1`, as `d₀ - d₁ + d₂`. -/
theorem cotangentComplex_d_negTwo_negOne :
    (cotangentComplex A B).d (-2) (-1) =
      (cotangentComplex_degreeIso A B 2).hom ≫
        (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ≫
        (cotangentComplex_degreeIso A B 1).inv := by
  refine (cotangentComplex_d A B 1).trans ?_
  rw [objD_one_eq]
  rfl

/-- The component of the comparison in cohomological degree `i`: the identity in degree zero,
the explicit arrow in degree `-1`, and zero in every other degree. -/
noncomputable def comparisonComponent (i : ℤ) :
    (cotangentComplex A B).X i ⟶
      (Algebra.Extension.naiveComplex (standardResolutionExtension A B 0)).X i :=
  if h : i = 0 then
    eqToHom (by rw [h]) ≫ comparisonDegreeZero A B ≫ eqToHom (by rw [h])
  else if h' : i = -1 then
    eqToHom (by rw [h']) ≫ comparisonDegreeNegOne A B ≫ eqToHom (by rw [h'])
  else 0

/-- In degree zero the component is `comparisonDegreeZero`. -/
theorem comparisonComponent_zero :
    comparisonComponent A B 0 = comparisonDegreeZero A B := by
  rw [comparisonComponent, dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- In degree `-1` the component is the explicit arrow. -/
theorem comparisonComponent_negOne :
    comparisonComponent A B (-1) = comparisonDegreeNegOne A B := by
  rw [comparisonComponent, dif_neg (by decide), dif_pos rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- **Stacks Project, Tag 08UP.** Outside cohomological degrees `0` and `-1` the comparison is
zero: the bottom row of the diagram vanishes there, so every downward arrow from
`Ω[Pₙ⁄A] ⊗[Pₙ] B` with `n ≥ 2` is zero. -/
@[stacks 08UP "the comparison vanishes outside degrees 0 and -1, the bottom row being zero
there"]
theorem comparisonComponent_eq_zero (i : ℤ) (h : i ≠ 0) (h' : i ≠ -1) :
    comparisonComponent A B i = 0 := by
  rw [comparisonComponent, dif_neg h, dif_neg h']

/-- **Stacks Project, Tag 08UP.** The map of complexes `L_{B/A} ⟶ NL_{B/A}` displayed by the
remark: the identity in degree zero, the explicit arrow `d f ⊗ b ↦ (d₀ f - d₁ f) b` in degree
`-1`, and zero above. This is the source's "Hence a map of complexes": the two commuting squares
are `CommAlgCat.core_lower` and `CommAlgCat.core_upper`, and in every other pair of adjacent
degrees the bottom row vanishes.

The agreement of this map with the comparison map `c` of Tag 08RB — the verification the source
omits — is not claimed by this definition; it is
`Stacks.Cotangent.explicitNaiveComparison_comp_comparison` of
`StacksFrontier/Cotangent/NaiveComparisonAgreement.lean`. -/
@[stacks 08UP "the map of complexes L_{B/A} → NL_{B/A} itself, assembled from the two squares
(the source's `Hence a map of complexes`): the identity in degree 0, the explicit arrow
d f ⊗ b ↦ (d₀ f - d₁ f) b in degree -1, and zero in every other degree"]
noncomputable def explicitNaiveComparison :
    cotangentComplex A B ⟶
      Algebra.Extension.naiveComplex (standardResolutionExtension A B 0) where
  f := comparisonComponent A B
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h1 : i = -1
    · have hj : j = 0 := by omega
      subst hj; subst h1
      rw [comparisonComponent_negOne, comparisonComponent_zero, comparisonDegreeNegOne,
        comparisonDegreeZero, Algebra.Extension.naiveComplex_d,
        cotangentComplex_d_negOne_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [core_lower_assoc]
    · by_cases h2 : i = -2
      · have hj : j = -1 := by omega
        subst hj; subst h2
        rw [comparisonComponent_eq_zero A B (-2) (by decide) (by decide),
          Limits.zero_comp, comparisonComponent_negOne, comparisonDegreeNegOne,
          cotangentComplex_d_negTwo_negOne]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [core_upper_assoc, Limits.zero_comp, Limits.comp_zero]
      · have hj : j ≠ 0 := by omega
        have hj' : j ≠ -1 := by omega
        rw [comparisonComponent_eq_zero A B j hj hj', Limits.comp_zero]
        exact (Algebra.Extension.isZero_naiveComplex_X
          (standardResolutionExtension A B 0) j hj' hj).eq_of_tgt _ 0

/-- The components of the map of complexes are `comparisonComponent`. -/
@[simp]
theorem explicitNaiveComparison_f (i : ℤ) :
    (explicitNaiveComparison A B).f i = comparisonComponent A B i := rfl

/-- **Stacks Project, Tag 08UP.** In degree zero the comparison is an isomorphism: the two rows
of the diagram have the same term `Ω[P₀⁄A] ⊗[P₀] B` there and the downward arrow is the identity
between the two presentations of it. -/
@[stacks 08UP "degree zero: the downward arrow is the identity, hence an isomorphism, the two
rows having the same term there"]
theorem isIso_comparisonDegreeZero : IsIso (comparisonDegreeZero A B) := by
  rw [comparisonDegreeZero]
  infer_instance

end CommAlgCat

end
