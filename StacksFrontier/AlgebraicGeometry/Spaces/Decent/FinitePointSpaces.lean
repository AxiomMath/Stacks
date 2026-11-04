module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZeroDimensionalFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointSpaceSober
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober

/-!
# Algebraic spaces over a field with finitely many points

Let `X` be a nonempty algebraic space locally of finite type over a field `k` and suppose that
above every point of `X` every étale chart of `X` by an affine scheme has a finite fibre —
condition `(α)` of Stacks 03JX, which is what a decent algebraic space gives. If `|X|` is a
finite set then all five conditions of Stacks 0ACA hold: `|X|` is discrete, `|X|` and `X` both
have dimension zero, and `X → Spec k` is locally quasi-finite. This file also assembles the
numbered conditions of **Stacks 0ACA** into the two equivalences the tag asserts: conditions
(2), (4) and (5) for an arbitrary such `X`, and conditions (2), (3), (4) and (5) for a decent
one. The implications among the last four are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ZeroDimensionalFibres.lean`.

## Main results

* `AlgebraicGeometry.Space.FiniteTypeOverField.locallyQuasiFiniteOverField_of_finitePoints`
  derives condition (5) from condition (1), and
  `zeroDimension_of_finitePoints`, `discretePoints_of_finitePoints` and
  `zeroTopologicalDimension_of_finitePoints` derive conditions (4), (2) and (3) from it.
* conditions (2), (4) and (5) are equivalent, with no decency hypothesis, by
  `FiniteTypeOverField.tfae_discretePoints_zeroDimension_locallyQuasiFinite` — this is the
  `dim = 0` reading of (4), hence for a nonempty space. The reading with no nonemptiness either is
  `AlgebraicGeometry.Space.tfae_discreteTopology_dimension_le_zero_isLocallyQuasiFinite`.
* `AlgebraicGeometry.Space.FiniteTypeOverField.tfae_of_isDecentSpace`: conditions (2), (3), (4)
  and (5) are equivalent for a decent space.
* `AlgebraicGeometry.Space.FiniteTypeOverField.discretePoints_of_finitePoints_of_isDecentSpace`
  and `discretePoints_of_zeroTopologicalDimension_of_isDecentSpace` take decency itself, the
  source's hypothesis, in place of condition `(α)` and of a `T₀` point space.

## Implementation notes

**The corrected statement of the tag.** What is true, and what the registrations of this tag
across the library state, is in three parts: conditions (2), (4) and (5) are equivalent with no
further hypothesis; condition (3) implies them once `|X|` is Kolmogorov, in particular when `X`
is decent; and condition (1) implies them when `X` is decent. Conditions (2) and (4) also imply
(3) unconditionally — it is only the arrow *out of* (3) that needs the separation hypothesis.

Condition (3) implies the others only under a separation hypothesis on `|X|`, so the source's
assertion that (2) to (5) are equivalent for every algebraic space locally of finite type over a
field is false as written: `𝔸¹_k/ℤ` in characteristic zero has indiscrete point space, hence
Krull dimension zero, while failing (2), (4) and (5). That counterexample is **formal, not
folklore**: it is
`Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints`
of `StacksFrontier/Examples/Spaces/ZeroDimensionalPointsNotDiscrete.lean`, which registers this
tag on the negation, so no unrestricted four-way equivalence can be added to this file. The
corrected arrow out of (3) is stated
for a decent space, where Stacks 03K3 supplies the `T₀` hypothesis of the sharp form
`AlgebraicGeometry.Space.FiniteTypeOverField.discretePoints_of_zeroTopologicalDimension`.
Condition (1) is strictly stronger than the others even for a decent space — an infinite
disjoint union of copies of `Spec k` satisfies (2) to (5) — so the source states it as an
implication and so does `discretePoints_of_finitePoints_of_isDecentSpace`.

Finiteness of `|X|` makes it compact, so `X` is quasi-compact (Stacks 03E4) and therefore has
a surjective étale chart `φ : h_U ⟶ X` with `U` affine (Stacks 03H6). Every fibre of `φ` on
points is finite by the hypothesis, and `|X|` is finite, so `|h_U|` is finite; the points of a
represented presheaf are the points of the representing scheme
(`AlgebraicGeometry.Space.schemePointsHomeomorph`), so `U` has finitely many points. A
morphism locally of finite type with finite fibres is locally quasi-finite, so the morphism of
charts `U → Spec k` is locally of finite type and locally quasi-finite; since that property of
schemes is étale local on the source and target (Stacks 04R3) and `φ` is surjective, the
structure morphism of `X` has it on *every* étale chart, which is condition (5).

The remaining three conditions follow from condition (5) by the equivalences of
Stacks 0ACA already available: `zeroDimension_iff_locallyQuasiFinite`,
`discretePoints_iff_zeroDimension` and `zeroTopologicalDimension_of_discretePoints`.

Decency is spelled here as `AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`,
condition `(α)` of Stacks 03JX, which is what the argument uses and which condition `(γ)` —
the source's definition of a decent algebraic space — gives; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/Conditions.lean` for the relation between the two
and `AlgebraicGeometry.Space.IsDecentSpace`.

## References

* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace FiniteTypeOverField

/-- **Stacks 0ACA, condition (1) implies the others.** A nonempty algebraic space locally of
finite type over a field whose étale charts by affine schemes have finite fibres above every
point — in particular a decent one — and whose point space is finite has locally quasi-finite
structure morphism. This is condition (5). -/
theorem locallyQuasiFiniteOverField_of_finitePoints (D : FiniteTypeOverField.{u})
    (hα : HasFiniteChartFibersAtEveryPoint D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hfinite : D.FinitePoints) : D.LocallyQuasiFiniteOverField := by
  classical
  have hpts : Finite (points D.B (Spec (.of D.k)) D.base_mem D.X.left) := hfinite
  have hqc : IsQuasiCompactSpace D.B (Spec (.of D.k)) D.base_mem D.X.left :=
    (isQuasiCompactSpace_iff_compactSpace_points D.B (Spec (.of D.k)) D.base_mem D.X.left
      D.isAlgebraicSpace).2 inferInstance
  obtain ⟨U, φ, hU, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover D.B (Spec (.of D.k))
      D.base_mem D.X.left D.isAlgebraicSpace).1 hqc
  have hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf φ := by
    simpa using hetale U (𝟙 (yoneda.obj U))
      (AlgebraicGeometry.Space.presheaf_etale_id D.B (Spec (.of D.k)) D.base_mem U)
  have hUpts : Finite (points D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) := by
    refine Finite.of_finite_univ (Set.Finite.of_finite_fibers
      (pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) φ) (Set.toFinite _) ?_)
    intro x _
    simpa using hα x U hU φ hφ
  have hUfin : Finite ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) :=
    Finite.of_equiv _ (schemePointsHomeomorph D.B (Spec (.of D.k)) D.base_mem U).toEquiv
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  let V : BigFppfOver D.B (Spec (.of D.k)) D.base_mem := Over.mk (𝟙 (D.B.obj D.base_mem))
  let h : U ⟶ V := baseChartMap D U φ
  have hLft : LocallyOfFiniteType (T.map h) :=
    D.locallyOfFiniteType U V φ (𝟙 _) h hφ (etale_id_base D) (baseChartMap_commutes D U φ)
  have hLqf : LocallyQuasiFinite (T.map h) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (T.map h) fun _ ↦ Set.toFinite _
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart D.B (Spec (.of D.k)) D.base_mem
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    D.isAlgebraicSpace
    (isAlgebraicSpace_yoneda D.B (Spec (.of D.k)) D.base_mem V) D.X.hom).2
    ⟨U, V, φ, 𝟙 _, h, hφ, etale_id_base D, hsurj, baseChartMap_commutes D U φ, hLft, hLqf⟩

/-- **Stacks 0ACA, condition (1) implies the others.** Condition (4): such an algebraic space
has dimension zero. -/
theorem zeroDimension_of_finitePoints (D : FiniteTypeOverField.{u})
    (hα : HasFiniteChartFibersAtEveryPoint D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hfinite : D.FinitePoints) : D.ZeroDimension :=
  (zeroDimension_iff_locallyQuasiFinite D).2
    (locallyQuasiFiniteOverField_of_finitePoints D hα hfinite)

/-- **Stacks 0ACA, condition (1) implies the others.** Condition (2): the point space of such
an algebraic space is discrete. -/
@[ega "I 6.4.4" "(c') => (b)"]
theorem discretePoints_of_finitePoints (D : FiniteTypeOverField.{u})
    (hα : HasFiniteChartFibersAtEveryPoint D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hfinite : D.FinitePoints) : D.DiscretePoints :=
  (discretePoints_iff_zeroDimension D).2 (zeroDimension_of_finitePoints D hα hfinite)

/-- **Stacks 0ACA, condition (1) implies the others.** Condition (3): the point space of such
an algebraic space has Krull dimension zero. -/
theorem zeroTopologicalDimension_of_finitePoints (D : FiniteTypeOverField.{u})
    (hα : HasFiniteChartFibersAtEveryPoint D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hfinite : D.FinitePoints) : D.ZeroTopologicalDimension :=
  zeroTopologicalDimension_of_discretePoints D (discretePoints_of_finitePoints D hα hfinite)

/-! ### The conditions of Stacks 0ACA under the source's own hypotheses -/

/-- **Stacks 0ACA, condition (1) implies the others for a decent space.** A decent algebraic
space locally of finite type over a field whose point space is finite has discrete point space;
the remaining conditions follow by `tfae_of_isDecentSpace`.

Decency gives condition `(α)` of Stacks 03JX, finiteness of the fibre of every affine étale
chart above every point, which is what the argument consumes. -/
@[stacks 0ACA "decent clause of the corrected statement: (1) implies the others"]
theorem discretePoints_of_finitePoints_of_isDecentSpace (D : FiniteTypeOverField.{u})
    (hdec : IsDecentSpace D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hfinite : D.FinitePoints) : D.DiscretePoints :=
  discretePoints_of_finitePoints D
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace D.B (Spec (.of D.k)) D.base_mem hdec)
    hfinite

/-- **Stacks 0ACA, condition (3) implies condition (2) for a decent space.** The point space of
a decent algebraic space is Kolmogorov, by Stacks 03K3, which is exactly the hypothesis that
`discretePoints_of_zeroTopologicalDimension` needs and that no algebraic space satisfies
automatically. -/
@[stacks 0ACA "corrected part (3) => (2): decency gives the Kolmogorov hypothesis, by 03K3"]
theorem discretePoints_of_zeroTopologicalDimension_of_isDecentSpace
    (D : FiniteTypeOverField.{u})
    (hdec : IsDecentSpace D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (hD : D.ZeroTopologicalDimension) : D.DiscretePoints :=
  discretePoints_of_zeroTopologicalDimension D
    (t0Space_points_of_isDecentSpace D.B (Spec (.of D.k)) D.base_mem D.isAlgebraicSpace hdec) hD

/-- **Stacks 0ACA, conditions (2), (4) and (5) are equivalent.** For a nonempty algebraic space
locally of finite type over a field, with no separation hypothesis and no decency: the point
space is discrete exactly when the space has dimension zero, exactly when the structure morphism
is locally quasi-finite.

Condition (3) is not among them: the arrow out of it needs `|X|` to be Kolmogorov, and is
`discretePoints_of_zeroTopologicalDimension`. Nonemptiness is carried by `FiniteTypeOverField`
and is what the `= 0` reading of conditions (3) and (4) needs — the dimensions of Tags 04N6 and
0055 are suprema in `WithBot ℕ∞`, so the empty space has dimension `⊥` while being discrete and
locally quasi-finite. Dropping nonemptiness as well means reading condition (4) as `dim(X) ≤ 0`,
which is
`AlgebraicGeometry.Space.tfae_discreteTopology_dimension_le_zero_isLocallyQuasiFinite`. -/
@[stacks 0ACA "(2) <=> (4) <=> (5), the dim = 0 form for a nonempty space; (3) not among them"]
theorem tfae_discretePoints_zeroDimension_locallyQuasiFinite (D : FiniteTypeOverField.{u}) :
    [D.DiscretePoints, D.ZeroDimension, D.LocallyQuasiFiniteOverField].TFAE := by
  tfae_have 1 ↔ 2 := discretePoints_iff_zeroDimension D
  tfae_have 2 ↔ 3 := zeroDimension_iff_locallyQuasiFinite D
  tfae_finish

/-- **Stacks 0ACA, conditions (2), (3), (4) and (5) are equivalent for a decent space.** For a
nonempty decent algebraic space locally of finite type over a field, the point space is
discrete exactly when it has Krull dimension zero, exactly when the space has dimension zero,
exactly when the structure morphism is locally quasi-finite.

Only the arrow out of condition (3) uses decency, and it uses it only through Stacks 03K3: the
other three conditions are equivalent for every algebraic space locally of finite type over a
field, by `tfae_discretePoints_zeroDimension_locallyQuasiFinite`. Condition (3) genuinely needs
a separation hypothesis on `|X|`; see the implementation notes. -/
@[stacks 0ACA "decent case: (2) <=> (3) <=> (4) <=> (5), the arrow out of (3) by 03K3"]
theorem tfae_of_isDecentSpace (D : FiniteTypeOverField.{u})
    (hdec : IsDecentSpace D.B (Spec (.of D.k)) D.base_mem D.X.left) :
    [D.DiscretePoints, D.ZeroTopologicalDimension, D.ZeroDimension,
      D.LocallyQuasiFiniteOverField].TFAE := by
  tfae_have 1 → 2 := zeroTopologicalDimension_of_discretePoints D
  tfae_have 2 → 1 := discretePoints_of_zeroTopologicalDimension_of_isDecentSpace D hdec
  tfae_have 1 ↔ 3 := discretePoints_iff_zeroDimension D
  tfae_have 3 ↔ 4 := zeroDimension_iff_locallyQuasiFinite D
  tfae_finish

end FiniteTypeOverField

end AlgebraicGeometry.Space

end
