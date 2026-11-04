module

public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.Examples.Spaces.FieldFibreZeroDimensionalNotDiscrete

/-!
# An empty fibre is discrete and quasi-finite without having dimension zero

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `p` be a field-valued point of `Y` whose point of `|Y|` is not in the image of
`f`. Stacks 0ACK asserts the equivalences

* (2) `F` is discrete `⇔` (3) `dim(F) = 0`,
* (5) `|X_k|` is discrete `⇔` (6) `dim(|X_k|) = 0`,
* (7) `dim(X_k) = 0` `⇔` (8) `f` is quasi-finite above the point,

where `F` is the set-theoretic fibre and `X_k` the field fibre. All three fail in the direction
towards a condition of the form `dim(-) = 0`, because the Krull dimension of Stacks 0055 of the
empty space is `-∞` and not `0`: an empty fibre is discrete and carries no point at which `f`
could fail to be quasi-finite, so (2), (5) and (8) hold, while (3), (6) and (7) read `-∞ = 0`.

The witness is the empty open subspace of `Spec(k)` mapping to `Spec(k)`, at the tautological
field-valued point of the target. It is a decent algebraic space over a decent target, so no
decency hypothesis repairs the defect.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEmpty_points`: a morphism out of a
  presheaf with no points is locally of finite type.
* `AlgebraicGeometry.Space.isDiscreteSetFibre_of_isEmpty_points`,
  `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isEmpty_points` and
  `AlgebraicGeometry.Space.isQuasiFiniteAboveFieldValuedPoint_of_isEmpty_points`: conditions
  (2), (5) and (8) hold for an empty fibre.
* `AlgebraicGeometry.Space.not_isZeroDimensionalSetFibre_of_isEmpty_points`,
  `AlgebraicGeometry.Space.not_isZeroDimensionalFieldFibrePoints_of_isEmpty_points` and
  `AlgebraicGeometry.Space.not_isZeroDimensionalFieldFibre_of_isEmpty_points`: conditions (3),
  (6) and (7) fail for an empty fibre.
* `AlgebraicGeometry.Space.exists_discrete_quasiFinite_not_zeroDimensional_fibre`: the datum
  realizing all six at once.
* `not_forall_isZeroDimensionalSetFibre_of_isDiscreteSetFibre`,
  `not_forall_isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints` and
  `not_forall_isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint`, in
  `AlgebraicGeometry.Space`: the three implications `(2) ⇒ (3)`, `(5) ⇒ (6)` and `(8) ⇒ (7)` of
  Stacks 0ACK are false.
* `AlgebraicGeometry.Space.not_forall_isZeroDimensionalSetFibre_of_finite_setFibre`: the
  source's last clause, that condition (1) implies all the others for decent `X` and `Y`, is
  false.

## Implementation notes

An étale chart of a presheaf with no points is represented by a scheme with no points, since
the points of a represented presheaf are the points of the representing scheme by Tag 03BX; a
morphism out of a scheme with no points is an open immersion and so locally of finite type.
That is why no finiteness hypothesis has to be arranged for the witness.

The empty open subspace is the sheafification of the bottom subfunctor, as in
`StacksFrontier/AlgebraicGeometry/Spaces/EmptyOpenSubspace.lean`; its target, the representable
presheaf on the terminal object of the site over `Spec(k)`, carries the tautological
field-valued point of `StacksFrontier/Examples/Spaces/FieldFibreZeroDimensionalNotDiscrete.lean`,
which is where the site, the field and the containment witness come from as well.

What repairs the implications is reading `dim(-) = 0` as `dim(-) ≤ 0`, or adding the
hypothesis that the fibre is nonempty; both repaired forms are in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreConditions.lean`.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The eight conditions of Stacks 0ACK at an empty fibre -/

/-- A morphism out of a presheaf with no points is locally of finite type: an étale chart of
the source is represented by a scheme with no points, and a morphism out of such a scheme is an
open immersion. -/
theorem isLocallyOfFiniteType_of_isEmpty_points (hX : IsEmpty (points B S hS X)) (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b h _ _ _
  have := hX
  have : IsEmpty (points B S hS (yoneda.obj U)) :=
    Function.isEmpty (pointsMap B S hS (yoneda.obj U) a)
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj U) :=
    (schemePointsHomeomorph B S hS U).symm.toEquiv.isEmpty
  exact inferInstance

/-- The point set of the field fibre of a morphism out of a presheaf with no points is empty:
the image of `|X_k| → |X|` is the set-theoretic fibre, which is empty. -/
theorem isEmpty_points_fieldFibre_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    IsEmpty (points B S hS (fieldFibre B S hS f p)) :=
  not_nonempty_iff.mp fun hne ↦
    hX.elim ((nonempty_points_fieldFibre_iff B S hS f p).mp hne).choose

/-- **Stacks 0ACK, condition (1)** holds at an empty fibre: the empty set is finite. -/
theorem finite_setFibre_of_isEmpty_points (hX : IsEmpty (points B S hS X)) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) :
    (setFibre B S hS f p).Finite :=
  have := hX
  Set.toFinite _

/-- **Stacks 0ACK, condition (2)** holds at an empty fibre: the empty space is discrete. -/
theorem isDiscreteSetFibre_of_isEmpty_points (hX : IsEmpty (points B S hS X)) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) :
    IsDiscreteSetFibre B S hS f p :=
  have := hX
  (inferInstance : DiscreteTopology (setFibre B S hS f p))

/-- An empty space does not have Krull dimension `0`: it has Krull dimension `-∞`. -/
private theorem false_of_topologicalKrullDim_eq_zero_of_isEmpty (T : Type*) [TopologicalSpace T]
    [IsEmpty T] (h : topologicalKrullDim T = (0 : WithBot ℕ∞)) : False := by
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr ‹_›] at h
  simp at h

/-- **Stacks 0ACK, condition (3)** fails at an empty fibre: the Krull dimension of Stacks 0055
of the empty space is `-∞`. -/
theorem not_isZeroDimensionalSetFibre_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    ¬ IsZeroDimensionalSetFibre B S hS f p := by
  intro hdim
  have := hX
  exact false_of_topologicalKrullDim_eq_zero_of_isEmpty (setFibre B S hS f p) hdim

/-- **Stacks 0ACK, condition (5)** holds at an empty fibre: the point set of the field fibre is
empty, hence discrete. -/
theorem isDiscreteFieldFibrePoints_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  have := isEmpty_points_fieldFibre_of_isEmpty_points B S hS hX f p
  (inferInstance : DiscreteTopology (points B S hS (fieldFibre B S hS f p)))

/-- **Stacks 0ACK, condition (6)** fails at an empty fibre: the point set of the field fibre is
empty, so its Krull dimension is `-∞`. -/
theorem not_isZeroDimensionalFieldFibrePoints_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    ¬ IsZeroDimensionalFieldFibrePoints B S hS f p := by
  intro hdim
  have := isEmpty_points_fieldFibre_of_isEmpty_points B S hS hX f p
  exact false_of_topologicalKrullDim_eq_zero_of_isEmpty _ hdim

/-- **Stacks 0ACK, condition (7)** fails at an empty fibre: the dimension of Stacks 04N6 is a
supremum over the points of the field fibre, which is `⊥` when there are none. -/
theorem not_isZeroDimensionalFieldFibre_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p)) :
    ¬ IsZeroDimensionalFieldFibre B S hS f p hXk := by
  intro hdim
  have h : (⨆ x : points B S hS (fieldFibre B S hS f p),
      dimensionAtPoint B S hS (fieldFibre B S hS f p) hXk x) = (0 : WithBot ℕ∞) := hdim
  have := isEmpty_points_fieldFibre_of_isEmpty_points B S hS hX f p
  rw [iSup_of_empty] at h
  simp at h

/-- **Stacks 0ACK, condition (8)** holds at an empty fibre: there is no point of `|X|` above
the point of `|Y|` at which quasi-finiteness could fail. -/
theorem isQuasiFiniteAboveFieldValuedPoint_of_isEmpty_points (hX : IsEmpty (points B S hS X))
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p :=
  fun x _ ↦ hX.elim x

/-! ### The witness: the empty open subspace of the spectrum of a field -/

/-- **A decent algebraic space, locally of finite type over a decent target, whose fibre over a
field-valued point of the target is empty.** Conditions (2), (5) and (8) of Stacks 0ACK hold
for it and conditions (3), (6) and (7) fail. The space is the empty open subspace of
`Spec(k)`. -/
theorem exists_discrete_quasiFinite_not_zeroDimensional_fibre :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hY : IsAlgebraicSpace B S hS Y) (_ : IsDecentSpace B S hS X)
      (_ : IsDecentSpace B S hS Y) (f : X ⟶ Y) (_ : IsLocallyOfFiniteType B S hS f)
      (p : FieldValuedPoint B S hS Y), (setFibre B S hS f p).Finite ∧
        IsDiscreteSetFibre B S hS f p ∧
        IsDiscreteFieldFibrePoints B S hS f p ∧
        IsQuasiFiniteAboveFieldValuedPoint B S hS f p ∧
        ¬ IsZeroDimensionalSetFibre B S hS f p ∧
        ¬ IsZeroDimensionalFieldFibrePoints B S hS f p ∧
        ¬ IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p) := by
  obtain ⟨D, -, -, -, -⟩ :=
    Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints.{u}
  have hYalg : IsAlgebraicSpace D.B (Spec (.of D.k)) D.base_mem
      (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) := isAlgebraicSpace_yoneda _ _ _ _
  obtain ⟨E, hEopen, hEpt⟩ :
      ∃ E : Subfunctor (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))),
        IsOpenSubspace D.B (Spec (.of D.k)) D.base_mem E ∧
          IsEmpty (points D.B (Spec (.of D.k)) D.base_mem E.toFunctor) :=
    ⟨_, isOpenSubspace_sheafify_bot D.B (Spec (.of D.k)) D.base_mem _ hYalg,
      isEmpty_points_sheafify_bot D.B (Spec (.of D.k)) D.base_mem _⟩
  exact ⟨D.B, Spec (.of D.k), D.base_mem, E.toFunctor,
    yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem))), hEopen.1, hYalg,
    isDecentSpace_of_isEmpty_points _ _ _ _ hEpt, isDecentSpace_yoneda _ _ _ _, E.ι,
    isLocallyOfFiniteType_of_isEmpty_points _ _ _ hEpt E.ι, tautologicalBasePoint D,
    finite_setFibre_of_isEmpty_points _ _ _ hEpt E.ι _,
    isDiscreteSetFibre_of_isEmpty_points _ _ _ hEpt E.ι _,
    isDiscreteFieldFibrePoints_of_isEmpty_points _ _ _ hEpt E.ι _,
    isQuasiFiniteAboveFieldValuedPoint_of_isEmpty_points _ _ _ hEpt E.ι _,
    not_isZeroDimensionalSetFibre_of_isEmpty_points _ _ _ hEpt E.ι _,
    not_isZeroDimensionalFieldFibrePoints_of_isEmpty_points _ _ _ hEpt E.ι _,
    not_isZeroDimensionalFieldFibre_of_isEmpty_points _ _ _ hEpt E.ι _ _⟩

/-! ### The three implications towards a condition `dim(-) = 0` are false -/

/-- **The source's implication from condition (2) to condition (3) is false.** There is a
decent algebraic space locally of finite type over a decent algebraic space, and a field-valued
point of the target, whose set-theoretic fibre is empty: that fibre is discrete and has Krull
dimension `-∞`. -/
@[stacks 0ACK "(2) => (3) is false: an empty fibre is discrete of dimension -infinity"]
theorem not_forall_isZeroDimensionalSetFibre_of_isDiscreteSetFibre :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS X → IsDecentSpace B S hS Y →
        ∀ f : X ⟶ Y, IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        IsDiscreteSetFibre B S hS f p → IsZeroDimensionalSetFibre B S hS f p := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, hXdec, hYdec, f, hft, p, -, h2, -, -, h3, -, -⟩ :=
    exists_discrete_quasiFinite_not_zeroDimensional_fibre.{u}
  exact h3 (h B S hS X Y hX hY hXdec hYdec f hft p h2)

/-- **The source's implication from condition (5) to condition (6) is false.** The field fibre
over a field-valued point outside the image has no points, so its point set is discrete and has
Krull dimension `-∞`. -/
@[stacks 0ACK "(5) => (6) is false: an empty field fibre is discrete of dimension -infinity"]
theorem not_forall_isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS X → IsDecentSpace B S hS Y →
        ∀ f : X ⟶ Y, IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        IsDiscreteFieldFibrePoints B S hS f p →
          IsZeroDimensionalFieldFibrePoints B S hS f p := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, hXdec, hYdec, f, hft, p, -, -, h5, -, -, h6, -⟩ :=
    exists_discrete_quasiFinite_not_zeroDimensional_fibre.{u}
  exact h6 (h B S hS X Y hX hY hXdec hYdec f hft p h5)

/-- **The source's implication from condition (8) to condition (7) is false.** A morphism is
quasi-finite above every point outside its image, while the field fibre there has no points and
so has dimension `-∞` in the sense of Stacks 04N6. -/
@[stacks 0ACK "(8) => (7) is false: an empty field fibre has dimension -infinity"]
theorem not_forall_isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
        (hY : IsAlgebraicSpace B S hS Y), IsDecentSpace B S hS X → IsDecentSpace B S hS Y →
        ∀ f : X ⟶ Y, IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        IsQuasiFiniteAboveFieldValuedPoint B S hS f p →
          IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p) := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, hXdec, hYdec, f, hft, p, -, -, -, h8, -, -, h7⟩ :=
    exists_discrete_quasiFinite_not_zeroDimensional_fibre.{u}
  exact h7 (h B S hS X Y hX hY hXdec hYdec f hft p h8)

/-- **The source's last clause is false.** Stacks 0ACK asserts that when `X` and `Y` are
decent, condition (1) implies all the other conditions; the empty fibre is finite while failing
condition (3), so it does not.

This is the clause `AlgebraicGeometry.Space.fibre_conditions_of_finite_setFibre_of_isDecent`
formalizes, and it is why that statement carries a nonemptiness hypothesis. -/
@[stacks 0ACK "decent spaces: (1) => (3) is false: an empty fibre is finite of dimension -infinity"]
theorem not_forall_isZeroDimensionalSetFibre_of_finite_setFibre :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS X → IsDecentSpace B S hS Y →
        ∀ f : X ⟶ Y, IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Finite → IsZeroDimensionalSetFibre B S hS f p := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, hXdec, hYdec, f, hft, p, h1, -, -, -, h3, -, -⟩ :=
    exists_discrete_quasiFinite_not_zeroDimensional_fibre.{u}
  exact h3 (h B S hS X Y hX hY hXdec hYdec f hft p h1)

end AlgebraicGeometry.Space

end
