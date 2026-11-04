module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Examples.Spaces.ZeroDimensionalPointsNotDiscrete

/-!
# A fibre whose point space has dimension zero without being discrete

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, and let
`X_k = X ×_Y Spec(k)` be the field fibre. Stacks 0ACK asserts that the four conditions

* (5) `|X_k|` is discrete,
* (6) `dim(|X_k|) = 0`,
* (7) `dim(X_k) = 0`,
* (8) `f` is quasi-finite at every point of `|X|` above the point `p` represents

are equivalent, with no hypothesis beyond `f` being locally of finite type, and that they are
moreover equivalent to the two corresponding conditions on the set-theoretic fibre when `Y` is
decent. Every implication out of condition (6) in those claims is false.

The counterexample is the one of Stacks 0ACA: the quotient `𝔸¹_k/ℤ` of the affine line by the
integer translations, whose point space is indiscrete on infinitely many points, hence of Krull
dimension zero without being discrete. Taking `Y = Spec(k)` — a scheme, so a decent algebraic
space — and `f` the structure morphism of that quotient turns it into a counterexample here,
because the field fibre at the tautological field-valued point of `Spec(k)` is the space itself.

## Main definitions

* `AlgebraicGeometry.Space.tautologicalBasePoint` is the field-valued point of the base of a
  space locally of finite type over a field given by the identity section.

## Main results

* `AlgebraicGeometry.Space.homeoTautologicalFieldFibre`: the point space of the field fibre at
  the tautological base point is homeomorphic to the point space of the space itself.
* `not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints`,
  `not_forall_isZeroDimensionalFieldFibre_of_isZeroDimensionalFieldFibrePoints` and
  `not_forall_isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibrePoints`, in
  `AlgebraicGeometry.Space`: the three implications out of condition (6) are false, even for a
  decent target.
* `not_forall_isDiscreteFieldFibrePoints_iff_isZeroDimensionalFieldFibrePoints`, in the same
  namespace: the equivalence of conditions (5) and (6) is false.
* `not_forall_isDiscreteSetFibre_of_isZeroDimensionalSetFibre` and
  `not_forall_isDiscreteSetFibre_iff_isZeroDimensionalSetFibre`, in the same namespace: the
  implication from condition (3) to condition (2) for a decent target, and the equivalence of
  those two conditions, are false.
* `AlgebraicGeometry.Space.nonempty_setFibre_tautologicalBasePoint`: the fibre of the
  counterexample is nonempty, which is why every refutation above is stated with the
  nonemptiness hypothesis that the repaired statements carry.

## Implementation notes

The base of a space locally of finite type over a field is the representable presheaf on the
terminal object of the big fppf site over `Spec(k)`, so the field-valued point of it with field
of definition `k`, structure map the identity and section the identity exists; its presenting
morphism is then the identity of that representable presheaf. The field fibre over it is a
pullback along an isomorphism, so its first projection is an isomorphism, and the point space of
Tag 03BX carries isomorphisms of presheaves to homeomorphisms.

The refuted implications are quantified over a target that is a *decent* algebraic space, so
each of them refutes at once the unrestricted row of equivalences of Stacks 0ACK and its clause
conditioned on `Y` being decent. For the set-theoretic fibre the same datum serves: the base has
a single point, so the fibre is the whole of `|X|`.

Each refuted implication is also quantified over a *nonempty* fibre. The nonemptiness is not
needed for the counterexample — it holds of `𝔸¹_k/ℤ` anyway — but the repaired statements of
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreZeroDimensionalDecent.lean` carry it, since the
empty fibre refutes the arrows in the opposite direction (see
`StacksFrontier/Examples/Spaces/EmptyFibreNotZeroDimensional.lean`), and a refutation stated
without it would leave open whether nonemptiness alone repairs these arrows. It does not.

What repairs the implications is that the fibre be Kolmogorov, for which a decency hypothesis
on `f` suffices; the repaired forms are in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreZeroDimensionalDecent.lean`.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : FiniteTypeOverField.{u})

/-! ### The field fibre at the tautological point of the base -/

/-- The field-valued point of the base of a space locally of finite type over a field given by
the identity section over the spectrum of that field. -/
def tautologicalBasePoint : FieldValuedPoint D.B (Spec (.of D.k)) D.base_mem
    (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) where
  carrier := D.k
  contained := D.base_mem
  toBase := 𝟙 _
  value := 𝟙 _

/-- The morphism presented by the tautological point of the base is the identity of the base. -/
theorem fieldMorphism_tautologicalBasePoint :
    fieldMorphism D.B (Spec (.of D.k)) D.base_mem
      (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) (tautologicalBasePoint D) = 𝟙 _ :=
  (Equiv.symm_apply_eq yonedaEquiv).mpr rfl

/-- The morphism presented by the tautological point of the base is an isomorphism. -/
theorem isIso_fieldMorphism_tautologicalBasePoint :
    IsIso (fieldMorphism D.B (Spec (.of D.k)) D.base_mem
      (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) (tautologicalBasePoint D)) := by
  rw [fieldMorphism_tautologicalBasePoint]
  exact IsIso.id _

/-- The point space of the field fibre at the tautological point of the base is homeomorphic to
the point space of the space itself: that fibre is a pullback along an isomorphism. -/
def homeoTautologicalFieldFibre :
    points D.B (Spec (.of D.k)) D.base_mem
        (fieldFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom (tautologicalBasePoint D)) ≃ₜ
      points D.B (Spec (.of D.k)) D.base_mem D.X.left :=
  haveI := isIso_fieldMorphism_tautologicalBasePoint D
  haveI := pullback_fst_iso_of_right_iso D.X.hom
    (fieldMorphism D.B (Spec (.of D.k)) D.base_mem
      (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) (tautologicalBasePoint D))
  pointsHomeomorphOfIso D.B (Spec (.of D.k)) D.base_mem
    (asIso (pullback.fst D.X.hom
      (fieldMorphism D.B (Spec (.of D.k)) D.base_mem
        (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) (tautologicalBasePoint D))))

/-- At the tautological point of the base, condition (6) of Stacks 0ACK is condition (3) of
Stacks 0ACA for the space itself. -/
theorem isZeroDimensionalFieldFibrePoints_tautologicalBasePoint_iff :
    IsZeroDimensionalFieldFibrePoints D.B (Spec (.of D.k)) D.base_mem D.X.hom
        (tautologicalBasePoint D) ↔ D.ZeroTopologicalDimension :=
  iff_of_eq (congrArg (fun d ↦ d = (0 : WithBot ℕ∞))
    (IsHomeomorph.topologicalKrullDim_eq _ (homeoTautologicalFieldFibre D).isHomeomorph))

/-- At the tautological point of the base, condition (5) of Stacks 0ACK is condition (2) of
Stacks 0ACA for the space itself. -/
theorem isDiscreteFieldFibrePoints_tautologicalBasePoint_iff :
    IsDiscreteFieldFibrePoints D.B (Spec (.of D.k)) D.base_mem D.X.hom
        (tautologicalBasePoint D) ↔ D.DiscretePoints :=
  (homeoTautologicalFieldFibre D).discreteTopology_iff

/-! ### The fibre of the counterexample is nonempty -/

/-- The set-theoretic fibre over the tautological point of the base is the whole point space,
the base having a single point. -/
theorem setFibre_tautologicalBasePoint :
    setFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom (tautologicalBasePoint D) = Set.univ := by
  have hsub : Subsingleton (points D.B (Spec (.of D.k)) D.base_mem
      (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem))))) :=
    subsingleton_points_yoneda_siteObject D.B (Spec (.of D.k)) D.base_mem
      (tautologicalBasePoint D)
  exact Set.eq_univ_of_forall fun _ ↦ hsub.elim _ _

/-- The set-theoretic fibre over the tautological point of the base is nonempty: it is the whole
point space of a space which, being locally of finite type over a field in the sense of
`AlgebraicGeometry.Space.FiniteTypeOverField`, has a point.

Every refutation below therefore holds with the nonemptiness hypothesis in force, which is what
shows the Kolmogorov hypothesis of the repaired statements to be forced: those statements
already assume a nonempty fibre, so nonemptiness alone does not repair them. -/
theorem nonempty_setFibre_tautologicalBasePoint :
    (setFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom (tautologicalBasePoint D)).Nonempty := by
  have := D.nonempty
  rw [setFibre_tautologicalBasePoint D]
  exact Set.univ_nonempty

/-! ### The implications out of condition (6) are false -/

/-- **The source's unrestricted implication from condition (6) to condition (5) is false.**
There is a morphism of algebraic spaces locally of finite type into a decent algebraic space,
and a field-valued point of the target, whose field fibre has point space of Krull dimension
zero and not discrete. -/
@[stacks 0ACK "the unrestricted (6) => (5) is false, even for a decent target"]
theorem not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        IsZeroDimensionalFieldFibrePoints B S hS f p →
          IsDiscreteFieldFibrePoints B S hS f p := by
  intro h
  obtain ⟨D, h6, h5, -, -⟩ :=
    Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints.{u}
  exact h5 ((isDiscreteFieldFibrePoints_tautologicalBasePoint_iff D).mp
    (h D.B (Spec (.of D.k)) D.base_mem _ _ D.isAlgebraicSpace (isAlgebraicSpace_yoneda _ _ _ _)
      (isDecentSpace_yoneda _ _ _ _) D.X.hom D.locallyOfFiniteType _
      (nonempty_setFibre_tautologicalBasePoint D)
      ((isZeroDimensionalFieldFibrePoints_tautologicalBasePoint_iff D).mpr h6)))

/-- **The source's unrestricted implication from condition (6) to condition (7) is false.**
Condition (7) implies condition (5) with no further hypothesis, which condition (6) does not. -/
@[stacks 0ACK "the source's unrestricted (6) => (7) is false, even for a decent target"]
theorem not_forall_isZeroDimensionalFieldFibre_of_isZeroDimensionalFieldFibrePoints :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
        (hY : IsAlgebraicSpace B S hS Y), IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        IsZeroDimensionalFieldFibrePoints B S hS f p →
          IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p) := by
  intro h
  refine not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints.{u}
    fun B S hS X Y hX hY hYdec f hft p hne h6 ↦ ?_
  exact isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibre B S hS hX hY hft p _
    (h B S hS X Y hX hY hYdec f hft p hne h6)

/-- **The source's unrestricted implication from condition (6) to condition (8) is false.**
Conditions (5) and (8) are equivalent with no further hypothesis, and condition (6) implies
neither. -/
@[stacks 0ACK "the source's unrestricted (6) => (8) is false, even for a decent target"]
theorem not_forall_isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibrePoints :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        IsZeroDimensionalFieldFibrePoints B S hS f p →
          IsQuasiFiniteAboveFieldValuedPoint B S hS f p := by
  intro h
  refine not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints.{u}
    fun B S hS X Y hX hY hYdec f hft p hne h6 ↦ ?_
  exact (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft
    p).mpr (h B S hS X Y hX hY hYdec f hft p hne h6)

/-- **The source's equivalence of conditions (5) and (6) is false.** This is the negation of
that equivalence, in the source's own vocabulary. -/
@[stacks 0ACK "the row (5) <=> (6) <=> (7) <=> (8) is false as stated"]
theorem not_forall_isDiscreteFieldFibrePoints_iff_isZeroDimensionalFieldFibrePoints :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        (IsDiscreteFieldFibrePoints B S hS f p ↔
          IsZeroDimensionalFieldFibrePoints B S hS f p) := by
  intro h
  exact not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints.{u}
    fun B S hS X Y hX hY hYdec f hft p hne ↦ (h B S hS X Y hX hY hYdec f hft p hne).mpr

/-! ### The decent-target clause fails on the set-theoretic fibre too -/

/-- The set-theoretic fibre over the tautological point of the base is homeomorphic to the point
space of the space itself. -/
def homeoSetFibreTautologicalBasePoint :
    setFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom (tautologicalBasePoint D) ≃ₜ
      points D.B (Spec (.of D.k)) D.base_mem D.X.left :=
  (Homeomorph.setCongr (setFibre_tautologicalBasePoint D)).trans (Homeomorph.Set.univ _)

/-- At the tautological point of the base, condition (3) of Stacks 0ACK is condition (3) of
Stacks 0ACA for the space itself. -/
theorem isZeroDimensionalSetFibre_tautologicalBasePoint_iff :
    IsZeroDimensionalSetFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom
        (tautologicalBasePoint D) ↔ D.ZeroTopologicalDimension :=
  iff_of_eq (congrArg (fun d ↦ d = (0 : WithBot ℕ∞))
    (IsHomeomorph.topologicalKrullDim_eq _ (homeoSetFibreTautologicalBasePoint D).isHomeomorph))

/-- At the tautological point of the base, condition (2) of Stacks 0ACK is condition (2) of
Stacks 0ACA for the space itself. -/
theorem isDiscreteSetFibre_tautologicalBasePoint_iff :
    IsDiscreteSetFibre D.B (Spec (.of D.k)) D.base_mem D.X.hom
        (tautologicalBasePoint D) ↔ D.DiscretePoints :=
  (homeoSetFibreTautologicalBasePoint D).discreteTopology_iff

/-- **The source's implication from condition (3) to condition (2) for a decent target is
false.** There is a morphism of algebraic spaces locally of finite type into a decent algebraic
space, and a field-valued point of the target, whose set-theoretic fibre has Krull dimension
zero and is not discrete. -/
@[stacks 0ACK "the decent-target clause's (3) => (2) is false"]
theorem not_forall_isDiscreteSetFibre_of_isZeroDimensionalSetFibre :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        IsZeroDimensionalSetFibre B S hS f p → IsDiscreteSetFibre B S hS f p := by
  intro h
  obtain ⟨D, h3, h2, -, -⟩ :=
    Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints.{u}
  exact h2 ((isDiscreteSetFibre_tautologicalBasePoint_iff D).mp
    (h D.B (Spec (.of D.k)) D.base_mem _ _ D.isAlgebraicSpace (isAlgebraicSpace_yoneda _ _ _ _)
      (isDecentSpace_yoneda _ _ _ _) D.X.hom D.locallyOfFiniteType _
      (nonempty_setFibre_tautologicalBasePoint D)
      ((isZeroDimensionalSetFibre_tautologicalBasePoint_iff D).mpr h3)))

/-- **The source's equivalence of conditions (2) and (3) for a decent target is false.** This is
the negation of that equivalence, in the source's own vocabulary. -/
@[stacks 0ACK "the decent-target clause's (2) <=> (3) is false as stated"]
theorem not_forall_isDiscreteSetFibre_iff_isZeroDimensionalSetFibre :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y → ∀ f : X ⟶ Y,
        IsLocallyOfFiniteType B S hS f → ∀ p : FieldValuedPoint B S hS Y,
        (setFibre B S hS f p).Nonempty →
        (IsDiscreteSetFibre B S hS f p ↔ IsZeroDimensionalSetFibre B S hS f p) := by
  intro h
  exact not_forall_isDiscreteSetFibre_of_isZeroDimensionalSetFibre.{u}
    fun B S hS X Y hX hY hYdec f hft p hne ↦ (h B S hS X Y hX hY hYdec f hft p hne).mpr

end AlgebraicGeometry.Space

end
