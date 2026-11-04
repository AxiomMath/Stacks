module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.Node
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.FieldTheory.Separable.PerfectField

/-!
# Ordinary double points are the points with a nodal local algebra

Over an algebraically closed field the two descriptions of a node used in the Stacks project
agree at a point of a scheme: the completed local ring is the two-branch multicross ring
(Tag 0C1W, `Stacks.Curves.IsOrdinaryDoublePoint`) exactly when the local ring is a nodal
algebra over the base field (Tag 0C49, `Stacks.Curves.IsNodalAlgebra`).

This is the step "the only nondegenerate quadric in two variables is `xy` up to a change of
coordinates" in the proof of Stacks Tag 0C4D, carried from the ring-theoretic form in which
`Stacks.Curves.nonempty_algEquiv_multicross_iff` states it to the form the scheme-level
conditions of that tag are written in.

Three inputs are supplied here rather than assumed.  Separability of the residue extension,
which `Stacks.Curves.IsNodalAlgebra` asks for, is automatic because an algebraically closed
field is perfect.  The coefficients of the quadratic form live in the residue field in
`Stacks.Curves.HasNodalCompletion` and in the base field in
`Stacks.Curves.HasMulticrossCompletion`, so the two conditions are compared along an
isomorphism of the residue field with the base field; at a closed point of a scheme locally of
finite type that isomorphism exists, because the residue field is then of finite type over the
base field, hence finite over it by Zariski's lemma, hence equal to it.  Finally the local ring
is Noetherian because a scheme locally of finite type over a field is locally Noetherian.

## Main results

* `Stacks.Curves.hasNodalCompletion_iff_nonempty_algEquiv_multicross` — for a local algebra
  whose residue field is the algebraically closed base field, the completion is a nondegenerate
  quadratic hypersurface if and only if it is the two-branch multicross ring.
* `Stacks.Curves.isNodalAlgebra_iff_nonempty_algEquiv_multicross` — the same comparison with
  the nodal-algebra condition on the left.
* `Stacks.Curves.ringHom_finiteType_evaluation_of_isClosed` — the residue field at a closed
  point of a scheme locally of finite type over a field is of finite type over that field.
* `Stacks.Curves.surjective_evaluation_of_isAlgClosed` — over an algebraically closed field the
  evaluation map to the residue field at such a point is surjective.
* `Stacks.Curves.isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk` — over an algebraically closed
  field, a point of a scheme locally of finite type is an ordinary double point exactly when it
  is closed and its local ring is a nodal algebra.

## Implementation notes

The `k`-algebra structure on the local ring is the one induced by the germ of the structure
morphism at the point, which is the structure `Stacks.Curves.HasMulticrossCompletion` uses, and
the residue-field comparison is phrased as surjectivity of the evaluation map
`AlgebraicGeometry.Scheme.Γevaluation` so that no algebra instance is needed to state it.

Note that `Stacks.Curves.hasNodalCompletion_iff_nonempty_algEquiv_multicross` really does need
the residue field to be the base field and not merely a separable extension of it: over an
algebraically closed `K` the complete local ring `K(t)[[x, y]]/(xy)` is a nodal `K`-algebra
whose completion is not the multicross ring of `K`, its residue field being `K(t)`.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
* [Stacks Project, Tag 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Curves

/-- The discriminant `4ac - b²` of a quadratic form stays nonzero under an isomorphism of
fields. -/
private theorem four_mul_sub_sq_ne_zero_map {K R S : Type*} [Field K] [Field R] [Field S]
    [Algebra K R] [Algebra K S] (e : R ≃ₐ[K] S) {a b c : R} (h : 4 * a * c - b ^ 2 ≠ 0) :
    4 * e a * e c - e b ^ 2 ≠ 0 := by
  have hmap : 4 * e a * e c - e b ^ 2 = e (4 * a * c - b ^ 2) := by
    simp [map_sub, map_mul, map_pow, map_ofNat]
  rw [hmap]
  exact fun hz => h (e.injective (by simpa using hz))

/-- **Over an algebraically closed field, a complete local algebra with residue field the base
field is a nondegenerate quadratic hypersurface exactly when it is the two-branch multicross
ring.**  This is the comparison of the completed-local-ring description of a node in Tag 0C49
with the one in Tag 0C1W, at the level of the completion. -/
theorem hasNodalCompletion_iff_nonempty_algEquiv_multicross
    (K : Type u) (A : Type v) [Field K] [IsAlgClosed K] [CommRing A] [IsLocalRing A]
    [Algebra K A] (e : ResidueField A ≃ₐ[K] K) :
    HasNodalCompletion K A ↔
      Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[K] ↥(multicross K 2)) := by
  rw [← nonempty_algEquiv_multicross_iff (k := K) (AdicCompletion (maximalIdeal A) A)]
  constructor
  · rintro ⟨a, b, c, hdet, ⟨f⟩⟩
    exact ⟨e a, e b, e c, four_mul_sub_sq_ne_zero_map e hdet,
      ⟨f.trans (nodalQuotientAlgEquiv e a b c)⟩⟩
  · rintro ⟨a, b, c, hdet, ⟨f⟩⟩
    exact ⟨e.symm a, e.symm b, e.symm c, four_mul_sub_sq_ne_zero_map e.symm hdet,
      ⟨f.trans (nodalQuotientAlgEquiv e.symm a b c)⟩⟩

/-- **Over an algebraically closed field, a Noetherian local algebra with residue field the base
field is nodal exactly when its completion is the two-branch multicross ring.**  Separability of
the residue extension, the third condition of Tag 0C49, is automatic here. -/
theorem isNodalAlgebra_iff_nonempty_algEquiv_multicross
    (K : Type u) (A : Type v) [Field K] [IsAlgClosed K] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra K A] (e : ResidueField A ≃ₐ[K] K) :
    IsNodalAlgebra K A ↔
      Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[K] ↥(multicross K 2)) := by
  rw [← hasNodalCompletion_iff_nonempty_algEquiv_multicross K A e]
  exact ((isNodalAlgebra_tfae K A).out 1 3).trans
    (and_iff_right (Algebra.isSeparableExtension_of_perfectField K (ResidueField A)))

/-- **The residue field at a closed point of a scheme locally of finite type over a field is of
finite type over that field.**  The point being closed, the canonical morphism from the spectrum
of its residue field is a closed immersion, so its composition with the structure morphism is
locally of finite type. -/
theorem ringHom_finiteType_evaluation_of_isClosed
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    RingHom.FiniteType
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have hnat :
      (((Scheme.ΓSpecIso (.of k)).inv ≫
            (AlgebraicGeometry.Spec (.of k)).presheaf.germ ⊤ (f.base x) trivial) ≫
          (AlgebraicGeometry.Spec (.of k)).residue (f.base x)) ≫ f.residueFieldMap x =
        (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x := by
    rw [Category.assoc, Category.assoc]
    congr 1
    exact Scheme.Γevaluation_naturality f x
  rwa [hnat] at hcomp

/-- **Over an algebraically closed field the evaluation map to the residue field at a closed
point of a scheme locally of finite type is surjective.**  The residue field is of finite type
over the base field, hence finite over it by Zariski's lemma (Tag 0CY7), hence equal to it. -/
theorem surjective_evaluation_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    Function.Surjective
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
  let : Algebra K (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : Algebra.FiniteType K (X.residueField x) :=
    ringHom_finiteType_evaluation_of_isClosed K f x hx
  have : Module.Finite K (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing K (X.residueField x)
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _
    (Algebra.isIntegral_def.mp (Algebra.IsIntegral.of_finite K (X.residueField x)))).2

/-- **Over an algebraically closed field, a point of a scheme locally of finite type is an
ordinary double point exactly when it is closed and its local ring is a nodal algebra.**

This compares condition (1) of Stacks Tag 0C1W with condition (2) of Stacks Tag 0C49 at a point
of a scheme, and is the step of the proof of Stacks Tag 0C4D that identifies the geometric
description of a node with the algebraic one over an algebraically closed field. -/
theorem isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of K))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of K))] (x : X) :
    let kToStalk : K →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
        X.presheaf.germ ⊤ x trivial).hom
    letI : Algebra K (X.presheaf.stalk x) := kToStalk.toAlgebra
    (IsOrdinaryDoublePoint K X x ↔
      IsClosed ({x} : Set X) ∧ IsNodalAlgebra K (X.presheaf.stalk x)) := by
  intro kToStalk
  let : Algebra K (X.presheaf.stalk x) := kToStalk.toAlgebra
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of K))
  have hequiv (hx : IsClosed ({x} : Set X)) : ResidueField (X.presheaf.stalk x) ≃ₐ[K] K :=
    (AlgEquiv.ofBijective (Algebra.ofId K (ResidueField (X.presheaf.stalk x)))
      ⟨(algebraMap K _).injective,
        surjective_evaluation_of_isAlgClosed K (X ↘ AlgebraicGeometry.Spec (.of K)) x hx⟩).symm
  exact ⟨fun ⟨hx, hmc⟩ => ⟨hx, (isNodalAlgebra_iff_nonempty_algEquiv_multicross K
      (X.presheaf.stalk x) (hequiv hx)).mpr hmc⟩,
    fun ⟨hx, hnodal⟩ => ⟨hx, (isNodalAlgebra_iff_nonempty_algEquiv_multicross K
      (X.presheaf.stalk x) (hequiv hx)).mp hnodal⟩⟩

end Stacks.Curves

end
