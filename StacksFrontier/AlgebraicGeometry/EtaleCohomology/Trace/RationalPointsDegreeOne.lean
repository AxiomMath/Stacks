module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne

/-!
# Rational points and closed points of degree one

A `k`-rational point of a scheme `X` locally of finite type over a field `k` is the same thing as
a closed point of `X` of residue degree `1`: the point it hits, together with the unique
`k`-embedding of the residue field there into `k`.  Over a finite field this identifies the sums
over `X(k)` in the trace formula of [Stacks, Tag 03V3] with the sums over closed points of degree
one in [Stacks, Tag 03V2].  At such a point the geometric point over the rational point maps to the
geometric point at the closed point, which is what compares the two geometric Frobenius actions.

## Main results

* `Stacks.EtaleCohomology.rationalPointsEquivDegreeOne`: `X(k)` is the set of closed points of
  residue degree one.
* `Stacks.EtaleCohomology.natCard_residueField_of_residueDegree_eq_one`: the residue field at a
  point of degree one has as many elements as `k`.
* `Stacks.EtaleCohomology.rationalGeometricPointHom`: the morphism from the geometric point over a
  rational point to the geometric point at the point it hits.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `X(k)`, read as the `k`-valued points of `X` over `k`. -/
def rationalPointsEquivFieldValuedPoints : rationalPoints f ≃ fieldValuedPoints f k :=
  Equiv.subtypeEquivRight fun g => by
    have h : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
      rw [Algebra.algebraMap_self]
      exact Spec.map_id _
    rw [h]

/-- At a point of residue degree one there is exactly one `k`-embedding of the residue field
into `k`. -/
theorem natCard_residueEmbeddings_self [Finite k] (x : X) (hx : residueDegree f x = 1) :
    Nat.card (residueEmbeddings f k x) = 1 := by
  rw [natCard_residueEmbeddings, Module.finrank_self, hx]
  simp

/-- The residue field at a point of residue degree one has as many elements as `k`. -/
theorem natCard_residueField_of_residueDegree_eq_one [Fintype k] (x : X)
    (hx : residueDegree f x = 1) : Nat.card (X.residueField x) = Fintype.card k := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have h : Module.finrank k (X.residueField x) = 1 := hx
  have : Module.Finite k (X.residueField x) := Module.finite_of_finrank_eq_succ h
  let e : X.residueField x ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq _ _ (h.trans (Module.finrank_self k).symm)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]

section GeometricPoint

variable (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]

/-- **The geometric point over a rational point maps to the geometric point at the point it
hits.**  If `y = Spec σ ≫ (Spec κ(x) ⟶ X)` with `σ : κ(x) → k`, an embedding of the algebraic
closure of `κ(x)` into `k̄` extending `κ(x) → k → k̄` is a morphism of geometric points. -/
def rationalGeometricPointHom (y : Spec (.of k) ⟶ X) :
    GeometricPoint.Hom (Stacks.Frobenius.rationalGeometricPoint kbar y)
      (Stacks.Frobenius.geometricPointAt X (Scheme.SpecToEquivOfField k X y).1) :=
  letI : Algebra (X.residueField (Scheme.SpecToEquivOfField k X y).1) kbar :=
    ((Scheme.SpecToEquivOfField k X y).2 ≫ CommRingCat.ofHom (algebraMap k kbar)).hom.toAlgebra
  { hom := Spec.map (CommRingCat.ofHom (IsAlgClosed.lift
      (R := X.residueField (Scheme.SpecToEquivOfField k X y).1)
      (S := AlgebraicClosure (X.residueField (Scheme.SpecToEquivOfField k X y).1))
      (M := kbar)).toRingHom)
    comm := by
      have hy := (Scheme.SpecToEquivOfField k X).symm_apply_apply y
      have hring : CommRingCat.ofHom
            (algebraMap (X.residueField (Scheme.SpecToEquivOfField k X y).1)
            (AlgebraicClosure (X.residueField (Scheme.SpecToEquivOfField k X y).1))) ≫
          CommRingCat.ofHom (IsAlgClosed.lift
            (R := X.residueField (Scheme.SpecToEquivOfField k X y).1)
            (S := AlgebraicClosure (X.residueField (Scheme.SpecToEquivOfField k X y).1))
            (M := kbar)).toRingHom =
          (Scheme.SpecToEquivOfField k X y).2 ≫ CommRingCat.ofHom (algebraMap k kbar) := by
        ext z
        exact AlgHom.commutes _ z
      change Spec.map _ ≫ Spec.map _ ≫ X.fromSpecResidueField _ =
        Spec.map (CommRingCat.ofHom (algebraMap k kbar)) ≫ y
      conv_rhs => rw [← hy]
      change _ = Spec.map _ ≫ Spec.map (Scheme.SpecToEquivOfField k X y).2 ≫
        X.fromSpecResidueField (Scheme.SpecToEquivOfField k X y).1
      rw [← Category.assoc, ← Spec.map_comp, hring, Spec.map_comp, Category.assoc] }

end GeometricPoint

variable [LocallyOfFiniteType f]

/-- A point admitting a `k`-embedding of its residue field into `k` is a closed point of residue
degree one. -/
theorem isClosed_and_residueDegree_eq_one [Finite k] (x : X) (σ : residueEmbeddings f k x) :
    IsClosed ({x} : Set X) ∧ residueDegree f x = 1 := by
  obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f k x σ
  rw [Module.finrank_self] at hd
  exact ⟨hc, Nat.dvd_one.mp hd⟩

/-- **`X(k)` is the set of closed points of residue degree one.** -/
def rationalPointsEquivDegreeOne [Finite k] :
    rationalPoints f ≃ {x : closedPoints X // residueDegree f x.1 = 1} :=
  (rationalPointsEquivFieldValuedPoints f).trans ((fieldValuedPointsEquiv f k).trans
    { toFun := fun c => ⟨⟨c.1, (isClosed_and_residueDegree_eq_one f c.1 c.2).1⟩,
        (isClosed_and_residueDegree_eq_one f c.1 c.2).2⟩
      invFun := fun x => ⟨x.1.1, (Nat.card_eq_one_iff_unique.mp
        (natCard_residueEmbeddings_self f x.1.1 x.2)).2.some⟩
      left_inv := fun c => by
        have := (Nat.card_eq_one_iff_unique.mp (natCard_residueEmbeddings_self f c.1
          (isClosed_and_residueDegree_eq_one f c.1 c.2).2)).1
        exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))
      right_inv := fun x => rfl })

/-- The closed point of degree one corresponding to a rational point is the point it hits, the
first component of `Scheme.SpecToEquivOfField`. -/
theorem rationalPointsEquivDegreeOne_apply [Finite k] (y : rationalPoints f) :
    ((rationalPointsEquivDegreeOne f y).1.1 : X) = (Scheme.SpecToEquivOfField k X y.1).1 :=
  rfl

/-- Over a finite field, a scheme of finite type has finitely many rational points. -/
theorem finite_rationalPoints [Finite k] [QuasiCompact f] : Finite (rationalPoints f) :=
  have : Finite {x : closedPoints X // residueDegree f x.1 = 1} :=
    ((finite_setOf_closedPoints_residueDegree_le f 1).subset fun _ hx => le_of_eq hx).to_subtype
  Finite.of_equiv _ (rationalPointsEquivDegreeOne f).symm

/-- **A sum over the closed points of degree one is a sum over `X(k)`.** -/
theorem finsum_residueDegree_eq_one_eq_sum {M : Type*} [AddCommMonoid M] [Finite k]
    [Fintype (rationalPoints f)] (g : closedPoints X → M) :
    ∑ᶠ (x : closedPoints X) (_ : residueDegree f x.1 = 1), g x =
      ∑ y : rationalPoints f, g (rationalPointsEquivDegreeOne f y).1 := by
  have : Fintype {x : closedPoints X // residueDegree f x.1 = 1} :=
    Fintype.ofEquiv _ (rationalPointsEquivDegreeOne f)
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  exact (Equiv.sum_comp (rationalPointsEquivDegreeOne f) (fun x => g x.1)).symm

end Stacks.EtaleCohomology
