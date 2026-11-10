module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.PrescribedResidueFieldPoint
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Points of a scheme over a finite field with values in a finite extension

Let `k` be a finite field, `X` a quasi-compact scheme locally of finite type over `k`, and `K` an
extension of `k` of degree `n ≥ 1`.  A `K`-valued point of `X` over `k` is a closed point `x`
together with a `k`-embedding `κ(x) → K`; such an embedding exists exactly when `deg x ∣ n`, and
then there are `deg x` of them.  Hence

`#X(K) = ∑_{x ∈ |X|, deg x ∣ n} deg x`,

which is the identity the source uses, without comment, to pass from the Euler product
`∏_{x ∈ |X|} (1 - T^{deg x})⁻¹` to the point counts `#X(k_n)`.

## Main definitions

* `Stacks.EtaleCohomology.fieldValuedPoints`: the set `X(K) = Mor_k(Spec K, X)`.

## Main results

* `Stacks.EtaleCohomology.fieldValuedPointsEquiv`: `X(K)` is the set of pairs of a point `x`
  and a `k`-algebra map `κ(x) → K`.
* `Stacks.EtaleCohomology.natCard_fieldValuedPoints`: `#X(K) = ∑_{deg x ∣ n} deg x`.
* `Stacks.EtaleCohomology.fieldValuedPointsEquivRationalPoints`: `X(K)` is the set of
  `K`-rational points of the base change `X_K`, the form in which Theorem 03V2 counts them.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The set `X(K)` of `K`-valued points of a scheme `X` over `k`: the morphisms `Spec K ⟶ X`
over `Spec k`. -/
public def fieldValuedPoints (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K] :
    Type u :=
  { g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) }

variable (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- The morphism `Spec K ⟶ X` determined by `σ : κ(x) → K` lies over `Spec k` exactly when `σ`
is a `k`-algebra map. -/
public theorem fromSpecResidueField_comp_eq_iff (x : X)
    (σ : X.residueField x ⟶ CommRingCat.of K) :
    (Spec.map σ ≫ X.fromSpecResidueField x) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ↔
      fieldToResidue f x ≫ σ = CommRingCat.ofHom (algebraMap k K) := by
  have key : (Spec.map σ ≫ X.fromSpecResidueField x) ≫ f =
      Spec.map (fieldToResidue f x ≫ σ) := by
    let : Field ↑(CommRingCat.of k) := inferInstanceAs (Field k)
    let : (f x).asIdeal.IsPrime := (f x).isPrime
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [fieldToResidue_eq_specGammaResidue_comp_residueFieldMap f x,
      ← Scheme.Spec.algebraMap_residueFieldIso_inv]
    simp only [Category.assoc]
  rw [key, Spec.map_inj]

/-- The `k`-embeddings `κ(x) → K` of the residue field at `x`, as morphisms of rings under `k`. -/
public def residueEmbeddings (x : X) : Type u :=
  { σ : X.residueField x ⟶ CommRingCat.of K //
      fieldToResidue f x ≫ σ = CommRingCat.ofHom (algebraMap k K) }

/-- A morphism `σ : κ(x) ⟶ K` under `k` is a `k`-algebra map, `κ(x)` being a `k`-algebra
through the structure morphism. -/
def residueEmbeddingsEquivAlgHom (x : X) :
    letI : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
    residueEmbeddings f K x ≃ (X.residueField x →ₐ[k] K) :=
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  { toFun := fun σ =>
      { toRingHom := σ.1.hom
        commutes' := fun r => by
          have h := congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of K => φ.hom r) σ.2
          simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
          exact h }
    invFun := fun φ => ⟨CommRingCat.ofHom φ.toRingHom, by
      ext r
      exact φ.commutes r⟩
    left_inv := fun σ => rfl
    right_inv := fun φ => rfl }

/-- **`X(K)` as pairs.**  A `K`-valued point of `X` over `k` is a point `x` of `X` together with
a `k`-embedding `κ(x) → K`. -/
public def fieldValuedPointsEquiv :
    fieldValuedPoints f K ≃ Σ x : X, residueEmbeddings f K x :=
  ((Scheme.SpecToEquivOfField K X).subtypeEquiv
      (q := fun a : Σ x : X, X.residueField x ⟶ CommRingCat.of K =>
        fieldToResidue f a.1 ≫ a.2 = CommRingCat.ofHom (algebraMap k K))
      fun g => by
        conv_lhs => rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply g]
        exact fromSpecResidueField_comp_eq_iff f K _ _).trans
    { toFun := fun c => ⟨c.1.1, ⟨c.1.2, c.2⟩⟩
      invFun := fun c => ⟨⟨c.1, c.2.1⟩, c.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ### Counting over a finite field -/

section Count

variable [Finite K]

/-- The number of `k`-embeddings of `κ(x)` into the finite field `K` is `deg x` if `deg x` divides
`[K : k]`, and `0` otherwise. -/
public theorem natCard_residueEmbeddings (x : X) :
    Nat.card (residueEmbeddings f K x) =
      if residueDegree f x ∣ Module.finrank k K then residueDegree f x else 0 := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  rw [Nat.card_congr (residueEmbeddingsEquivAlgHom f K x)]
  change _ = if Module.finrank k (X.residueField x) ∣ Module.finrank k K then
    Module.finrank k (X.residueField x) else 0
  split_ifs with h
  · exact FiniteField.natCard_algHom_of_finrank_dvd h
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun φ => h (FiniteField.nonempty_algHom_iff_finrank_dvd.1 ⟨φ⟩)⟩

/-- A residue degree dividing the degree of the finite extension `K` of `k` is nonzero. -/
private theorem residueDegree_ne_zero_of_dvd_finrank {x : X}
    (h : residueDegree f x ∣ Module.finrank k K) : residueDegree f x ≠ 0 := by
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  intro h0
  rw [h0, zero_dvd_iff] at h
  omega

/-- A point admitting a `k`-embedding of its residue field into the finite extension `K` is a
closed point, of residue degree dividing `[K : k]`. -/
public theorem isClosed_and_dvd_of_residueEmbeddings [LocallyOfFiniteType f] (x : X)
    (σ : residueEmbeddings f K x) :
    IsClosed ({x} : Set X) ∧ residueDegree f x ∣ Module.finrank k K := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have hdvd : residueDegree f x ∣ Module.finrank k K :=
    FiniteField.nonempty_algHom_iff_finrank_dvd.1 ⟨residueEmbeddingsEquivAlgHom f K x σ⟩
  refine ⟨?_, hdvd⟩
  have hfin : Module.Finite k (X.residueField x) :=
    Module.finite_of_finrank_pos
      (Nat.pos_of_ne_zero (residueDegree_ne_zero_of_dvd_finrank f K hdvd))
  refine isClosed_singleton_of_module_finite_residueField f x ?_
  have hbridge : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.Γevaluation x =
      fieldToResidue f x := by
    simp only [fieldToResidue, fieldToStalk, Scheme.Γevaluation, Scheme.evaluation,
      Category.assoc]
  rw [hbridge]
  exact hfin

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **The number of points of `X` with values in a finite extension.**  If `K` is an extension of
the finite field `k` of degree `n`, then `#X(K) = ∑_{x ∈ |X|, deg x ∣ n} deg x`. -/
public theorem natCard_fieldValuedPoints :
    Nat.card (fieldValuedPoints f K) =
      ∑ x ∈ (closedPointsDegreeLE f (Module.finrank k K)).filter
        (fun x => residueDegree f x.1 ∣ Module.finrank k K), residueDegree f x.1 := by
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  set S := (closedPointsDegreeLE f (Module.finrank k K)).filter
    (fun x => residueDegree f x.1 ∣ Module.finrank k K)
  have hmem : ∀ (x : X) (σ : residueEmbeddings f K x),
      ∃ h : IsClosed ({x} : Set X), (⟨x, h⟩ : closedPoints X) ∈ S := by
    intro x σ
    obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f K x σ
    refine ⟨hc, Finset.mem_filter.2 ⟨?_, hd⟩⟩
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_of_dvd hpos hd
  let e : (Σ x : X, residueEmbeddings f K x) ≃ Σ y : S, residueEmbeddings f K y.1.1 :=
    { toFun := fun c => ⟨⟨⟨c.1, (hmem c.1 c.2).1⟩, (hmem c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : ∀ y : S, Finite (residueEmbeddings f K y.1.1) := by
    intro y
    refine Nat.finite_of_card_ne_zero ?_
    have hd := (Finset.mem_filter.1 y.2).2
    rw [natCard_residueEmbeddings, ite_eq_left hd]
    exact residueDegree_ne_zero_of_dvd_finrank f K hd
  rw [Nat.card_congr ((fieldValuedPointsEquiv f K).trans e), Nat.card_sigma,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [natCard_residueEmbeddings, ite_eq_left (Finset.mem_filter.1 y.2).2]

end Count

end Stacks.EtaleCohomology

end
