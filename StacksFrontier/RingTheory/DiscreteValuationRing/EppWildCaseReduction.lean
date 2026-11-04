module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppBaseChangeEmbedding
public import StacksFrontier.RingTheory.Henselian.Criteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Epp's unramified base change without a perfect residue field

Let `A → B` be a local homomorphism of discrete valuation rings satisfying Epp's condition
`Stacks.EppTheorem.EppCondition`. This file replaces the perfect core of `κ_B`, which is an
intermediate field of `κ_B / κ_A` only when `κ_A` is perfect, by the compositum
`κ_A(perfectCore κ_B p)`, and constructs the finite weakly unramified base change of `A` whose
residue field is this compositum, with no perfectness hypothesis on `κ_A`. It also shows that the
henselian hypothesis on `B` needed to embed the base change into `B` is supplied by completeness,
and that the base change is separable over the fraction field of `A`.

## Main definitions

* `perfectCoreCompositum K L p`: the compositum `K(perfectCore L p)` inside `L`, as an
  intermediate field of `L / K`.

## Main results

* `isSeparable_perfectCoreCompositum_iff`: the compositum is separable over `K` if and only if
  every element of the perfect core of `L` is separable over `K`.
* `perfectCoreCompositum_eq_perfectCoreIntermediateField`: over a perfect base the compositum is
  the perfect core.
* `Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algEquiv`: a finite weakly unramified
  extension of a discrete valuation ring realising a prescribed finite separable residue
  extension.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_residueField_algEquiv_compositum`: the
  finite weakly unramified base change with residue field the compositum.
* `Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algHom_fieldRange_eq`: the
  residue-field embedding with prescribed image.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum`:
  for a henselian `B`, the base change embeds into `B` with residue field mapped onto the
  compositum.
* `EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum_of_complete`
  (namespace `Stacks.EppTheorem`): the same with `B` complete instead of henselian.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_completion`: the base change
  embeds into a complete extension of `B` with the same residue field.
* `AdjoinRoot.separable_map_algebraMap_of_separable_map_residue`: a monic polynomial over a
  discrete valuation ring with separable irreducible reduction is separable over the fraction
  field.
* `AdjoinRoot.isSeparable_of_separable`: `K[X] ⧸ (q)` is separable over `K` for `q` monic,
  irreducible and separable.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EJ](https://stacks.math.columbia.edu/tag/09EJ)
-/

@[expose] public section

open IsLocalRing Polynomial

/-! ### The compositum of the base field with the perfect core -/

section Compositum

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar L p]

/-- The compositum `K(perfectCore L p)` of `K` with the perfect core of `L`, as an intermediate
field of `L / K`. -/
def perfectCoreCompositum : IntermediateField K L :=
  IntermediateField.adjoin K (perfectCore L p : Set L)

variable {K L p}

/-- The perfect core is contained in the compositum. -/
theorem mem_perfectCoreCompositum_of_mem_perfectCore {x : L} (hx : x ∈ perfectCore L p) :
    x ∈ perfectCoreCompositum K L p :=
  IntermediateField.subset_adjoin K _ hx

/-- The compositum is the smallest intermediate field of `L / K` containing the perfect core. -/
theorem perfectCoreCompositum_le_iff {E : IntermediateField K L} :
    perfectCoreCompositum K L p ≤ E ↔ ∀ x : L, x ∈ perfectCore L p → x ∈ E :=
  IntermediateField.adjoin_le_iff

/-- If every element of the perfect core of `L` is separable algebraic over `K`, then
`K(perfectCore L p) / K` is a separable extension. -/
theorem isSeparable_perfectCoreCompositum
    (h : ∀ x : L, x ∈ perfectCore L p → IsSeparable K x) :
    Algebra.IsSeparable K (perfectCoreCompositum K L p) :=
  (le_separableClosure_iff _ _ _).mp <| IntermediateField.adjoin_le_iff.mpr fun x hx =>
    mem_separableClosure_iff.mpr (h x hx)

/-- The compositum `K(perfectCore L p)` is separable over `K` if and only if every element of the
perfect core of `L` is separable over `K`. -/
theorem isSeparable_perfectCoreCompositum_iff :
    (∀ x : L, x ∈ perfectCore L p → IsSeparable K x) ↔
      Algebra.IsSeparable K (perfectCoreCompositum K L p) :=
  ⟨isSeparable_perfectCoreCompositum, fun hsep _x hx =>
    mem_separableClosure_iff.mp <|
      (le_separableClosure_iff _ _ _).mpr hsep (IntermediateField.subset_adjoin _ _ hx)⟩

/-- Over a perfect base the compositum is the perfect core. -/
theorem perfectCoreCompositum_eq_perfectCoreIntermediateField [ExpChar K p] [PerfectRing K p] :
    perfectCoreCompositum K L p = perfectCoreIntermediateField K L p :=
  le_antisymm (perfectCoreCompositum_le_iff.mpr fun _ hx => hx)
    fun _ hx => mem_perfectCoreCompositum_of_mem_perfectCore hx

end Compositum

/-! ### Epp's condition and the compositum -/

namespace Stacks.EppTheorem

section EppConditionCompositum

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]

/-- Under Epp's residue-field condition the compositum of `κ_A` with the perfect core of `κ_B` is
a separable extension of `κ_A`. -/
theorem EppCondition.isSeparable_perfectCoreCompositum (h : EppCondition A B p) :
    Algebra.IsSeparable (ResidueField A)
      (perfectCoreCompositum (ResidueField A) (ResidueField B) p) :=
  _root_.isSeparable_perfectCoreCompositum h

end EppConditionCompositum

end Stacks.EppTheorem

/-! ### The finite unramified base change, for an arbitrary finite separable residue extension -/

namespace Stacks.EppTheorem

universe u v w

/-- Let `A` be a discrete valuation ring and let `E / κ_A` be a finite separable extension of its
residue field. Then there is a discrete valuation ring `A₁`, finite as an `A`-module, with
`A₁ / A` an extension of discrete valuation rings which is weakly unramified (`e = 1`), whose
residue field is `κ_A`-isomorphic to `E`. -/
@[ega "II 7.1.2" "partial"]
theorem exists_isWeaklyUnramified_residueField_algEquiv {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (E : Type w) [Field E] [Algebra (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A] E) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) E
  have hint : IsIntegral (ResidueField A) α := IsIntegral.of_finite (ResidueField A) α
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift_map_residue_eq A (minpoly.monic hint)
  have hirr : Irreducible (P.map (residue A)) := hPmap ▸ minpoly.irreducible hint
  have hd : 0 < P.natDegree :=
    hP.natDegree_map (residue A) ▸ hPmap ▸ minpoly.natDegree_pos hint
  have hdeg := Polynomial.natDegree_pos_iff_degree_pos.mp hd
  have hlocal := AdjoinRoot.isLocalRing_of_irreducible_map_residue hP hirr
  have hdom := AdjoinRoot.isDomain_of_irreducible_map_residue hP hirr
  have hdvr := AdjoinRoot.isDiscreteValuationRing hP hirr hd
  have hext : IsDiscreteValuationRing.IsExtension A (AdjoinRoot P) :=
    { toFaithfulSMul := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hP hdeg
      toIsLocalHom := AdjoinRoot.isLocalHom_of_monic_of_degree_pos (g := P) hP hdeg }
  exact ⟨AdjoinRoot P, inferInstance, hdom, hdvr, inferInstance, hP.finite_adjoinRoot, hext,
    AdjoinRoot.ramificationIdx_eq_one hP hirr hd,
    ⟨(AdjoinRoot.residueFieldAlgEquiv hP hirr hd).symm.trans
      ((AdjoinRoot.algEquivOfEq (ResidueField A) _ _ hPmap).trans
        (AdjoinRoot.algEquivOfPrimitiveElement hint hα))⟩⟩

/-- Let `A → B` be a local homomorphism from a discrete valuation ring to a local ring and suppose

* Epp's condition holds: every element of `perfectCore κ_B p` is separable algebraic over `κ_A`;
* the compositum `κ_A(perfectCore κ_B p)` is finite-dimensional over `κ_A`.

Then there is a discrete valuation ring `A₁`, finite over `A`, with `A₁ / A` weakly unramified
(`e = 1`), whose residue field is `κ_A`-isomorphic to `κ_A(perfectCore κ_B p)`. -/
theorem EppCondition.exists_isWeaklyUnramified_residueField_algEquiv_compositum {A : Type u}
    {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDiscreteValuationRing A]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ}
    [ExpChar (ResidueField B) p] (hepp : EppCondition A B p)
    (hfin : FiniteDimensional (ResidueField A)
      (perfectCoreCompositum (ResidueField A) (ResidueField B) p)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A]
          perfectCoreCompositum (ResidueField A) (ResidueField B) p) := by
  have := hepp.isSeparable_perfectCoreCompositum
  exact exists_isWeaklyUnramified_residueField_algEquiv
    (perfectCoreCompositum (ResidueField A) (ResidueField B) p)

/-- For a finite separable intermediate field `E` of `κ_B / κ_A` there is a discrete valuation
ring `A₁`, a finite weakly unramified extension of `A`, together with a `κ_A`-embedding of its
residue field into `κ_B` whose image is exactly `E`. -/
theorem exists_isWeaklyUnramified_residueField_algHom_fieldRange_eq {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∃ φ : ResidueField A₁ →ₐ[ResidueField A] ResidueField B,
          (φ : ResidueField A₁ →+* ResidueField B).fieldRange = E.toSubfield := by
  obtain ⟨A₁, _, _, _, _, hmf, hext, hwu, ⟨e⟩⟩ :=
    exists_isWeaklyUnramified_residueField_algEquiv (A := A) E
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, hmf, hext, hwu,
    E.val.comp (e : ResidueField A₁ →ₐ[ResidueField A] E), ?_⟩
  ext x
  simp only [RingHom.mem_fieldRange, IntermediateField.mem_toSubfield]
  refine ⟨?_, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
  rintro ⟨z, rfl⟩
  exact (e z).2

end Stacks.EppTheorem

/-! ### The embedding into a henselian `B`, and its image -/

namespace Stacks.EppTheorem

universe u v w

/-- Let `A → B` be a local homomorphism of discrete valuation rings with `B` henselian, satisfying
Epp's condition, with `κ_A(perfectCore κ_B p)` finite over `κ_A`. Then the finite weakly unramified
base change `A₁ / A` with residue field `κ_A(perfectCore κ_B p)` embeds into `B`, and the induced
map of residue fields has image `κ_A(perfectCore κ_B p)`. -/
theorem EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum {A : Type u}
    {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B] [HenselianLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p] (hepp : EppCondition A B p)
    (hfin : FiniteDimensional (ResidueField A)
      (perfectCoreCompositum (ResidueField A) (ResidueField B) p)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A]
          perfectCoreCompositum (ResidueField A) (ResidueField B) p) ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange =
          (perfectCoreCompositum (ResidueField A) (ResidueField B) p).toSubfield := by
  have := hepp.isSeparable_perfectCoreCompositum
  exact exists_isWeaklyUnramified_algebraMap_fieldRange_eq_of_isSeparable
    (perfectCoreCompositum (ResidueField A) (ResidueField B) p)

end Stacks.EppTheorem

/-! ### Completeness supplies the henselian hypothesis -/

namespace Stacks.EppTheorem

universe u v w

/-- The statement of
`Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum`
with `B` complete for its maximal-ideal-adic topology instead of henselian. -/
theorem EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum_of_complete
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ}
    [ExpChar (ResidueField B) p] (hepp : EppCondition A B p)
    (hfin : FiniteDimensional (ResidueField A)
      (perfectCoreCompositum (ResidueField A) (ResidueField B) p)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A]
          perfectCoreCompositum (ResidueField A) (ResidueField B) p) ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange =
          (perfectCoreCompositum (ResidueField A) (ResidueField B) p).toSubfield := by
  have := henselianLocalRing_of_isAdicComplete_maximalIdeal B
  exact hepp.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum hfin

section Completion

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A] [IsLocalRing B]
  [IsLocalRing B'] [Algebra A B] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
  [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B B')] [IsLocalHom (algebraMap A B')]

include A B B' in
/-- The residue fields of a tower of local homomorphisms form a tower. -/
theorem isScalarTower_residueField :
    IsScalarTower (ResidueField A) (ResidueField B) (ResidueField B') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨y, rfl⟩ := residue_surjective (R := A) x
    rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
      ResidueField.algebraMap_residue, IsScalarTower.algebraMap_apply A B B']

/-- Epp's condition for `A → B` implies Epp's condition for `A → B'` when `κ_B → κ_{B'}` is
surjective. -/
theorem EppCondition.of_residueField_surjective_right {p : ℕ} [ExpChar (ResidueField B) p]
    [ExpChar (ResidueField B') p]
    (hsurj : Function.Surjective (algebraMap (ResidueField B) (ResidueField B')))
    (h : EppCondition A B p) : EppCondition A B' p := by
  have := isScalarTower_residueField (A := A) (B := B) (B' := B')
  exact fun _ hx => isSeparable_of_mem_perfectCore_of_surjective hsurj h hx

end Completion

/-- Let `A → B → B'` be local homomorphisms, `A` and `B'` discrete valuation rings, with

* `B'` complete for its maximal-ideal-adic topology;
* `κ_B → κ_{B'}` surjective;
* Epp's condition for `A → B`, and `κ_A(perfectCore κ_{B'} p)` finite over `κ_A`.

Then the finite weakly unramified base change `A₁ / A` exists and embeds into `B'`, with
`(algebraMap κ_{A₁} κ_{B'}).fieldRange = κ_A(perfectCore κ_{B'} p)`. -/
theorem EppCondition.exists_isWeaklyUnramified_algHom_of_completion {A : Type u} {B : Type v}
    {B' : Type w} [CommRing A] [CommRing B] [CommRing B'] [IsDomain A] [IsDomain B']
    [IsDiscreteValuationRing A] [IsLocalRing B] [IsDiscreteValuationRing B']
    [IsAdicComplete (maximalIdeal B') B'] [Algebra A B] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B'] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B B')]
    [IsLocalHom (algebraMap A B')] {p : ℕ} [ExpChar (ResidueField B) p]
    [ExpChar (ResidueField B') p]
    (hsurj : Function.Surjective (algebraMap (ResidueField B) (ResidueField B')))
    (hepp : EppCondition A B p)
    (hfin : FiniteDimensional (ResidueField A)
      (perfectCoreCompositum (ResidueField A) (ResidueField B') p)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B')
      (_ : IsScalarTower A A₁ B') (_ : IsLocalHom (algebraMap A₁ B')),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A]
          perfectCoreCompositum (ResidueField A) (ResidueField B') p) ∧
        (algebraMap (ResidueField A₁) (ResidueField B')).fieldRange =
          (perfectCoreCompositum (ResidueField A) (ResidueField B') p).toSubfield :=
  (hepp.of_residueField_surjective_right
      hsurj).exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum_of_complete hfin

end Stacks.EppTheorem

/-! ### The base change is separable over the fraction field -/

namespace AdjoinRoot

/-- Let `A` be a discrete valuation ring with fraction field `K` and let `P ∈ A[X]` be monic with
`P̄ ∈ κ_A[X]` irreducible and separable. Then `P` is separable over `K`. -/
theorem separable_map_algebraMap_of_separable_map_residue {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {P : A[X]} (hP : P.Monic) (hirr : Irreducible (P.map (residue A)))
    (hsep : (P.map (residue A)).Separable) : (P.map (algebraMap A K)).Separable := by
  have hKirr : Irreducible (P.map (algebraMap A K)) :=
    irreducible_map_algebraMap_of_irreducible_map_residue hP hirr
  rw [Polynomial.separable_iff_derivative_ne_zero hKirr, Polynomial.derivative_map]
  intro h
  refine (Polynomial.separable_iff_derivative_ne_zero hirr).mp hsep ?_
  rw [Polynomial.derivative_map, (Polynomial.map_eq_zero_iff (IsFractionRing.injective A K)).mp h,
    Polynomial.map_zero]

/-- `K[X] ⧸ (q)` for `q` monic, irreducible and separable is a separable extension of `K`. -/
theorem isSeparable_of_separable {K : Type*} [Field K] {q : K[X]} [Fact (Irreducible q)]
    (hq : q.Monic) (hsep : q.Separable) : Algebra.IsSeparable K (AdjoinRoot q) := by
  have hfin : Module.Finite K (AdjoinRoot q) := hq.finite_adjoinRoot
  have hint : IsIntegral K (AdjoinRoot.root q) := IsIntegral.of_finite K _
  have hmin : minpoly K (AdjoinRoot.root q) = q := by
    rw [AdjoinRoot.minpoly_root hq.ne_zero, hq.leadingCoeff, inv_one, map_one, mul_one]
  have htop : IntermediateField.adjoin K ({AdjoinRoot.root q} : Set (AdjoinRoot q)) = ⊤ :=
    IntermediateField.toSubalgebra_injective <| by
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        AdjoinRoot.adjoinRoot_eq_top, IntermediateField.top_toSubalgebra]
  rw [← IntermediateField.isSeparable_top, ← htop,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro x rfl
  show (minpoly K (AdjoinRoot.root q)).Separable
  rwa [hmin]

end AdjoinRoot
