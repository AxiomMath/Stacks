module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Nullstellensatz
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed points of the projective space of a vector space

A nonzero linear functional `f` on a vector space `V` cuts out a point of `P(V) = Proj (Sym V)`,
namely the homogeneous prime of elements killed by `Sym f : Sym V → Sym k`. That point is
closed, it depends only on the class of `f` in the projectivization of the dual, and over an
algebraically closed field with `V` finite-dimensional every closed point arises this way
exactly once. So the closed points of `P(V)` are the one-dimensional quotients of `V`.

## Main definitions

* `Projectivization.mapEquiv`: the equivalence of projectivizations induced by a linear
  equivalence.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint`: the point of `P(V)` cut out
  by a nonzero linear functional.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointOfDual`: the induced map from the
  projectivized dual to the closed points of `P(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointsEquivDual`: that map as an equivalence,
  over an algebraically closed field and for finite-dimensional `V`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed`: the point cut out
  by a nonzero functional is closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointOfDual_injective` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointOfDual_surjective`.

## Implementation notes

Closedness is proved by exhibiting the point as the projective zero locus of its own
homogeneous ideal. The key input is a section `k → V` of `f`, which splits `Sym f` and so
forces any homogeneous prime containing the ideal to be contained in it as well.

Surjectivity is the Nullstellensatz: a closed point of `Proj (Sym V)` is a homogeneous prime
whose transport along a basis is a prime ideal of a polynomial ring, and over an algebraically
closed field such an ideal has a nonzero point in its zero locus; the coordinates of that point
are the values of the functional on the basis.

A few lemmas on symmetric algebras that have no other consumer in the library are proved here:
that the canonical map of the base ring into the symmetric algebra of itself is injective, that
a unit multiple of a linear map has the same kernel on symmetric algebras, and that the
degree-`n` part of `Sym_k k` is the line spanned by the `n`-th power of the canonical generator.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public section

namespace SymmetricAlgebra

/-- The canonical map of a commutative ring into the symmetric algebra of itself, as a module
over itself, kills only zero. -/
public theorem ι_self_eq_zero_iff {R : Type*} [CommSemiring R] (a : R) :
    SymmetricAlgebra.ι R R a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  simpa using congrArg (SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R)) h

end SymmetricAlgebra

namespace SymPow

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Multiplying a linear map by a unit does not change which elements of the symmetric algebra
the induced map kills. -/
public theorem symAlgMap_units_smul_zero_iff (c : Rˣ) (f : M →ₗ[R] N)
    (x : SymmetricAlgebra R M) : symAlgMap (c • f) x = 0 ↔ symAlgMap f x = 0 := by
  have h : c • f = ((c : R) • (LinearMap.id : N →ₗ[R] N)) ∘ₗ f := by ext; rfl
  rw [h, symAlgMap_comp_apply]
  refine ⟨fun hx => ?_, fun hx => by rw [hx, map_zero]⟩
  have hinv := congrArg
    (symAlgMap (((c⁻¹ : Rˣ) : R) • (LinearMap.id : N →ₗ[R] N))) hx
  rw [map_zero, ← symAlgMap_comp_apply] at hinv
  have hid : (((c⁻¹ : Rˣ) : R) • (LinearMap.id : N →ₗ[R] N)) ∘ₗ
      ((c : R) • (LinearMap.id : N →ₗ[R] N)) = LinearMap.id := by
    ext t
    simp [smul_smul]
  simpa only [hid, symAlgMap_id_apply] using hinv

/-- The degree-`n` part of the symmetric algebra of the base ring on itself is the line spanned
by the `n`-th power of the canonical generator. -/
public theorem symmetricPower_self_eq_span_singleton (R : Type*) [CommSemiring R] (n : ℕ) :
    symmetricPower n R R = Submodule.span R {(SymmetricAlgebra.ι R R (1 : R)) ^ n} := by
  classical
  have hrange : LinearMap.range (SymmetricAlgebra.ι R R) =
      Submodule.span R {SymmetricAlgebra.ι R R (1 : R)} := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have ha : SymmetricAlgebra.ι R R a = a • SymmetricAlgebra.ι R R 1 := by
        simpa using (SymmetricAlgebra.ι R R).map_smul a (1 : R)
      rw [ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (LinearMap.mem_range_self _ _))
  rw [symmetricPower, hrange, Submodule.span_pow]
  congr 1
  ext z
  simp

/-- An element of the degree-`n` part of `Sym_R R` killed by the lift of the identity is zero:
that part is a free module of rank one on which the lift is injective. -/
public theorem eq_zero_of_mem_symmetricPower_of_lift_id_eq_zero (R : Type*) [CommSemiring R]
    (n : ℕ) {z : SymmetricAlgebra R R} (hz : z ∈ symmetricPower n R R)
    (heval : SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R) z = 0) : z = 0 := by
  classical
  rw [symmetricPower_self_eq_span_singleton R n] at hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  have hc0 : c = 0 := by
    rw [← hc] at heval
    simpa using heval
  rw [← hc, hc0, zero_smul]

end SymPow

namespace Projectivization

/-- A linear equivalence induces an equivalence of projectivizations. -/
public def mapEquiv {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    Projectivization K V ≃ Projectivization K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp [Projectivization.map_mk]
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp [Projectivization.map_mk]

/-- A linear functional kills the chosen representative of the transported class exactly when it
kills the image of the chosen representative. -/
public theorem apply_mapEquiv_rep_eq_zero_iff {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (p : Projectivization K V)
    (f : Module.Dual K W) : f ((mapEquiv e p).rep) = 0 ↔ f (e p.rep) = 0 := by
  have hp : e p.rep ≠ 0 := e.map_ne_zero_iff.mpr p.rep_nonzero
  have hmk : Projectivization.mk K (e p.rep) hp = mapEquiv e p := by
    conv_rhs => rw [← Projectivization.mk_rep p]
    rfl
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K (e p.rep) hp
  rw [← hmk, ← hc]
  simp [Units.smul_def, c.ne_zero]

end Projectivization

namespace Module.Dual

/-- Two linear functionals with the same kernel differ by a unit scalar. -/
public theorem exists_units_smul_eq_of_forall_eq_zero_iff {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] {f g : Module.Dual k V} (hg : g ≠ 0)
    (h : ∀ v, f v = 0 ↔ g v = 0) : ∃ c : kˣ, f = c • g := by
  classical
  obtain ⟨v, hv : g v ≠ 0⟩ := DFunLike.exists_ne hg
  have hfv : f v ≠ 0 := fun hh => hv ((h v).1 hh)
  refine ⟨Units.mk0 (f v / g v) (div_ne_zero hfv hv), ?_⟩
  ext w
  have hz : g (w - (g w / g v) • v) = 0 := by simp [hv]
  have hfw := (h _).2 hz
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hfw
  show f w = (f v / g v) * g w
  rw [hfw]
  ring

end Module.Dual

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- A nonzero linear functional cuts out a point of `P(V)`: the homogeneous prime of elements
of `Sym V` killed by the induced map to `Sym k`. -/
public theorem exists_linearFunctionalPoint (f : Module.Dual k V) (hf : f ≠ 0) :
    ∃ q : projectiveSpaceOfModule k V,
      (∀ w : V, SymmetricAlgebra.ι k V w ∈ q.asHomogeneousIdeal ↔ f w = 0) ∧
      (∀ z : SymmetricAlgebra k V,
        z ∈ q.asHomogeneousIdeal ↔ SymPow.symAlgMap f z = 0) := by
  classical
  set ψ := SymPow.gradedSymAlgMap f with hψ
  let q : projectiveSpaceOfModule k V :=
    { asHomogeneousIdeal :=
        (⊥ : HomogeneousIdeal (fun n => SymPow.symmetricPower n k k)).comap ψ
      isPrime := by
        show (Ideal.comap (SymPow.gradedSymAlgMap f).toRingHom
          (⊥ : Ideal (SymmetricAlgebra k k))).IsPrime
        infer_instance
      not_irrelevant_le := by
        intro hi
        obtain ⟨w, hw : f w ≠ 0⟩ := DFunLike.exists_ne hf
        have hmem : SymmetricAlgebra.ι k V w ∈
            (HomogeneousIdeal.irrelevant
              (fun n => SymPow.symmetricPower n k V)).toIdeal := by
          apply HomogeneousIdeal.mem_irrelevant_of_mem
            (fun n => SymPow.symmetricPower n k V) Nat.one_pos
          show SymmetricAlgebra.ι k V w ∈
            (LinearMap.range (SymmetricAlgebra.ι k V)) ^ 1
          rw [pow_one]
          exact LinearMap.mem_range_self _ _
        have hz := hi hmem
        change ψ (SymmetricAlgebra.ι k V w) = 0 at hz
        simp only [hψ, SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι] at hz
        exact hw ((SymmetricAlgebra.ι_self_eq_zero_iff (f w)).mp hz) }
  refine ⟨q, fun w => ?_, fun z => Iff.rfl⟩
  show ψ (SymmetricAlgebra.ι k V w) = 0 ↔ f w = 0
  simp only [hψ, SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι]
  exact SymmetricAlgebra.ι_self_eq_zero_iff (f w)

/-- Not every element of `V` maps into a given homogeneous prime of `Sym V`: otherwise the whole
irrelevant ideal would. -/
public theorem exists_ι_notMem (p : projectiveSpaceOfModule k V) :
    ∃ x : V, SymmetricAlgebra.ι k V x ∉ p.asHomogeneousIdeal := by
  by_contra! h
  apply p.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn z hz
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r => simp at hn
  | add a b i ha hb ia ib => exact add_mem (ia hn) (ib hn)
  | mem_mul a ha i b hb ih =>
    obtain ⟨x, rfl⟩ := ha
    exact p.asHomogeneousIdeal.toIdeal.mul_mem_right b (h x)

/-- The point cut out by a nonzero linear functional is a closed point of `P(V)`. -/
public theorem isClosed_singleton_of_forall_mem_iff (f : Module.Dual k V) (hf : f ≠ 0)
    (q : projectiveSpaceOfModule k V)
    (hqall : ∀ z : SymmetricAlgebra k V,
      z ∈ q.asHomogeneousIdeal ↔ SymPow.symAlgMap f z = 0) :
    IsClosed ({q} : Set (projectiveSpaceOfModule k V)) := by
  classical
  set A := fun n => SymPow.symmetricPower n k V with hA
  set B := fun n => SymPow.symmetricPower n k k with hB
  set ψ := SymPow.gradedSymAlgMap f with hψ
  obtain ⟨w, hw : f w ≠ 0⟩ := DFunLike.exists_ne hf
  set w₀ : V := (f w)⁻¹ • w with hw₀def
  have hw₀ : f w₀ = 1 := by simp [hw₀def, hw]
  set g : k →ₗ[k] V :=
    { toFun c := c • w₀
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro a b; simp [mul_smul] } with hgdef
  set s := SymPow.symAlgMap g with hsdef
  have hsection : (SymPow.symAlgMap f).comp s = AlgHom.id k _ := by
    apply SymmetricAlgebra.algHom_ext
    ext
    simp [hsdef, hgdef, SymPow.symAlgMap, hw₀]
  show IsClosed ({(q : ProjectiveSpectrum A)} : Set (ProjectiveSpectrum A))
  rw [ProjectiveSpectrum.isClosed_iff_zeroLocus]
  refine ⟨q.asHomogeneousIdeal.toIdeal, ?_⟩
  ext y
  rw [ProjectiveSpectrum.mem_zeroLocus]
  refine ⟨by rintro rfl; exact le_rfl, fun hqy => ?_⟩
  have hqle : q.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal := hqy
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have hhomY : y.asHomogeneousIdeal.toIdeal.IsHomogeneous A :=
    y.asHomogeneousIdeal.isHomogeneous
  have hhomQ : q.asHomogeneousIdeal.toIdeal.IsHomogeneous A :=
    q.asHomogeneousIdeal.isHomogeneous
  have hideal : y.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal := by
    intro z hz
    rw [hhomY.mem_iff] at hz
    rw [hhomQ.mem_iff]
    intro n
    have hzcomp : GradedRing.proj A n z ∈ y.asHomogeneousIdeal.toIdeal := hz n
    have hzero : ψ (GradedRing.proj A n z) = 0 := by
      by_contra hne
      have hψmem : ψ (GradedRing.proj A n z) ∈ B n := by
        exact SymPow.symAlgMap_mapsTo n f _ (DirectSum.decompose A z n).property
      have hspan : ψ (GradedRing.proj A n z) ∈
          Submodule.span k {(SymmetricAlgebra.ι k k 1) ^ n} := by
        rw [← SymPow.symmetricPower_self_eq_span_singleton k n]
        exact hψmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hne
        rw [← hc, hc0, zero_smul]
      have hsec (t : SymmetricAlgebra k k) : ψ (s t) = t :=
        DFunLike.congr_fun hsection t
      have hdiff (t : SymmetricAlgebra k V) :
          t - s (ψ t) ∈ y.asHomogeneousIdeal.toIdeal := by
        apply hqle
        apply (hqall _).2
        show ψ (t - s (ψ t)) = 0
        rw [map_sub, hsec, sub_self]
      have hsz : s (ψ (GradedRing.proj A n z)) ∈ y.asHomogeneousIdeal.toIdeal := by
        simpa using
          y.asHomogeneousIdeal.toIdeal.sub_mem hzcomp (hdiff (GradedRing.proj A n z))
      rw [← hc] at hsz
      have hpow : (SymmetricAlgebra.ι k V w₀) ^ n ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsmul : c • (SymmetricAlgebra.ι k V w₀) ^ n ∈
            Submodule.restrictScalars k y.asHomogeneousIdeal.toIdeal := by
          simpa [hsdef, hgdef, SymPow.symAlgMap_ι] using hsz
        simpa [smul_smul, hc0] using Submodule.smul_mem
          (Submodule.restrictScalars k y.asHomogeneousIdeal.toIdeal) c⁻¹ hsmul
      have hwmem : SymmetricAlgebra.ι k V w₀ ∈ y.asHomogeneousIdeal.toIdeal :=
        y.isPrime.mem_of_pow_mem _ hpow
      obtain ⟨x, hx⟩ := exists_ι_notMem k V y
      apply hx
      have hsmem : s (ψ (SymmetricAlgebra.ι k V x)) ∈ y.asHomogeneousIdeal.toIdeal := by
        simpa [hsdef, hψ, hgdef, SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι] using
          Submodule.smul_mem
            (Submodule.restrictScalars k y.asHomogeneousIdeal.toIdeal) (f x) hwmem
      simpa using y.asHomogeneousIdeal.toIdeal.add_mem
        (hdiff (SymmetricAlgebra.ι k V x)) hsmem
    exact (hqall (GradedRing.proj A n z)).2 hzero
  exact Set.mem_singleton_iff.mpr <| ProjectiveSpectrum.ext <|
    HomogeneousIdeal.toIdeal_injective (le_antisymm hideal hqle)

/-- The point of `P(V)` cut out by a nonzero linear functional on `V`. -/
public noncomputable def linearFunctionalPoint (f : Module.Dual k V) (hf : f ≠ 0) :
    projectiveSpaceOfModule k V := (exists_linearFunctionalPoint k V f hf).choose

/-- An element of `Sym V` lies in the point cut out by `f` exactly when `Sym f` kills it. -/
public theorem linearFunctionalPoint_mem (f : Module.Dual k V) (hf : f ≠ 0)
    (z : SymmetricAlgebra k V) :
    z ∈ (linearFunctionalPoint k V f hf).asHomogeneousIdeal ↔ SymPow.symAlgMap f z = 0 :=
  (exists_linearFunctionalPoint k V f hf).choose_spec.2 z

/-- A vector lies in the point cut out by `f` exactly when `f` kills it. -/
public theorem linearFunctionalPoint_ι_mem (f : Module.Dual k V) (hf : f ≠ 0) (x : V) :
    SymmetricAlgebra.ι k V x ∈ (linearFunctionalPoint k V f hf).asHomogeneousIdeal ↔
      f x = 0 := (exists_linearFunctionalPoint k V f hf).choose_spec.1 x

/-- The point cut out by a nonzero linear functional is closed. -/
public theorem linearFunctionalPoint_isClosed (f : Module.Dual k V) (hf : f ≠ 0) :
    IsClosed ({linearFunctionalPoint k V f hf} : Set (projectiveSpaceOfModule k V)) :=
  isClosed_singleton_of_forall_mem_iff k V f hf _ (linearFunctionalPoint_mem k V f hf)

/-- The point cut out by a functional depends only on its class up to a unit scalar. -/
public theorem linearFunctionalPoint_units_smul (c : kˣ) (f : Module.Dual k V)
    (hf : f ≠ 0) (hcf : c • f ≠ 0) :
    linearFunctionalPoint k V (c • f) hcf = linearFunctionalPoint k V f hf := by
  apply ProjectiveSpectrum.ext
  ext z
  exact (linearFunctionalPoint_mem k V (c • f) hcf z).trans
    ((SymPow.symAlgMap_units_smul_zero_iff c f z).trans
      (linearFunctionalPoint_mem k V f hf z).symm)

/-- The closed point of `P(V)` attached to a class in the projectivization of the dual. -/
public noncomputable def closedPointOfDual :
    Projectivization k (Module.Dual k V) → ClosedPoints k V :=
  Quotient.lift
    (fun f => ⟨linearFunctionalPoint k V f.val f.property,
      linearFunctionalPoint_isClosed k V f.val f.property⟩)
    (by
      rintro ⟨f, hf⟩ ⟨g, hg⟩ ⟨c, hc⟩
      obtain rfl : c • g = f := hc
      exact Subtype.ext (linearFunctionalPoint_units_smul k V c g hg hf))

/-- On a representative, the closed point attached to a class is the point cut out by it. -/
public theorem closedPointOfDual_mk (f : Module.Dual k V) (hf : f ≠ 0) :
    (closedPointOfDual k V (Projectivization.mk k f hf)).val =
      linearFunctionalPoint k V f hf := rfl

/-- A vector lies in the closed point attached to a class exactly when the chosen representative
kills it. -/
public theorem closedPointOfDual_ι_mem (p : Projectivization k (Module.Dual k V)) (x : V) :
    SymmetricAlgebra.ι k V x ∈ (closedPointOfDual k V p).val.asHomogeneousIdeal ↔
      p.rep x = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  exact linearFunctionalPoint_ι_mem k V p.rep p.rep_nonzero x

/-- Distinct classes in the projectivized dual cut out distinct points. -/
public theorem closedPointOfDual_injective : Function.Injective (closedPointOfDual k V) := by
  intro p q
  induction p using Projectivization.ind with | h f hf =>
  induction q using Projectivization.ind with | h g hg =>
  intro hpq
  have h : ∀ x, f x = 0 ↔ g x = 0 := by
    intro x
    rw [← linearFunctionalPoint_ι_mem k V f hf, ← linearFunctionalPoint_ι_mem k V g hg]
    exact congrArg (fun p : projectiveSpaceOfModule k V =>
      SymmetricAlgebra.ι k V x ∈ p.asHomogeneousIdeal) (congrArg Subtype.val hpq) |> Iff.of_eq
  obtain ⟨c, hc⟩ := Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff hg h
  exact (Projectivization.mk_eq_mk_iff k f g hf hg).2 ⟨c, hc.symm⟩

/-- Over an algebraically closed field a closed point of `P(V)` has a nonzero point of the
affine zero locus of its ideal, read through a basis of `V`. -/
public theorem exists_basis_coordinates_of_closedPoint [IsAlgClosed k] [Module.Finite k V]
    (p : ClosedPoints k V) :
    ∃ (b : Module.Basis (Module.Free.ChooseBasisIndex k V) k V)
      (x : Module.Free.ChooseBasisIndex k V → k),
      x ≠ 0 ∧
      ∀ f ∈ (p.val.asHomogeneousIdeal.toIdeal.comap
        (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom),
        MvPolynomial.aeval x f = 0 := by
  classical
  set b := Module.Free.chooseBasis k V with hb
  have : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  set e := SymmetricAlgebra.equivMvPolynomial b with he
  set I : Ideal (MvPolynomial (Module.Free.ChooseBasisIndex k V) k) :=
    p.val.asHomogeneousIdeal.toIdeal.comap e.symm.toRingHom with hI
  have : p.val.asHomogeneousIdeal.toIdeal.IsPrime := p.val.isPrime
  have hIprime : I.IsPrime := by
    rw [hI]
    infer_instance
  have hvan : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I
  have hex : ∃ x, x ≠ 0 ∧ x ∈ MvPolynomial.zeroLocus k I := by
    by_contra hn
    have hX : ∀ i,
        (MvPolynomial.X i : MvPolynomial (Module.Free.ChooseBasisIndex k V) k) ∈ I := by
      intro i
      rw [← hvan, MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      have hx0 : x = 0 := not_not.mp fun hx0 => hn ⟨x, hx0, hx⟩
      simp [hx0]
    have hBasis : ∀ i, SymmetricAlgebra.ι k V (b i) ∈ p.val.asHomogeneousIdeal.toIdeal := by
      intro i
      have hmem : e.symm (MvPolynomial.X i) ∈ p.val.asHomogeneousIdeal.toIdeal := hX i
      simpa [he] using hmem
    have hgen : ∀ x : V, SymmetricAlgebra.ι k V x ∈ p.val.asHomogeneousIdeal.toIdeal := by
      intro x
      rw [← b.sum_repr x]
      simp only [map_sum, LinearMap.map_smul]
      show (∑ i, (b.repr x) i • SymmetricAlgebra.ι k V (b i)) ∈
        Submodule.restrictScalars k p.val.asHomogeneousIdeal.toIdeal
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hBasis i)
    obtain ⟨x, hx⟩ := exists_ι_notMem k V p.val
    exact hx (hgen x)
  obtain ⟨x, hx0, hx⟩ := hex
  exact ⟨b, x, hx0, hx⟩

/-- A functional whose values on a basis are the coordinates of a point of the zero locus kills
the whole ideal of the corresponding closed point. -/
public theorem symAlgMap_eq_zero_of_mem_closedPoint [IsAlgClosed k] [Module.Finite k V]
    (p : ClosedPoints k V)
    (b : Module.Basis (Module.Free.ChooseBasisIndex k V) k V)
    (x : Module.Free.ChooseBasisIndex k V → k)
    (hxvan : ∀ f ∈ (p.val.asHomogeneousIdeal.toIdeal.comap
      (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom),
        MvPolynomial.aeval x f = 0)
    (f : Module.Dual k V) (hfv : ∀ i, f (b i) = x i)
    {z : SymmetricAlgebra k V} (hz : z ∈ p.val.asHomogeneousIdeal.toIdeal) :
    SymPow.symAlgMap f z = 0 := by
  classical
  set A := fun n => SymPow.symmetricPower n k V with hA
  set B := fun n => SymPow.symmetricPower n k k with hB
  set e := SymmetricAlgebra.equivMvPolynomial b with he
  set I : Ideal (MvPolynomial (Module.Free.ChooseBasisIndex k V) k) :=
    p.val.asHomogeneousIdeal.toIdeal.comap e.symm.toRingHom with hI
  set ψ := SymPow.gradedSymAlgMap f with hψ
  have hlin : f = (MvPolynomial.aeval x).toLinearMap.comp
      (e.toLinearMap.comp (SymmetricAlgebra.ι k V)) := by
    apply b.ext
    intro i
    rw [hfv i]
    simp [he, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  have hmaps : (MvPolynomial.aeval x).comp e.toAlgHom = SymmetricAlgebra.lift f := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    have hpoint : (MvPolynomial.aeval x) (e (SymmetricAlgebra.ι k V w)) = f w :=
      (congrArg (fun g : Module.Dual k V => g w) hlin).symm
    convert hpoint using 1 <;> simp
  have hcomp : (SymmetricAlgebra.lift (LinearMap.id : k →ₗ[k] k)).comp
      (SymPow.symAlgMap f) = SymmetricAlgebra.lift f := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    simp [SymPow.symAlgMap]
  have hhom : p.val.asHomogeneousIdeal.toIdeal.IsHomogeneous A :=
    p.val.asHomogeneousIdeal.isHomogeneous
  have hcompzero (n : ℕ) : ψ (GradedRing.proj A n z) = 0 := by
    have hzmem : GradedRing.proj A n z ∈ p.val.asHomogeneousIdeal.toIdeal :=
      (hhom.mem_iff.mp hz) n
    have hmemI : e (GradedRing.proj A n z) ∈ I := by
      rw [hI]
      show e.symm (e (GradedRing.proj A n z)) ∈ p.val.asHomogeneousIdeal.toIdeal
      simpa using hzmem
    have heval : SymmetricAlgebra.lift f (GradedRing.proj A n z) = 0 := by
      rw [← hmaps]
      exact hxvan (e (GradedRing.proj A n z)) hmemI
    have hψmem : ψ (GradedRing.proj A n z) ∈ B n :=
      SymPow.symAlgMap_mapsTo n f _ (DirectSum.decompose A z n).property
    have hEvalψ : SymmetricAlgebra.lift (LinearMap.id : k →ₗ[k] k)
        (ψ (GradedRing.proj A n z)) = 0 := by
      have h := congrArg (fun g : SymmetricAlgebra k V →ₐ[k] k =>
        g (GradedRing.proj A n z)) hcomp
      change SymmetricAlgebra.lift (LinearMap.id : k →ₗ[k] k)
          (SymPow.symAlgMap f (GradedRing.proj A n z)) =
        SymmetricAlgebra.lift f (GradedRing.proj A n z) at h
      rwa [heval] at h
    exact SymPow.eq_zero_of_mem_symmetricPower_of_lift_id_eq_zero k n hψmem hEvalψ
  have hdecomp : DirectSum.decompose B (ψ z) = 0 := by
    rw [DirectSum.decompose_map A B ψ]
    apply DirectSum.ext
    intro n
    simp only [DirectSum.map_apply]
    apply Subtype.ext
    show ψ (DirectSum.decompose A z n) = 0
    simpa only [GradedRing.proj_apply] using hcompzero n
  have hzero : ψ z = 0 := (DirectSum.decomposeAlgEquiv B).injective (by simpa using hdecomp)
  exact hzero

/-- Over an algebraically closed field, every closed point of `P(V)` is cut out by a nonzero
linear functional. -/
public theorem exists_dual_of_closedPoint [IsAlgClosed k] [Module.Finite k V]
    (p : ClosedPoints k V) :
    ∃ f : Module.Dual k V, f ≠ 0 ∧
      (∀ x : V, SymmetricAlgebra.ι k V x ∈ p.val.asHomogeneousIdeal ↔ f x = 0) ∧
      (∀ z : SymmetricAlgebra k V, z ∈ p.val.asHomogeneousIdeal ↔
        SymPow.symAlgMap f z = 0) := by
  classical
  obtain ⟨b, x, hx0, hxvan⟩ := exists_basis_coordinates_of_closedPoint k V p
  have : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  have : Fintype (Module.Free.ChooseBasisIndex k V) := Fintype.ofFinite _
  set f : Module.Dual k V := b.dualBasis.equivFun.symm x with hf
  have hfv (i) : f (b i) = x i := by
    have he := congrFun (b.dualBasis.equivFun.apply_symm_apply x) i
    simpa [hf, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr] using he
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hx0
    funext i
    rw [← hfv, hf0]
    simp
  obtain ⟨q, hq, hqall⟩ := exists_linearFunctionalPoint k V f hf0
  have hpqI : p.val.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal := fun z hz =>
    (hqall z).mpr <| symAlgMap_eq_zero_of_mem_closedPoint k V p b x hxvan f hfv hz
  have hqmem : q ∈ closure ({p.val} : Set (projectiveSpaceOfModule k V)) := by
    let A : ℕ → Submodule k (SymmetricAlgebra k V) := fun n => SymPow.symmetricPower n k V
    let pp : ProjectiveSpectrum A := p.val
    let qq : ProjectiveSpectrum A := q
    show qq ∈ closure ({pp} : Set (ProjectiveSpectrum A))
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, ProjectiveSpectrum.mem_zeroLocus]
    intro z hz
    rw [ProjectiveSpectrum.vanishingIdeal_singleton] at hz
    exact hpqI hz
  have hqp : q = p.val := by simpa [p.property.closure_eq] using hqmem
  refine ⟨f, hf0, fun w => ⟨fun hv => (SymmetricAlgebra.ι_self_eq_zero_iff (f w)).mp ?_,
    fun hv => by simpa [hqp] using (hq w).2 hv⟩, by simpa [hqp] using hqall⟩
  simpa [SymPow.symAlgMap_ι] using
    symAlgMap_eq_zero_of_mem_closedPoint k V p b x hxvan f hfv hv

/-- Over an algebraically closed field every closed point of `P(V)` arises from a class in the
projectivized dual. -/
public theorem closedPointOfDual_surjective [IsAlgClosed k] [Module.Finite k V] :
    Function.Surjective (closedPointOfDual k V) := by
  intro p
  obtain ⟨f, hf, _, hfull⟩ := exists_dual_of_closedPoint k V p
  refine ⟨Projectivization.mk k f hf, Subtype.ext <| ProjectiveSpectrum.ext ?_⟩
  ext z
  exact (linearFunctionalPoint_mem k V f hf z).trans (hfull z).symm

/-- **The closed points of `P(V)` are the one-dimensional quotients of `V`**: over an
algebraically closed field and for finite-dimensional `V`, they are canonically the classes in
the projectivization of the dual of `V`. -/
@[sga "7 XII 1.1" "special case"]
public noncomputable def closedPointsEquivDual [IsAlgClosed k] [Module.Finite k V] :
    Projectivization k (Module.Dual k V) ≃ ClosedPoints k V :=
  Equiv.ofBijective (closedPointOfDual k V)
    ⟨closedPointOfDual_injective k V, closedPointOfDual_surjective k V⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
