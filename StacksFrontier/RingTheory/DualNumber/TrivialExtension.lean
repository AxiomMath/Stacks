module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.RingTheory.Flat.DualNumber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trivial deformation of an algebra over the dual numbers

Let `k` be a field and `P` a `k`-algebra.  The dual numbers `P[ε]` of `P` form an algebra over
the dual numbers `k[ε]` of `k`, and this is the *trivial* flat deformation of `P` over `k[ε]`:

* it is flat over `k[ε]`, and
* reducing it modulo `ε` returns `P`, in the strong sense that
  ```
  k[ε] ⟶ P[ε]
    ↓       ↓
   k   ⟶   P
  ```
  is a pushout square of commutative rings.

Both facts are what the Stacks proof of Tag 0DY3 uses to exhibit the split square-zero extension
of `P` by `P` as a flat deformation over the dual numbers, so this file is the ring-theoretic
input to the comparison between deformations of `P` over `k[ε]` and square-zero extensions of
`P` by `P`.

## Main definitions

* `DualNumber.mapOfAlgebra`: the `k`-algebra map `k[ε] → P[ε]` induced by `k → P`, obtained
  from `DualNumber.lift` applied to the element `ε` of `P[ε]`.
* `DualNumber.algebraOfAlgebra`: the resulting `k[ε]`-algebra structure on `P[ε]`.

## Main results

* `DualNumber.flat_dualNumber`: `P[ε]` is flat over `k[ε]`.  Proved from the criterion
  `DualNumber.flat_iff_forall_exists_eq_eps_smul`: multiplication by `ε` on `P[ε]` is
  `(p, q) ↦ (0, p)`, whose kernel and image are both `{(0, q)}`.
* `DualNumber.isPushout_fst`: the reduction square above is a pushout of commutative rings.
  Proved directly from the universal property: a cocone map out of `P[ε]` kills `(0, q) = (p, 0)·ε`
  because `ε` maps to `0` in `k`, so it factors uniquely through `P[ε] → P`.

## Implementation notes

The pushout is established by hand rather than through `CommRingCat.isPushout_of_isPushout`,
which would need the composite algebra structure `k[ε] → k → P` as an instance.  That instance
competes with `TrivSqZeroExt.algebra' k[ε] P P : Algebra k[ε] P[ε]`, whose structure map is
`x ↦ inl (algebraMap k[ε] P x)` and therefore *not* the intended `mapOfAlgebra`; the direct proof
avoids ever having both in scope.

Note for consumers in deformation theory: the `CommRing` structure that
`Deformation.augmentedDualNumbers` carries on `TrivSqZeroExt k k` is **not** definitionally equal
to Mathlib's instance on `k[ε]` — it is built from the `Module kᵐᵒᵖ k` instance that
`Deformation.trivSqZeroExtFunctor` installs locally — so the results here have to be transported
along a ring equivalence rather than used directly on that object.

## References

* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt DualNumber

namespace DualNumber

universe w

variable {k : Type w} [Field k] {P : Type w} [CommRing P] [Algebra k P]

/-- The `k`-algebra map `k[ε] → P[ε]` induced by the structure map `k → P`: it sends `ε` to `ε`
and acts on the two coordinates through `algebraMap k P`. -/
public noncomputable def mapOfAlgebra (k : Type w) [Field k] (P : Type w) [CommRing P]
    [Algebra k P] : k[ε] →ₐ[k] P[ε] :=
  DualNumber.lift ⟨(Algebra.ofId k P[ε], (ε : P[ε])), by simp, fun a ↦ Commute.all _ _⟩

/-- `mapOfAlgebra` agrees with `algebraMap k P` on the constant part. -/
public theorem mapOfAlgebra_inl (a : k) :
    mapOfAlgebra k P (inl a) = inl (algebraMap k P a) := by
  rw [mapOfAlgebra, DualNumber.lift_apply_inl]
  rfl

/-- `mapOfAlgebra` sends `ε` to `ε`. -/
@[simp]
public theorem mapOfAlgebra_eps : mapOfAlgebra k P (ε : k[ε]) = (ε : P[ε]) := by
  rw [mapOfAlgebra, DualNumber.lift_apply_eps]

/-- `mapOfAlgebra` is compatible with the two augmentations. -/
public theorem fst_mapOfAlgebra (x : k[ε]) :
    fst (mapOfAlgebra k P x) = algebraMap k P (fst x) := by
  rw [mapOfAlgebra, DualNumber.lift_apply_apply]
  show fst ((algebraMap k P[ε]) (fst x) + (algebraMap k P[ε]) (snd x) * (ε : P[ε])) = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]
  show (algebraMap k P) (fst x) + (algebraMap k P) (snd x) * (0 : P) = _
  rw [mul_zero, add_zero]

/-- The dual numbers of `P` as an algebra over the dual numbers of `k`. -/
@[instance_reducible]
public noncomputable def algebraOfAlgebra (k : Type w) [Field k] (P : Type w) [CommRing P]
    [Algebra k P] : Algebra k[ε] P[ε] :=
  (mapOfAlgebra k P).toRingHom.toAlgebra

/-- Multiplication by `ε` on `P[ε]` sends `(p, q)` to `(0, p)`. -/
public theorem eps_smul_eq_inr_fst (m : P[ε]) :
    letI := algebraOfAlgebra k P
    (ε : k[ε]) • m = inr (fst m) := by
  let := algebraOfAlgebra k P
  rw [Algebra.smul_def]
  show mapOfAlgebra k P (ε : k[ε]) * m = _
  rw [mapOfAlgebra_eps]
  show inr (1 : P) * m = _
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]

/-- The dual numbers of `P` are flat over the dual numbers of `k`: the trivial deformation of a
`k`-algebra over `k[ε]` is flat. -/
public theorem flat_dualNumber :
    letI := algebraOfAlgebra k P
    Module.Flat k[ε] P[ε] := by
  let := algebraOfAlgebra k P
  rw [DualNumber.flat_iff_forall_exists_eq_eps_smul]
  intro m hm
  refine ⟨inl (snd m), ?_⟩
  rw [eps_smul_eq_inr_fst]
  rw [eps_smul_eq_inr_fst] at hm
  have h0 : fst m = 0 := by
    have := congrArg TrivSqZeroExt.snd hm
    simpa using this
  apply TrivSqZeroExt.ext <;> simp [h0]

section Pushout

/-- The structure map `k[ε] ⟶ P[ε]`, as a morphism of commutative rings. -/
public noncomputable def mapOfAlgebraHom (k : Type w) [Field k] (P : Type w) [CommRing P]
    [Algebra k P] : CommRingCat.of k[ε] ⟶ CommRingCat.of P[ε] :=
  CommRingCat.ofHom (mapOfAlgebra k P).toRingHom

/-- The augmentation `k[ε] ⟶ k`, as a morphism of commutative rings. -/
@[ega "0 22.1.3.2" "augmentation F → K"]
public noncomputable def fstHomOf (k : Type w) [CommRing k] :
    CommRingCat.of k[ε] ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom

/-- The structure map `k ⟶ P`, as a morphism of commutative rings. -/
public noncomputable def algebraMapHom (k : Type w) [Field k] (P : Type w) [CommRing P]
    [Algebra k P] : CommRingCat.of k ⟶ CommRingCat.of P :=
  CommRingCat.ofHom (algebraMap k P)

/-- The reduction square of the trivial deformation commutes. -/
public theorem mapOfAlgebraHom_comp_fstHomOf :
    mapOfAlgebraHom k P ≫ fstHomOf P = fstHomOf k ≫ algebraMapHom k P :=
  CommRingCat.hom_ext (RingHom.ext fun x ↦ fst_mapOfAlgebra x)

/-- A cocone over the reduction span sends `mapOfAlgebra x` and `fst x` to the same element. -/
private theorem inl_mapOfAlgebra_eq_inr_fst (s : PushoutCocone (mapOfAlgebraHom k P) (fstHomOf k))
    (x : k[ε]) : s.inl.hom (mapOfAlgebra k P x) = s.inr.hom (fst x) := by
  have := congrArg (fun q : CommRingCat.of k[ε] ⟶ s.pt ↦ q.hom x) s.condition
  simpa [mapOfAlgebraHom, fstHomOf] using this

/-- Reducing the trivial deformation modulo `ε` gives back `P`: the square
`k[ε] → P[ε]`, `k[ε] → k`, `P[ε] → P`, `k → P` is a pushout of commutative rings.  This is the
cartesian condition on the trivial deformation of `P` over the dual numbers. -/
public theorem isPushout_fst :
    IsPushout (mapOfAlgebraHom k P) (fstHomOf k) (fstHomOf P) (algebraMapHom k P) := by
  refine IsPushout.of_isColimit' ⟨mapOfAlgebraHom_comp_fstHomOf⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (s.inl.hom.comp (TrivSqZeroExt.inlHom P P))) ?_ ?_ ?_)
  · intro s
    refine CommRingCat.hom_ext (RingHom.ext fun m ↦ ?_)
    have key : ∀ p : P, s.inl.hom (inr p) = 0 := by
      intro p
      have h1 : (inr p : P[ε]) = inl p * (ε : P[ε]) := by
        show _ = inl p * inr (1 : P)
        rw [inl_mul_inr]
        simp
      rw [h1, map_mul, ← mapOfAlgebra_eps (k := k) (P := P), inl_mapOfAlgebra_eq_inr_fst]
      simp
    show s.inl.hom (inl (fst m)) = s.inl.hom m
    calc s.inl.hom (inl (fst m))
        = s.inl.hom (inl (fst m)) + s.inl.hom (inr (snd m)) := by rw [key, add_zero]
      _ = s.inl.hom (inl (fst m) + inr (snd m)) := (map_add _ _ _).symm
      _ = s.inl.hom m := by rw [inl_fst_add_inr_snd_eq]
  · intro s
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    show s.inl.hom (inl (algebraMap k P a)) = s.inr.hom a
    rw [← mapOfAlgebra_inl, inl_mapOfAlgebra_eq_inr_fst, fst_inl]
  · intro s m h₁ _
    refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    have := congrArg (fun q : CommRingCat.of P[ε] ⟶ s.pt ↦ q.hom (inl p : P[ε])) h₁
    simpa [fstHomOf] using this

end Pushout

end DualNumber

end
