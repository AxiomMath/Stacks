module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs

/-!
# Multiplicity of a finite-length two-periodic complex

The multiplicity of a two-periodic complex whose two terms have finite length is the
difference of the lengths of those terms. In particular, it vanishes when the two terms are
isomorphic. For a `(2, 1)`-periodic complex whose first map vanishes, the multiplicity is the
length of the cokernel of the second map minus the length of its kernel.

## Main results

* `AlgebraicGeometry.periodicLength_eq_length_sub_length` computes the multiplicity from the
  lengths of the two terms.
* `AlgebraicGeometry.periodicLength_eq_zero_of_iso` gives the corresponding vanishing result
  when the two terms are isomorphic.
* `AlgebraicGeometry.periodicLength_zero_eq_length_quotient_sub_length_ker` computes the
  multiplicity of a `(2, 1)`-periodic complex with vanishing first map.

## Implementation notes

`AlgebraicGeometry.periodicLength_eq_zero_of_iso` states the `(2, 1)`-periodic case with the two
terms isomorphic rather than definitionally equal.

A two-periodic complex over a ring is a `CochainComplex` indexed by `ZMod 2`, its cohomology
modules are `HomologicalComplex.homology` in the two degrees, and exactness is
`HomologicalComplex.Acyclic`; a `(2, 1)`-periodic complex is
`AlgebraicGeometry.twoPeriodicComplex`. The last result needs no finiteness hypothesis: the two
cohomology modules are isomorphic to the cokernel and the kernel of the second map, so the
lengths agree in `ℕ∞` before `ENat.toNat` is applied.

## References

* [Stacks Project, Tag 02PG](https://stacks.math.columbia.edu/tag/02PG)
* [Stacks Project, Tag 0EA6](https://stacks.math.columbia.edu/tag/0EA6)
* [Stacks Project, Tag 0EA8](https://stacks.math.columbia.edu/tag/0EA8)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The length of a module is the sum of the lengths of the kernel and of the range of any
linear map out of it. -/
private lemma length_eq_ker_add_range {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Module.length R M =
      Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
  Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by simp))

/-- Corestricting a linear map to a submodule containing its image does not change its
range, up to the evident isomorphism. -/
private noncomputable def rangeCodRestrictEquiv {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (P : Submodule R N) (h : ∀ x, f x ∈ P) :
    LinearMap.range (f.codRestrict P h) ≃ₗ[R] LinearMap.range f where
  toFun x := ⟨x.1.1, by
    obtain ⟨y, hy⟩ := x.2; exact ⟨y, congr_arg Subtype.val hy⟩⟩
  invFun x := ⟨⟨x.1, by
    obtain ⟨y, hy⟩ := x.2; rw [← hy]; exact h y⟩, by
    obtain ⟨y, hy⟩ := x.2; exact ⟨y, Subtype.ext hy⟩⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In a two-periodic complex, the length of the cohomology in a degree plus the length of the
range of the incoming differential is the length of the kernel of the outgoing one. -/
private lemma length_homology_add_length_range_eq_length_ker
    {R : Type u} [Ring R]
    (C : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)))
    (i j : ZMod 2) (hji : (ComplexShape.up (ZMod 2)).prev i = j) :
    Module.length R (C.homology i) + Module.length R (LinearMap.range (C.d j i).hom) =
      Module.length R (LinearMap.ker (C.d i ((ComplexShape.up (ZMod 2)).next i)).hom) := by
  let S := C.sc i
  let K := LinearMap.ker S.g.hom
  let I := LinearMap.range S.moduleCatToCycles
  have hlen : Module.length R K = Module.length R I + Module.length R (K ⧸ I) :=
    Module.length_eq_add_of_exact I.subtype I.mkQ (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_iff.mpr (by simp))
  have hH : Module.length R (C.homology i) = Module.length R (K ⧸ I) :=
    S.moduleCatHomologyIso.toLinearEquiv.length_eq
  have hI : Module.length R I = Module.length R (LinearMap.range (C.d j i).hom) := by
    change Module.length R (LinearMap.range S.moduleCatToCycles) = _
    rw [(rangeCodRestrictEquiv S.f.hom (LinearMap.ker S.g.hom)
      S.moduleCat_zero_apply).length_eq]
    subst j; rfl
  rw [hH, ← hI, add_comm, ← hlen]
  change Module.length R (LinearMap.ker (C.d i _).hom) = _; rfl

/-- If `a + b = c` in `ℕ∞` with `c` finite, then `a` is finite and `toNat` is additive. -/
private lemma toNat_add_of_add_eq {a b c : ℕ∞} (h : a + b = c) (hc : c ≠ ⊤) :
    a ≠ ⊤ ∧ a.toNat + b.toNat = c.toNat := by
  subst h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hc le_self_add
  exact ⟨ha, (ENat.toNat_add ha (ne_top_of_le_ne_top hc le_add_self)).symm⟩

/-- The multiplicity of a two-periodic complex of finite-length modules is the difference of
the lengths of its two terms. -/
@[stacks 0EA8 "the length formula"]
public lemma periodicLength_eq_length_sub_length {R : Type u} [Ring R]
    (C : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)))
    (h₀ : IsFiniteLength R (C.X (0 : ZMod 2)))
    (h₁ : IsFiniteLength R (C.X (1 : ZMod 2))) :
    periodicLength C =
      ((Module.length R (C.X (0 : ZMod 2))).toNat : ℤ) -
        ((Module.length R (C.X (1 : ZMod 2))).toNat : ℤ) := by
  let f₀ := (C.d (0 : ZMod 2) (1 : ZMod 2)).hom
  let f₁ := (C.d (1 : ZMod 2) (0 : ZMod 2)).hom
  have hterm₀ := length_eq_ker_add_range f₀
  have hterm₁ := length_eq_ker_add_range f₁
  have hhom₀ := length_homology_add_length_range_eq_length_ker C
    (0 : ZMod 2) (1 : ZMod 2) (by simp [CochainComplex.prev])
  have hhom₁ := length_homology_add_length_range_eq_length_ker C
    (1 : ZMod 2) (0 : ZMod 2) (by simp [CochainComplex.prev])
  rw [show (ComplexShape.up (ZMod 2)).next (0 : ZMod 2) = 1 by
    simp [CochainComplex.next]] at hhom₀
  rw [show (ComplexShape.up (ZMod 2)).next (1 : ZMod 2) = 0 by
    rw [CochainComplex.next]; decide] at hhom₁
  change ((Module.length R (C.homology 0)).toNat : ℤ) -
    ((Module.length R (C.homology 1)).toNat : ℤ) = _
  change Module.length R (C.homology 0) + Module.length R (LinearMap.range f₁) =
    Module.length R (LinearMap.ker f₀) at hhom₀
  change Module.length R (C.homology 1) + Module.length R (LinearMap.range f₀) =
    Module.length R (LinearMap.ker f₁) at hhom₁
  have hx₀ : Module.length R (C.X 0) ≠ ⊤ := Module.length_ne_top_iff.mpr h₀
  have hx₁ : Module.length R (C.X 1) ≠ ⊤ := Module.length_ne_top_iff.mpr h₁
  obtain ⟨hk₀, hnterm₀⟩ := toNat_add_of_add_eq hterm₀.symm hx₀
  obtain ⟨hk₁, hnterm₁⟩ := toNat_add_of_add_eq hterm₁.symm hx₁
  have hnhom₀ := (toNat_add_of_add_eq hhom₀ hk₀).2
  have hnhom₁ := (toNat_add_of_add_eq hhom₁ hk₁).2
  lia

/-- The multiplicity of a finite-length two-periodic complex with isomorphic terms vanishes. -/
@[stacks 0EA8 "the (2, 1)-periodic case"]
public lemma periodicLength_eq_zero_of_iso {R : Type u} [Ring R]
    (C : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)))
    (hfin : IsFiniteLength R (C.X (0 : ZMod 2)))
    (e : C.X (0 : ZMod 2) ≅ C.X (1 : ZMod 2)) :
    periodicLength C = 0 := by
  have hfin₁ : IsFiniteLength R (C.X (1 : ZMod 2)) :=
    Module.length_ne_top_iff.mp (by
      rw [← e.toLinearEquiv.length_eq]
      exact Module.length_ne_top_iff.mpr hfin)
  rw [periodicLength_eq_length_sub_length C hfin hfin₁]
  simp [← e.toLinearEquiv.length_eq]

/-- In the `(2, 1)`-periodic complex of a module with maps `0` and `ψ`, the degree-zero
cohomology has the length of the cokernel of `ψ`. -/
private lemma length_homology_zero_eq_length_quotient {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] (ψ : Module.End R M) :
    Module.length R
        ((twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)).homology
          (0 : ZMod 2)) =
      Module.length R (M ⧸ LinearMap.range ψ) := by
  have h := homology_length_eq_ker_quotient (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)
    (0 : ZMod 2) (Or.inl rfl)
  rw [ite_eq_left rfl] at h
  rw [h]
  exact quotient_length_of_bijective_map (LinearMap.ker (0 : Module.End R M)).subtype
    (fun y => ⟨⟨y, by simp⟩, rfl⟩) (LinearMap.range ψ)

/-- In the `(2, 1)`-periodic complex of a module with maps `0` and `ψ`, the degree-one
cohomology has the length of the kernel of `ψ`. -/
private lemma length_homology_one_eq_length_ker {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] (ψ : Module.End R M) :
    Module.length R
        ((twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)).homology
          (1 : ZMod 2)) =
      Module.length R (LinearMap.ker ψ) := by
  have h := homology_length_eq_ker_quotient (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)
    (1 : ZMod 2) (Or.inr rfl)
  rw [ite_eq_right (by decide : ¬((1 : ZMod 2) = 0))] at h
  rw [h]
  exact (Submodule.quotEquivOfEqBot _ (by simp)).length_eq

/-- The additive Herbrand quotient of a `(2, 1)`-periodic complex whose first map is zero is the
length of the cokernel of its second map minus the length of the kernel of that map. -/
@[stacks 0EA6]
public lemma periodicLength_zero_eq_length_quotient_sub_length_ker {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] (ψ : Module.End R M) :
    periodicLength (twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)) =
      ((Module.length R (M ⧸ LinearMap.range ψ)).toNat : ℤ) -
        ((Module.length R (LinearMap.ker ψ)).toNat : ℤ) := by
  change ((Module.length R
      ((twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)).homology
        (0 : ZMod 2))).toNat : ℤ) -
      ((Module.length R
        ((twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)).homology
          (1 : ZMod 2))).toNat : ℤ) = _
  rw [length_homology_zero_eq_length_quotient, length_homology_one_eq_length_ker]

end AlgebraicGeometry

add_to_stacks 02PG "part (1): 2-periodic complexes" CochainComplex
add_to_sga "2 VIII 1.2" CochainComplex
add_to_sga "4 XVII 2.2.7" "special case" CochainComplex
add_to_sga "4 XVII 5.5.3" CochainComplex
add_to_sga "4½ Etat_0 1.2.1" CochainComplex
add_to_sga "6 I 1.1.5" CochainComplex
add_to_ega "0 11.2.1" CochainComplex
add_to_ega "0 13.2.3" CochainComplex
add_to_ega "III 6.2.1" CochainComplex
add_to_stacks 02PG "part (1): cohomology modules" HomologicalComplex.homology
add_to_ega "0 11.2.1" HomologicalComplex.homology
add_to_ega "0 11.3.1" "more general" HomologicalComplex.homology
add_to_ega "0 11.3.5" HomologicalComplex.homology
add_to_ega "III 7.6.11" HomologicalComplex.homology
add_to_stacks 02PG "part (1): vanishing of cohomology in a degree" HomologicalComplex.ExactAt
add_to_stacks 02PG "part (1): exactness" HomologicalComplex.Acyclic
add_to_stacks 02PG "part (2): (2, 1)-periodic complexes" AlgebraicGeometry.twoPeriodicComplex
