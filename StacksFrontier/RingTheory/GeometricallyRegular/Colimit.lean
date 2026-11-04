module

public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension

@[expose] public section

universe u v w

/-!
# Geometric regularity over a directed colimit of subfields

Let `k` be a field which is the directed union of a nonempty family of subfields `t i`, and let
`A` be a `k`-algebra that is geometrically regular over every `t i`. Then `A` is geometrically
regular over `k`.

## Main results

* `Stacks.GeometricallyRegular.FieldColimit.exists_subalgebra_basis_of_repr_mem`: if a subfield
  `R` of `k` contains the structure constants of a `k`-algebra `K` in a `k`-basis `b`, then the
  `R`-span of `b` is an `R`-subalgebra of `K` with `b` as an `R`-basis.
* `Stacks.GeometricallyRegular.FieldColimit.lift_bijective_of_basis`: multiplication
  `k ⊗[R] B → K` is bijective when an `R`-basis of `B` is carried to a `k`-basis of `K`.
* `Algebra.IsGeometricallyRegular.of_directed_of_iSup_eq_top`: geometric regularity of a
  `k`-algebra over each member of a nonempty directed family of subfields of `k` with supremum
  `⊤` implies geometric regularity over `k`.

## References

* [StacksProject 07QG](https://stacks.math.columbia.edu/tag/07QG)
* [StacksProject 0382](https://stacks.math.columbia.edu/tag/0382)
* [StacksProject 0381](https://stacks.math.columbia.edu/tag/0381)
-/

@[expose] public section

namespace Stacks.GeometricallyRegular.FieldColimit



open scoped TensorProduct

/-- A finite set of elements of the supremum of a nonempty directed family of subfields is
contained in a single member of the family. -/
private theorem exists_subset_of_directed {k : Type u} [Field k] {ι : Type w} [Nonempty ι]
    {t : ι → Subfield k} (dir : Directed (· ≤ ·) t) {s : Set k} (hs : s.Finite)
    (hsub : s ⊆ ↑(⨆ i, t i)) : ∃ i, s ⊆ (t i : Set k) := by
  lift s to Finset k using hs
  rw [Subfield.coe_iSup_of_directed dir] at hsub
  exact Directed.exists_mem_subset_of_finset_subset_biUnion
    dir hsub

/-- An element of a `k`-module all of whose coordinates in a `k`-basis `b` lie in a subfield `R` of
`k` lies in the `R`-span of `b`. -/
theorem mem_span_of_repr_mem {k : Type u} [Field k] (R : Subfield k) {K : Type v}
    [AddCommGroup K] [Module k K] {σ : Type*} (b : Module.Basis σ k K) {x : K}
    (hx : ∀ s, b.repr x s ∈ R) : x ∈ Submodule.span ↥R (Set.range b) := by
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun r _ ↦
    Submodule.smul_mem _ (⟨b.repr x r, hx r⟩ : ↥R) (Submodule.subset_span ⟨r, rfl⟩)

/-- Let `K` be an algebra over a field `k` with a `k`-basis `b`, and let `R` be a subfield of `k`
containing every structure constant `b.repr (b p * b q) r` of the multiplication of `K` and every
coordinate `b.repr 1 r` of its unit. Then the `R`-span of the `b s` inside `K` is an
`R`-subalgebra `B` of `K` which is free with the `b s` as a basis. -/
theorem exists_subalgebra_basis_of_repr_mem {k : Type u} [Field k] (R : Subfield k)
    {K : Type v} [Ring K] [Algebra k K] {σ : Type*} (b : Module.Basis σ k K)
    (hmul : ∀ p q r, b.repr (b p * b q) r ∈ R) (hone : ∀ r, b.repr 1 r ∈ R) :
    ∃ (B : Subalgebra ↥R K) (c : Module.Basis σ ↥R ↥B), ∀ s, (c s : K) = b s := by
  have hli : LinearIndependent ↥R fun s ↦ b s :=
    b.linearIndependent.restrict_scalars fun x y hxy ↦ Subtype.ext (by simpa using hxy)
  have h : Submodule.span ↥R (Set.range b) * Submodule.span ↥R (Set.range b) ≤
      Submodule.span ↥R (Set.range b) := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨x, ⟨p, rfl⟩, y, ⟨q, rfl⟩, rfl⟩
    exact mem_span_of_repr_mem R b (hmul p q)
  exact ⟨(Submodule.span ↥R (Set.range b)).toSubalgebra (mem_span_of_repr_mem R b hone)
    fun _ _ hx hy ↦ h (Submodule.mul_mem_mul hx hy), Module.Basis.span hli,
    fun s ↦ congrArg Subtype.val (Module.Basis.span_apply hli s)⟩

/-- Let `k` be a field which is the directed union of a nonempty family of subfields `t`, and let
`K` be a `k`-algebra with a finite `k`-basis `b`. Then for some member `t i` the `t i`-span of the
`b s` inside `K` is a `t i`-subalgebra `B` of `K` which is free with the `b s` as a basis. -/
private theorem exists_subalgebra_basis_of_directed {k : Type u} [Field k] {ι : Type w} [Nonempty ι]
    {t : ι → Subfield k} (dir : Directed (· ≤ ·) t) (htop : ⨆ i, t i = ⊤) {K : Type v} [Ring K]
    [Algebra k K] {σ : Type*} [Finite σ] (b : Module.Basis σ k K) :
    ∃ (i : ι) (B : Subalgebra ↥(t i) K) (c : Module.Basis σ ↥(t i) ↥B), ∀ s, (c s : K) = b s := by
  obtain ⟨i, hi⟩ := exists_subset_of_directed dir
    (s := Set.range (fun x : σ × σ × σ ↦ b.repr (b x.1 * b x.2.1) x.2.2) ∪
      Set.range fun r : σ => b.repr 1 r)
    ((Set.finite_range _).union (Set.finite_range _)) (by simp [htop])
  rw [Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff] at hi
  exact ⟨i, exists_subalgebra_basis_of_repr_mem (t i) b (fun p q r ↦ hi.1 (p, q, r)) hi.2⟩

/-- Multiplication `k ⊗[R] B → K`, for `B` an `R`-algebra mapping to the `k`-algebra `K` over a
common base ring `R`, is bijective as soon as some `R`-basis of `B` is carried to a `k`-basis of
`K`. -/
theorem lift_bijective_of_basis {R k B K : Type*} [CommRing R] [CommRing k] [CommRing B]
    [CommRing K] [Algebra R k] [Algebra R B] [Algebra k K] [Algebra R K] [IsScalarTower R k K]
    {σ : Type*} (b : Module.Basis σ k K) (f : B →ₐ[R] K) (c : Module.Basis σ R B)
    (hc : ∀ s, f (c s) = b s) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId k K) f
      (fun _ _ => Commute.all _ _) : k ⊗[R] B → K) := by
  have h : ((Algebra.TensorProduct.lift (Algebra.ofId k K) f
        (fun _ _ ↦ Commute.all _ _) : k ⊗[R] B →ₐ[k] K) : (k ⊗[R] B) →ₗ[k] K)
      = ((Algebra.TensorProduct.basis k c).equiv b (Equiv.refl σ) : (k ⊗[R] B) →ₗ[k] K) :=
    (Algebra.TensorProduct.basis k c).ext fun s ↦ by
      simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
      simp [Algebra.TensorProduct.basis_apply, hc]
  have hb := ((Algebra.TensorProduct.basis k c).equiv b (Equiv.refl σ)).bijective
  rwa [← LinearEquiv.coe_coe, ← h] at hb

/-- If `K` is the base change `k ⊗[R] B` of an `R`-algebra `B` and `B ⊗[R] A` is a regular ring,
then `K ⊗[k] A` is a regular ring. -/
private theorem isRegularRing_tensorProduct_of_baseChange {R k B K : Type*} (A : Type*)
    [CommRing R] [CommRing k] [CommRing B] [CommRing K] [CommRing A] [Algebra R k] [Algebra R B]
    [Algebra k K] [Algebra k A] [Algebra R A] [IsScalarTower R k A] (e : k ⊗[R] B ≃ₐ[k] K)
    [IsRegularRing (B ⊗[R] A)] : IsRegularRing (K ⊗[k] A) :=
  IsRegularRing.of_ringEquiv <|
    (Algebra.TensorProduct.comm R B A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R k k A B).symm.trans
        ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans
          (Algebra.TensorProduct.comm k A K))).toRingEquiv

/-- The base change of `A` to a finite extension `K` of `k` is a regular ring, `A` being
geometrically regular over every member of a nonempty directed family of subfields of `k` with
supremum `⊤`. -/
private theorem isRegularRing_tensorProduct_of_finite {k : Type u} {A : Type v} {ι : Type w}
    [Nonempty ι] [Field k] [CommRing A] [Algebra k A] {t : ι → Subfield k}
    (dir : Directed (· ≤ ·) t) (htop : ⨆ i, t i = ⊤)
    [∀ i, Algebra.IsGeometricallyRegular (t i) A] (K : Type u) [Field K] [Algebra k K]
    [Module.Finite k K] : IsRegularRing (K ⊗[k] A) := by
  obtain ⟨i, B, c, hc⟩ := exists_subalgebra_basis_of_directed dir htop (Module.finBasis k K)
  have : Module.Finite ↥(t i) ↥B := .of_basis c
  let : Field ↥B := (isField_of_isIntegral_of_isField' (Field.toIsField ↥(t i))).toField
  have : IsRegularRing (↥B ⊗[↥(t i)] A) :=
    Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct ↥B
  exact isRegularRing_tensorProduct_of_baseChange A
    (AlgEquiv.ofBijective _ (lift_bijective_of_basis (Module.finBasis k K) B.val c hc))

/-- A `k`-algebra that is geometrically regular over every member of a nonempty directed family of
subfields of `k` with supremum `⊤` is geometrically regular over `k`. -/
public theorem solution {k : Type u} {A : Type v} {ι : Type w} [Nonempty ι] [Field k] [CommRing A]
    [Algebra k A] (t : ι → Subfield k) (dir : Directed (· ≤ ·) t) (htop : ⨆ i, t i = ⊤)
    [∀ i, Algebra.IsGeometricallyRegular (t i) A] :
    Algebra.IsGeometricallyRegular k A := by
  exact ⟨fun K _ _ _ ↦
    (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      k A).mpr (fun F _ _ _ _ ↦ isRegularRing_tensorProduct_of_finite dir htop F) K⟩

end Stacks.GeometricallyRegular.FieldColimit

end

@[expose] public section



namespace Algebra

/-- Let `k` be a field, `A` a `k`-algebra, and let `t : ι → Subfield k` be a nonempty directed
family of subfields of `k` with `⨆ i, t i = ⊤`, that is, `k = colim (t i)`. If `A` is
geometrically regular over every `t i`, then `A` is geometrically regular over `k`. -/
@[stacks 07QG "The source's `k = colim k_i` over subfields is a directed family \
  `t : ι → Subfield k` with `⨆ i, t i = ⊤`, equivalently (`Subfield.mem_iSup_of_directed`) every \
  element of `k` lying in some `t i`; `Nonempty ι` is necessary, since for `ι` empty and `k` a \
  prime field the supremum is `⊤` and the hypothesis vacuous. `A` is a `t i`-algebra by \
  restriction of scalars along `t i ↪ k` (`IsScalarTower ↥(t i) k A`), and geometric regularity \
  is `Algebra.IsGeometricallyRegular` (Definition 0382), which already implies the Noetherianness \
  Definition 0382 assumes. See the module docstring."]
public theorem IsGeometricallyRegular.of_directed_of_iSup_eq_top {k : Type u} {A : Type v}
    {ι : Type w} [Nonempty ι] [Field k] [CommRing A] [Algebra k A] (t : ι → Subfield k)
    (dir : Directed (· ≤ ·) t) (htop : ⨆ i, t i = ⊤)
    [∀ i, IsGeometricallyRegular (t i) A] :
    IsGeometricallyRegular k A :=
  Stacks.GeometricallyRegular.FieldColimit.solution t dir htop

end Algebra

end
