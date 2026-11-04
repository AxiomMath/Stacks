module

public import Mathlib.RingTheory.FiniteStability
public import StacksCore.RingTheory.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs

/-!
# Descent of algebra finiteness along universally injective ring maps

Let `R → S` be a universally injective map of commutative rings. An `R`-algebra is of finite
type, respectively of finite presentation, exactly when its base change to `S` is.

## Main results

* `Algebra.finiteType_iff_tensorProduct`: finite type descends along a universally injective
  ring map and is preserved by base change.
* `Algebra.finitePresentation_iff_baseChange_of_universallyInjective`: the same for finite
  presentation.

## Implementation notes

Finite type is stated for the base change in the source order `A ⊗[R] S`, equipped with its
canonical right-hand `S`-algebra structure, while finite presentation is stated for
`S ⊗[R] A`; the two are interchanged by `Algebra.TensorProduct.commRight` where the proofs
need it. Since `Algebra.TensorProduct.rightAlgebra` is not a global instance, it is enabled
locally here.

Finite type descends because a finite generating set of `A ⊗[R] S` over `S` is a finite sum of
elementary tensors, and the left factors of those tensors generate `A` over `R`: a universally
injective ring map reflects surjections. Finite presentation then descends by reflecting
finite generation of the relation ideal, using that the extension `P → S ⊗[R] P` of a
polynomial ring does not enlarge the contraction of an extended ideal.

## References

* [Stacks Project, Tag 08XE](https://stacks.math.columbia.edu/tag/08XE)
-/

@[expose] public section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Algebra

/-- **Stacks Project, Tag 08XE (finite type).** Finite type descends along a
universally injective ring map and is preserved by base change. -/
@[stacks 08XE "finite_type", ega "IV 1.3.1" "special case"]
theorem finiteType_iff_tensorProduct
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (h : Algebra.UniversallyInjective R S) :
    Algebra.FiniteType R A ↔ Algebra.FiniteType S (A ⊗[R] S) := by
  refine ⟨fun _ ↦ Algebra.FiniteType.equiv (Algebra.FiniteType.baseChange S)
    (Algebra.TensorProduct.commRight R S A), fun _ ↦ ?_⟩
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := S) (A := A ⊗[R] S)
  choose k a t hat using fun x : s => TensorProduct.exists_sum_tmul_eq x.1
  let f : MvPolynomial (Σ x : s, Fin (k x)) R →ₐ[R] A :=
    MvPolynomial.aeval (fun ⟨x, i⟩ ↦ a x i)
  apply Algebra.FiniteType.of_surjective f
  apply reflects_surjections h f.toLinearMap
  let g : S ⊗[R] MvPolynomial (Σ x : s, Fin (k x)) R →ₐ[S] A ⊗[R] S :=
    (Algebra.TensorProduct.commRight R S A).toAlgHom.comp
      (Algebra.TensorProduct.map (.id S S) f)
  have hg : Function.Surjective g := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ (j : Fin (k i)), t i j ⊗ₜ MvPolynomial.X ⟨i, j⟩
    simp [g, f, ← hat, i]
  intro y
  obtain ⟨z, rfl⟩ := hg y
  use TensorProduct.comm R S (MvPolynomial (Σ x : s, Fin (k x)) R) z
  induction z with
  | zero => rfl
  | add x y hx hy => simp_all
  | tmul x y => rfl

/-- The contraction along `P → S ⊗[R] P` of the extension of an ideal `I ⊆ P` is `I` again,
when `R → S` is universally injective. -/
private theorem ideal_comap_map_includeRight
    {R S P : Type u} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P]
    (h : _root_.UniversallyInjective (Algebra.linearMap R S)) (I : Ideal P) :
    Ideal.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P)).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P)).toRingHom I) =
      I := by
  let ι : P →ₐ[R] S ⊗[R] P := Algebra.TensorProduct.includeRight
  refine le_antisymm (fun x hx ↦ ?_) Ideal.le_comap_map
  let k : S ⊗[R] P →ₐ[R] S ⊗[R] (P ⧸ I) :=
    Algebra.TensorProduct.map (AlgHom.id R S) (Ideal.Quotient.mkₐ R I)
  have hzero : k (ι x) = 0 := by
    apply (Ideal.map_le_iff_le_comap.mpr ?_ : Ideal.map ι.toRingHom I ≤
      RingHom.ker k.toRingHom) hx
    intro y hy
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    change (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I y) = 0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply baseChangeUnit_injective h (P ⧸ I)
  rw [map_zero, baseChangeUnit_apply]
  change (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I x) = 0 at hzero
  simpa using congrArg (TensorProduct.comm R S (P ⧸ I)) hzero

/-- An ideal whose extension along a ring map with trivial contraction is finitely generated
is itself finitely generated. -/
private theorem ideal_fg_of_map_fg
    {P T : Type u} [CommRing P] [CommRing T] (f : P →+* T)
    (h : ∀ I : Ideal P, Ideal.comap f (Ideal.map f I) = I) (I : Ideal P)
    (hI : (Ideal.map f I).FG) :
    I.FG := by
  classical
  rcases hI with ⟨t, ht⟩
  have hz (z : {z // z ∈ t}) : z.1 ∈ Submodule.span T (f '' (I : Set P)) := by
    change z.1 ∈ Ideal.map f I
    exact ht ▸ Submodule.subset_span z.2
  choose v hvsub hvspan using fun z => Submodule.mem_span_finite_of_mem_span (hz z)
  let V : Finset T := t.attach.biUnion v
  obtain ⟨U, hUI, hUimage⟩ := Finset.subset_set_image_iff.mp (show
    (V : Set T) ⊆ f '' (I : Set P) from fun w hw ↦ by
      obtain ⟨z, -, hwz⟩ := Finset.mem_biUnion.mp hw
      exact hvsub z hwz)
  refine ⟨U, le_antisymm (Submodule.span_le.mpr hUI) fun x hx ↦ ?_⟩
  have hVle : Ideal.span (V : Set T) ≤ Ideal.map f (Ideal.span (U : Set P)) := by
    rw [Ideal.span_le]
    intro w hw
    rw [← hUimage] at hw
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hw
    exact Ideal.mem_map_of_mem f (Submodule.subset_span hr)
  have htV : Ideal.span (t : Set T) ≤ Ideal.span (V : Set T) := by
    rw [Ideal.span_le]
    intro z hzmem
    exact Submodule.span_mono (fun w hw ↦
      Finset.mem_biUnion.mpr ⟨⟨z, hzmem⟩, Finset.mem_attach _ _, hw⟩) (hvspan ⟨z, hzmem⟩)
  have hle : Ideal.map f I ≤ Ideal.map f (Ideal.span (U : Set P)) := ht ▸ htV.trans hVle
  simpa only [h] using Ideal.mem_comap.mpr (hle (Ideal.mem_map_of_mem f hx))

/-- Finite presentation of an algebra descends and ascends along a universally injective
ring map. -/
@[stacks 08XE "finite_presentation"]
theorem finitePresentation_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FinitePresentation R A ↔
      Algebra.FinitePresentation S (TensorProduct R S A) := by
  refine ⟨fun _ ↦ Algebra.FinitePresentation.baseChange S, fun _ ↦ ?_⟩
  have : Algebra.FinitePresentation S (TensorProduct R A S) :=
    Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight R S A)
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ((finiteType_iff_tensorProduct R S A hRS).mpr inferInstance)
  let P := MvPolynomial (Fin n) R
  let g : TensorProduct R S P →ₐ[S] TensorProduct R S A :=
    Algebra.TensorProduct.map (AlgHom.id S S) f
  have : Algebra.FinitePresentation S (TensorProduct R S P) :=
    Algebra.FinitePresentation.baseChange (R := R) (A := P) S
  have hkerG : (RingHom.ker g.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective g
    (Algebra.TensorProduct.map_surjective (AlgHom.id S S) f Function.surjective_id hf)
  have hkerMap : Ideal.map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P)).toRingHom
      (RingHom.ker f.toRingHom) = RingHom.ker g.toRingHom :=
    (Algebra.TensorProduct.lTensor_ker f hf).symm
  apply Algebra.FinitePresentation.of_surjective hf
  apply ideal_fg_of_map_fg _ (ideal_comap_map_includeRight hRS)
  rwa [hkerMap]

end Algebra

end
