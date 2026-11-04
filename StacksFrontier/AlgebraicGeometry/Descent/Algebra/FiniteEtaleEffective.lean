module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SchemeEffective

/-!
# Effective descent of a finite étale algebra along a faithfully flat ring map

Let `R → A` be a faithfully flat ring map, let `B` be an `A`-algebra which is finite and étale
over `A`, and let `θ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B` be a transition isomorphism over `A ⊗[R] A`
satisfying the cocycle condition.  Then the invariant subalgebra `C ⊆ B` of
`Stacks.AlgebraDescent.invariantSubalgebra` is itself finite and étale over `R`.

Finiteness and étaleness are the two properties the descended algebra has to inherit for the
descended scheme `Spec C` to be finite étale over `Spec R`, and both are obtained here at the
level of rings.  That matters because this library does *not* have effective descent of the
morphism property `AlgebraicGeometry.IsFinite` along a faithfully flat covering: that would be
Stacks 02L5, whose only route here
(`Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom`) carries the unproved
hypothesis that `AlgebraicGeometry.IsAffineHom` is fpqc-local at the target.  The descended
object built here is a spectrum by construction, so affineness is free and only
module-finiteness has to descend, which it does: that is
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.

## Main results

* `Stacks.AlgebraDescent.module_finite_of_tensorEquiv` — an `R`-algebra whose base change to `A`
  is a finite `A`-algebra is a finite `R`-algebra.
* `Stacks.AlgebraDescent.etale_of_tensorEquiv` — the same for étaleness.
* `Stacks.AlgebraDescent.exists_finiteEtale_subalgebra_tensorEquiv_of_faithfullyFlat` — **the
  affine case of Stacks 0245 for finite étale algebras**: the invariant subalgebra of a
  transition isomorphism on a finite étale `A`-algebra is a finite étale `R`-algebra whose base
  change along `R → A` is the given algebra, compatibly with the transition.
* `Stacks.AlgebraDescent.exists_finiteEtale_subalgebra_trivialTransition` — the hypotheses are
  satisfiable, so the previous statement is not vacuous.

## Implementation notes

The two descent statements are stated for an arbitrary `R`-algebra `C` together with an
isomorphism `A ⊗[R] C ≃ₐ[A] B`, rather than for the invariant subalgebra, because that is the
form in which `Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat` delivers
its conclusion and the form in which other producers of a descended algebra would.

Both reduce to a Mathlib codescent statement after transporting along the isomorphism:
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and
`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` are stated for `A ⊗[R] C` itself, so
the only step is `Module.Finite.equiv` respectively `Algebra.Etale.of_equiv` along `e.symm`.

Non-vacuity uses the identity covering `R → R` and the canonical transition
`Stacks.SchemeDescent.trivialTransition`, whose three hypotheses are already discharged in
`StacksFrontier.AlgebraicGeometry.Descent.Algebra.SchemeEffective`; the witness algebra is an
arbitrary finite étale `R`-algebra, and the subalgebra produced is then the whole of it.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace Stacks.AlgebraDescent

/-! ### Finiteness and étaleness of a descended algebra -/

section Descend

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Module.FaithfullyFlat R A]

/-- **Module-finiteness descends.**  An `R`-algebra whose base change along the faithfully flat
`R → A` is isomorphic to a finite `A`-algebra is a finite `R`-algebra. -/
theorem module_finite_of_tensorEquiv [Module.Finite A B] (C : Type u) [CommRing C]
    [Algebra R C] (e : (A ⊗[R] C) ≃ₐ[A] B) : Module.Finite R C :=
  have : Module.Finite A (A ⊗[R] C) := Module.Finite.equiv e.symm.toLinearEquiv
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A

/-- **Étaleness descends.**  An `R`-algebra whose base change along the faithfully flat `R → A`
is isomorphic to an étale `A`-algebra is an étale `R`-algebra. -/
theorem etale_of_tensorEquiv [Algebra.Etale A B] (C : Type u) [CommRing C] [Algebra R C]
    (e : (A ⊗[R] C) ≃ₐ[A] B) : Algebra.Etale R C :=
  have : Algebra.Etale A (A ⊗[R] C) := Algebra.Etale.of_equiv e.symm
  Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A

end Descend

/-! ### The affine case of Stacks 0245 for finite étale algebras -/

section Effective

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
  (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)

include hleft hright in
/-- **The affine case of Stacks 0245 for finite étale algebras.**  Along a faithfully flat ring
map `R → A`, a transition isomorphism satisfying the cocycle condition on a finite étale
`A`-algebra `B` descends it to a finite étale `R`-algebra: the invariant subalgebra `C` of `θ`
is finite and étale over `R`, its base change along `R → A` is `B`, and the isomorphism
`A ⊗[R] C ≃ B` is compatible with `θ`. -/
theorem exists_finiteEtale_subalgebra_tensorEquiv_of_faithfullyFlat
    [Module.FaithfullyFlat R A] [Module.Finite A B] [Algebra.Etale A B]
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    ∃ C : Subalgebra R B, Module.Finite R C ∧ Algebra.Etale R C ∧
      (∀ b : B, b ∈ C ↔ θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b) ∧
      ∃ e : (A ⊗[R] C) ≃ₐ[A] B,
        (∀ (a : A) (c : C), e (a ⊗ₜ[R] c) = a • (c : B)) ∧
        ∀ (a b : A) (c : C),
          θ ((e (a ⊗ₜ[R] c)) ⊗ₜ[R] b) = a ⊗ₜ[R] (e (b ⊗ₜ[R] c)) := by
  obtain ⟨C, hmem, e, he, hθ⟩ :=
    exists_subalgebra_tensorEquiv_of_faithfullyFlat R A B θ hleft hright hcoc
  exact ⟨C, module_finite_of_tensorEquiv R A B C e, etale_of_tensorEquiv R A B C e, hmem,
    e, he, hθ⟩

end Effective

/-! ### The descended scheme is finite étale over the base -/

section Geometric

/-- The spectrum of a finite étale algebra is finite étale over the spectrum of the base.

This is where the route taken in this file pays off.  Concluding
`AlgebraicGeometry.IsFinite` of a morphism from its restrictions would need
`MorphismProperty.IsZariskiLocalAtTarget @IsFinite`, which does not synthesize at this Mathlib
pin; here the morphism is `Spec` of an algebra map whose module-finiteness is already known, so
`AlgebraicGeometry.IsFinite.SpecMap_iff` applies directly. -/
theorem isFinite_etale_specMap_algebraMap (R C : Type u) [CommRing R] [CommRing C]
    [Algebra R C] [Module.Finite R C] [Algebra.Etale R C] :
    AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
  refine ⟨?_, ?_⟩
  · rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := R) (B := C)).mpr ‹_›
  · rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact (RingHom.etale_algebraMap (R := R) (S := C)).mpr ‹_›

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
  (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)

include hleft hright in
/-- **The affine case of Stacks 0245 for finite étale morphisms of schemes.**  A transition
isomorphism satisfying the cocycle condition on a finite étale `A`-algebra `B`, along a
faithfully flat `R → A`, descends to a morphism `Spec C ⟶ Spec R` which is finite and étale,
and whose base change along `R → A` is `Spec B`. -/
theorem exists_finiteEtale_spec_tensorEquiv_of_faithfullyFlat
    [Module.FaithfullyFlat R A] [Module.Finite A B] [Algebra.Etale A B]
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    ∃ C : Subalgebra R B,
      AlgebraicGeometry.IsFinite
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
        AlgebraicGeometry.Etale
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
          Nonempty ((A ⊗[R] C) ≃ₐ[A] B) := by
  obtain ⟨C, hfin, het, -, e, -⟩ :=
    exists_finiteEtale_subalgebra_tensorEquiv_of_faithfullyFlat R A B θ hleft hright hcoc
  have := hfin
  have := het
  obtain ⟨h₁, h₂⟩ := isFinite_etale_specMap_algebraMap R C
  exact ⟨C, h₁, h₂, ⟨e⟩⟩

end Geometric

/-! ### The hypotheses are satisfiable -/

section Nonvacuity

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- **The hypotheses of
`Stacks.AlgebraDescent.exists_finiteEtale_subalgebra_tensorEquiv_of_faithfullyFlat` are
satisfiable, so it is not vacuous.**  They all hold for the identity covering `R → R`, an
arbitrary finite étale `R`-algebra `B` and the canonical transition isomorphism
`Stacks.SchemeDescent.trivialTransition`. -/
theorem exists_finiteEtale_subalgebra_trivialTransition [Module.Finite R B]
    [Algebra.Etale R B] :
    ∃ C : Subalgebra R B, Module.Finite R C ∧ Algebra.Etale R C ∧
      (∀ b : B, b ∈ C ↔
        Stacks.SchemeDescent.trivialTransition R B (b ⊗ₜ[R] (1 : R)) = (1 : R) ⊗ₜ[R] b) ∧
      ∃ e : (R ⊗[R] C) ≃ₐ[R] B,
        (∀ (a : R) (c : C), e (a ⊗ₜ[R] c) = a • (c : B)) ∧
        ∀ (a b : R) (c : C),
          Stacks.SchemeDescent.trivialTransition R B ((e (a ⊗ₜ[R] c)) ⊗ₜ[R] b) =
            a ⊗ₜ[R] (e (b ⊗ₜ[R] c)) :=
  exists_finiteEtale_subalgebra_tensorEquiv_of_faithfullyFlat R R B
    (Stacks.SchemeDescent.trivialTransition R B)
    (Stacks.SchemeDescent.trivialTransition_left R B)
    (Stacks.SchemeDescent.trivialTransition_right R B)
    (Stacks.SchemeDescent.trivialTransition_cocycle R B)

end Nonvacuity

end Stacks.AlgebraDescent

end
