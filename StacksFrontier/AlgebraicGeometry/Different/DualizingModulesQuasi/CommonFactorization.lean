module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A common finite factorization of an algebra

Two factorizations of an algebra `B` over `A` through finite `A`-algebras, one of whose induced
maps on prime spectra is an open immersion, are dominated by a single finite subalgebra of `B`
whose own induced map on spectra is again an open immersion.

## Main results

* `Stacks.Discriminant.exists_finite_subalgebra_dominating`: two finite factorizations, one
  open, admit a common finite open refinement inside the target.

## Implementation notes

A factorization through the resulting subalgebra is recorded by an algebra homomorphism whose
composite with the subalgebra inclusion is the original map. The subalgebra is the join of the
two ranges; that the join still induces an open immersion is proved by exhibiting the square
relating it to the given open factorization as a pullback of spectra, which comes from the
corresponding pushout of rings. The pushout in turn uses that an open immersion of affine
spectra is flat and a ring epimorphism.

## References

* [Stacks Project, Tag 0BT0](https://stacks.math.columbia.edu/tag/0BT0)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w

open AlgebraicGeometry CategoryTheory TensorProduct Algebra.TensorProduct

/-- If `R → T` is a flat epimorphism factoring through `S` with `S → T` injective, then `T` is
the pushout of `S` and `T` over `R`. -/
lemma isPushout_of_flat_of_isEpi_of_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] [Algebra.IsEpi R T] (hS : Function.Injective (algebraMap S T)) :
    Algebra.IsPushout R S T T := by
  let j : S →ₐ[R] T := IsScalarTower.toAlgHom R S T
  let μ : T ⊗[R] T →ₐ[R] T := Algebra.TensorProduct.lmul' R
  have hμ : Function.Injective μ := by
    show Function.Injective (TensorProduct.lift (LinearMap.mul R T))
    exact Algebra.IsEpi.injective_lift_mul
  let F : S ⊗[R] T →ₐ[S] T :=
    Algebra.TensorProduct.lift (Algebra.ofId S T) (AlgHom.id R T) (fun _ _ => Commute.all _ _)
  have hmap : Function.Injective
      (TensorProduct.map j.toLinearMap (LinearMap.id : T →ₗ[R] T)) :=
    TensorProduct.map_injective_of_flat_flat j.toLinearMap (LinearMap.id : T →ₗ[R] T)
      hS Function.injective_id
  have hcomp :
      μ.toLinearMap.comp (TensorProduct.map j.toLinearMap (LinearMap.id : T →ₗ[R] T)) =
        F.toLinearMap.restrictScalars R := by
    ext x y
    simp [μ, F, j]
  have hF : Function.Injective F := by
    intro x y hxy
    apply hmap
    apply hμ
    show (μ.toLinearMap.comp
      (TensorProduct.map j.toLinearMap (LinearMap.id : T →ₗ[R] T))) x =
      (μ.toLinearMap.comp
      (TensorProduct.map j.toLinearMap (LinearMap.id : T →ₗ[R] T))) y
    rw [hcomp]
    simpa using hxy
  have hFsurj : Function.Surjective F := fun b => ⟨1 ⊗ₜ[R] b, by simp [F]⟩
  let e : S ⊗[R] T ≃ₐ[S] T := AlgEquiv.ofBijective F ⟨hF, hFsurj⟩
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  let : Algebra S (S ⊗[R] T) := Algebra.TensorProduct.leftAlgebra
  exact Algebra.IsPushout.of_equiv e (by
    ext b
    show F (1 ⊗ₜ[R] b) = b
    simp [F])

private lemma dominating_open_immersion
    {A : Type u} {B B₁ : Type v}
    [CommRing A] [CommRing B] [CommRing B₁]
    [Algebra A B] [Algebra A B₁]
    (f₁ : B₁ →ₐ[A] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₁.toRingHom))]
    (C : Subalgebra A B)
    (g₁ : B₁ →ₐ[A] C) (hg₁ : C.val.comp g₁ = f₁) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom C.val.toRingHom)) := by
  let : Algebra B₁ B := f₁.toRingHom.toAlgebra
  let : Algebra B₁ C := g₁.toRingHom.toAlgebra
  have : IsScalarTower B₁ C B := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact congrArg (fun f : B₁ →ₐ[A] B => f x) hg₁.symm
  have : Module.Flat B₁ B := by
    show RingHom.Flat f₁.toRingHom
    exact (AlgebraicGeometry.Flat.SpecMap_iff (f := CommRingCat.ofHom f₁.toRingHom)).mp
      inferInstance
  have hepi : CategoryTheory.Epi (CommRingCat.ofHom f₁.toRingHom) := by
    apply (CategoryTheory.op_mono_iff _).mp
    apply (CategoryTheory.Functor.mono_map_iff_mono AlgebraicGeometry.Scheme.Spec _).mp
    show Mono (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom f₁.toRingHom).op)
    rw [AlgebraicGeometry.Scheme.Spec_map]
    exact (inferInstance : Mono (Spec.map (CommRingCat.ofHom f₁.toRingHom)))
  have : Algebra.IsEpi B₁ B := CommRingCat.epi_iff_epi.mp hepi
  have : Algebra.IsPushout B₁ C B B :=
    isPushout_of_flat_of_isEpi_of_injective (fun _ _ h => Subtype.ext h)
  have hpb : IsPullback
      (Spec.map (CommRingCat.ofHom C.val.toRingHom))
      (𝟙 (Spec (CommRingCat.of B)))
      (Spec.map (CommRingCat.ofHom g₁.toRingHom))
      (Spec.map (CommRingCat.ofHom f₁.toRingHom)) := by
    convert isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom f₁.toRingHom)
      (CommRingCat.ofHom C.val.toRingHom) (𝟙 (CommRingCat.of B))
      (CommRingCat.isPushout_of_isPushout B₁ C B B) using 1
    simp
  exact MorphismProperty.of_isPullback hpb.flip inferInstance

/-- An algebra map whose range lies in a subalgebra `C` factors through `C`. -/
private lemma exists_comp_eq_of_range_le {A : Type*} {B B' : Type*}
    [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (f : B' →ₐ[A] B) (C : Subalgebra A B) (h : f.range ≤ C) :
    ∃ g : B' →ₐ[A] C, C.val.comp g = f :=
  ⟨f.codRestrict C fun x => h (f.mem_range_self x), AlgHom.val_comp_codRestrict f C _⟩

/-- Two finite algebra factorizations, the first of which induces an open immersion on spectra,
are dominated by a finite subalgebra inducing an open immersion. -/
@[stacks 0BT0]
lemma exists_finite_subalgebra_dominating
    {A : Type u} {B B₁ : Type v} {B₂ : Type w}
    [CommRing A] [CommRing B] [CommRing B₁] [CommRing B₂]
    [Algebra A B]
    [Algebra A B₁] [Module.Finite A B₁] [Algebra A B₂] [Module.Finite A B₂]
    (f₁ : B₁ →ₐ[A] B) (f₂ : B₂ →ₐ[A] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₁.toRingHom))] :
    ∃ C : Subalgebra A B,
      Module.Finite A C ∧
        IsOpenImmersion (Spec.map (CommRingCat.ofHom C.val.toRingHom)) ∧
          (∃ g₁ : B₁ →ₐ[A] C, C.val.comp g₁ = f₁) ∧
            ∃ g₂ : B₂ →ₐ[A] C, C.val.comp g₂ = f₂ := by
  let C : Subalgebra A B := f₁.range ⊔ f₂.range
  have hfinite₁ : Module.Finite A ↥f₁.range := Module.Finite.range f₁.toLinearMap
  have hfinite₂ : Module.Finite A ↥f₂.range := Module.Finite.range f₂.toLinearMap
  have : Module.Finite A C := Subalgebra.finite_sup f₁.range f₂.range
  obtain ⟨g₁, hg₁⟩ := exists_comp_eq_of_range_le f₁ C le_sup_left
  obtain ⟨g₂, hg₂⟩ := exists_comp_eq_of_range_le f₂ C le_sup_right
  exact ⟨C, inferInstance, dominating_open_immersion f₁ C g₁ hg₁, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩

end Stacks.Discriminant
