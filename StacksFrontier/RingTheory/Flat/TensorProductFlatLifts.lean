module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Flatness of a tensor product along a flat base change and flat lifts of the two factors

Let `R₀ → R'` be a flat ring map, let `A₀` and `C₀` be `R₀`-algebras and let `A'` and `C'` be
`R'`-algebras receiving `A₀` and `C₀` over `R₀`.  If the two lifts `A₀ ⊗_{R₀} R' → A'` and
`C₀ ⊗_{R₀} R' → C'` are flat, then the canonical map

`A₀ ⊗_{R₀} C₀ → A' ⊗_{R'} C'`

is flat.  These are exactly the hypotheses of Stacks 08HW, so a diagram for which that tag
compares the Tor modules also has a flat map between the two tensor-product algebras over which
those Tor modules are modules; that is what makes the comparison usable at a prime of
`A₀ ⊗_{R₀} C₀`.

## Main results

* `RingHom.Flat.tensorProduct_of_flat_lifts`: the canonical map `A₀ ⊗_{R₀} C₀ → A' ⊗_{R'} C'`
  is flat.

## Implementation notes

The map is factored as

`A₀ ⊗_{R₀} C₀ → (A₀ ⊗_{R₀} R') ⊗_{R₀} C₀ ≅ (A₀ ⊗_{R₀} R') ⊗_{R'} (R' ⊗_{R₀} C₀) → A' ⊗_{R'} C'`

whose first and last maps are `Algebra.TensorProduct.map` of two flat maps, so
`RingHom.Flat.tensorProductMap` applies to both, and whose middle map is
`Algebra.TensorProduct.cancelBaseChange`, a ring isomorphism.  The first map changes the left
factor along `A₀ → A₀ ⊗_{R₀} R'`, which is flat because it is the base change of the flat
`R₀ → R'`; the last map changes both factors along the two flat lifts, over the *one* base ring
`R'`.

The symmetric-looking factorisation

`A₀ ⊗_{R₀} C₀ → A' ⊗_{R₀} C₀ → A' ⊗_{R₀} C' → A' ⊗_{R'} C'`

does **not** work: its last map is the base change along `R' ⊗_{R₀} R' → R'`, which is not flat
for a general flat `R₀ → R'` — flatness of that map is a strong condition on `R₀ → R'`, not a
consequence of flatness.  So the regrouping of the base has to be done before the two factors
are changed, which is what the factorisation above does.

The target map is taken as a parameter pinned by its values on pure tensors rather than built
here, because the consumers have it already in the shape produced by
`Algebra.TensorProduct.lift` for two maps into `A' ⊗_{R'} C'` that need not be literally this
file's composite.

## References

* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace RingHom.Flat

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Ring maps out of a tensor product agree when they agree on pure tensors. -/
private theorem ringHom_tensorProduct_ext {R M N S : Type*} [CommRing R] [CommRing M]
    [CommRing N] [CommRing S] [Algebra R M] [Algebra R N] {f g : (M ⊗[R] N) →+* S}
    (h : ∀ m n, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) : f = g :=
  RingHom.ext fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact h m n
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **A tensor product is flat over a flat base change with flat lifts of both factors.**  Let
`R₀ → R'` be flat, let `A₀`, `C₀` be `R₀`-algebras and `A'`, `C'` be `R'`-algebras receiving them
over `R₀` by maps whose lifts `A₀ ⊗_{R₀} R' → A'` and `C₀ ⊗_{R₀} R' → C'` are flat.  Then any
ring map `A₀ ⊗_{R₀} C₀ → A' ⊗_{R'} C'` sending `a ⊗ c` to `fA a ⊗ fC c` is flat.

These are the hypotheses of Stacks 08HW; the conclusion is the flatness of the map of
tensor-product algebras over which the two Tor modules that tag compares are modules. -/
theorem tensorProduct_of_flat_lifts
    {R₀ A₀ C₀ : Type u} {R' A' C' : Type v}
    [CommRing R₀] [CommRing A₀] [CommRing C₀] [CommRing R'] [CommRing A'] [CommRing C']
    [Algebra R₀ A₀] [Algebra R₀ C₀] [Algebra R₀ R'] [Algebra R₀ A'] [Algebra R₀ C']
    [Algebra R' A'] [Algebra R' C'] [IsScalarTower R₀ R' A'] [IsScalarTower R₀ R' C']
    (fA : A₀ →ₐ[R₀] A') (fC : C₀ →ₐ[R₀] C')
    (hR' : RingHom.Flat (algebraMap R₀ R'))
    (hA : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R₀ R' A') fun _ _ => Commute.all _ _).toRingHom)
    (hC : RingHom.Flat (Algebra.TensorProduct.lift fC
      (IsScalarTower.toAlgHom R₀ R' C') fun _ _ => Commute.all _ _).toRingHom)
    (φ : (A₀ ⊗[R₀] C₀) →+* (A' ⊗[R'] C'))
    (hφ : ∀ (a : A₀) (c : C₀), φ (a ⊗ₜ[R₀] c) = fA a ⊗ₜ[R'] fC c) :
    RingHom.Flat φ := by
  have : Module.Flat R₀ R' := RingHom.flat_algebraMap_iff.mp hR'
  -- the `R'`-algebra structures of the two intermediate factors
  let fA₁ : (A₀ ⊗[R₀] R') →ₐ[R'] A' :=
    { Algebra.TensorProduct.lift fA (IsScalarTower.toAlgHom R₀ R' A')
        (fun _ _ => Commute.all _ _) with
      commutes' := fun r => by
        change Algebra.TensorProduct.lift _ _ _ ((1 : A₀) ⊗ₜ[R₀] r) = _
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  let fC₁ : (R' ⊗[R₀] C₀) →ₐ[R'] C' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' C') fC (fun _ _ => Commute.all _ _)
  -- the first map changes the left factor along the flat base change `A₀ → A₀ ⊗_{R₀} R'`
  have hincl : (Algebra.TensorProduct.includeLeft (R := R₀) (S := R₀)
      (A := A₀) (B := R')).Flat := by
    have he : (Algebra.TensorProduct.includeLeft (R := R₀) (S := R₀)
        (A := A₀) (B := R')).toRingHom = algebraMap A₀ (A₀ ⊗[R₀] R') :=
      RingHom.ext fun _ => rfl
    rw [he]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hid : (AlgHom.id R₀ C₀).Flat :=
    RingHom.Flat.of_bijective (f := (AlgHom.id R₀ C₀).toRingHom) Function.bijective_id
  -- the last map changes both factors along the two flat lifts, over the one base ring `R'`
  have hfA₁ : fA₁.Flat := hA
  have hfC₁ : fC₁.Flat := by
    have he : fC₁.toRingHom = (Algebra.TensorProduct.lift fC
        (IsScalarTower.toAlgHom R₀ R' C') fun _ _ => Commute.all _ _).toRingHom.comp
        (Algebra.TensorProduct.comm R₀ R' C₀).toRingHom := by
      refine ringHom_tensorProduct_ext fun r c => ?_
      change (Algebra.ofId R' C') r * fC c = _
      simpa using (mul_comm (algebraMap R' C' r) (fC c))
    rw [he]
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R₀ R' C₀).bijective) hC
  set m₁ : (A₀ ⊗[R₀] C₀) →ₐ[R₀] ((A₀ ⊗[R₀] R') ⊗[R₀] C₀) :=
    Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id R₀ C₀) with hm₁def
  set e : ((A₀ ⊗[R₀] R') ⊗[R₀] C₀) ≃ₐ[R']
      ((A₀ ⊗[R₀] R') ⊗[R'] (R' ⊗[R₀] C₀)) :=
    (Algebra.TensorProduct.cancelBaseChange R₀ R' R' (A₀ ⊗[R₀] R') C₀).symm with hedef
  set m₃ : ((A₀ ⊗[R₀] R') ⊗[R'] (R' ⊗[R₀] C₀)) →ₐ[R'] (A' ⊗[R'] C') :=
    Algebra.TensorProduct.map fA₁ fC₁ with hm₃def
  have hcomp : φ = (m₃.toRingHom.comp e.toRingHom).comp m₁.toRingHom := by
    refine ringHom_tensorProduct_ext fun a c => ?_
    rw [hφ]
    change _ = m₃ (e (m₁ (a ⊗ₜ[R₀] c)))
    rw [hm₁def, hm₃def, hedef]
    rw [Algebra.TensorProduct.map_tmul]
    change _ = Algebra.TensorProduct.map fA₁ fC₁
      ((Algebra.TensorProduct.cancelBaseChange R₀ R' R' (A₀ ⊗[R₀] R') C₀).symm
        ((a ⊗ₜ[R₀] (1 : R')) ⊗ₜ[R₀] c))
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.map_tmul]
    change _ = (fA a * algebraMap R' A' 1) ⊗ₜ[R'] (algebraMap R' C' 1 * fC c)
    simp
  rw [hcomp]
  exact (RingHom.Flat.tensorProductMap hincl hid).comp
    ((RingHom.Flat.of_bijective e.bijective).comp
      (RingHom.Flat.tensorProductMap hfA₁ hfC₁))

end RingHom.Flat

end
