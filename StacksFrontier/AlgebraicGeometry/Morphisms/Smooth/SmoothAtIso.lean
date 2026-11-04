module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointGeneralizing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion

/-!
# Smoothness and generic points of fibres across an isomorphism of squares

Let `e : X ≅ X'` and `σ : S ≅ S'` be isomorphisms making
```
X  --e.hom-->  X'
|f               |f'
S  --σ.hom-->  S'
```
commute, that is, with `e.hom ≫ f' = f ≫ σ.hom`.  **Then `f` is smooth at `x` exactly when `f'`
is smooth at `e.hom x`, and `x` is a generic point of an irreducible component of its own fibre
of `f` exactly when `e.hom x` is one of its own fibre of `f'`.**

The case `σ = Iso.refl S` transports the two conditions along an isomorphism of the *source* over
a fixed base, as between the normalization of `X ×_{Spec A} Spec B₁` and that of
`Y₀ ×_{Spec B₀} Spec B₁`; the general case transports them along an isomorphism of the *base* as
well, as between `integralClosure A L₁` and `integralClosure B₀ L₁`, the same subring of `L₁`
presented as two different types.

Smoothness is moved by reading it as membership of the smooth locus
(`Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus`) and then by the smooth locus of a
base change being the preimage of the smooth locus
(`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`), applied to the square
whose horizontal arrows are `e.hom` and `σ.hom` — a cartesian square because both are
isomorphisms, and one whose flatness side condition is discharged by `σ.hom`, an isomorphism
being flat.

The generic-point condition is moved in its ambient form
(`AlgebraicGeometry.mem_genericPoints_asFiber_iff`): a generalization of `e.hom x` in the same
fibre is carried by `e.inv` to a generalization of `x` in the same fibre, the two fibre
conditions matching because `σ.hom` is injective on points.

## Main results

* `InfinitesimalLifting.smoothAt_iso_hom_iff`: smoothness at a point across an isomorphism of
  squares.
* `AlgebraicGeometry.mem_genericPoints_asFiber_iso_hom_iff`: the generic-point condition across
  an isomorphism of squares.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}} (e : X ≅ X') (σ : S ≅ S') (f : X ⟶ S) (f' : X' ⟶ S')
  (he : e.hom ≫ f' = f ≫ σ.hom)

include he

/-- **The smooth locus is carried to the smooth locus by an isomorphism of squares.**  The
square whose horizontal arrows are `e.hom` and `σ.hom` is cartesian, both being isomorphisms, so
the smooth locus of `f` is the preimage of the smooth locus of `f'`. -/
theorem Scheme.Hom.smoothLocus_eq_preimage_of_iso [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation f'] :
    f.smoothLocus = e.hom ⁻¹ᵁ f'.smoothLocus :=
  Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
    (IsPullback.of_horiz_isIso ⟨he⟩) (Or.inr inferInstance)

/-- **Smoothness at a point across an isomorphism of squares.** -/
theorem InfinitesimalLifting.smoothAt_iso_hom_iff [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation f'] (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔ InfinitesimalLifting.SmoothAt f' (e.hom.base x) := by
  rw [show InfinitesimalLifting.SmoothAt f x = Stacks.SmoothAtJacobian.Condition1 f x from rfl,
    show InfinitesimalLifting.SmoothAt f' (e.hom.base x) =
      Stacks.SmoothAtJacobian.Condition1 f' (e.hom.base x) from rfl,
    Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus,
    Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus,
    Scheme.Hom.smoothLocus_eq_preimage_of_iso e σ f f' he]
  exact Iff.rfl

/-- **The generic-point condition on a fibre across an isomorphism of squares.** -/
theorem mem_genericPoints_asFiber_iso_hom_iff (x : X) :
    f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x)) ↔
      f'.asFiber (e.hom.base x) ∈ genericPoints ↥(f'.fiber (f'.base (e.hom.base x))) := by
  have hfx : ∀ z : X, f'.base (e.hom.base z) = σ.hom.base (f.base z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, he]
  have hσinj : Function.Injective σ.hom.base := fun a b hab ↦ by
    have h := congrArg σ.inv.base hab
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, σ.hom_inv_id] at h
  have hinv : ∀ z : X', e.hom.base (e.inv.base z) = z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; simp
  have hinv' : ∀ z : X, e.inv.base (e.hom.base z) = z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; simp
  rw [mem_genericPoints_asFiber_iff, mem_genericPoints_asFiber_iff]
  constructor
  · intro h z hz hfz
    have hz' : e.inv.base z ⤳ x := by
      have hm := hz.map e.inv.continuous
      rwa [hinv'] at hm
    have hfz' : f.base (e.inv.base z) = f.base x := by
      refine hσinj ?_
      rw [← hfx (e.inv.base z), ← hfx x, hinv, hfz]
    calc z = e.hom.base (e.inv.base z) := (hinv z).symm
      _ = e.hom.base x := congrArg _ (h _ hz' hfz')
  · intro h z hz hfz
    have hz' : e.hom.base z ⤳ e.hom.base x := hz.map e.hom.continuous
    have hfz' : f'.base (e.hom.base z) = f'.base (e.hom.base x) := by
      rw [hfx z, hfx x, hfz]
    calc z = e.inv.base (e.hom.base z) := (hinv' z).symm
      _ = e.inv.base (e.hom.base x) := congrArg _ (h _ hz' hfz')
      _ = x := hinv' x

end AlgebraicGeometry

end
