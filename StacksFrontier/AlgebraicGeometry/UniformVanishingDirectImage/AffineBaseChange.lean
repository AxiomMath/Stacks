module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# Affine opens over an affine open stay affine when cut down by the base

Let `f : X ⟶ S` be a morphism of schemes and let `S₀ ⊆ S` be an affine open. If `A ⊆ f⁻¹(S₀)` is
an affine open of `X` and `V ⊆ S₀` is an affine open of `S`, then `A ∩ f⁻¹(V)` is again affine:
it is `A ×_{S₀} V`, a fibre product of affine schemes.

## Main results

* `AlgebraicGeometry.isAffineOpen_inf_preimage_of_le`: the affineness above.
* `AlgebraicGeometry.Scheme.Hom.finsetInf_preimage`: taking preimages commutes with nonempty
  finite intersections of opens.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Taking preimages of opens commutes with nonempty finite intersections. -/
theorem Scheme.Hom.finsetInf_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*}
    (U : ι → Y.Opens) {s : Finset ι} (hs : s.Nonempty) :
    s.inf (fun i ↦ f ⁻¹ᵁ U i) = f ⁻¹ᵁ s.inf U := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
      rw [Finset.inf_cons, Finset.inf_cons, ih, Scheme.Hom.preimage_inf]

/-- **An affine open lying over an affine open of the base meets the preimage of an affine open
of that base in an affine open.** If `S₀` and `V ≤ S₀` are affine opens of `S` and `A` is an
affine open of `X` with `A ≤ f⁻¹(S₀)`, then `A ⊓ f⁻¹(V)` is an affine open of `X`. -/
theorem isAffineOpen_inf_preimage_of_le {X S : Scheme.{u}} (f : X ⟶ S) {S₀ V : S.Opens}
    {A : X.Opens} (hS₀ : IsAffineOpen S₀) (hV : IsAffineOpen V) (hA : IsAffineOpen A)
    (hVS₀ : V ≤ S₀) (hAS₀ : A ≤ f ⁻¹ᵁ S₀) :
    IsAffineOpen (A ⊓ f ⁻¹ᵁ V) := by
  have : IsAffine A.toScheme := hA
  have : IsAffine S₀.toScheme := hS₀
  have hV' : IsAffineOpen (S₀.ι ⁻¹ᵁ V) :=
    hV.preimage_of_isOpenImmersion S₀.ι (by simpa using hVS₀)
  have heq : f.resLE S₀ A hAS₀ ⁻¹ᵁ (S₀.ι ⁻¹ᵁ V) = A.ι ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
  have hpre : IsAffineOpen (A.ι ⁻¹ᵁ (f ⁻¹ᵁ V)) := heq ▸ hV'.preimage (f.resLE S₀ A hAS₀)
  rw [← Scheme.Opens.opensRange_ι A, ← Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact hpre.image_of_isOpenImmersion A.ι

end AlgebraicGeometry
