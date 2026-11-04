module

public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
public import StacksFrontier.RingTheory.Unramified.ThickeningDerivationExtension

/-!
# Universal first-order thickenings of affine schemes, on global sections

Let `i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X` be a universal first-order thickening of
`h : Z ⟶ X`.  When the three schemes are affine, the comorphism of `h'` on global sections is a
universal first order thickening of rings, with ideal the kernel of the comorphism of `i`.  The
universal property also transports along an isomorphism of the ambient scheme.

## Main results

* `Stacks.Thickenings.isUniversalFirstOrderThickening_appTop`: on affine schemes a universal
  first-order thickening is one of rings on global sections, in the sense of
  `RingHom.IsUniversalFirstOrderThickening`.
* `Stacks.Thickenings.IsUniversalFirstOrderThickening.of_iso`: the universal property transports
  along an isomorphism of the ambient scheme.

## References

* [Stacks Project, Tag 04EW](https://stacks.math.columbia.edu/tag/04EW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-- **A universal first-order thickening of affine schemes is one of rings, on global
sections.**  Let `i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X` be a universal first-order
thickening of `h : Z ⟶ X`, all three schemes being affine.  Then the comorphism of `h'` on global
sections is a universal first-order thickening, with ideal the kernel of the comorphism of `i`,
in the sense of `RingHom.IsUniversalFirstOrderThickening`. -/
theorem isUniversalFirstOrderThickening_appTop {Z X Z' : Scheme.{u}}
    {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h')
    [IsAffine Z] [IsAffine X] [IsAffine Z'] :
    h'.appTop.hom.IsUniversalFirstOrderThickening (RingHom.ker i.appTop.hom) := by
  let : Algebra Γ(X, ⊤) Γ(Z', ⊤) := h'.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := h.appTop.hom.toAlgebra
  let : Algebra Γ(Z', ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
  have hcomp : i.appTop.hom.comp h'.appTop.hom = h.appTop.hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hi.inclusion_toBase]
  have : IsScalarTower Γ(X, ⊤) Γ(Z', ⊤) Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : IsClosedImmersion i := hi.isFirstOrderThickening.1
  have hsurj : Function.Surjective (algebraMap Γ(Z', ⊤) Γ(Z, ⊤)) :=
    i.app_surjective ⊤ (isAffineOpen_top Z')
  exact RingHom.IsUniversalFirstOrderThickening.of_ofSurjective rfl
    (IsScalarTower.toAlgHom Γ(X, ⊤) Γ(Z', ⊤) Γ(Z, ⊤)) hsurj rfl
    (isUniversalFirstOrderThickening_ofSurjective_appTop hi rfl rfl rfl hsurj)

/-- **A universal first-order thickening transports along an isomorphism of the ambient
scheme.** -/
theorem IsUniversalFirstOrderThickening.of_iso {Z X Z' Z'' : Scheme.{u}} {h : Z ⟶ X}
    {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h') (e : Z' ≅ Z'')
    {i'' : Z ⟶ Z''} {h'' : Z'' ⟶ X} (hi'' : i ≫ e.hom = i'') (hh'' : e.hom ≫ h'' = h')
    (hfirst : IsFirstOrderThickening i'') : IsUniversalFirstOrderThickening h i'' h'' := by
  refine ⟨hfirst, ?_, ?_⟩
  · rw [← hi'', Category.assoc, hh'', hi.inclusion_toBase]
  · intro T T' j hj a b hab
    obtain ⟨c, hc, hcu⟩ := hi.existsUnique_lift j hj a b hab
    refine ⟨c ≫ e.hom, ⟨?_, ?_⟩, fun k hk => ?_⟩
    · rw [← Category.assoc, hc.1, Category.assoc, hi'']
    · rw [Category.assoc, hh'', hc.2]
    · have := hcu (k ≫ e.inv) ⟨?_, ?_⟩
      · rw [← this, Category.assoc, e.inv_hom_id, Category.comp_id]
      · rw [← Category.assoc, hk.1, Category.assoc, ← hi'', Category.assoc, e.hom_inv_id,
          Category.comp_id]
      · rw [Category.assoc, ← hh'', ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
          hk.2]

end Stacks.Thickenings

end
