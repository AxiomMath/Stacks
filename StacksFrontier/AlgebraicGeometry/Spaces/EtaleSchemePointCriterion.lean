module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Étaleness of a morphism of algebraic spaces from its scheme-valued base changes

A morphism of algebraic spaces over `S` is étale as soon as every base change of it along a
morphism from a representable algebraic space is étale.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_forall_pullback_yoneda`: the scheme-point criterion.

## Implementation notes

The proof does not go through `AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`, which
needs an fppf `CategoryTheory.MorphismProperty.IsLocalAtTarget` instance for étaleness. It uses
the chart criterion of Stacks 03FS, condition (3): for an atlas `a : h_T ⟶ G` the second
projection of `F ×_G h_T` is the first projection of `h_T ×_G F` precomposed with the symmetry
isomorphism of the two fibre products.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The scheme-point criterion for étaleness of a morphism of algebraic spaces over `S`.** If
the first projection of `h_V ×_G F` is étale for every morphism `h_V ⟶ G` from a representable
algebraic space, then `m : F ⟶ G` is étale. -/
theorem isEtale_of_forall_pullback_yoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (m : F ⟶ G)
    (hpoint : ∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ G),
      IsEtale B S hS (pullback.fst v m)) :
    IsEtale B S hS m := by
  obtain ⟨T, a, hsurj, hetale⟩ := hG.exists_atlas
  rw [isEtale_iff_exists_target_chart B S hS hF hG m]
  refine ⟨T, a, hsurj, hetale, ?_⟩
  have heq : pullback.snd m a = (pullbackSymmetry m a).hom ≫ pullback.fst a m := by simp
  rw [heq]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) (hpoint T a)

end AlgebraicGeometry.Space

end
