module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Pseudo-coherent morphisms over a locally Noetherian algebraic space

Over a locally Noetherian target, a morphism of algebraic spaces is pseudo-coherent exactly
when it is locally of finite type.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_iff_isLocallyOfFiniteType`: **Stacks 06BX**,
  the equivalence over a locally Noetherian target.

## Implementation notes

Local Noetherianity of the target is `AlgebraicGeometry.Space.HasEtaleLocalProperty` of
Stacks 03E6 for the scheme property `AlgebraicGeometry.IsLocallyNoetherian`, and
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` of Stacks 03E8 turns it from a
condition on one surjective atlas into a condition on every étale chart of the target. Each
chart of the target is then a locally Noetherian scheme, so the scheme-level equivalence
`AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType` of Stacks 0684 applies to the
induced scheme morphism, which is what both chartwise conditions assert.

Algebraicity of the target is used, through Stacks 03E8; algebraicity of the source is a
hypothesis of the source statement but is not needed for the argument.

## References

* [Stacks Project, Tag 06BX](https://stacks.math.columbia.edu/tag/06BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 06BX.** For a morphism of algebraic spaces over `S` whose target is locally
Noetherian, pseudo-coherence is equivalent to being locally of finite type. -/
@[stacks 06BX, sga "6 III 1.3" "Y loc. noetherian case"]
theorem isPseudoCoherent_iff_isLocallyOfFiniteType (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYNoetherian : HasEtaleLocalProperty B S hS Y
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : X ⟶ Y) :
    IsPseudoCoherent B S hS f ↔ IsLocallyOfFiniteType B S hS f := by
  constructor <;> intro H U V a b h ha hb hc <;>
    let _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
      ((exists_atlas_iff_forall_etale B S hS Y
        (fun T : Scheme.{u} => IsLocallyNoetherian T) hY).mp hYNoetherian) V b hb
  all_goals
    simpa only [_root_.AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType] using
      H U V a b h ha hb hc

end AlgebraicGeometry.Space

end
