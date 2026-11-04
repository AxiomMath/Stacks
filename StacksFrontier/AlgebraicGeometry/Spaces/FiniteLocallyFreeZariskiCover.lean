module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae

/-!
# Finite local freeness of a morphism of algebraic spaces is Zariski local on the target

Stacks 03ZW lists four equivalent conditions on a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`; the fourth is that there exists a Zariski covering `Y = ⋃ Yᵢ` such that each
`f⁻¹(Yᵢ) ⟶ Yᵢ` is finite locally free.
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal` proves the equivalence of
conditions (1) and (3); this file adds condition (4), for finite local freeness and for finite
local freeness of a fixed rank.

## Main statements

* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_zariskiCover`: **Stacks 03ZW,
  conditions (1) and (4)**, and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_exists_zariskiCover`, its rank
  refinement.

## Implementation notes

Being finite locally free in the sense of condition (1) is Zariski local at the target, and
`AlgebraicGeometry.Space.presheaf_tfae` — Stacks 03M4 for an arbitrary property of scheme
morphisms Zariski local at the target — already carries a Zariski-covering condition in exactly
the shape of condition (4). The two statements below are that theorem instantiated at finite
local freeness and at finite local freeness of rank `r`, whose Zariski locality at the target is
the same instance that condition (3) uses. In particular condition (4) does not go
through the affine-base-change shape, so it needs no effective descent beyond what Stacks 03M4
already asks for.

## References

* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (4): a Zariski covering of the target -/

/-- **Stacks 03ZW, conditions (1) and (4).** A morphism of algebraic spaces over `S` is
representable and finite locally free exactly when there is a Zariski covering `Y = ⋃ Yᵢ` of its
target such that each `f⁻¹(Yᵢ) ⟶ Yᵢ` is.

This is the equivalence the source obtains from the fact that being finite locally free is
Zariski local on the target, which it notes is a weakening of the fpqc locality established
along the way to conditions (1) and (3).  Here it is
`AlgebraicGeometry.Space.presheaf_tfae` — Stacks 03M4 for an arbitrary property of scheme
morphisms Zariski local at the target — instantiated at finite local freeness: the restriction
`f⁻¹(Yᵢ) ⟶ Yᵢ` is read, as the source reads it, as the base change of `f` along the inclusion of
the open subspace `Yᵢ`, and both sides are read in the representable sense of condition (1). -/
@[stacks 03ZW "conditions (1) and (4)"]
theorem isFiniteLocallyFree_presheaf_iff_exists_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, (MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (U i).ι) :=
  (presheaf_tfae B S hS _ inferInstance
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree B S hS) hX hY f).out 1 5

/-- **The rank refinement of Stacks 03ZW, conditions (1) and (4).** A morphism of algebraic
spaces over `S` is representable and finite locally free of rank `r` exactly when there is a
Zariski covering of its target over whose members its base changes are.

Stacks 03ZW states no rank, so this carries no attribute, for the reason recorded on
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_exists_etaleChart`. -/
theorem isFiniteLocallyFreeOfRank_presheaf_iff_exists_zariskiCover (r : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, (MorphismProperty.inverseImage
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (U i).ι) :=
  (presheaf_tfae B S hS _ inferInstance
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank B S hS r) hX hY f).out 1 5

end AlgebraicGeometry.Space

end
