module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of the base change of an affine morphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `g` affine.  Then `g'` is affine as well, and the
inverse image along `f` of the direct image `g_*𝒪_{S'}` is the direct image `g'_*𝒪_{X'}`:

`f^*(g_*𝒪_{S'}) ≅ g'_*𝒪_{X'}`.

This is the affine base-change isomorphism of [Stacks, Tag 02KG] at the structure sheaf of `S'`.

## Main results

* `AlgebraicGeometry.pullbackPushforwardUnitIso` is the isomorphism above.
* `AlgebraicGeometry.isQuasicoherent_pushforward_unitObj`: the direct image of the structure
  sheaf along an affine morphism is quasi-coherent.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineBaseChange

universe u

namespace AlgebraicGeometry

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The structure sheaf of a scheme is quasi-coherent. -/
instance isQuasicoherent_unitObj (Z : Scheme.{u}) : (unitObj Z).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z

/-- The direct image of the structure sheaf along an affine morphism of schemes is
quasi-coherent. -/
instance isQuasicoherent_pushforward_unitObj (h : S' ⟶ S) [IsAffineHom h] :
    ((Scheme.Modules.pushforward h).obj (unitObj S')).IsQuasicoherent :=
  inferInstance

/-- In a Cartesian square of schemes, the base change `g'` of an affine morphism `g` is
affine. -/
theorem isAffineHom_of_isPullback_right (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    IsAffineHom g' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance

/-- For a Cartesian square of schemes whose bottom arrow `g` is affine, the inverse image along
`f` of `g_*𝒪_{S'}` is `g'_*𝒪_{X'}` ([Stacks, Tag 02KG] at the structure sheaf). -/
@[ega "II 1.5.5" "partial"]
def pullbackPushforwardUnitIso (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward g).obj (unitObj S')) ≅
      (Scheme.Modules.pushforward g').obj (unitObj X') :=
  haveI : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      hsq.flip.w).app (unitObj S')) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      hsq.flip (unitObj S')
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      hsq.flip.w).app (unitObj S')) ≪≫
    (Scheme.Modules.pushforward g').mapIso (pullbackUnitIso f')

/-- The forward map of `AlgebraicGeometry.pullbackPushforwardUnitIso` is the affine base-change
morphism at `𝒪_{S'}` followed by the direct image of `pullbackUnitIso f'`. -/
theorem pullbackPushforwardUnitIso_hom (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    (pullbackPushforwardUnitIso hsq).hom =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
          hsq.flip.w).app (unitObj S') ≫
        (Scheme.Modules.pushforward g').map (pullbackUnitIso f').hom :=
  rfl

end AlgebraicGeometry

end
