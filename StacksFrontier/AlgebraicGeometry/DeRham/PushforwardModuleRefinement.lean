module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiIso
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex

/-!
# The de Rham pushforward in abelian sheaves is the image of its module refinement

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. The canonical map of de Rham complexes
of Section 50.3 of the source exists in two readings:

* `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`, a morphism of complexes of
  **abelian** sheaves on `Y`, which is the one every derived statement about `RΓ` is phrased
  with; and
* `Stacks.DeRhamPullback.deRhamPushforwardChain`, a morphism of complexes of sheaves of
  **`g^{-1}𝒪_S`-modules** on `Y`, built from the same degreewise maps
  `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`.

This file proves that the first **is** the image of the second under the forgetful functor to
abelian sheaves. That is what lets `Stacks.SheafOfModules.quasiIso_toSheaf_map_iff` fire on it,
so that quasi-isomorphy of the abelian reading and of the module reading become the same
question.

## Main results

* `Stacks.DeRhamPullback.deRhamAbelianPushforwardMap_eq_toSheaf_map`: **the abelian de Rham
  pushforward is the forgetful image of `deRhamPushforwardChain`.**
* `Stacks.DeRhamPullback.quasiIso_deRhamAbelianPushforwardMap`: consequently, if
  `deRhamPushforwardChain` is a quasi-isomorphism then so is the abelian reading.

## What this corrects

The module docstring of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceAffineModel` records that
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` "is built degreewise as
`SheafOfModules.toSheaf.map` of `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom` […] but
it is not stated as the image of a morphism of complexes of modules", and treats that as a reason
the locality lemmas for complexes of modules cannot be used on it. The morphism of complexes of
modules does exist — it is `deRhamPushforwardChain` — and the identification below is the
statement that was missing. That docstring is stale on this point.

## Implementation notes

Two facts make this cheap, and they are worth separating because only one of them is about the
de Rham complex.

The functor identity is free: `_root_.pushforward (relativeBase f g) ⋙ toSheaf = toSheaf ⋙`
the abelian direct image, **by `rfl`** — restriction of scalars and the two pushforwards agree on
underlying abelian sheaves on the nose, so the two complexes the two readings land in are the
same object and no transport is needed.

The morphism identity is *not* `rfl`. `deRhamPushforwardChain`'s components carry the factor
`Stacks.DeRhamPullback.pushforwardSquareIso.inv`, which is the identity **on sections**
(`Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app`) but not syntactically the identity.
Asking `exact` to see through it times out at `whnf` — this is the family in which raising
`maxHeartbeats` does not help. So the proof goes degreewise and then on sections, which is
exactly how `deRhamPushforwardChain`'s own `comm'` field is proved.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamPullback

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The abelian de Rham pushforward is the forgetful image of its module refinement.** The
canonical map `Ω^•_{Y/S} ⟶ f_*Ω^•_{X/S}` of complexes of abelian sheaves is the image under
`SheafOfModules.toSheaf` of the map `deRhamPushforwardChain` of complexes of
`g^{-1}𝒪_S`-modules.

Both sides have the same degreewise maps, `deRhamFormsPushforwardHom`; the content is that the
extra factor `pushforwardSquareIso.inv` carried by `deRhamPushforwardChain` does nothing, which
is `pushforwardSquareIso_inv_val_app`. -/
theorem deRhamAbelianPushforwardMap_eq_toSheaf_map (hcomm : f ≫ g = (f ≫ g) ≫ 𝟙 S) :
    Scheme.Hom.deRhamAbelianPushforwardMap f g (f ≫ g) (𝟙 S) hcomm =
      ((_root_.SheafOfModules.toSheaf.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj
                S.sheaf))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (deRhamPushforwardChain f g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  ext U x
  exact (pushforwardSquareIso_inv_val_app f g
    (Scheme.Hom.relativeDifferentialForms (f ≫ g) (n : ℤ)) U
    ((formsPushforwardComponent f g n).val.app U x)).symm

/-- **Quasi-isomorphy of the de Rham pushforward may be checked in sheaves of modules.** If
`deRhamPushforwardChain` is a quasi-isomorphism then so is the canonical map of complexes of
abelian sheaves.

This is `Stacks.SheafOfModules.quasiIso_toSheaf_map_iff` read through the identification above —
the forgetful functor to abelian sheaves preserves homology, so it carries a quasi-isomorphism of
complexes of modules to one of complexes of abelian sheaves. -/
theorem quasiIso_deRhamAbelianPushforwardMap (hcomm : f ≫ g = (f ≫ g) ≫ 𝟙 S)
    (h : QuasiIso (deRhamPushforwardChain f g)) :
    QuasiIso (Scheme.Hom.deRhamAbelianPushforwardMap f g (f ≫ g) (𝟙 S) hcomm) := by
  have := h
  rw [deRhamAbelianPushforwardMap_eq_toSheaf_map f g hcomm]
  exact (Stacks.SheafOfModules.quasiIso_toSheaf_map_iff (deRhamPushforwardChain f g)).2 h

end Stacks.DeRhamPullback

end
