module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cartesian square of affine schemes attached to a tensor product

Let `A` be a commutative ring and let `A'` and `B` be `A`-algebras. The square
```
Spec (A' ⊗[A] B) ---→ Spec A'
        |                |
        ↓                ↓
      Spec B  ------→  Spec A
```
whose horizontal arrows are `Spec` of `a' ↦ a' ⊗ₜ 1` and of `b ↦ 1 ⊗ₜ b` and whose vertical
arrows are `Spec` of the two structure maps, is cartesian: the fibre product of two affine
schemes over an affine scheme is the `Spec` of the tensor product of their rings
[Stacks Project, Tag 01JQ]. Consequently flatness of a structure map transfers to the opposite
projection of the square, which is the affine case of the stability of flat morphisms under base
change [Stacks Project, Tag 01U9].

## Main results

* `Stacks.AffineCartesianBaseChange.isPullback_specTensor`: the square above is cartesian, i.e.
  `Spec (A' ⊗[A] B)` is the fibre product `Spec A' ×_{Spec A} Spec B` with the two inclusions of
  the tensor factors as its projections.
* `Stacks.AffineCartesianBaseChange.flat_specMap_includeRight`: if `A'` is a flat `A`-module then
  the projection `Spec (A' ⊗[A] B) ⟶ Spec B` is a flat morphism of schemes.
* `Stacks.AffineCartesianBaseChange.flat_specMap_includeLeft`: if `B` is a flat `A`-module then
  the projection `Spec (A' ⊗[A] B) ⟶ Spec A'` is a flat morphism of schemes.
* `Stacks.AffineCartesianBaseChange.isPushout_appTop`: taking global sections turns the cartesian
  square above into the pushout square of rings presenting `Γ(Spec (A' ⊗[A] B), ⊤)` as the base
  change of `Γ(Spec A', ⊤)` along `Γ(Spec A, ⊤) ⟶ Γ(Spec B, ⊤)`.

## References

* [Stacks Project, Tag 01JQ](https://stacks.math.columbia.edu/tag/01JQ)
* [Stacks Project, Tag 01U9](https://stacks.math.columbia.edu/tag/01U9)
* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open Algebra.TensorProduct CommRingCat

universe u

namespace Stacks.AffineCartesianBaseChange

variable (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]

/-- **The fibre product of affine schemes is the `Spec` of a tensor product**
[Stacks Project, Tag 01JQ]. For `A`-algebras `A'` and `B`, the square
```
Spec (A' ⊗[A] B) ---→ Spec A'
        |                |
        ↓                ↓
      Spec B  ------→  Spec A
```
with horizontal arrows `Spec` of `a' ↦ a' ⊗ₜ 1` and `Spec` of `b ↦ 1 ⊗ₜ b`, and vertical arrows
`Spec` of the structure maps `A ⟶ A'` and `A ⟶ B`, is cartesian. -/
@[ega "I 3.3.13"]
theorem isPullback_specTensor :
    IsPullback (Spec.map (ofHom (S := A' ⊗[A] B) includeLeftRingHom))
      (Spec.map (ofHom (R := B) (S := A' ⊗[A] B) includeRight.toRingHom))
      (Spec.map (ofHom (algebraMap A A'))) (Spec.map (ofHom (algebraMap A B))) :=
  .of_iso_pullback
    ⟨by
      simpa only [← Spec.map_comp] using
        congrArg Spec.map (CommRingCat.isPushout_tensorProduct A A' B).w⟩
    (pullbackSpecIso A A' B).symm (pullbackSpecIso_inv_fst A A' B)
    (pullbackSpecIso_inv_snd A A' B)

/-- `Spec` of the structure map of an `A`-algebra `A'` is a flat morphism of schemes as soon as
`A'` is flat as an `A`-module. -/
theorem flat_specMap_algebraMap [Module.Flat A A'] :
    Flat (Spec.map (ofHom (algebraMap A A'))) :=
  Flat.SpecMap_iff.mpr <| by
    rw [CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A A'›

/-- **Flatness transfers to the opposite projection, first direction.** If `A'` is a flat
`A`-module then `A' ⊗[A] B` is a flat `B`-module, so the projection
`Spec (A' ⊗[A] B) ⟶ Spec B` obtained from `b ↦ 1 ⊗ₜ b` is a flat morphism of schemes. This is
the affine case of [Stacks Project, Tag 01U9]: the morphism in question is the base change of
`Spec A' ⟶ Spec A` along `Spec B ⟶ Spec A`. -/
instance flat_specMap_includeRight [Module.Flat A A'] :
    Flat (Spec.map (ofHom (R := B) (S := A' ⊗[A] B) includeRight.toRingHom)) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_specTensor A A' B)
    (flat_specMap_algebraMap A A')

/-- **Flatness transfers to the opposite projection, second direction.** If `B` is a flat
`A`-module then `A' ⊗[A] B` is a flat `A'`-module, so the projection
`Spec (A' ⊗[A] B) ⟶ Spec A'` obtained from `a' ↦ a' ⊗ₜ 1` is a flat morphism of schemes. This is
the affine case of [Stacks Project, Tag 01U9] with the roles of the two factors exchanged. -/
instance flat_specMap_includeLeft [Module.Flat A B] :
    Flat (Spec.map (ofHom (S := A' ⊗[A] B) includeLeftRingHom)) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_specTensor A A' B).flip
    (flat_specMap_algebraMap A B)

/-- **The cartesian square of affine schemes is a tensor product square on global sections.**
Applying `Γ(-, ⊤)` to the cartesian square of
`Stacks.AffineCartesianBaseChange.isPullback_specTensor` yields a pushout square of commutative
rings, which exhibits `Γ(Spec (A' ⊗[A] B), ⊤)` as the base change of `Γ(Spec A', ⊤)` along
`Γ(Spec A, ⊤) ⟶ Γ(Spec B, ⊤)`. -/
theorem isPushout_appTop :
    IsPushout (Spec.map (ofHom (algebraMap A A'))).appTop
      (Spec.map (ofHom (algebraMap A B))).appTop
      (Spec.map (ofHom (S := A' ⊗[A] B) includeLeftRingHom)).appTop
      (Spec.map (ofHom (R := B) (S := A' ⊗[A] B) includeRight.toRingHom)).appTop :=
  (CommRingCat.isPushout_tensorProduct A A' B).of_iso
    (Scheme.ΓSpecIso (.of A)).symm (Scheme.ΓSpecIso (.of A')).symm
    (Scheme.ΓSpecIso (.of B)).symm (Scheme.ΓSpecIso (.of (A' ⊗[A] B))).symm
    (Scheme.ΓSpecIso_inv_naturality _) (Scheme.ΓSpecIso_inv_naturality _)
    (Scheme.ΓSpecIso_inv_naturality _) (Scheme.ΓSpecIso_inv_naturality _)

end Stacks.AffineCartesianBaseChange
