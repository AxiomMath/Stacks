module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChange

/-!
# The twisted inverse image of a morphism which is an isomorphism over an open

Let `g : Z ⟶ X` be a morphism of schemes and let `u : U ⟶ X` be an open immersion over which `g`
is an isomorphism: the square

```
U --u'--> Z
|         |
𝟙         g
v         v
U --u---> X
```

is cartesian. Write `a_g` for the twisted inverse image of `g` ([Stacks, Tag 0A9E]). The map of
[Stacks, Tag 0A9L] for this square is `u'^* ∘ a_g ⟶ a_{𝟙_U} ∘ u^* = u^*`; where it is an
isomorphism, `a_g(K)|_U ≅ K|_U`. Composed with `a_{g ≫ h} ≅ a_g ∘ a_h` this compares the twisted
inverse images of two proper morphisms `Z ⟶ Y`, `X ⟶ Y` related by `g`, over `U`. This is how two
compactifications are compared in the proof of [Stacks, Tag 0AA0].

## Main definitions

* `Stacks.Duality.twistedInverseImageRestrictIsoOfIsPullback` — `a_g(K)|_U ≅ K|_U`, wherever the
  map of [Stacks, Tag 0A9L] is invertible at `K`.
* `Stacks.Duality.twistedInverseImageCompRestrictIsoOfIsPullback` — `a_{g ≫ h}(K)|_U ≅ a_h(K)|_U`,
  wherever that map is invertible at `a_h(K)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {U Z X Y : Scheme.{u}} (g : Z ⟶ X) (u : U ⟶ X) (u' : U ⟶ Z)
  [IsOpenImmersion u] [IsOpenImmersion u'] (sq : IsPullback u' (𝟙 U) g u)
  [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace X] [QuasiSeparatedSpace X]

/-- The map of [Stacks, Tag 0A9L] for a cartesian square along which `g` is the identity of `U`:
`u'^* ∘ a_g ⟶ u^* ∘ a_{𝟙_U}`. -/
abbrev twistedInverseImageRestrictionMapOfIsPullback :=
  OpenImmersion.twistedInverseImageRestrictionMap u' (𝟙 U) g u
    (isQuasicoherent_homology_derivedPushforward_of_qcqs u')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 U))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs u)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict u)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict u') sq

/-- **`a_g(K)|_U ≅ K|_U`** for `g` an isomorphism over the open `U`, wherever the map of
[Stacks, Tag 0A9L] is invertible at `K`: that map ends in `a_{𝟙_U}(K|_U)`, and the twisted
inverse image of the identity is the identity. -/
def twistedInverseImageRestrictIsoOfIsPullback (K : quasiCoherentDerivedCategory X)
    [IsIso ((twistedInverseImageRestrictionMapOfIsPullback g u u' sq).app K)] :
    (OpenImmersion.restrictedDerivedRestrict u').obj
        ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K) ≅
      (OpenImmersion.restrictedDerivedRestrict u).obj K :=
  asIso ((twistedInverseImageRestrictionMapOfIsPullback g u u' sq).app K) ≪≫
    (twistedInverseImageIdIso U _).app _

variable (h : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`a_{g ≫ h}(K)|_U ≅ a_h(K)|_U`** for `g` an isomorphism over the open `U`, wherever the map
of [Stacks, Tag 0A9L] for `g` is invertible at `a_h(K)`: `a_{g ≫ h} ≅ a_g ∘ a_h` by
`Stacks.Duality.twistedInverseImageCompIso`, and then
`Stacks.Duality.twistedInverseImageRestrictIsoOfIsPullback` at `a_h(K)`. -/
def twistedInverseImageCompRestrictIsoOfIsPullback (K : quasiCoherentDerivedCategory Y)
    [IsIso ((twistedInverseImageRestrictionMapOfIsPullback g u u' sq).app
      ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj K))] :
    (OpenImmersion.restrictedDerivedRestrict u').obj
        ((twistedInverseImage (g ≫ h)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ h))).obj K) ≅
      (OpenImmersion.restrictedDerivedRestrict u).obj
        ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj K) :=
  (OpenImmersion.restrictedDerivedRestrict u').mapIso
      ((twistedInverseImageCompIso g h _ _ _).app K) ≪≫
    twistedInverseImageRestrictIsoOfIsPullback g u u' sq _

end Stacks.Duality
