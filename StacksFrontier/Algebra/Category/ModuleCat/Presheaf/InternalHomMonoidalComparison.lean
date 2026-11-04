module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Closed
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction

/-!
# The monoidal-closed internal hom of presheaves of modules is the internal Hom of Stacks 03EM

There are two constructions of the internal hom of presheaves of `O`-modules:

* `PresheafOfModules.ihom M N`, the internal hom of the monoidal closed structure
  (`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/MonoidalClosed.lean`), realized as the
  linear sections of `coind M N`, i.e. as a subfunctor of Mathlib's `presheafHom`;
* `Stacks.PresheafOfModules.InternalHom.internalHom O M N`, the internal Hom of Stacks 03EM,
  whose sections over `U` are the morphisms of
  `O|_U`-modules `M|_U ⟶ N|_U` on the slice site `C/U`.

This file identifies them. The identification is not a comparison of the two constructions:
both are internal homs out of `M`, hence right adjoints of tensoring by `M`, so they agree by
uniqueness of adjoints. The two adjunctions have opposite handedness —
Stacks 03EO's `presheafTensorHomAdjunction` is for `- ⊗ M` and Mathlib's `ihom.adjunction` is
for `M ⊗ -` — and reconciling them is the braiding, which presheaves of modules carry.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.tensoringRightIsoTensorLeft`: the braiding, as an
  isomorphism between tensoring on the right and on the left by a fixed presheaf of modules.
* `Stacks.PresheafOfModules.InternalHom.tensorLeftInternalHomAdjunction`: Stacks 03EO's
  adjunction, re-seated so that its left adjoint is `M ⊗ -`.

## Main results

* `Stacks.PresheafOfModules.InternalHom.ihomIsoInternalHomFunctor`: the two internal-hom
  functors out of `M` are isomorphic.
* `Stacks.PresheafOfModules.InternalHom.ihomIsoInternalHom`: the object-level identification
  `PresheafOfModules.ihom M N ≅ internalHom O M N`.

## Implementation notes

The structure presheaf and modules are valued in universe `max u v w`, which contains the
underlying category and may be larger. Both realizations of internal Hom use this same value
universe, as required by the presheaf monoidal structure.

Everything here is formal: no sections are computed, and neither construction is unfolded. The
only inputs are the two adjunctions, the braiding, `Adjunction.ofNatIsoLeft` and
`Adjunction.rightAdjointUniq`.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CategoryTheory.MonoidalClosed

noncomputable section

universe v u w

namespace Stacks.PresheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v w})
variable (M : _root_.PresheafOfModules.{max u v w} (Oforget O))

/-- The braiding of presheaves of modules, as an isomorphism between tensoring on the right by
`M` and tensoring on the left by `M`. -/
def tensoringRightIsoTensorLeft :
    (tensoringRight (_root_.PresheafOfModules.{max u v w} (Oforget O))).obj M ≅ tensorLeft M :=
  NatIso.ofComponents (fun N => β_ N M) (by intros; simp)

/-- **Stacks 03EO, re-seated.** Stacks 03EO exhibits `internalHom O M -` as a right adjoint of
`- ⊗ M`; composing with the braiding exhibits it as a right adjoint of `M ⊗ -`, which is the
handedness of Mathlib's `MonoidalClosed`. -/
def tensorLeftInternalHomAdjunction :
    tensorLeft M ⊣ internalHomSecondFunctor.{v, u, max u v w, u} O M :=
  Adjunction.ofNatIsoLeft (presheafTensorHomAdjunction O M) (tensoringRightIsoTensorLeft O M)

/-- **The two internal homs out of `M` agree.** Both `PresheafOfModules.ihom M` and Stacks
03EM's `internalHom O M -` are right adjoint to `M ⊗ -`, so they are isomorphic as functors. -/
def ihomIsoInternalHomFunctor :
    ihom M ≅ internalHomSecondFunctor.{v, u, max u v w, u} O M :=
  Adjunction.rightAdjointUniq (ihom.adjunction M) (tensorLeftInternalHomAdjunction O M)

/-- **The monoidal-closed internal hom is Stacks 03EM's internal Hom.** The internal hom of the
monoidal closed structure on presheaves of `O`-modules, realized as the linear sections of
`coind M N`, is the internal Hom presheaf of Stacks 03EM, whose sections over `U` are the
morphisms `M|_U ⟶ N|_U` on the slice site. -/
def ihomIsoInternalHom (N : _root_.PresheafOfModules.{max u v w} (Oforget O)) :
    _root_.PresheafOfModules.ihom M N ≅ internalHom O M N :=
  (ihomIsoInternalHomFunctor O M).app N

end Stacks.PresheafOfModules.InternalHom

end

end
