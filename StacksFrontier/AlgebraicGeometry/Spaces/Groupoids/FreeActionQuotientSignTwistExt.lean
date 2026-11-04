module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientSignTwist
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistExt

/-!
# The derived form of Stacks 0727 for the quotient of an object of a big fppf site

Let a group `G` act freely on an object `V` of a big fppf site over a scheme `S`, let `U = V/G`
be the quotient algebraic space and let `χ : G → {±1}` be a character.  The chart `h_V ⟶ U` is a
`G`-torsor over the final object of the spaces-étale site of `U`, so the identification of
`Ext` out of the twist `ℤ(χ)` with the cohomology of the twisted coefficients,
`CategoryTheory.IsTorsorObject.characterTwistExtAddEquiv`, applies to it in every degree.

This file reads that statement off at the geometric situation, which is the derived form of
`AlgebraicGeometry.Space.freeActionChartSectionsEquiv`: that identification is the degree-zero
case, the global sections of `ℱ ⊗_ℤ ℤ(χ)` being `Ext⁰(ℤ(χ), ℱ)`.

## Main results

* `AlgebraicGeometry.Space.freeActionChartExtAddEquiv`: `Ext^q(ℤ(χ), ℱ) ≅ H^q(U, ℱ ⊗_ℤ ℤ(χ))`
  for every `q`, for the quotient of an object of a big fppf site by a free action.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) (χ : G →* ℤˣ)

/-- **The derived form of [Stacks, Tag 0727] for the quotient of an object of a big fppf site by
a free action.**  For every degree `q`, the `Ext`-group out of the twist `ℤ(χ)` attached to the
chart `h_V` with coefficients in an abelian sheaf `ℱ` on the spaces-étale site of `U = V/G` is
the degree-`q` cohomology of the twisted coefficients `ℱ ⊗_ℤ ℤ(χ)`.

Degree zero is `AlgebraicGeometry.Space.freeActionChartSectionsEquiv`.  The general case is
`CategoryTheory.IsTorsorObject.characterTwistExtAddEquiv` at the torsor
`AlgebraicGeometry.Space.isTorsorObject_freeActionChartAut`. -/
def freeActionChartExtAddEquiv
    (F : Sheaf (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))
      AddCommGrpCat.{u + 1}) (q : ℕ) :
    Abelian.Ext.{u + 1}
        (characterTwist (freeActionQuotientChart G B S hS V a ha)
          (freeActionChartAut G B S hS V a ha) χ
          (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))) F q ≃+
      Sheaf.H.{u + 1, u + 1}
        (characterTwistTensor F.obj (freeActionChartAut G B S hS V a ha) χ
          (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))) q :=
  (isTorsorObject_freeActionChartAut G B S hS V a ha).characterTwistExtAddEquiv χ F q

end AlgebraicGeometry.Space

end
