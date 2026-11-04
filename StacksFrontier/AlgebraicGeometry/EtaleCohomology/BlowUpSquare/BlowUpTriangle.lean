module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.FiniteTypeCentre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.Triangle

/-!
# The Mayer–Vietoris triangle of a blowup square

Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal `I` of
finite type, with blowup square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
and `c = i ∘ π = b ∘ j`. For `K ∈ D⁺(X_étale)` with torsion cohomology sheaves there is a
distinguished triangle
`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K[1]`
in `D(X_étale)`. This is Stacks Tag 0EW5.

## Main results

* `AlgebraicGeometry.exists_distTriang_blowUp`: the distinguished triangle (Stacks 0EW5).

## Implementation notes

This is
`Stacks.EtaleCohomology.exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange`
(the Mayer–Vietoris triangle of a cartesian square that is an isomorphism off a closed
subscheme, for a morphism along which cohomology commutes with base change) applied to the
blowup square: it is cartesian (`AlgebraicGeometry.isPullback_exceptionalDivisor`), the blowup
morphism is an isomorphism over `X \ Z` (Stacks 02OS,
`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`), and since `I` is of finite type
the blowup morphism is proper, so cohomology of torsion sheaves commutes with base change along
it by the proper base change theorem
(`AlgebraicGeometry.cohomologyCommutesWithBaseChange_blowUpToBase_of_fg`, Stacks 0A3U). The
derived form of proper base change used in the source (Stacks 0DDE) is applied inside the general
triangle.

## References

* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EW5.** Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by
a quasi-coherent ideal `I` of finite type (finitely generated on every affine open), with blowup
square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
(`X'` the blowup of `X` in `I`, `E = b⁻¹(Z)` the exceptional divisor) and `c = i ∘ π = b ∘ j`.
For every `K` in `D⁺(X_étale)` (a complex of abelian sheaves on the small étale site, bounded
below: `K.IsGE n`) with torsion cohomology sheaves there is a distinguished triangle
`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K[1]`
in `D(X_étale)`, where `K|_Y` is the derived inverse image. Its first map is formed by the two
adjunction units and its second map is the difference of the two comparison maps
`Ri_*(K|_Z) ⟶ Rc_*(K|_E)` (along `c = i ∘ π`) and `Rb_*(K|_{X'}) ⟶ Rc_*(K|_E)` (along
`c = b ∘ j`). -/
@[stacks 0EW5]
public theorem exists_distTriang_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology K) :
    ∃ δ : (etaleAbelianDerivedDirectImage.{u, 0}
          ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I)).obj
        ((etaleAbelianDerivedInverseImage.{u, 0}
          ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I)).obj K) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk (etaleAbelianDerivedSquareUnits.{u, 0} I.subschemeι (blowUpToBase I) K)
        (etaleAbelianDerivedSquareDifference.{u, 0} I.subschemeι (blowUpToBase I)
          (exceptionalIdeal I).subschemeι (exceptionalDivisorToCenter I)
          ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I)
          (isPullback_exceptionalDivisor I).w rfl K) δ ∈
        distTriang (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, 0}
    I.subschemeι (blowUpToBase I) (exceptionalIdeal I).subschemeι (exceptionalDivisorToCenter I)
    _ (isPullback_exceptionalDivisor I).w rfl (Scheme.Opens.ι I.support.compl)
    (range_subschemeι_compl_eq I) (isPullback_exceptionalDivisor I)
    _ _ (isPullback_blowUpToBase_restrict_compl_support I)
    (cohomologyCommutesWithBaseChange_blowUpToBase_of_fg I hI) K n hK hT

end AlgebraicGeometry

end
