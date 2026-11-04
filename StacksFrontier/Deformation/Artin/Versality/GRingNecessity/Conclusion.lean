module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.Versality

/-!
# The conclusion of Stacks Lemma 98.12.7

Stacks Lemma 98.12.7 (tag 07XH) says that an effective versal formal object `ξ` of a category
`𝒳` fibred in groupoids over the big fppf site of a locally Noetherian scheme `S`, limit
preserving on objects, whose image point has a G-ring as local ring, is the system of
infinitesimal restrictions of an object over a scheme of finite type over `S`, versal at a
finite type point with the residue field of `ξ`. Stacks Example 98.12.8 (tag 07XI) studies what
the conclusion of that lemma alone implies, without its G-ring hypothesis; this file records
that conclusion as a predicate.

## Main definitions

* `Deformation.Artin.AlgebraizationConclusion`: the conclusion of Stacks 07XH for `𝒳` and `ξ`.

## Implementation notes

The body of `AlgebraizationConclusion` is copied verbatim from the conclusion of the formalized
statement of Stacks 07XH, `Deformation.Artin.exists_finiteType_versal_approximation`, in
`StacksFrontier/Deformation/Artin/Versality/FormalObjectApproximation.lean`, where the definitions
its statement uses agree
with the ones here. The conclusion consists of a scheme `U` of finite type over `S`, given both
as an object of schemes over `S` and as an object `V` of the site, a finite type point `u₀ ∈ U`
whose residue field is isomorphic to that of `ξ`, an object `x` of `𝒳` over `U` versal at `u₀`,
and the realization of `ξ` by the restriction of `x`: an object `x_R` of `𝒳` over a complete
local base whose formal object is isomorphic to `ξ`, a cartesian morphism `x_R ⟶ x`, and an
isomorphism of the completion of `𝒪_{U,u₀}` with the base of `x_R` under which `x_R ⟶ x` lies
over the canonical morphism `Spec 𝒪_{U,u₀}^∧ → U`. The only change is the name of the bound
variable `e` of the isomorphism `ξ ≅ (approximationFunctor ..).obj x_R`, which is not referred to
and is written `_e` (an alpha-equivalent statement, avoiding the unused variable linter).

## References

* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-- **The conclusion of Stacks Lemma 98.12.7 (tag 07XH)** for a category `𝒳` fibred in groupoids
over the big fppf site of `S` and a formal object `ξ` of `𝒳`: there are a morphism of finite
type `U → S`, a finite type point `u₀ ∈ U` whose residue field is isomorphic to that of `ξ`, and
an object `x` of `𝒳` over `U` which is versal at `u₀` and whose restriction to the completion of
the local ring of `U` at `u₀` realizes `ξ`. This is copied verbatim from the conclusion of the
formalization of Stacks 07XH (see the implementation notes). -/
def AlgebraizationConclusion (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p) : Prop :=
  ∃ (U : Over S) (u₀ : U.left)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (_ : (Over.post B.inclusion).obj V = U)
    (x : 𝒳.val.p.Fiber V)
    (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x.1 = U),
    LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧
    AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
    (letI : CommRing ξ.base.R := ξ.base.commRing
     letI : IsLocalRing ξ.base.R := ξ.base.localRing
     Nonempty (U.left.residueField u₀ ≃+* ResidueField ξ.base.R)) ∧
    Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x.1 hx ∧
    ∃ (xR : Deformation.Artin.CompleteLocalObjects B S hS 𝒳.val.p)
      (_e : ξ ≅ (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
        𝒳.property).obj xR)
      (r : xR.obj.1 ⟶ x.1)
      (eR : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
        (Deformation.Artin.chosenBase B S hS 𝒳.val.p xR.obj).R),
      𝒳.val.p.IsCartesian (𝒳.val.p.map r) r ∧
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xR.obj).symm ≫
          𝒳.val.p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
        (Spec.map (CommRingCat.ofHom
          eR.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀)

end Deformation.Artin

end
