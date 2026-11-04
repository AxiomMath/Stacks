module

public import StacksFrontier.AlgebraicGeometry.Morphism.Glue
public import StacksFrontier.AlgebraicGeometry.TwistUnique.Basic

/-!
# Locality of module-sheaf morphisms on the domain of definition of Tag 07ZG

Tag 07ZG attaches to a homomorphism `ψ : A ⟶ B` of quasi-coherent graded `𝒪_S`-algebras three
things: the open `U(ψ)` of `Proj_S(B)` where the induced map is defined, a morphism
`r_ψ : U(ψ) ⟶ Proj_S(A)` over `S`, and maps `θ_n` on all integer twists. The first two are proved
as `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain` and
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom`.

This file supplies the **separation half** for the third: a morphism of sheaves of modules on
`U(ψ)` is determined by its restrictions to the pieces of `U(ψ)` over the affine opens of the
base. Equivalently, the twist maps `θ_n` are *unique* given their affine-chart description, so the
only thing still owed for assertion (3) is their **existence**.

Nothing here mentions the twists, so nothing here needs a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`; the statements are about arbitrary
objects of `AlgebraicGeometry.Scheme.Modules` on `U(ψ)`. The corollary that names the twists,
`twistMap_ext`, takes the two twist data as explicit hypotheses, so that it applies to any twist
data whatever — in particular to
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, the twists of the relative
projective spectrum of a quasi-coherent graded algebra.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.iSup_preimage_chartImage_eq_top`: the pieces of
  `U(ψ)`, pulled back to opens of `U(ψ)` itself, cover it. By the definition of
  `relativeMapDomain` this is the supremum it is defined as, read inside the open subscheme.
* `Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.hom_ext_of_chartImage`: **two morphisms of
  sheaves of modules on `U(ψ)` with equal restrictions to every piece are equal.**
* `Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.twistMap_ext`: the same statement at the type of
  Tag 07ZG's twist maps, for two given twist data. **The uniqueness clause of Tag 07ZG is not the
  obstruction; the existence of the maps is.**

## The route

`Stacks.AlgebraicGeometry.TwistUnique.hom_ext_of_cover` is the separation half of the sheaf axiom
for the target: a morphism is determined by its action on the sections over the opens inside the
members of a covering. The covering is
`Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.iSup_preimage_chartImage_eq_top`, and the passage
from "equal restriction along the inclusion of a piece" to "equal on the sections over the opens
inside that piece" is `Stacks.AlgebraicGeometry.TwistUnique.app_eq_of_restrictFunctor_map_eq_of_le`
together with `Stacks.AlgebraicGeometry.RelativeProjMapDomain.opensRange_homOfLE`,
which identifies the range of
the inclusion of a piece with the corresponding open of `U(ψ)`.

## Implementation notes

`iSup_preimage_chartImage_eq_top` is proved by transporting membership with `▸` rather than by
`rw [relativeMapDomain_eq_iSup]`. The two opens are definitionally equal, but the hypothesis is a
membership in a *coercion* of `ψ.relativeMapDomain`, so rewriting it produces a motive that is not
type-correct at implicit transparency and the rewrite fails on a pattern that is present — the
error names the coercion. The same measurement is recorded for the chart-domain spellings in
`StacksFrontier/AlgebraicGeometry/Morphism/Glue.lean`.

The index of the covering is `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen`,
whose second
projection has type `IsAffineOpen U` on the nose, for the reason recorded at that definition; it
also puts the index in `Type u`, which is what
`Stacks.AlgebraicGeometry.TwistUnique.hom_ext_of_cover` asks for.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwistLocality

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- **The pieces of `U(ψ)` cover it**, read as opens of `U(ψ)` itself. `U(ψ)` is by definition the
supremum of its pieces, so this is that definition pulled back along the inclusion. -/
public theorem iSup_preimage_chartImage_eq_top :
    (⨆ U : AffineOpen S, ψ.relativeMapDomain.ι ⁻¹ᵁ chartImage ψ U) = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show (x.1 : (relativeProj B).scheme) ∈ ⨆ U : AffineOpen S, chartImage ψ U from
      (relativeMapDomain_eq_iSup ψ) ▸ x.2)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩

/-- The range of the inclusion of a piece into `U(ψ)` is the corresponding open of `U(ψ)`. -/
public theorem image_top_homOfLE_chartImage_le (U : AffineOpen S) :
    (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ''ᵁ ⊤ =
      ψ.relativeMapDomain.ι ⁻¹ᵁ chartImage ψ U := by
  rw [Scheme.Hom.image_top_eq_opensRange, opensRange_homOfLE]

/-- **A morphism of sheaves of modules on `U(ψ)` is determined by its restrictions to the pieces.**

This is the separation half of the sheaf axiom for the target, applied to the covering of `U(ψ)`
by its pieces. Applied to the maps on twists it says that Tag 07ZG's assertion (3) has at most one
solution satisfying the affine-chart description; see `twistMap_ext`. -/
public theorem hom_ext_of_chartImage {M N : ψ.relativeMapDomain.toScheme.Modules}
    {φ φ' : M ⟶ N}
    (h : ∀ U : AffineOpen S,
      (Scheme.Modules.restrictFunctor
          ((relativeProj B).scheme.homOfLE (chartImage_le ψ U))).map φ =
        (Scheme.Modules.restrictFunctor
          ((relativeProj B).scheme.homOfLE (chartImage_le ψ U))).map φ') :
    φ = φ' :=
  TwistUnique.hom_ext_of_cover (iSup_preimage_chartImage_eq_top ψ) fun U _V hV s =>
    TwistUnique.app_eq_of_restrictFunctor_map_eq_of_le
      ((relativeProj B).scheme.homOfLE (chartImage_le ψ U)) (h U)
      (hV.trans (image_top_homOfLE_chartImage_le ψ U).ge) s

/-- **The maps on twists of Tag 07ZG are unique given their affine-chart description.** Two
candidates for the `n`-th twist map which have equal restrictions to every piece of `U(ψ)` are
equal.

The two twist data are hypotheses rather than fixed constructions: the statement does not depend
on how they are built, only on the type of the twist map, so it applies in particular to
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. The existence half of Tag
07ZG's assertion (3) is still owed; what blocks it is the agreement of the chart-local comparison
maps of Tag 01MY over a nested pair of affine opens of the base, which is the twist assertion of
Tag 01MZ for homomorphisms that are not everywhere defined. -/
public theorem twistMap_ext (DA : TwistData A) (DB : TwistData B) (n : ℤ)
    {θ θ' : (Scheme.Modules.pullback (relativeMapHom ψ)).obj (DA.algebra.piece n) ⟶
      (Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (DB.algebra.piece n)}
    (h : ∀ U : AffineOpen S,
      (Scheme.Modules.restrictFunctor
          ((relativeProj B).scheme.homOfLE (chartImage_le ψ U))).map θ =
        (Scheme.Modules.restrictFunctor
          ((relativeProj B).scheme.homOfLE (chartImage_le ψ U))).map θ') :
    θ = θ' :=
  hom_ext_of_chartImage ψ h

end Stacks.AlgebraicGeometry.Tag07ZGTwistLocality

end
