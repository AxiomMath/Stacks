module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftGroup
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledCokernelDifferentials

/-!
# The identification `κ` of the two acting groups of Stacks 08U8 for a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. Clause (2) of
[Stacks Project, Tag 08U8] makes the homomorphisms out of `H⁰(Lf^*𝖭𝖫_{Y/k})` act on the lifts of
`f` between two deformations, while [Stacks Project, Tag 0CK2] — the torsor structure the library
actually constructs, in
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts` — makes the third
term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V] act. The two statements
differ exactly by an identification of those groups, the input called `κ` by
`Deformation.Examples.nonempty_schemeMorphismLiftEquivCokernelHom` and
`nonempty_schemeMorphismLiftEquivFactorization`, which carry it as a hypothesis.

This file constructs it:

`Der_k(𝒪_Y, f_*𝒪_X) ≃ Hom_{𝒪_X}(Coker(f^*(𝒥/𝒥² ⟶ Ω)), 𝒢)`.

## Main definitions

* `Deformation.Examples.schemeMorphismDerivationsEquivCokernelHom`: **the identification `κ`**.

## Implementation notes

`κ` is the composite of the two factors the implementation notes of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftFactorization.lean` name.
`Deformation.Examples.schemeMorphismLiftHomLinearEquiv` is
`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒢) ≃ₗ[k] Der_k(𝒪_Y, f_*𝒢)`, which at `𝒢 = 𝒪_X` is the third term of the
sequence of [Stacks Project, Tag 0E3V]; and
`AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoPullbackCotangent` is
`Coker(f^*(𝒥/𝒥² ⟶ Ω)) ≅ f^*Ω_{Y/k}` at the spelling of `f^*Ω_{Y/k}` that
`Deformation.Examples.schemeMorphismPullbackCotangent` — and hence
`schemeMorphismLiftHomLinearEquiv` — is written in. The second factor is what was missing; see
the implementation notes of
`StacksFrontier/Deformation/RingedSpaceThickening/PulledCokernelDifferentials.lean` for the
spellings it reconciles.

The cokernel is written as the cokernel of
`AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap` rather than of the differential `P.d`
of a two-term structure `P`, so that `κ` applies at every `P` whose differential is the
pulled-back conormal map. That holds by `rfl` of
`AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm`
(`pulledNaiveCotangentTwoTerm_d`) and of `derivedPullbackNaiveCotangentTwoTerm`
(`derivedPullbackNaiveCotangentTwoTerm_d`), the intended instance of **Stacks 08U8** for the
sequence of [Stacks Project, Tag 0E3V].

The coefficient sheaf is an arbitrary `𝒢` with an identification `ε : 𝒢 ≅ 𝒪_X`, which is the
shape the surrounding development uses: nothing here needs `𝒢` to be the structure sheaf on the
nose, only the derivations to take their values in `f_*𝒪_X`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8), whose clause (2) reads
  its acting group out of `H⁰`.
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2), the torsor structure on
  the lifts.
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V), whose third term is the
  derivations.
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ), the sheaf the
  homomorphisms are taken out of.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening (pulledConormalMap
  pulledCokernelConormalIsoPullbackCotangent)

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- **The identification `κ` of the two acting groups of [Stacks Project, Tag 08U8] for a
morphism of schemes.** The third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of
[Stacks Project, Tag 0E3V] is the group of homomorphisms out of the cokernel of the differential
of `f^*𝖭𝖫_{Y/k}` — the acting group of clause (2) of [Stacks Project, Tag 08U8], which the
source further identifies with `Ext⁰(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)`.

This is the input carried as the hypothesis `κ` by
`Deformation.Examples.nonempty_schemeMorphismLiftEquivCokernelHom`,
`nonempty_schemeMorphismLiftEquivFactorization` and
`exists_simplyTransitive_cokernelHom_schemeMorphismLifts`, and the content that the tag
docstrings of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean` record as
not proved with **Stacks 08U8** itself. It is the composite of
`Deformation.Examples.schemeMorphismLiftHomLinearEquiv`, the universal property of `Ω_{Y/k}`
through the adjunction `f^* ⊣ f_*`, with
`AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoPullbackCotangent`, which
identifies that cokernel with `f^*Ω_{Y/k}`. -/
def schemeMorphismDerivationsEquivCokernelHom
    {G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : G ≅ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :
    schemeMorphismDerivations f pY ≃
      (cokernel (pulledConormalMap f.toLRSHom.toShHom pY.toLRSHom.toShHom) ⟶ G) :=
  (schemeMorphismLiftHomLinearEquiv f pY ε).toEquiv.symm.trans
    (Iso.homCongr
      (pulledCokernelConormalIsoPullbackCotangent
        f.toLRSHom.toShHom pY.toLRSHom.toShHom).symm (Iso.refl G))

end Deformation.Examples

end
