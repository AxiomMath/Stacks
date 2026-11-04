module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothCohomologySheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomology

/-!
# The first page of the spectral sequence of a smooth morphism in the flat case

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
`S`. The remark [Stacks, Tag 0FMN] observes that when the de Rham cohomology sheaves
`ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})` are flat `𝒪_Y`-modules, the first page

`E_1^{p, q} = H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`

of the spectral sequence of [Stacks, Tag 0FMM] is `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, by a "tiny
argument" the source omits. This file supplies that argument: it inhabits
`Stacks.DeRhamSmooth.FlatDegenerateDerivedTensor`, the statement the base development isolates
for it, so that the first-page identification holds with no hypothesis beyond the flatness of
the `ℋ^q_dR(X/Y)`.

## Main definitions

* `Stacks.DeRhamSmooth.flatDegenerateDerivedTensor`: for every scheme `Y`, every `𝒪_Y`-module `M`
  and every object `K` of `D(𝒪_Y)` with flat cohomology sheaves,
  `H^t(M ⊗^𝐋_{𝒪_Y} K) ≅ M ⊗_{𝒪_Y} H^t(K)`. This is
  `Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology` at the ringed site of
  opens of `Y`.
* `Stacks.DeRhamSmooth.deRhamFirstPageIsoOfIsFlat`: **the first page in the flat case**,
  `H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y}) ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, assuming only that
  the `ℋ^q_dR(X/Y)` are flat.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-- **The "tiny argument" of [Stacks, Tag 0FMN].** For a scheme `Y`, an `𝒪_Y`-module `M` and an
object `K` of `D(𝒪_Y)` all of whose cohomology sheaves are flat,
`H^t(M ⊗^𝐋_{𝒪_Y} K) ≅ M ⊗_{𝒪_Y} H^t(K)` for every `t`.

This is `Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology` on the ringed site
of opens of `Y`, the module `M` being read as the complex `M[0]` through
`DerivedCategory.singleFunctorIsoCompQ`. -/
def flatDegenerateDerivedTensor (Y : Scheme.{u}) : FlatDegenerateDerivedTensor Y :=
  fun M K hK t =>
    (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).mapIso
        (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ
            (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) 0).app M)).app K) ≪≫
      Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology
        (R := Y.toRingedSpace.sheaf) M K hK t

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The first page of [Stacks, Tag 0FMM] in the flat case of [Stacks, Tag 0FMN].** If the de
Rham cohomology sheaves `ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules then

`H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y}) ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`,

as sheaves of `g^{-1}𝒪_S`-modules. This is `Stacks.DeRhamSmooth.deRhamFirstPageIsoFlat` with its
hypothesis `FlatDegenerateDerivedTensor` discharged by `flatDegenerateDerivedTensor`. -/
def deRhamFirstPageIsoOfIsFlat
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    deRhamFirstPage f g p q ≅ deRhamFirstPageFlat f g p q :=
  deRhamFirstPageIsoFlat f g (flatDegenerateDerivedTensor Y) hflat p q

end Stacks.DeRhamSmooth

end
