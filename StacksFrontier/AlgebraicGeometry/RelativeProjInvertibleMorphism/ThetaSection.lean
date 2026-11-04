module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseOne

/-!
# The map `θ` of Stacks 01O9 read on the whole scheme when `U(ψ)` is everything

Let `(S, 𝒜, f : T ⟶ S, ℒ, ψ)` be the data of [Stacks, Tag 01O8], `U(ψ) ⊆ T` the open of
[Stacks, Tag 01O8], `r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` the morphism and
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` the map of [Stacks, Tag 01O9].  When `U(ψ)` is all of
`T`, the inclusion `ι : U(ψ) ⟶ T` has an inverse `g : T ⟶ U(ψ)`, and `θ` is read on `T` itself:
in degree `n` it is the map

`(g ≫ r)^*𝒪(n) ≅ g^*(r^*𝒪(n)) ⟶ g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ (g ≫ ι)^*ℒ^{⊗ n} = ℒ^{⊗ n}`

of `𝒪_T`-modules.  This is how `θ` is read on the scheme points of the open subspace `U(ψ)` of an
algebraic space in Stacks 0D2Z: for a scheme point `w : W ⟶ X` lying in `U(ψ)` the open
`U(w^*ψ)` is all of `W`, and the morphism `W ⟶ U(w^*ψ)` with `W ⟶ U(w^*ψ) ⟶ W` the identity is the
one through which the value of `r_{ℒ,ψ}` at `w` is defined.

The statements are made for an arbitrary right inverse `g` of the inclusion `ι`, so that no
equality `U(ψ) = ⊤` of opens enters the morphisms.

## Main definitions

* `…GradedPowerMap.laurentOnSectionPieceIso`: `g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ ℒ^{⊗ n}` for `g ≫ ι = 𝟙`.
* `…GradedPowerMap.thetaOnSection`: **`θ` read on `T` along `g`**, in degree `n`.

## Main results

* `…GradedPowerMap.thetaOnSection_eq`: the definition written out.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

/-- **`g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ ℒ^{⊗ n}` for a right inverse `g` of the inclusion `ι : U(ψ) ⟶ T`**:
the restriction to `U(ψ)` is the inverse image along `ι`, followed by the pseudofunctoriality of
the inverse image along `g ≫ ι = 𝟙_T`. -/
def laurentOnSectionPieceIso (n : ℤ) :
    (Scheme.Modules.pullback g).obj ((laurentOn P.L P.coveringOpen).piece n) ≅
      tensorPowerModule T P.L n :=
  (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).app
        (tensorPowerModule T P.L n)) ≪≫
    (Scheme.Modules.pullbackComp g P.coveringOpen.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr hg).app _ ≪≫
    (Scheme.Modules.pullbackId T).app _

/-- **`θ` read on `T` along a right inverse `g` of the inclusion `ι : U(ψ) ⟶ T`**, in degree `n`:
the map `(g ≫ r)^*𝒪(n) ≅ g^*(r^*𝒪(n)) ⟶ g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ ℒ^{⊗ n}` of `𝒪_T`-modules, the
middle arrow being the inverse image along `g` of the degree-`n` part of `θ` of
[Stacks, Tag 01O9]. -/
def thetaOnSection (n : ℤ) :
    (Scheme.Modules.pullback (g ≫ P.globalMorphism (relativeProj A))).obj
        ((twD A).algebra.piece n) ⟶ tensorPowerModule T P.L n :=
  (Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).inv.app _ ≫
    (Scheme.Modules.pullback g).map (P.theta.app n) ≫ (P.laurentOnSectionPieceIso g hg n).hom

/-- `θ` read along `g`, written out. -/
theorem thetaOnSection_eq (n : ℤ) :
    P.thetaOnSection g hg n =
      (Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).inv.app _ ≫
        (Scheme.Modules.pullback g).map (P.theta.app n) ≫ (P.laurentOnSectionPieceIso g hg n).hom :=
  rfl

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
