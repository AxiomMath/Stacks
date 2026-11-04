module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechPullbackClass
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechUnitBasis

/-!
# The class of `x ∧ ν` is `ξ ∪ f^*[ν]`

Let `f : X ⟶ Y` be smooth with `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)`, `R = Γ(S, 𝒪_S)`, and let `U`
be a finite open covering of `X` with affine intersections, `X` having affine diagonal. For a
cocycle `z` of `Tot(Č(U, Ω^•_{X/S}))` of degree `m`, with class `ξ ∈ H^m_{dR}(X/S)`, and a closed
form `ν` of `Ω^•_{A/R}` of degree `b`, the class of the product `z ∧ ν`
(`Stacks.KatzOda.Cech.mulTot`) is `ξ ∪ f^*[ν]`, where `[ν] ∈ H^b_{dR}(Y/S)` through
`H^b(Ω^•_{A/R}) ≅ H^b_{dR}(Y/S)`. This is the identification of the map `x̃` of the proof of
[Stacks, Tag 0FUM] with the map of the statement.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.classMap_mulTot_intForm`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)

/-- The product of a cocycle with a closed form of the base is a cocycle, in any degree
`N = m + b`. -/
theorem mulTot_cocycle' (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    (hν : Stacks.KatzOda.dForms (baseMap g) b ν = 0) (m : ℕ) {N : ℤ} (hN : (m : ℤ) + b = N)
    (z : TotX U (f ≫ g).sectionsDeRhamComplex m)
    (hz : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d m (m + 1)).hom z = 0) :
    ((cechTot U (f ≫ g).sectionsDeRhamComplex).d N (N + 1)).hom
      (Stacks.KatzOda.Cech.mulTot (chartData f g U haff) (formsDataTotal f g U haff) b ν hN z) =
        0 := by
  subst hN
  exact mulTot_cocycle f g U haff b ν hν m z hz

/-- **The class of `z ∧ ν` is `[z] ∪ f^*[ν]`** ([Stacks, Tag 0FUM], facts (3)--(5) of its
proof): for a cocycle `z` of `Tot(Č(U, Ω^•_{X/S}))` of degree `m` and a cocycle `ν` of degree
`b` of `Ω^•_{A/R}`, the class in `H^N_{dR}(X/S)`, `N = m + b`, of the product of `z` with the
pull-backs of `ν` is the cup product of the class of `z` with the pull-back
`f^* : H^b_{dR}(Y/S) ⟶ H^b_{dR}(X/S)` of the class of `ν`. -/
theorem classMap_mulTot_intForm [IsAffineHom (pullback.diagonal (terminal.from X))]
    (m b : ℕ) {N : ℤ} (hN : (m : ℤ) + b = N)
    (z : TotX U (f ≫ g).sectionsDeRhamComplex m)
    (hz : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d m (m + 1)).hom z = 0)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom ν = 0) :
    (classMap (f ≫ g) U hU N).hom ((cocycleClass N (toMor (Stacks.KatzOda.Cech.mulTot
        (chartData f g U haff) (formsDataTotal f g U haff) b (intForm g b ν) hN z))
        (toMor_comp_d_eq_zero _ (mulTot_cocycle' f g U haff b _ (dForms_intForm g b ν hν) m hN z
          hz))).hom 1) =
      Scheme.Hom.deRhamCup (f ≫ g) m b N hN
        ((classMap (f ≫ g) U hU m).hom ((cocycleClass m (toMor z)
          (toMor_comp_d_eq_zero _ hz)).hom 1))
        (deRhamPullbackModule f g b ((affineClassMap g b).hom
          ((cocycleClass b (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1))) := by
  subst hN
  rw [deRhamPullbackModule_affineClassMap f g U haff hU b ν hν]
  exact classMap_mulTot f g U haff hU b (intForm g b ν) (dForms_intForm g b ν hν) m z hz

end AlgebraicGeometry.DeRhamKatzOdaCech

end
