module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksCore.Tactic.StacksAttribute

/-!
# When the de Rham complex of log poles is defined along a divisor

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor. The
de Rham complex of log poles `Ω^•_{X/S}(log Y)` is *defined* for `Y ⊆ X` over `S` when at every
point `y` of `Y` and for every local equation `t ∈ 𝒪_{X, y}` of `Y`

* the `𝒪_{X, y}`-linear map `𝒪_{X, y} → Ω_{X/S, y}`, `g ↦ g · dt`, is a split injection, and
* `Ω^p_{X/S, y}` is `t`-torsion free for every `p`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex`: the two conditions above.

## Main results

* `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex.exists_retraction_toSpanSingleton`:
  the first condition, read off from the definition.
* `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex.isSMulRegular`: the second condition,
  read off from the definition.

## References

* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The *de Rham complex of log poles is defined* for an effective Cartier divisor `Y ⊆ X`,
recorded by its ideal sheaf `I`, over a base `S` if for every point `y` of `Y` and every local
equation `t ∈ 𝒪_{X, y}` of `Y` the map `𝒪_{X, y} → Ω_{X/S, y}`, `g ↦ g · dt`, is a split injection
and `Ω^p_{X/S, y}` is `t`-torsion free for all `p`. -/
@[stacks 0FMV]
def HasLogPolesDeRhamComplex (f : X ⟶ S) (I : X.IdealSheafData) : Prop :=
  ∀ (y : I.subscheme) (U : X.Opens) (hy : I.subschemeι y ∈ U) (t : Γ(X, U)),
    RingHom.ker (I.subschemeι.stalkMap y).hom =
        Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t} →
      (letI : Module (X.presheaf.stalk (I.subschemeι y))
            ((relativeDifferentials f).presheaf.stalk (I.subschemeι y)) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) (relativeDifferentials f).val (I.subschemeι y)
        ∃ r : (relativeDifferentials f).presheaf.stalk (I.subschemeι y) →ₗ[
              X.presheaf.stalk (I.subschemeι y)] X.presheaf.stalk (I.subschemeι y),
          r ∘ₗ LinearMap.toSpanSingleton _ _
              (TopCat.Presheaf.germ (relativeDifferentials f).presheaf U (I.subschemeι y) hy
                ((universalRelativeDerivation f).d t)) =
            LinearMap.id) ∧
        ∀ p : ℕ,
          letI : Module (X.presheaf.stalk (I.subschemeι y))
              ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk (I.subschemeι y)) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) (relativeDifferentialForms f (p : ℤ)).val (I.subschemeι y)
          IsSMulRegular ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk (I.subschemeι y))
            ((X.presheaf.germ U (I.subschemeι y) hy).hom t)

/-- If the de Rham complex of log poles is defined, then at a point `y` of the divisor and for a
local equation `t` there, the map `𝒪_{X, y} → Ω_{X/S, y}`, `g ↦ g · dt`, admits an
`𝒪_{X, y}`-linear retraction. -/
theorem HasLogPolesDeRhamComplex.exists_retraction_toSpanSingleton {f : X ⟶ S}
    {I : X.IdealSheafData} (h : HasLogPolesDeRhamComplex f I) (y : I.subscheme) (U : X.Opens)
    (hy : I.subschemeι y ∈ U) (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) :
    letI : Module (X.presheaf.stalk (I.subschemeι y))
        ((relativeDifferentials f).presheaf.stalk (I.subschemeι y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (relativeDifferentials f).val (I.subschemeι y)
    ∃ r : (relativeDifferentials f).presheaf.stalk (I.subschemeι y) →ₗ[
          X.presheaf.stalk (I.subschemeι y)] X.presheaf.stalk (I.subschemeι y),
      r ∘ₗ LinearMap.toSpanSingleton _ _
          (TopCat.Presheaf.germ (relativeDifferentials f).presheaf U (I.subschemeι y) hy
            ((universalRelativeDerivation f).d t)) =
        LinearMap.id :=
  (h y U hy t ht).1

/-- If the de Rham complex of log poles is defined, then at a point `y` of the divisor and for a
local equation `t` there, multiplication by `t` is injective on `Ω^p_{X/S, y}` for every `p`. -/
theorem HasLogPolesDeRhamComplex.isSMulRegular {f : X ⟶ S} {I : X.IdealSheafData}
    (h : HasLogPolesDeRhamComplex f I) (y : I.subscheme) (U : X.Opens)
    (hy : I.subschemeι y ∈ U) (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) (p : ℕ) :
    letI : Module (X.presheaf.stalk (I.subschemeι y))
        ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk (I.subschemeι y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (relativeDifferentialForms f (p : ℤ)).val (I.subschemeι y)
    IsSMulRegular ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk (I.subschemeι y))
      ((X.presheaf.germ U (I.subschemeι y) hy).hom t) :=
  (h y U hy t ht).2 p

end AlgebraicGeometry.Scheme.Hom

end
