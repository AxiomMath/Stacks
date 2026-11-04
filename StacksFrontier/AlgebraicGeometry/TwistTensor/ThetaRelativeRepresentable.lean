module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaAffineRepresentable

/-!
# Lemma 01O1's `θ`-assertion over an arbitrary base

`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaAffineRepresentable` proves the `θ`-assertion of
[Stacks, Tag 01O1] — the existence of `θ`, the commutativity of its characterising triangle and
its uniqueness among homomorphisms of graded algebras — on the hypotheses `IsAffine S` and
`0 < d`, by feeding `...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_universal` the
representation `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of [Stacks, Tag 01NU] for
an affine base.

**The affineness is not needed.** The degree-`d` open `U_d` of an arbitrary relative homogeneous
spectrum represents `F_d` over an arbitrary base: that is residue (i) of the source's proof of
[Stacks, Tag 01NY], proved in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv` as the bijection
`...RelativeProjQcohSheaf.Fd.degreeOpenEquiv` together with its naturality
`...RelativeProjQcohSheaf.Fd.homDegreeOpen_pullback'`. This file packages that bijection as a
`CategoryTheory.Functor.RepresentableBy` and reruns the affine argument on it, so the
`θ`-assertion holds in Situation 01NN with no hypothesis on `S`.

## Main results

* `...RelativeProjQcohSheaf.Fd.representableByDegreeOpenOfCharts`: **the functor `F_d` is
  represented by the relative degree-`d` open of an arbitrary relative homogeneous spectrum**,
  over an arbitrary base.
* `...RelativeProjQcohSheaf.Fd.representableByDegreeOpenOfCharts_comp`: that representation is a
  representation **over `S`** — the morphism it attaches to a class, followed by the structure
  morphism of `U_d`, is the morphism the class records.
* `...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_relativeProjData`: **the
  `θ`-assertion of [Stacks, Tag 01O1] over an arbitrary base**, on `0 < d` alone.

## What is still presented on the universal quadruple's data

Exactly what `...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_isAffine` presents it on,
and for the same reason: the source of `θ` here is the Laurent algebra of the pullback along `r`
of the universal invertible module of the representation, and the second leg of the triangle is
the universal quadruple's own `ψ`, rather than the tag's `r^*(⨁_n 𝒪(nd))` and the `ψ_univ` of
[Stacks, Tag 01NR]. Identifying the two is the one step of the source's proof that this
repository does not have — the source establishes it by showing that the quadruple
`(U_d → S, d, 𝒪_{U_d}(d), ψ_univ|_{𝒜^{(d)}})` built from [Stacks, Tag 01NR] **is** the universal
element of `F_d(U_d)`, and no declaration here identifies a representation's universal quadruple
with a `...RelativeProjTwists.TwistData`. What this file removes is the restriction to an affine
base, which is a different gap and an independent one.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S T : Scheme.{u}} {f : T ⟶ S} {A : SheafGradedAlgebra.{u} S} {k : ℕ}

/-! ### The relative degree-`d` open represents `F_d` over an arbitrary base -/

/-- The structure morphism `U_d ⟶ Proj_S(𝒜) ⟶ S` of the relative degree-`d` open of a relative
homogeneous spectrum. -/
abbrev Fd.degreeOpenHom (A : SheafGradedAlgebra.{u} S) (P : RelativeProjData A) (k : ℕ) :
    (P.degreeOpen k).toScheme ⟶ S :=
  (P.degreeOpen k).ι ≫ P.toBase

/-- **The relative degree-`d` open of a relative homogeneous spectrum represents `F_d`**, over an
arbitrary base: the bijection `...RelativeProjQcohSheaf.Fd.degreeOpenEquiv` of residue (i) of
[Stacks, Tag 01NY], packaged with its naturality
`...RelativeProjQcohSheaf.Fd.homDegreeOpen_pullback'` as a
`CategoryTheory.Functor.RepresentableBy`.

This is `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` with the affineness of the base
removed and the absolute `U_d ⊆ Proj Γ(S, 𝒜)` replaced by the relative one. -/
def Fd.representableByDegreeOpenOfCharts (A : SheafGradedAlgebra.{u} S)
    (P : RelativeProjData A) (hk : 0 < k) :
    (Fd.functor (situationAlgebra A) (k : ℤ)).RepresentableBy (P.degreeOpen k).toScheme where
  homEquiv := (Fd.degreeOpenEquiv A P hk _).symm
  homEquiv_comp g φ :=
    (Fd.degreeOpenEquiv A P hk _).injective
      (((Fd.degreeOpenEquiv A P hk _).apply_symm_apply (g ≫ φ)).trans
        ((congrArg (fun z => g ≫ z)
            ((Fd.degreeOpenEquiv A P hk _).apply_symm_apply φ)).symm.trans
          (Fd.homDegreeOpen_pullback' A P hk g ((Fd.degreeOpenEquiv A P hk _).symm φ)).symm))

/-- **The representation of `F_d` by the relative degree-`d` open is a representation over `S`**:
the morphism it attaches to a class in `F_d(T')`, followed by the structure morphism of `U_d`, is
the morphism the class records.

This is `...RelativeProjQcohSheaf.Fd.homDegreeOpen_comp_toBase`, which is the shape
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_universal` consumes. -/
theorem Fd.representableByDegreeOpenOfCharts_comp (A : SheafGradedAlgebra.{u} S)
    (P : RelativeProjData A) (hk : 0 < k) (T' : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (k : ℤ) T') :
    (Fd.representableByDegreeOpenOfCharts A P hk).homEquiv.symm ξ
        ≫ Fd.degreeOpenHom A P k = ξ.1 :=
  Fd.homDegreeOpen_comp_toBase A P hk ξ

/-! ### Lemma 01O1's `θ`-assertion over an arbitrary base -/

/-- **Stacks Project, Tag 01O1 over an arbitrary base, with nothing carried.** Let `S` be a
scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `X` a relative homogeneous
spectrum of `𝒜` — in particular `Proj_S(𝒜)` of [Stacks, Tag 01NQ] — let `d ≥ 1`, and let
`(f : T → S, d, ℒ, ψ)` be a quadruple of Section 01NS. Then there are a morphism `r : T ⟶ U_d`
into the relative degree-`d` open with `r ≫ (structure morphism of U_d) = f`, a universal
quadruple `(U_d → S, d, ℒ_univ, ψ_univ)`, and an isomorphism

`θ : ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n} ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras with `u_n ≫ θ_n = ψ_n` in every integer degree, `u` being
the pullback of `ψ_univ` along `r`; and `θ` is the only homomorphism of graded algebras with that
property.

Nothing is assumed beyond `0 < d`. This is
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_isAffine` with the affineness of the
base removed: the representation of `F_d` is `Fd.representableByDegreeOpenOfCharts` and its
over-`S` clause is `Fd.representableByDegreeOpenOfCharts_comp`, both over an arbitrary base. See
the module docstring for why the source of `θ` is not the tag's own `r^*(⨁_n 𝒪(nd))`. -/
theorem Quadruple.existsUnique_theta_of_relativeProjData
    (A : SheafGradedAlgebra.{u} S) (P : RelativeProjData A) (hk : 0 < k)
    (Q : Quadruple f (situationAlgebra A) (k : ℤ)) :
    ∃ (r : T ⟶ (P.degreeOpen k).toScheme)
      (Qu : Quadruple (Fd.degreeOpenHom A P k) (situationAlgebra A) (k : ℤ))
      (hf : r ≫ Fd.degreeOpenHom A P k = f),
      (∃ θ : laurent (Qu.pullback r).L ≅ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n) ∧
        ∃! Θ : laurent (Qu.pullback r).L ⟶ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ Θ.app n = Q.twisting.app n := by
  obtain ⟨Qu, hf, hθ, huniq⟩ :=
    Q.existsUnique_theta_universal
      (Fd.representableByDegreeOpenOfCharts A P hk)
      (Fd.representableByDegreeOpenOfCharts_comp A P hk)
      (r := (Fd.representableByDegreeOpenOfCharts A P hk).homEquiv.symm (Fd.mk f Q))
      (Equiv.apply_symm_apply _ _)
  exact ⟨_, Qu, hf, hθ, huniq⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
