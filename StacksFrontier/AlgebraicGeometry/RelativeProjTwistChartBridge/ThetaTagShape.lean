module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.AffineThetaInputs
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaRelativeRepresentable
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoRepresenting

/-!
# The morphism `r_{d, ℒ, ψ}` of Lemma 01O1 over an arbitrary base

[Stacks, Tag 01O1] opens by naming two things about its morphism: it is *attached to the
quadruple* `(f : T → S, d, ℒ, ψ)`, and it is an *`S`-morphism* `T ⟶ Proj_S(𝒜)`. Its proof names a
third: the morphism lands in the degree-`d` locus `U_d` of Equation 27.12.0.1, because the
quadruple defines an element of `F_d(T)` and `U_d` represents `F_d`.

Before this file the repository had those clauses only in weakened form.
`...RelativeProjTwistChartBridge.classifyingHom_topChart_comp_toBase` proves the over-`S` identity
for a base that is **affine**, and
`...RelativeProjQcohSheaf.RepresentingProjData.associatedMorphism_comp_toBase` proves it for a
morphism defined from a **carried** `RepresentingProjData`.

**Neither restriction is needed.** `...RelativeProjQcohSheaf.Fd.homDegreeOpen` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv` attaches to a class in
`F_d(T)` a morphism into the relative `U_d` of an arbitrary relative homogeneous spectrum over an
arbitrary base, and `...Fd.homDegreeOpen_comp_toBase` says it lies over the morphism the class
records. Composing with the inclusion `U_d ⊆ Proj_S(𝒜)` gives the tag's morphism with both
clauses, under Situation 01NN and `d ≥ 1` alone.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.thetaMorphism`: **the morphism
  `r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O1]**, over an arbitrary base.

## Main results

* `...RelativeProjTwistChartBridge.thetaMorphism_eq_homEquiv_symm`: **it is the morphism the
  representability of `F` attaches to the class of the quadruple**, through the representation of
  [Stacks, Tag 01NZ].
* `...RelativeProjTwistChartBridge.thetaMorphism_comp_toBase`: **it is a morphism over `S`.**
* `...RelativeProjTwistChartBridge.thetaMorphism_mem_degreeOpen`: **it lands in the degree-`d`
  locus `U_d`**, which is what makes the inputs of the `θ`-assertion available at it.

## What this file does not do

**It does not produce `θ`.** The results above are the structural half of the tag; the
`θ`-assertion needs the commutativity of the characterising triangle. The sibling module
`ThetaTriangle` of this directory states the equation and records why neither an induction on the
degree nor its degree-one instance alone reaches it; the whole tag is
`...RelativeProjTwistChartBridge.tag01O1` of
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaIsomorphism`.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {d : ℕ} {f : T ⟶ S}

/-! ### The morphism the tag attaches to a quadruple -/

/-- **The morphism `r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O1]**, over an arbitrary base:
the morphism into the relative degree-`d` locus `U_d` that the representation of `F_d` attaches to
the class of the quadruple, followed by the inclusion `U_d ⊆ Proj_S(𝒜)`.

This is the source's own description — *"the quadruple defines an element of `F_d(T)`; let
`U_d ⊆ Proj_S(𝒜)` be the locus where `𝒪(d)` is invertible; `U_d` represents `F_d`"* — with
`...RelativeProjQcohSheaf.Fd.homDegreeOpen` supplying the representation over an arbitrary base.

It **is** the morphism that the representability of `F` gives: by
`...RelativeProjTwistChartBridge.thetaMorphism_eq_homEquiv_symm` it is the image of the class of
the quadruple under the representation
`...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional` of the functor `F` of
the display 01NX by `Proj_S(𝒜)`, which is the representation registered for [Stacks, Tag 01NZ]
and [Stacks, Tag 01NY]. (`...RelativeProjQcohSheaf.RepresentingProjData.associatedMorphism` is the
same construction relative to a representation carried as a hypothesis bundle; the representation
used here is the one the repository proves.) -/
def thetaMorphism (hd : 0 < d) (P : Quadruple f (situationAlgebra A) (d : ℤ)) :
    T ⟶ (relativeProj A).scheme :=
  Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f P) ≫
    ((relativeProj A).degreeOpen d).ι

/-- **The canonical isomorphism of [Stacks, Tag 01NZ] from `Proj_S(𝒜)` to itself is the
identity**: the identity is compatible with the charts and lies over `S`, and the isomorphism with
those two properties is unique. -/
theorem canonicalIso_relativeProj_eq_refl :
    canonicalIso A (relativeProj A) = Iso.refl (relativeProj A).scheme :=
  (existsUnique_isoOver A (relativeProj A)).unique
    ⟨fun U => chart_comp_canonicalIso_hom A (relativeProj A) U,
      canonicalIso_hom_comp_toBase A (relativeProj A)⟩
    ⟨fun _ => Category.comp_id _, Category.id_comp _⟩

/-- **`r_{d, ℒ, ψ}` is the morphism the representability of `F` gives.** The morphism of
`thetaMorphism` is the image of the class of the quadruple in `F(T)` under the representation
`...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional` of the functor `F` of
the display 01NX by `Proj_S(𝒜)` — the representation of [Stacks, Tag 01NZ], i.e. the `S`-morphism
the source calls *associated* to the quadruple.

The representation sends that class to the morphism into `U_d` followed by `U_d ⊆ Proj_S(𝒜)` and
by the canonical isomorphism `Proj_S(𝒜) ≅ Proj_S(𝒜)` (`...F.classifyingMorphism_mk`), and that
isomorphism is the identity (`canonicalIso_relativeProj_eq_refl`). -/
theorem thetaMorphism_eq_homEquiv_symm (hd : 0 < d)
    (P : Quadruple f (situationAlgebra A) (d : ℤ)) :
    thetaMorphism hd P =
      (relativeProjRepresentableByFunctorUnconditional A).homEquiv.symm
        (RelativeProjInvertibleMorphism.F.toLim A (F.mk f (by exact_mod_cast hd) P)) := by
  refine Eq.trans ?_ (RelativeProjInvertibleMorphism.F.classifyingMorphism_mk A hd P).symm
  rw [canonicalIso_relativeProj_eq_refl, Iso.refl_inv, Category.comp_id]
  rfl

/-- **[Stacks, Tag 01O1]: the morphism attached to a quadruple is a morphism over `S`**, over an
arbitrary base. Composed with the structure morphism of `Proj_S(𝒜)` it is the quadruple's own `f`.

This is `...RelativeProjQcohSheaf.Fd.homDegreeOpen_comp_toBase` read through the associativity of
composition. Nothing is assumed beyond Situation 01NN and `d ≥ 1`: in particular the base is not
required to be affine, as in
`...RelativeProjTwistChartBridge.classifyingHom_topChart_comp_toBase`, and no
`RepresentingProjData` is carried, as in
`...RelativeProjQcohSheaf.RepresentingProjData.associatedMorphism_comp_toBase`. -/
theorem thetaMorphism_comp_toBase (hd : 0 < d) (P : Quadruple f (situationAlgebra A) (d : ℤ)) :
    thetaMorphism hd P ≫ (relativeProj A).toBase = f := by
  rw [thetaMorphism, Category.assoc]
  exact Fd.homDegreeOpen_comp_toBase A (relativeProj A) hd (Fd.mk f P)

/-- **The morphism attached to a quadruple lands in the degree-`d` locus `U_d`**, over an
arbitrary base: it factors through `U_d` by construction, so every point of `T` goes to a point of
that open.

This is the condition `hg` that
`...RelativeVeroneseTwists.laurentComparisonOfDegreeOpen` and
`...RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` ask for, and it is where the source's
sentence *"the locus where the sheaf `𝒪(d)` is invertible and generated by the image of `ψ`"*
enters. -/
theorem thetaMorphism_mem_degreeOpen (hd : 0 < d) (P : Quadruple f (situationAlgebra A) (d : ℤ))
    (t : T) : (thetaMorphism hd P).base t ∈ (relativeProj A).degreeOpen d :=
  ((Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f P)).base t).2

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
