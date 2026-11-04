/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.GraphAmbientTensorAmple
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalRelativeMorphismsImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace

/-!
# `Mor^{P, ℳ}_Q(Z, X)`: relative morphisms whose graph has Hilbert polynomial `P`

Let `z : Z ⟶ Q` be flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, morphisms of algebraic spaces over a scheme `S` of a big fppf site, so that
the graph transformation of Stacks 0D1A realises `Mor_Q(Z, X)` inside the Hilbert functor
`Hilb_{Z ×_Q X / Q}` (Stacks 0D1B).  For an invertible module `ℳ` on `Z ×_Q X` and `P : ℤ → ℤ`,
Remark 0DPQ of the Stacks project, in its last case `I = ℤ`, `E_i = ℳ^{⊗ i}`, defines

`Mor^{P, ℳ}_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^{P, ℳ}_{Z ×_Q X / Q}`,

where `Hilb^{P, ℳ}_{Z ×_Q X / Q}` is the subfunctor of the Hilbert functor of the families
`W ⊆ (Z ×_Q X)_T` with `χ((Z ×_Q X)_t, 𝒪_{W_t} ⊗ ℳ_t^{⊗ n}) = P(n)` for every `n ∈ ℤ` and every
point `t ∈ T` (Remark 0DPG; through `Hilb = Quot_{𝒪}` of Stacks 0D00 it is
`Quot^{P, ℳ}_{𝒪/(Z ×_Q X)/Q}`, `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`).
The intersection is formed as the inverse image along the graph transformation
(`AlgebraicGeometry.Space.relativeHomGraphPreimage`): a relative morphism lies in
`Mor^{P, ℳ}_Q(Z, X)` exactly when its graph has Hilbert polynomial `P` with respect to `ℳ`.

Stacks 0DPR takes `ℳ = pr₁^* 𝒩 ⊗ pr₂^* ℒ` (`AlgebraicGeometry.Space.graphAmbientTensor`) for
`𝒩` ample on `Z/Q` and `ℒ` ample on `X/Q`.

## Main definitions

* `AlgebraicGeometry.Space.hilbertPolynomialSubfunctor`: `Hilb^{P, L}_{X/Y}`, in particular
  `Hilb^{P, ℳ}_{Z ×_Q X / Q}`.
* `AlgebraicGeometry.Space.relativeHomHilbertPolynomial`: `Mor^{P, ℳ}_Q(Z, X)`.

## Main results

* `AlgebraicGeometry.Space.mem_relativeHomHilbertPolynomial_iff`: a relative morphism lies in
  `Mor^{P, ℳ}_Q(Z, X)` exactly when the object `(T, 𝒪_Γ)` of `Coh_{Z ×_Q X / Q}` of its graph
  `Γ` has Hilbert polynomial `P` with respect to `ℳ`.

## References

* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Hilb^{P, L}_{X/Y}`** (Stacks 0DPG with `E_n = L^{⊗ n}`): for `f : X ⟶ Y` of finite
presentation, an invertible `𝒪_X`-module `L` and `P : ℤ → ℤ`, the subfunctor of the Hilbert
functor of the families `W ⊆ X_T` whose object `(T, 𝒪_W)` of `Coh_{X/Y}` has Hilbert polynomial
`P` with respect to `L`, that is `χ(X_t, 𝒪_{W_t} ⊗ L_t^{⊗ n}) = P(n)` for all `n ∈ ℤ` and all
points `t ∈ T`.  It is the inverse image of `Quot^{P, L}_{𝒪_X/X/Y}` under `Hilb = Quot_{𝒪}`
(Stacks 0D00). -/
def hilbertPolynomialSubfunctor (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (P : ℤ → ℤ) : Subfunctor (hilbertPresheaf f) :=
  letI : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (structureSheafQuotSituation f hf).toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (structureSheafQuotSituation f hf).toCoherentSituation.X.1
        (structureSheafQuotSituation f hf).toCoherentSituation.X.2).O)).property L := hL
  hilbertCondition f hf (CoherentObject.HasHilbertPolynomial L P)
    (fun {A' A} m h => @CoherentObject.hasHilbertPolynomial_of_coherentHom B S hS
      (structureSheafQuotSituation f hf).toCoherentSituation L this P A' A m h)

end General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z)
    (M : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property M]
    (P : ℤ → ℤ)

/-- **`Mor^{P, ℳ}_Q(Z, X)`** (Stacks 0DPQ, the case `I = ℤ`, `E_i = ℳ^{⊗ i}`): the subfunctor
`Mor_Q(Z, X) ∩ Hilb^{P, ℳ}_{Z ×_Q X / Q}` of `Mor_Q(Z, X)` of the relative morphisms whose graph
(Stacks 0D1A) has Hilbert polynomial `P` with respect to `ℳ`. -/
def relativeHomHilbertPolynomial : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
    (hilbertPolynomialSubfunctor (graphAmbientMap B S hS z x hZ hX hQ)
      (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp) M P)

/-- A relative morphism lies in `Mor^{P, ℳ}_Q(Z, X)` exactly when its graph lies in
`Hilb^{P, ℳ}_{Z ×_Q X / Q}`. -/
theorem mem_relativeHomHilbertPolynomial_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj T) :
    s ∈ (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).obj T ↔
      (graphTransformation hZ hX hQ hsep hfp hflat hproper).app T (ULift.up s) ∈
        (hilbertPolynomialSubfunctor (graphAmbientMap B S hS z x hZ hX hQ)
          (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp) M P).obj T :=
  Iff.rfl

end AlgebraicGeometry.Space

end
