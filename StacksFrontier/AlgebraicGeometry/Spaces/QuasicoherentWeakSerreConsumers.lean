module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerreFirstQuadrant
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.TwoStepApproximation

/-!
# Recognising a quasi-coherent module from an exact sequence or a spectral sequence

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  By clauses (3)
and (4) of Stacks 03M1, quasi-coherence of `𝒪_F`-modules is a weak Serre class in the sense of
Stacks 0754 (`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`, at
the module universe of the schemes).  This module records three ways a weak Serre class
recognises a quasi-coherent module, as used in the proof of Stacks 0720.

The first is the five-term exact sequence of Stacks 02MO, part (2): a module sitting in an exact
`M₀ ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ M₄` whose four outer terms are quasi-coherent is itself quasi-coherent.

The second is the two-step approximation
`CategoryTheory.ObjectProperty.prop_kernel_of_prop_kernel_comp`, which recognises a kernel whose
target is *not* known to be quasi-coherent.

The third is part (4) of Stacks 0132 at the abutment of a spectral sequence: if every term of
one page of a cohomological spectral sequence of `𝒪_F`-modules is quasi-coherent, so is every
term of what it abuts to.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_exact₄`: **the middle term of a five-term
  exact sequence of `𝒪_F`-modules whose other four terms are quasi-coherent is quasi-coherent**,
  with no hypothesis.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_exact_epi`: the same for an exact
  `M₀ ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`, the shape a long exact cohomology sequence produces.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_twoStepApproximation`: **a kernel into
  an `𝒪_F`-module carrying a two-step quasi-coherent approximation is quasi-coherent**, with no
  hypothesis, and with no assumption that the module itself is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_abutsTo`: **a cohomological spectral sequence
  of `𝒪_F`-modules one of whose pages is quasi-coherent at every bidegree abuts to
  quasi-coherent modules**, with no hypothesis.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_abutsTo_firstQuadrant`: the same with the page
  hypothesis split into vanishing outside the first quadrant and quasi-coherence at the
  nonnegative bidegrees.

## Implementation notes

*No `@[stacks]` attribute is carried.*  Clause (4) of Stacks 03M1 is already claimed, on the
element-level statements of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClausesUnconditional`; Stacks 02MO, part (2),
and Stacks 0132, part (4), are claimed on the abstract statements
`CategoryTheory.ObjectProperty.prop_obj₂_of_exact` and
`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page_firstQuadrant`.  Everything below is
one of those abstract statements with its weak Serre class supplied by
`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`, so a second claim
on any tag would double-count it.

*The five-term statement is given with the three exactness clauses as separate short complexes*
rather than as a `CategoryTheory.ComposableArrows`, because that is the shape in which a long
exact cohomology sequence is available; `CategoryTheory.ObjectProperty.prop_mid_of_exact₄`
performs the conversion.

*The module universe* is `u`, the universe of the schemes, because the weak Serre class is: its
statement mentions `CategoryTheory.Abelian` of the `𝒪_F`-modules, and clause (4) of Stacks 03M1
is itself proved only at `u` for that reason.

*The local priority raise is load-bearing*, as in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional`: without it the
`CategoryTheory.Abelian` instance that the statements below mention is sought among the
module-universe-`max u v r w` instances of the import closure and the universe constraint fails.
The attribute is `local`, so no global instance is declared.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Recognition from a five-term exact sequence -/

/-- **The middle term of a five-term exact sequence of `𝒪_F`-modules whose other four terms are
quasi-coherent is quasi-coherent**: Stacks 02MO, part (2), for the weak Serre class of
quasi-coherent modules. -/
theorem isQuasicoherentOnSite_of_exact₄ {M₀ M₁ M₂ M₃ M₄ : Modules.{u, u} B S hS F hF}
    {f₀ : M₀ ⟶ M₁} {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} {f₃ : M₃ ⟶ M₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₀ : M₀.IsQuasicoherentOnSite) (h₁ : M₁.IsQuasicoherentOnSite)
    (h₃ : M₃.IsQuasicoherentOnSite) (h₄ : M₄.IsQuasicoherentOnSite) :
    M₂.IsQuasicoherentOnSite :=
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS F hF
  ObjectProperty.prop_mid_of_exact₄
    (fun T hT a b c d ↦
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).prop_obj₂_of_exact T hT a b c d)
    w₀ w₁ w₂ e₀ e₁ e₂ h₀ h₁ h₃ h₄

/-- **A term of a long exact sequence of `𝒪_F`-modules is quasi-coherent as soon as its two
predecessors and its quasi-coherent successor-with-zero are**: if `M₀ ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is
exact and `M₀`, `M₁`, `M₃` are quasi-coherent, then so is `M₂`. -/
theorem isQuasicoherentOnSite_of_exact_epi {M₀ M₁ M₂ M₃ : Modules.{u, u} B S hS F hF}
    {f₀ : M₀ ⟶ M₁} {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (he : Epi f₂)
    (h₀ : M₀.IsQuasicoherentOnSite) (h₁ : M₁.IsQuasicoherentOnSite)
    (h₃ : M₃.IsQuasicoherentOnSite) :
    M₂.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_exact₄ B S hS F hF w₀ w₁ (f₃ := (0 : M₃ ⟶ M₃)) (by simp) e₀ e₁
    ((ShortComplex.exact_iff_epi _ rfl).2 he) h₀ h₁ h₃ h₃

/-- **A kernel into an `𝒪_F`-module with a two-step quasi-coherent approximation is
quasi-coherent**.  Let `δ : W ⟶ M` with `W` quasi-coherent, and let
`b : M ⟶ N` be a morphism with `N` and `ker b` quasi-coherent — an exact sequence
`0 ⟶ ker b ⟶ M ⟶ N` approximating `M` by quasi-coherent modules.  Then `ker δ` is quasi-coherent,
even though `M` itself is not known to be. -/
theorem isQuasicoherentOnSite_kernel_of_twoStepApproximation
    {W M N : Modules.{u, u} B S hS F hF} (δ : W ⟶ M) (b : M ⟶ N)
    (hW : W.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hA : (kernel b).IsQuasicoherentOnSite) : (kernel δ).IsQuasicoherentOnSite :=
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS F hF
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).prop_kernel_of_prop_kernel_comp
      δ b hW hN hA

/-! ### Recognition at the abutment of a spectral sequence -/

/-- **A cohomological spectral sequence of `𝒪_F`-modules one of whose pages is quasi-coherent at
every bidegree abuts to quasi-coherent modules**: part (4) of Stacks 0132 at the abutment, for
the weak Serre class of quasi-coherent modules. -/
theorem isQuasicoherentOnSite_of_abutsTo {r₀ : ℤ}
    {E : CohomologicalSpectralSequence (Modules.{u, u} B S hS F hF) r₀}
    {H : ℤ → Modules.{u, u} B S hS F hF} (hE : SpectralSequence.AbutsTo E H) {r : ℤ}
    (hr : r₀ ≤ r) (hpage : ∀ pq : ℤ × ℤ, ((E.page r hr).X pq).IsQuasicoherentOnSite) (n : ℤ) :
    (H n).IsQuasicoherentOnSite :=
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS F hF
  hE.prop_of_prop_page
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)) hr hpage n

/-- **A first-quadrant cohomological spectral sequence of `𝒪_F`-modules whose page is
quasi-coherent at the nonnegative bidegrees abuts to quasi-coherent modules**. -/
theorem isQuasicoherentOnSite_of_abutsTo_firstQuadrant {r₀ : ℤ}
    {E : CohomologicalSpectralSequence (Modules.{u, u} B S hS F hF) r₀}
    {H : ℤ → Modules.{u, u} B S hS F hF} (hE : SpectralSequence.AbutsTo E H) {r : ℤ}
    (hr : r₀ ≤ r) (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (hpage : ∀ p q : ℕ, ((E.page r hr).X ((p : ℤ), (q : ℤ))).IsQuasicoherentOnSite) (n : ℤ) :
    (H n).IsQuasicoherentOnSite :=
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS F hF
  hE.prop_of_prop_page_firstQuadrant
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)) hr hzero hpage n

end AlgebraicGeometry.Space

end
