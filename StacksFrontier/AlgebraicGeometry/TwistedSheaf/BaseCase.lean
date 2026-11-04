module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Descent

/-!
# The base case of Tag 0BEM, reduced to a sheaf-level isomorphism

The induction of [Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) starts where the
dimension of the support is zero, and there the source does not argue with Euler
characteristics at all: it cites [Stacks, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT),
whose proof writes `ℱ = i_*𝒢` for the scheme-theoretic support `i : Z → X`, observes that `Z`
is a finite disjoint union of spectra of Artinian local rings, so that `i^*𝓔 ≅ 𝒪_Z^{⊕ n}` for
every locally free `𝓔` of rank `n`, and concludes `ℱ ⊗ 𝓔 ≅ ℱ^{⊕ n}` by the projection formula.
At rank one — which is what an invertible twist is — that reads

  `ℱ ⊗ 𝓛 ≅ ℱ`.

This file takes **that** isomorphism as the hypothesis and derives the base case of the
induction from it, so the input Tag 0BEM still needs at dimension zero is exactly the statement
the source proves, with no Euler characteristic, no iterated twist and no polynomial in it.

## Main definitions

* `AlgebraicGeometry.twistedSheafIsoOfTensorInvertibleIso`: if tensoring `𝒢` by **any**
  invertible sheaf of modules gives `𝒢` back, then every twist of `𝒢` is `𝒢`. The twisting
  factors are the integer tensor powers `𝓛_i^{⊗ n_i}`, which are invertible
  (`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`), so one hypothesis covers the
  whole fold.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_twistedSheaf_eq_of_tensorInvertibleIso`: under the same
  hypothesis the Euler characteristic of every twist of `𝒢` equals that of `𝒢`. This is the
  `hbase` of
  `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_eulerCharacteristic_twist_eq`.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_tensorInvertibleIso`: Tag 0BEM's
  conclusion with `hbase` replaced by the sheaf-level isomorphism above.

## Implementation notes

**Why one hypothesis suffices for the whole fold.** The fold accumulates, so a hypothesis
mentioning only the factors `𝓛_i^{⊗ n_i}` would have to be reapplied to each partial twist,
which is a different sheaf at every step. Quantifying over *all* invertible second factors
avoids that: the induction below is on the list of indices with `𝒢` held fixed, and each step
uses the hypothesis for `𝒢` itself and then the functoriality of the fold
(`AlgebraicGeometry.twistListIso`) to move the resulting isomorphism through the remaining
factors. So the hypothesis is used `r` times, always at `𝒢`.

**The hypothesis is stated at `X.Modules`.**
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf X.ringCatSheaf.2`
lands in `SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
  X.ringCatSheaf.2)`, which is
definitionally `AlgebraicGeometry.Scheme.Modules` but not syntactically, and the isomorphism has
to be formed in one category; the ascription is the same one the coherence statements of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/Basic.lean` use.

**No dimension hypothesis appears here.** Zero-dimensionality of the support is what makes the
hypothesis true; it plays no part in deriving the base case from it, and leaving it out keeps
this file independent of which `dim` the induction is run with.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {r : ℕ} (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **Twisting does not move a sheaf that no invertible sheaf moves.** If
`(tensorSheaf 𝒢 M : X.Modules) ≅ 𝒢` for every invertible `M`, then `twistList L e l 𝒢 ≅ 𝒢` for
every list of indices and every exponent vector: each factor `𝓛_i^{⊗ e_i}` is invertible, so the
hypothesis applies to it, and `AlgebraicGeometry.twistListIso` carries the resulting isomorphism
through the remaining factors. -/
noncomputable def twistListIsoOfTensorInvertibleIso (e : Fin r → ℤ) (G : X.Modules)
    (h : ∀ M : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M →
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.2)⟩).obj (G)).obj (M)) : X.Modules) ≅ G)) :
    ∀ l : List (Fin r), twistList L e l G ≅ G := by
  intro l
  induction l with
  | nil => exact Iso.refl _
  | cons i t ih =>
    exact twistListIso L e t
        (h (tensorPower X.presheaf X.ringCatSheaf.2 (L i) (e i))
          (tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 (L i) (e i))) ≪≫ ih

/-- **Every twist of `𝒢` is `𝒢`**, if tensoring `𝒢` by any invertible sheaf of modules gives
`𝒢` back. At zero-dimensional support that hypothesis is clause (5) of [Stacks, Tag 0AYT] at
rank one. -/
noncomputable def twistedSheafIsoOfTensorInvertibleIso (G : X.Modules)
    (h : ∀ M : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M →
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.2)⟩).obj (G)).obj (M)) : X.Modules) ≅ G))
    (n : Fin r → ℤ) :
    twistedSheaf G L n ≅ G :=
  twistListIsoOfTensorInvertibleIso L n G h (List.finRange r)

section EulerCharacteristic

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The base case of Tag 0BEM's induction, from the sheaf-level isomorphism.** If tensoring
the coherent sheaf `𝒢` by any invertible sheaf of modules gives `𝒢` back, then the Euler
characteristic of every twist of `𝒢` is that of `𝒢`, the two sheaves being isomorphic. -/
theorem eulerCharacteristic_twistedSheaf_eq_of_tensorInvertibleIso (G : X.Modules)
    (hG : SheafOfModules.IsCoherent G)
    (h : ∀ M : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M →
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.2)⟩).obj (G)).obj (M)) : X.Modules) ≅ G))
    (n : Fin r → ℤ) :
    @eulerCharacteristic k _ X f _ (twistedSheaf G L n)
        (@twistedSheaf_isCoherent X r G L _ hG n)
      = @eulerCharacteristic k _ X f _ G hG :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _ (@twistedSheaf_isCoherent X r G L _ hG n) hG
    (twistedSheafIsoOfTensorInvertibleIso L G h n)

/-- **[Stacks, Tag 0BEM] with its base case stated as the source proves it.** This is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_eulerCharacteristic_twist_eq` with
`hbase` replaced by the isomorphism `𝒢 ⊗ M ≅ 𝒢` for invertible `M` — the statement [Stacks, Tag
0AYT] establishes at zero-dimensional support, from which that tag's clause (5) at rank one
follows. The remaining debt of Tag 0BEM is `hstep` and `hdim`. -/
theorem exists_eulerPolynomial_twistedSheaf_of_tensorInvertibleIso (dim : X.Modules → ℕ)
    (hbase : ∀ (G : X.Modules), SheafOfModules.IsCoherent G → dim G = 0 →
      ∀ M : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M →
        (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              (X.ringCatSheaf.2)⟩).obj (G)).obj (M)) : X.Modules) ≅ G))
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G ≠ 0 → ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂), dim G₁ < dim G ∧ dim G₂ < dim G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (hdim : SheafOfModules.supp F ≠ ∅ →
      ((dim F : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (SheafOfModules.supp F)) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_eulerCharacteristic_twist_eq k f L dim
    (fun G hG hG0 n =>
      eulerCharacteristic_twistedSheaf_eq_of_tensorInvertibleIso L k f G hG (hbase G hG hG0) n)
    hstep F hF hdim

end EulerCharacteristic

end AlgebraicGeometry

end
