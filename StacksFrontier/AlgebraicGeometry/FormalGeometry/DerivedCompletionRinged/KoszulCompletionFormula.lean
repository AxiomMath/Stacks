module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulNaiveDualTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion on a ringed site is the derived limit of Koszul tensor products

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, let `ℐ ⊂ 𝒪` be the
ideal sheaf they generate and let `K ∈ D(𝒪)`. [Stacks, Tag 0A0E] states that the derived
completion `K^∧` of [Stacks, Tag 099B] is

`K^∧ = R lim (K ⊗^𝐋_𝒪 K_n)`,

where `K_n = K(𝒪, f_1^n, …, f_r^n)` is the Koszul complex on `f_1^n, …, f_r^n` over `𝒪`, sitting
in degrees `-r, …, 0`. This file states and proves that formula with no hypothesis beyond the
source's.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorKoszulComplex_completionFunctor`:
  **[Stacks, Tag 0A0E].**

## The statement, clause by clause

* *A ringed site, global sections `f_1, …, f_r`, `K ∈ D(𝒪)`.* `X : RingedSite.{u, u, u}`,
  `f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat)` and an object `K` of the
  unbounded derived category of sheaves of `𝒪`-modules. Every instance the statement uses —
  sheafification and local bijectivity for `AddCommGrpCat`, additivity of the sheaf tensor
  product, the total tensor complexes, countable products in `D(𝒪)` — is found by instance search
  for such a site; none is a binder. The ideal sheaf `ℐ` enters the source only through the
  completion, as it does here.
* *`K^∧`.* `AlgebraicGeometry.RingedSite.completionFunctor`, the formula
  `K^∧ = R𝑆heafHom_𝒪(Č(f), K)` of [Stacks, Tag 099B]. That it *is* the derived completion along
  `ℐ = AlgebraicGeometry.RingedSite.idealOfGlobalSections X f` — the left adjoint of the inclusion
  of the derived-complete objects, with unit `K ⟶ K^∧` — is the content of the two carriers of
  Tag 099B, `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections`
  and `AlgebraicGeometry.RingedSite.bijective_precomp_completionUnit_idealOfGlobalSections`.
* *`K_n`.* `AlgebraicGeometry.RingedSite.koszulNaiveDualComplex X f n`, the Koszul complex on
  `f_1^{n+1}, …, f_r^{n+1}` in degrees `-r, …, 0`: its degree-`-p` term is the product of copies
  of `𝒪` indexed by the `p`-element subsets of `{1, …, r}`, that is `∧^p(𝒪^{⊕ r})`
  (`AlgebraicGeometry.RingedSite.koszulNaiveDualComplex_X`), and its differential is the Koszul
  contraction (`AlgebraicGeometry.RingedSite.koszulNaiveDualComplex_d`). It is, as the source's
  proof says, `𝑆heafHom_𝒪(K^n, 𝒪)` for the Koszul complex `K^n` in degrees `0, …, r` whose colimit
  is the extended alternating Čech complex (`AlgebraicGeometry.RingedSite.koszulPowerComplex`):
  `AlgebraicGeometry.RingedSite.koszulNaiveDualComplexIso`. The transition maps of the tower are
  the duals of those of `K^n` (`AlgebraicGeometry.RingedSite.koszulNaiveDualSystem`).
* *`K ⊗^𝐋_𝒪 K_n`.* The canonical derived tensor product of [Stacks, Tag 06YU],
  `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, with `K` in the first variable.
* *`R lim`.* `CategoryTheory.Pretriangulated.IsDerivedLimit`: `R lim` of an inverse system in a
  triangulated category is defined only up to non-unique isomorphism (it completes the Milnor
  difference map to a distinguished triangle), so the source's equality is read as *`K^∧` is a
  derived limit of the tower*, which determines it up to isomorphism.
* *Indexing.* The index `n : ℕ` carries the exponent `n + 1`, so the tower runs over the positive
  powers of the `f_i`, as the source's does.

## Proof

As in the source: the Čech complex is the homotopy colimit of the Koszul complexes `K^n`
([Stacks, Tag 0913] followed by [Stacks, Tag 0949],
`AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem`), the completion is
`R𝑆heafHom` out of it, and [Stacks, Tag 0A0A] turns that into the derived limit of
`K ⊗^𝐋_𝒪 (K^n)^∨`, its input clause 3 of [Stacks, Tag 08JJ] at the Koszul complexes being
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_koszulPowerSystem`; finally the
derived dual of `K^n` is its termwise dual `K_n`, compatibly with the transition maps
(`AlgebraicGeometry.RingedSite.koszulNaiveDualSystemIso`).

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `K ∈ D(𝒪)`.
The derived completion `K^∧` of [Stacks, Tag 099B] along the ideal sheaf generated by `f_1, …, f_r`
is `R lim (K ⊗^𝐋_𝒪 K_n)`, where `K_n` is the Koszul complex on `f_1^n, …, f_r^n` over `𝒪`, in
degrees `-r, …, 0`.

Here `K^∧` is `AlgebraicGeometry.RingedSite.completionFunctor X f`, the tower is indexed by the
positive exponents `n + 1`, `K_{n+1}` is
`AlgebraicGeometry.RingedSite.koszulNaiveDualComplex X f n` (the `n`-th member of
`AlgebraicGeometry.RingedSite.koszulNaiveDualSystem X f`), `⊗^𝐋_𝒪` is the canonical derived tensor
product, and `R lim` is read as the predicate `CategoryTheory.Pretriangulated.IsDerivedLimit`. -/
@[stacks 0A0E]
theorem isDerivedLimit_tensorKoszulComplex_completionFunctor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsDerivedLimit
      (koszulNaiveDualSystem X f ⋙ DerivedCategory.Q ⋙
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K)
      ((completionFunctor X f).obj K) :=
  isDerivedLimit_tensorKoszulNaiveDualSystem_koszulPowerSystem X f _ K

end AlgebraicGeometry.RingedSite

end
