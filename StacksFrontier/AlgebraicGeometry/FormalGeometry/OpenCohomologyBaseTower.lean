module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentSheafHypothesisTranslation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologySpelling
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TildeAdicQuotientTower

/-!
# `Hⁱ(U, −)` on the open complement as a functor, and the tower `n ↦ Hⁱ(U, ℱ/Iⁿℱ)`

`Stacks.Algebraization.openCohomologyBase` is `Hⁱ(W, 𝒢)` for a module `𝒢` on an open subscheme
`W ⊆ Spec(A)`, read as an `A`-module; it is the left-hand side of the comparison of
[Stacks, Tag 0DXQ] as the source writes it, a cohomology group of a sheaf *on the open*.  That
spelling is given objectwise, which is enough to name one group and not enough to name an inverse
limit over a tower: a limit needs the transition maps.

This file supplies the functor form and the one comparison a tower needs.

## Main definitions

* `Stacks.Algebraization.openCohomologyBaseFunctor` — `Hⁱ(W, −)` on the modules of an open
  subscheme `W ⊆ Spec(A)`, valued in `A`-modules.  Its value at `𝒢` is
  `Stacks.Algebraization.openCohomologyBase`, by `rfl`.

## Main results

* `Stacks.Algebraization.restrictedTildeOpenCohomologyBaseNatIso` — on the restricted associated
  sheaves `Ñ|_U` the functor above agrees with
  `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor`, naturally in `N`.
* `Stacks.Algebraization.quotientSystemOpenCohomologyNatIso` — for a module `ℱ` on
  `U = Spec(A) ∖ V(𝔞)` whose adic quotient tower `n ↦ ℱ/Iⁿℱ` is presented as
  `n ↦ (M/IⁿM)~|_U`, the tower of `A`-modules `n ↦ Hⁱ(U, ℱ/Iⁿℱ)` is isomorphic — transition maps
  included — to `n ↦ Hⁱ(U, (M/IⁿM)~)`.  The limit of the latter is the target of the comparison
  map of [Stacks, Tag 0DXQ],
  `Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodToPuncturedLimit`, so this is what
  identifies that target with the source's `lim_n Hⁱ(U, ℱ/Iⁿℱ)`.

## Implementation notes

The functor is the one `Stacks.Algebraization.openCohomologyFunctor` already derives, with the
open subscheme as a parameter in place of a whole
`Stacks.Algebraization.AlgebraizationSituation`: deriving the global sections of `𝒪_W`-modules and
restricting scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(W, 𝒪_W)` in two steps rather than one.  The two
agree on the nose — `Stacks.Cohomology.AffineBase.moduleGlobalSections W.toScheme` is the
evaluation at `⊤` that `openCohomologyFunctor` derives, and iterated restriction of scalars is
restriction along the composite — so
`Stacks.Algebraization.restrictedTildeOpenCohomologyBaseNatIso` is
`Stacks.Algebraization.openCohomologyRestrictedTildeNatIso` at the situation with `I = ⊥`, whose
`U` is this `W`.  The ideal `I` of a situation plays no part in its `U`, which is why `⊥` may be
taken: the reparameterization drops the standing `I ⊆ 𝔞` of
`Stacks.Algebraization.AlgebraizationSituation`, and so applies to an open complement that is not
a neighbourhood of the formal locus of any ideal.

With that in hand the tower comparison is two whiskerings of the given presentation of
`n ↦ ℱ/Iⁿℱ`, the associativity of functor composition being definitional.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite
open AlgebraicGeometry.ProEtale
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.LocalCohomologyTilde (globalToBase)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

variable {A : Type u} [CommRing A]

/-! ### `Hⁱ(W, −)` as a functor -/

/-- **`Hⁱ(W, −)` for an open subscheme `W ⊆ Spec(A)`, valued in `A`-modules.**  The `i`-th right
derived functor of global sections on `W`, with scalars restricted along
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(W, 𝒪_W)`.  Its value at `𝒢` is
`Stacks.Algebraization.openCohomologyBase A W 𝒢 i`. -/
abbrev openCohomologyBaseFunctor (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).Opens) (i : ℕ) : W.toScheme.Modules ⥤ ModuleCat.{u} A :=
  (moduleGlobalSections W.toScheme).rightDerived i ⋙
    ModuleCat.restrictScalars W.ι.appTop.hom ⋙ globalToBase (CommRingCat.of A)

/-- The value of `openCohomologyBaseFunctor A W i` at `G` is `openCohomologyBase A W G i`. -/
theorem openCohomologyBaseFunctor_obj (W : (Spec (CommRingCat.of A)).Opens)
    (G : W.toScheme.Modules) (i : ℕ) :
    (openCohomologyBaseFunctor A W i).obj G = openCohomologyBase A W G i :=
  rfl

/-! ### The two spellings of `Hⁱ(U, −)` agree on the restricted associated sheaves -/

variable [IsNoetherianRing A]

/-- **[Stacks, Tag 01E1] (2), as a natural isomorphism in the `complementZeroLocus` spelling.**
For `U = Spec(A) ∖ V(𝔞)` the cohomology `Hⁱ(U, Ñ|_U)` of a module on the open subscheme `U` and
the cohomology `Hⁱ(U, Ñ)` over `U` of a sheaf on the ambient `Spec(A)` —
`Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor` — agree, naturally in the
`A`-module `N`.

This is `Stacks.Algebraization.openCohomologyRestrictedTildeNatIso` at the algebraization
situation with the same `𝔞` and with `I = ⊥`: the ideal `I` of a situation does not enter its
open complement, so taking it `⊥` costs nothing and drops the standing hypothesis `I ⊆ 𝔞`. -/
def restrictedTildeOpenCohomologyBaseNatIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (i : ℕ) :
    (tilde.functor (CommRingCat.of A) ⋙
          Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι) ⋙
        openCohomologyBaseFunctor A (complementZeroLocus A a) i ≅
      complementCohomologyBaseFunctor (A := CommRingCat.of A) a i :=
  openCohomologyRestrictedTildeNatIso { A := A, I := ⊥, a := a, I_le_a := bot_le } i

/-! ### The tower `n ↦ Hⁱ(U, ℱ/Iⁿℱ)` -/

/-- **The tower of cohomology groups of the adic quotients, read through a presentation.**  Let
`ℱ` be a module on `U = Spec(A) ∖ V(𝔞)` and let `M` be an `A`-module presenting the adic quotient
tower of `ℱ` as `n ↦ (M/IⁿM)~|_U`.  Then the tower of `A`-modules `n ↦ Hⁱ(U, ℱ/Iⁿℱ)` is
isomorphic to `n ↦ Hⁱ(U, (M/IⁿM)~)`, transition maps included.

Taking the limit of the right-hand tower gives the target of
`Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodToPuncturedLimit`, the comparison map
of [Stacks, Tag 0DXQ]; so this is the identification of that target with the source's
`lim_n Hⁱ(U, ℱ/Iⁿℱ)`.  Being an isomorphism of towers it is stronger than the induced
isomorphism of limits, and in particular it does not depend on either limit existing. -/
def quotientSystemOpenCohomologyNatIso (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (M : ModuleCat.{u} A)
    (e : quotientSystemNearVanishing A I a F ≅
      (adicQuotientModuleSystem A I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι)
    (i : ℕ) :
    quotientSystemNearVanishing A I a F ⋙
        openCohomologyBaseFunctor A (complementZeroLocus A a) i ≅
      adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) a i :=
  Functor.isoWhiskerRight e (openCohomologyBaseFunctor A (complementZeroLocus A a) i) ≪≫
    Functor.isoWhiskerLeft (adicQuotientModuleSystem A I M)
      (restrictedTildeOpenCohomologyBaseNatIso A a i)

end Stacks.Algebraization

end
