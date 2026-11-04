module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Affine
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Universal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective bundle of a quasi-coherent module on an affine scheme

`Stacks.SymGraded.symSheafGradedAlgebra` takes an `R`-module `M` and produces `Sym(M~)` as
relative Proj data on `Spec R`. A quasi-coherent module `E` on `Spec R` is not literally an
associated sheaf, but it is canonically isomorphic to one: Mathlib's
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` says the counit
`Γ(E)~ ⟶ E` of the tilde–Gamma adjunction is an isomorphism. **This file therefore attaches to
every quasi-coherent module on an affine scheme its symmetric algebra as relative Proj data, and
its projective bundle** — which is Tag 01OB for an affine base.

## Main definitions

* `Stacks.SymGraded.globalSections`: the `R`-module of global sections of a module on `Spec R`,
  the module whose associated sheaf it is.
* `Stacks.SymGraded.qcohSheafGradedAlgebra`: **`Sym(E)` as relative Proj data**, for `E`
  quasi-coherent on `Spec R`.
* `Stacks.SymGraded.qcohGenerator`: its degree-one generator `E ⟶ Sym(E)₁`, the inverse of the
  counit followed by `Stacks.SymGraded.symGen`.
* `Stacks.SymGraded.qcohProjectiveBundle`: **`P(E) = Proj_{Spec R}(Sym(E))`**, with its
  projection and its affine Proj charts.

## Main results

* `Stacks.SymGraded.qcohSheafGradedAlgebra_piece`: the degree-`n` piece is `Sym^n_R(Γ(E))~`.
* `Stacks.SymGraded.isSymmetricAlgebra_qcoh`: the underlying sheaf of graded algebras **is** the
  symmetric algebra of `Γ(E)~`, in the sense of the full universal property
  `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`.
* `Stacks.SymGraded.qcohProjectiveBundle_isPullback` and
  `qcohProjectiveBundle_chart_transition`: the charts are the inverse images of the affine opens
  and are compatible with restriction of homogeneous sections.

## Implementation notes

The module `E` is replaced by `globalSections E` and not the other way round: every statement
about the bundle is then a statement about `Stacks.SymGraded.symAlgebra (globalSections E)`, for
which the development already has the universal property, the functoriality and the comparison
with the symmetric powers of the associated sheaf. The only place `E` itself appears is
`qcohGenerator`, which is where the counit isomorphism is inverted.

Quasi-coherence of `E` is used for exactly one thing — that the counit is an isomorphism — and it
is not needed at all for `qcohSheafGradedAlgebra`, which is why that definition does not assume
it. A reader wanting `Sym` of a *non*-quasi-coherent module should note that
`qcohSheafGradedAlgebra E` is then the symmetric algebra of the associated sheaf of `Γ(E)`, which
is not `E`.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)

## Not done here

**Tag 01OB is not claimed here.** It is the projective bundle of a quasi-coherent module on an
arbitrary scheme, and the base here is affine.

**The two things this section used to record as blocking the general case are now proved**, and a
projective bundle on an arbitrary scheme exists; what 01OB still lacks is its twists, below.

* the base change of a symmetric power is
  `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int` of
  `StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/BaseChange.lean`;
* quasi-coherence of the homogeneous pieces of the sectionwise symmetric algebra of a
  quasi-coherent module on a scheme is
  `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` of
  `StacksFrontier/AlgebraicGeometry/SymAlgebraQcohPieces/Basic.lean`.

So `Stacks.SymGraded.schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)` of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Scheme.lean` is an unconditional
construction of `P(E)` for a quasi-coherent `E` on an arbitrary scheme. The reason 01OB is still
unclaimed anywhere is its remaining two clauses: neither the twists of the bundle nor their
invertibility is addressed, because this repository has no twist construction over
`SheafGradedAlgebra` data.

Nothing is proved about the functoriality of `qcohProjectiveBundle` in `E`, nor about its fibres.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.SymGraded

universe u

variable {R : CommRingCat.{u}} (E : (Spec R).Modules)

/-- The `R`-module of global sections of a module on `Spec R`. For `E` quasi-coherent, `E` is the
associated sheaf of this module. -/
public abbrev globalSections : ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj E).presheaf.obj (.op ⊤)

/-- **The symmetric algebra of a module on an affine scheme, as relative Proj data.** For `E`
quasi-coherent this is `Sym(E)`. -/
public def qcohSheafGradedAlgebra : SheafGradedAlgebra (Spec R) :=
  symSheafGradedAlgebra (globalSections E)

/-- The degree-`n` piece is the associated sheaf of the `n`-th symmetric power of the global
sections, on the nose. -/
public theorem qcohSheafGradedAlgebra_piece (n : ℕ) :
    (qcohSheafGradedAlgebra E).piece (n : ℤ) =
      tilde (ModuleCat.of R (SymPow.symmetricPower n R (globalSections E))) := rfl

/-- **The underlying sheaf of graded algebras is the symmetric algebra of `Γ(E)~`**, with its
full universal property: every morphism of the degree-one part into a sheaf of graded algebras
with pairwise commuting image extends uniquely to a unital homomorphism. -/
public theorem isSymmetricAlgebra_qcoh :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra
      (symAlgebra (globalSections E)) (symGen (globalSections E)) :=
  isSymmetricAlgebra (globalSections E)

/-- **The degree-one generator** `E ⟶ Sym(E)₁`, for `E` quasi-coherent: the inverse of the
tilde–Gamma counit followed by the degree-one inclusion of the symmetric algebra. -/
public def qcohGenerator [E.IsQuasicoherent] : E ⟶ (qcohSheafGradedAlgebra E).piece 1 :=
  inv E.fromTildeΓ ≫ symGen (globalSections E)

/-- **The projective bundle `P(E) = Proj_{Spec R}(Sym(E))`** of a quasi-coherent module on an
affine scheme, with its projection to `Spec R` and its affine Proj charts. -/
@[ega "II 4.1.1" "special case"]
public def qcohProjectiveBundle :
    Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData (qcohSheafGradedAlgebra E) :=
  Stacks.AlgebraicGeometry.RelativeProj.relativeProj (qcohSheafGradedAlgebra E)

/-- The projection of the projective bundle to its base. -/
public def qcohProjectiveBundleToBase : (qcohProjectiveBundle E).scheme ⟶ Spec R :=
  (qcohProjectiveBundle E).toBase

/-- **Each chart of the projective bundle is the inverse image of its affine open.** -/
public theorem qcohProjectiveBundle_isPullback (U : (Spec R).Opens) (hU : IsAffineOpen U) :
    IsPullback ((qcohProjectiveBundle E).chart U hU)
      (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (qcohSheafGradedAlgebra E) U hU)
      (qcohProjectiveBundleToBase E) U.ι :=
  (qcohProjectiveBundle E).chart_isPullback U hU

/-- **The charts are compatible with restriction of homogeneous sections.** -/
public theorem qcohProjectiveBundle_chart_transition (U V : (Spec R).Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap
        (qcohSheafGradedAlgebra E) U V h hU hV ≫ (qcohProjectiveBundle E).chart V hV =
      (qcohProjectiveBundle E).chart U hU :=
  (qcohProjectiveBundle E).chart_transition U V h hU hV

end Stacks.SymGraded

end
