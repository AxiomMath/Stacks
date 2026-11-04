module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjDescent.Basic
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.Compare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twisting a module by an invertible module does not change its projective bundle

Let `X` be a scheme, `E` a quasi-coherent `𝒪_X`-module and `ℒ` an invertible `𝒪_X`-module. The
projective bundle `𝐏(E) = Proj_X(Sym E)` of Tag 01O4 is unchanged by twisting `E` by `ℒ`:
**`𝐏(E ⊗ ℒ) ≅ 𝐏(E)` as schemes over `X`.** This is [Stacks, Tag 02NC] in its projective-bundle
form.

The source's argument is *"This is the identity map when `ℒ ≅ 𝒪_X`. In general choose an open
covering of `X` such that `ℒ` is trivialized over the pieces and glue the corresponding maps."*
That is exactly what happens here, with the pieces being the trivializing affine opens of `ℒ`.
Over such an open `U` a trivialization of `ℒ` identifies `Γ(E, U)` with `Γ(E ⊗ ℒ, U)`, hence the
graded ring of sections of `Sym(E ⊗ ℒ)` over `U` with that of `Sym(E)`, hence the two charts of
the projective bundles over `U`
(`Stacks.SymTwistChart.chartProjIso`); the identification is over the base
(`Stacks.SymTwistChart.chartProjIso_hom_toBase`), does not depend on the trivialization chosen
(`Stacks.SymTwistChart.chartProjIso_eq`) and commutes with the transition morphisms of the charts
(`Stacks.SymTwistChart.chartProjIso_naturality`). Those are exactly the hypotheses of the descent
lemma `Stacks.AlgebraicGeometry.RelativeProjDescent.exists_iso_relativeProj_of_chartIso`, which
glues them.

## Main definitions

* `Stacks.SymProjectiveBundleTwist.chartIso`: the chart comparison over a trivializing affine
  open, for the chosen trivialization there.

## Main results

* `Stacks.SymProjectiveBundleTwist.exists_iso_schemeProjectiveBundle_tensorObj`:
  **`𝐏(E ⊗ ℒ) ≅ 𝐏(E)` over `X`** — there is an isomorphism of the projective bundle of `E ⊗ ℒ`
  with the projective bundle of `E` carrying one projection to `X` to the other.
* `Stacks.SymProjectiveBundleTwist.chartIso_hom_toBase` and
  `Stacks.SymProjectiveBundleTwist.chartIso_naturality`: the two compatibilities, at the chosen
  trivializations.

## Implementation notes

**No quasi-coherence of `E ⊗ ℒ` is assumed.** It is derived: an invertible module is
quasi-coherent (`Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible`) and the tensor
product of quasi-coherent modules is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj`, Tag 01CE). Quasi-coherence of
every homogeneous piece of the symmetric algebra, which is what the projective bundle of a module
on an arbitrary scheme needs, then follows from quasi-coherence of the module by
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`; so the statement carries no
hypothesis beyond quasi-coherence of `E` and invertibility of `ℒ`.

**One spelling of the tensor product.** `E ⊗ ℒ` is `Stacks.SymTwistChart.tensorObj E L`, which is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.sheaf.obj X.ringCatSheaf.property E L`;
that is the one spelling used, and `AlgebraicGeometry.Scheme.Modules.tensorObj` is accepted where
it is written because the two are definitionally equal.

**Two spellings of invertibility.** The chart comparison needs none, but the local triviality of
Tag 0B8M is stated for `AlgebraicGeometry.SheafOfModules.IsInvertible` while the hypothesis below
is `Stacks.SheafOfModules.IsInvertible`. They are the same statement about the same data, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; the `local instance` below is that
theorem, so that one hypothesis serves both and the statement of the result mentions only one.

**The bridge to the relative Proj is `rfl`.** `(schemeProjectiveBundle E hqc).scheme` is by
definition `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` of
`(schemeSheafGradedAlgebra E hqc).toGradedAlgebra`, and `schemeProjectiveBundleToBase` is
`relativeProjToBase` of the same, so the descent lemma's conclusion is the statement below with
no transport.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.TrivializingSite
open Stacks.SymGraded (schemeSheafGradedAlgebra schemeProjectiveBundle
  schemeProjectiveBundleToBase isQuasicoherentPieces_of_isQuasicoherent)

universe u

namespace Stacks.SymProjectiveBundleTwist

/-- The invertibility predicate of Tag 0B8M from the one of Tag 01CS: the two are the same
statement about the same data, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. Local, so that the library keeps
exactly one invertibility hypothesis in scope elsewhere. -/
local instance isInvertible_toAlgebraicGeometry {X : Scheme.{u}} {L : X.Modules}
    [h : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L h

variable {X : Scheme.{u}} (E L : X.Modules) [E.IsQuasicoherent]
  [hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **`E ⊗ ℒ` is quasi-coherent**, by Tag 01CE: `E` is quasi-coherent by hypothesis and `ℒ` is
quasi-coherent because it is invertible
(`Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible`, applied at the invertibility
spelling of Tag 01CS). So nothing about `E ⊗ ℒ` has to be assumed. -/
instance isQuasicoherent_tensorObj : (Stacks.SymTwistChart.tensorObj E L).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_tensorObj E L inferInstance
    (@Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L hinv)

/-- **The chart comparison over a trivializing affine open**, for the trivialization chosen
there. Which one is chosen does not matter:
`Stacks.SymTwistChart.chartProjIso_eq`. -/
def chartIso (W : Site L) :
    (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toGradedAlgebra.projOver W.1 ≅
      (schemeSheafGradedAlgebra E
          (isQuasicoherentPieces_of_isQuasicoherent E)).toGradedAlgebra.projOver W.1 :=
  Stacks.SymTwistChart.chartProjIso E L (isQuasicoherentPieces_of_isQuasicoherent E)
    (isQuasicoherentPieces_of_isQuasicoherent _) W.2.some W.1.2

/-- **Each chart comparison is an isomorphism over the base.** -/
theorem chartIso_hom_toBase (W : Site L) :
    (chartIso E L W).hom ≫ (schemeSheafGradedAlgebra E
        (isQuasicoherentPieces_of_isQuasicoherent E)).toGradedAlgebra.toBase W.1 =
      (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
        (isQuasicoherentPieces_of_isQuasicoherent _)).toGradedAlgebra.toBase W.1 :=
  Stacks.SymTwistChart.chartProjIso_hom_toBase E L (isQuasicoherentPieces_of_isQuasicoherent E)
    (isQuasicoherentPieces_of_isQuasicoherent _) W.1 W.2.some

/-- **The chart comparisons are natural in the trivializing affine open.** The trivializations
chosen over the two opens are unrelated, which is harmless because the comparison does not depend
on the trivialization. -/
theorem chartIso_naturality {W W' : Site L} (h : W ⟶ W') :
    (chartIso E L W).hom ≫ (chartFunctor (schemeSheafGradedAlgebra E
          (isQuasicoherentPieces_of_isQuasicoherent E)).toGradedAlgebra).map (Site.homVal h) =
      (chartFunctor (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toGradedAlgebra).map (Site.homVal h) ≫
        (chartIso E L W').hom :=
  Stacks.SymTwistChart.chartProjIso_naturality E L (isQuasicoherentPieces_of_isQuasicoherent E)
    (isQuasicoherentPieces_of_isQuasicoherent _) W'.1 W.1 (Site.homVal h) W'.2.some W.2.some

/-- **[Stacks, Tag 02NC] for projective bundles.** For a scheme `X`, a quasi-coherent
`𝒪_X`-module `E` and an invertible `𝒪_X`-module `ℒ`, the projective bundle `𝐏(E ⊗ ℒ)` is
isomorphic to the projective bundle `𝐏(E)`, by an isomorphism of schemes over `X`: it carries the
projection `𝐏(E) ⟶ X` to the projection `𝐏(E ⊗ ℒ) ⟶ X`.

Over the chart of an affine open of `X` trivializing `ℒ` the isomorphism is the chart comparison
`Stacks.SymTwistChart.chartProjIso`; the glueing is
`Stacks.AlgebraicGeometry.RelativeProjDescent.exists_iso_relativeProj_of_chartIso`. -/
@[ega "II 4.1.4" "partial"]
theorem exists_iso_schemeProjectiveBundle_tensorObj :
    ∃ f : (schemeProjectiveBundle (Stacks.SymTwistChart.tensorObj E L)
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅
        (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).scheme,
      f.hom ≫ schemeProjectiveBundleToBase E (isQuasicoherentPieces_of_isQuasicoherent E) =
        schemeProjectiveBundleToBase (Stacks.SymTwistChart.tensorObj E L)
          (isQuasicoherentPieces_of_isQuasicoherent _) :=
  Stacks.AlgebraicGeometry.RelativeProjDescent.exists_iso_relativeProj_of_chartIso L
    (chartIso E L) (chartIso_hom_toBase E L) (fun {_ _} h => chartIso_naturality E L h)

end Stacks.SymProjectiveBundleTwist

end
