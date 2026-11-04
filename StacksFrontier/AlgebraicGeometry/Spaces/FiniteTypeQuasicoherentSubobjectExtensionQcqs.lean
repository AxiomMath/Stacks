module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple

/-!
# Stacks 0853: extending a finite type quasi-coherent submodule from a quasi-compact open

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `U ⊆ X` a
quasi-compact open subspace, `ℱ` a quasi-coherent `𝒪_X`-module and `𝒢 ⊆ ℱ|_U` a quasi-coherent
`𝒪_U`-submodule of finite type.  Stacks 0853 asserts that there is a quasi-coherent submodule
`𝒢' ⊆ ℱ` of finite type with `𝒢'|_U = 𝒢`.  This file proves it, unconditionally.

## The argument

The source deduces the statement from Stacks 0829, whose colimit assertion it obtains from
Stacks 07V9 and so from absolute Noetherian approximation, Stacks 07SU.  The proof here avoids
both, and goes by the induction principle for quasi-compact quasi-separated algebraic spaces,
Stacks 08GP (`AlgebraicGeometry.Space.qcqs_induction_on_self`), applied to the *extension
property* `AlgebraicGeometry.Space.ExtensionProperty`:

* on an affine algebraic space the extension property holds
  (`AlgebraicGeometry.Space.extensionProperty_of_isAffineSpace`): there the colimit assertion
  of Stacks 0829 is proved directly, in `AlgebraicGeometry` as
  `Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace`, and the
  source's argument then goes through;
* the extension property passes across an elementary distinguished square with affine étale
  member (`AlgebraicGeometry.Space.extensionProperty_of_isElementaryDistinguishedSquare`), by
  glueing submodules over the open subspace and over the étale member.

## Main results

* `AlgebraicGeometry.Space.extensionProperty_of_isQuasiCompactSpace`: every quasi-compact and
  quasi-separated algebraic space has the extension property.
* `AlgebraicGeometry.Space.exists_etaleSubmodule_extension`: **Stacks 0853**.

## Implementation notes

A submodule of `ℱ|_U` is a `SheafOfModules.Submodule` of the étale restriction of `ℱ` to the
open subspace `U`, and `𝒢'|_U = 𝒢` is the equality of submodules
`AlgebraicGeometry.Space.etaleSubmoduleRestrict … 𝒢' = 𝒢`: the restriction of a submodule has the
sections of the submodule over the composite charts.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every quasi-compact and quasi-separated algebraic space has the extension property**, by
the induction principle of Stacks 08GP. -/
theorem extensionProperty_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ExtensionProperty B S hS X := by
  have h := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y, ExtensionProperty B S hS ⟨Y, hY⟩)
    (fun V hVa hY => extensionProperty_of_isAffineSpace B S hS hZ ⟨V.1.left.1, hY⟩ hVa)
    (fun W V U f _ hsq _ hWqs hUqc hVa hPU hPV _ hY =>
      extensionProperty_of_isElementaryDistinguishedSquare B S hS hZ (W := ⟨W.1.left.1, hY⟩)
        hsq hWqs hUqc hVa (hPU _) (hPV _))
  exact h X.2

/-- **Stacks 0853.** Let `X` be a quasi-compact and quasi-separated algebraic space over `S`,
`U ⊆ X` a quasi-compact open subspace, `ℱ` a quasi-coherent `𝒪_X`-module and `𝒢 ⊆ ℱ|_U` a
quasi-coherent `𝒪_U`-submodule of finite type.  Then there is a quasi-coherent submodule
`𝒢' ⊆ ℱ` of finite type with `𝒢'|_U = 𝒢`. -/
@[stacks 0853]
theorem exists_etaleSubmodule_extension (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (G : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU)).obj F).Submodule)
    (hGq : G.toSheafOfModules.IsQuasicoherentOnSite) (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ G' : F.Submodule, G'.toSheafOfModules.IsQuasicoherentOnSite ∧
      G'.toSheafOfModules.IsFiniteType ∧
      etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U hU) G' = G :=
  extensionProperty_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs F hF U hU hUqc G hGq hGf

end AlgebraicGeometry.Space

end
