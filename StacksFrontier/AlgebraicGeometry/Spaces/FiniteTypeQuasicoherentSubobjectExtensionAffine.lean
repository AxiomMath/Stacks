module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionOfColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finite type quasi-coherent submodule on an affine algebraic space

Let `V` be an affine algebraic space, `U ⊆ V` a quasi-compact open subspace, `ℱ` a quasi-coherent
`𝒪_V`-module and `𝒢 ⊆ ℱ|_U` a quasi-coherent submodule of finite type.  This file proves that
`𝒢` is the restriction of a quasi-coherent submodule of `ℱ` of finite type: the base case of the
induction on elementary distinguished squares by which Stacks 0853 is proved here.

It is the extension argument of
`AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension_of_isColimit`, fed with
the colimit clause of Stacks 0829 on an affine algebraic space,
`Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace`, and with Stacks
03M9 for the inclusion of `U`, which is quasi-compact because `U` is and an affine algebraic space
is quasi-separated.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAffineSpace`: an affine algebraic space
  is quasi-separated.
* `AlgebraicGeometry.Space.exists_etaleSubmodule_extension_of_isAffineSpace`: the extension, for
  sheaf submodules.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine algebraic space is quasi-separated**: it is represented by an affine scheme,
which is quasi-separated, and Stacks 03JX applies. -/
theorem isAbsolutelyQuasiSeparated_of_isAffineSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAffineSpace B S hS V) : IsAbsolutelyQuasiSeparated B S hS hZ V := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hV
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS V hZ
    ⟨T, inferInstance, ⟨Functor.representableByEquiv.symm e.symm⟩⟩

/-- **Stacks 0853 on an affine algebraic space**, for sheaf submodules.  Let `V` be an affine
algebraic space, `U ⊆ V` a quasi-compact open subspace, `ℱ` a quasi-coherent `𝒪_V`-module and
`𝒢 ⊆ ℱ|_U` a quasi-coherent submodule of finite type.  Then `𝒢` is the restriction of a
quasi-coherent submodule of `ℱ` of finite type. -/
@[sga "6 0 2.11" "special case"]
theorem exists_etaleSubmodule_extension_of_isAffineSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (V : AlgebraicSpaces B S hS)
    (hVa : IsAffineSpace B S hS V.1) (U : Subfunctor V.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (F : Modules.{u, u} B S hS V.1 V.2) (hF : F.IsQuasicoherentOnSite)
    (G : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU)).obj F).Submodule)
    (hGq : G.toSheafOfModules.IsQuasicoherentOnSite) (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧
      etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U hU) K = G := by
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hj : IsOpenImmersion B S hS (openSubspaceHom B S hS U hU).hom := hU.2
  have hjqc : IsQuasiCompact B S hS (openSubspaceHom B S hS U hU).hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ V.2 hVqs hUqc _
  have hjqs : IsQuasiSeparated B S hS (openSubspaceHom B S hS U hU).hom :=
    isQuasiSeparated_of_mono B S hS _ (mono_of_presheaf_isOpenImmersion hj)
  exact exists_etaleSubmodule_extension_of_isColimit B S hS (openSubspaceHom B S hS U hU) hj
    (fun M hM => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS _ hjqc hjqs M hM)
    (fun H hH => by
      have := hH
      exact nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace
        B S hS V.2 hVa H)
    hUqc F hF G hGq hGf

end AlgebraicGeometry.Space

end
