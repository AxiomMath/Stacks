module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic

/-!
# Affine sections of the tower of ideal-power quotients

Two towers of ideal-power quotients of one coherent module occur in the formal-geometry chapters,
and they differ by an index shift. The completion functor of Stacks 0880 keeps the numbering of
the source, where the system is indexed by positive integers, so its `n`-th term is
`F / I ^ (n+1) F`. The tower `Stacks.Algebraization.adicQuotientSystem` is indexed by the exponent
itself, so its `n`-th term is `F / I ^ n F`; that is the indexing of
`Stacks.Algebraization.formalSections`, which evaluates that tower on an open.

The affine-sections computation of Stacks 0880 is stated at the first indexing:
`Stacks.Algebraization.completionQuotientSectionsEquiv` identifies the sections of the completion's
`n`-th term over an affine open `U` with `F(U) / I(U) ^ (n+1) F(U)`. This file transports it to the
second, so that the computation reads as a statement about the sections of the tower that
`formalSections` actually evaluates, namely its term at `n + 1`.

## Main definitions

* `Stacks.Algebraization.adicQuotientSectionsEquiv` — the sections over an affine open `U` of the
  `(n+1)`-st term `F / I ^ (n+1) F` of the tower of ideal-power quotients, identified with the
  module quotient `F(U) / I(U) ^ (n+1) F(U)`.

## Main results

* `Stacks.Algebraization.adicQuotientSectionsEquiv_mk` — the identification sends the class of a
  section to its image under the quotient projection.

## Implementation notes

The comparison of the two towers is not proved here: it already exists. At the level of objects it
is `Stacks.Algebraization.completionFunctor_obj`, which states the completion's `n`-th term as
`idealPowerQuotient I (n+1) F.obj` — the very term the ideal-power tower takes at `n + 1`, since
`Stacks.Algebraization.adicQuotientSystem` is defined by that same cokernel and reduces to it.
`Stacks.Algebraization.NeighbourhoodHoms.towerIso` packages that equality as an isomorphism and
carries the transition maps across it. Only the object comparison is needed here, and it is used
through `eqToIso`; `towerIso` itself is not imported, since `NeighbourhoodHoms` proves Stacks 0EIV
and sits far above this file.

The transport on sections is `AlgebraicGeometry.sectionsLinearEquivOfIso`, which is linear for the
sections of the structure sheaf, so composing it with
`Stacks.Algebraization.completionQuotientSectionsEquiv` stays inside `Γ(X, U)`-linear maps and
needs no `RingHomCompTriple`.

The statement elaborates only once the module structure on sections is available at the spelling
in which the scalar ring is `Γ(X, U)` and the module is the sections of a
`SheafOfModules X.ringCatSheaf`: it is in that spelling that `Ideal • Submodule` resolves, and the
elaborator otherwise selects the `ringCatSheaf.val` spelling of the scalar ring, for which the
action of an ideal on a submodule has no instance. The bridging `local instance`s are those of
`Stacks.Algebraization.CompletionFunctor.AffineSections`, reactivated here rather than restated.

`adicQuotientSectionsEquiv_mk` is the computation rule, and the quotient projection it names is
the plain `cokernel.π` of the ideal-power subsheaf rather than
`Stacks.Algebraization.completionProjection`, which is that projection followed by the `eqToHom`
of the object comparison. Cancelling that `eqToHom` against the one introduced by the transport is
`Stacks.Algebraization.comp_eqToHom_symm_comp_eqToHom`.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf
attribute [local instance] sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

/-- The projection of `F` onto the `n`-th term of its completion, read in the tower of ideal-power
quotients, is the quotient projection onto `F / I ^ (n+1) F`.

`Stacks.Algebraization.completionProjection` is by definition the quotient projection followed by
the `eqToHom` of `Stacks.Algebraization.completionFunctor_obj`, so composing with the `eqToHom`
back cancels it. -/
private theorem completionProjection_comp_eqToHom (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X I F n ≫ eqToHom (completionFunctor_obj X I F n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι :=
  (congrArg (fun k => completionProjection X I F n ≫ k)
      (Category.comp_id (eqToHom (completionFunctor_obj X I F n))).symm).trans
    ((comp_eqToHom_symm_comp_eqToHom
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι)
        (completionFunctor_obj X I F n) (𝟙 _)).trans
      (Category.comp_id _))

/-- **Stacks 0880**, read off the tower of ideal-power quotients. The sections over an affine open
`U` of the `(n+1)`-st term `F / I ^ (n+1) F` of the tower
`Stacks.Algebraization.adicQuotientSystem`, identified with the module quotient
`F(U) / I(U) ^ (n+1) F(U)`.

This is `Stacks.Algebraization.completionQuotientSectionsEquiv` transported along the comparison of
the two indexings of the tower, so that the affine-sections computation applies to the tower that
`Stacks.Algebraization.formalSections` evaluates. -/
public noncomputable def adicQuotientSectionsEquiv (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    (Γ(F.obj, U) ⧸ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U))) ≃ₗ[Γ(X, U)]
      ((adicQuotientSystem I F.obj).obj (op (n + 1))).val.obj (op U.1) :=
  (completionQuotientSectionsEquiv X I F n U).trans
    (AlgebraicGeometry.sectionsLinearEquivOfIso
      (eqToIso (completionFunctor_obj X I F n)) U.1)

/-- The identification of affine sections of the tower of ideal-power quotients sends the class of
a section to its image under the quotient projection. -/
public theorem adicQuotientSectionsEquiv_mk (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) (x : Γ(F.obj, U)) :
    adicQuotientSectionsEquiv X I F n U (Submodule.Quotient.mk x) =
      (cokernel.π (C := X.Modules)
        (idealPowerMultiple I (n + 1) F.obj).ι).val.app (op U.1) x := by
  have h1 : adicQuotientSectionsEquiv X I F n U (Submodule.Quotient.mk x) =
      (eqToHom (completionFunctor_obj X I F n)).val.app (op U.1)
        ((completionProjection X I F n).val.app (op U.1) x) := by
    simp only [adicQuotientSectionsEquiv]
    rfl
  exact h1.trans
    (congrArg (fun g : F.obj ⟶ (adicQuotientSystem I F.obj).obj (op (n + 1)) =>
        g.val.app (op U.1) x)
      (completionProjection_comp_eqToHom X I F n))

end Stacks.Algebraization

end
