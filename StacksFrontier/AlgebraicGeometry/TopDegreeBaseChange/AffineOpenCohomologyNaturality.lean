module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology

/-!
# [Stacks, Tag 01XK] is natural in the coefficient, in the spelling its consumers meet

`Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward` is
[Stacks, Tag 01XK]: for a quasi-compact quasi-separated `f : X ⟶ S` with **affine** target, the
degree-`q` cohomology of a quasi-coherent module on `X` is the module of global sections of its
degree-`q` higher direct image. It is stated as an isomorphism of *functors* on the quasi-coherent
modules, so it is natural in the coefficient by construction — but the naturality square is only
available as `CategoryTheory.NatTrans.naturality` at a composite of three whiskered functors,
which is not the shape a consumer meets.

This file names the two squares, written out: with the restriction of scalars along `f^♯` and the
global sections of `S` applied to `rightDerivedPlus` of the morphism of modules, which is how
`AffineOpenSectionsCohomology.lean`'s identifications over an affine open are built.

## Why this is wanted

Conclusion (c) of [Stacks, Tag 0EX3], over a compatible pair of affine opens, compares a map
built from the unit of an adjunction **upstairs** — the unit of `(h' ∣)^* ⊣ (h' ∣)_*` over
`f'⁻¹(V)`, inside `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` — with one built
downstairs. The unit upstairs is a morphism of quasi-coherent modules on `f'⁻¹(V)` and not the
restriction of anything on `X'`, so what carries it across [Stacks, Tag 01XK] is naturality in the
coefficient at the morphism `f' ∣_ V`, and not naturality in a module on `X'`.

The other two factors of those identifications already have their squares:
`…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_hom_naturality` and `…_inv_naturality` in
`SchemeRestriction.lean` for the restriction comparison of [Stacks, Tag 01E5], and
`AlgebraicGeometry.openSectionsModuleIso_hom_apply` for the change of spelling of the sections.
This file supplies the one that was missing.

## Main results

* `…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality`:
  **[Stacks, Tag 01XK] is natural in the coefficient**, written out.
* `…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward_inv_naturality`: the
  same square with the identification inverted.

## Implementation notes

*Each proof is one application of `CategoryTheory.NatTrans.naturality`.* The content is entirely
in the statements: the two sides of the square are the images of the morphism under the two
composite functors the identification compares, and writing those images out — `Functor.comp`
being `rfl` on morphisms — is what makes the square usable without unfolding anything. In
particular the two-branch tactic body of the identification itself is never entered; it does not
have to be, because naturality is a property of the bundled `Iso` and not of how it was built.

*Which copy of the tag.* There are two in the repository: this one, in
`AffineCohomologyVanishing/AffineBase.lean`, and
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.cohomologyIsoGlobalSectionsRightDerivedPushforward`
in `HigherDirectImageQcqs/AffineBaseSections.lean`. The identifications of
`AffineOpenSectionsCohomology.lean` — and hence everything conclusion (c) is computed with — use
the first, so that is the one treated here.

*No `@[stacks 01XK]` or `@[stacks 0EX3]` attribute is placed.* The tag's own carrier is the
identification, which already has the attribute; a naturality square of an isomorphism that is
already natural by construction states nothing the tag does not.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S] (q : ℤ)
  {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : A ⟶ B)

/-- **[Stacks, Tag 01XK] is natural in the coefficient.** For a quasi-compact quasi-separated
`f : X ⟶ S` with affine target and a morphism `φ` of quasi-coherent modules on `X`, the
identification of the degree-`q` cohomology over `X` with the global sections of the degree-`q`
higher direct image carries `H^q(X, φ)` to `Γ(S, R^q f_* φ)`.

This is `CategoryTheory.NatTrans.naturality` of the identification, with the two composite
functors written out: on the left the restriction of scalars along `f^♯` of the derived functor of
global sections on `X`, on the right the global sections of `S` of the derived functor of the
direct image. -/
theorem cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality :
    (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerivedPlus q).map
            ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map φ)) ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).hom.app B =
      (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).hom.app A ≫
        (moduleGlobalSections S).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus q).map
            ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map φ)) :=
  (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).hom.naturality φ

/-- **[Stacks, Tag 01XK] inverted is natural in the coefficient.** The square of
`…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality` read
through the inverse of the identification: `Γ(S, R^q f_* φ)` is carried to `H^q(X, φ)`.

This is the form a consumer meets when the identification enters a computation inverted, as it
does in `…TopDegreeBaseChange.affineOpenCohomologyIsoSectionsOf` at the source end of the
comparison of conclusion (c). -/
theorem cohomologyIsoGlobalSectionsRightDerivedPushforward_inv_naturality :
    (moduleGlobalSections S).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus q).map
            ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map φ)) ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).inv.app B =
      (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).inv.app A ≫
        (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerivedPlus q).map
            ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map φ)) :=
  (cohomologyIsoGlobalSectionsRightDerivedPushforward f q).inv.naturality φ

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
