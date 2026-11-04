module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.GeneratorClauses
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
public import StacksFrontier.Homology.Perfect.Characterizing
import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf generates on a quasi-affine scheme

This is the first consequence [Stacks, Tag 0BQT] draws from its remark: if `X` is a quasi-affine
scheme then `𝒪_X` is a generator of `D_QCoh(𝒪_X)`.

The argument is the source's. A quasi-affine scheme is quasi-compact and its canonical morphism
`j : X ⟶ Spec Γ(X, 𝒪_X)` is an open immersion, so the three conditions of the remark hold for
`j`; in particular `Lj^*` carries a generator of `D_QCoh(𝒪_{Spec Γ(X, 𝒪_X)})` to a generator of
`D_QCoh(𝒪_X)`. The structure sheaf is such a generator on an affine scheme, and `Lj^*𝒪` is `𝒪`.

*The affine case.* `R` in degree zero generates `D(R)`
(`StacksDraft.Perfect.isWeakTriangulatedGenerator_regularModule`: `R` is a projective separator),
derived sheafification `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence commuting with the shift
([Stacks, Tag 06Z0], `AlgebraicGeometry.derivedTildeQuasicoherentEquivalence`), and an
equivalence commuting with the shift carries a weak generator to a weak generator. Finally the
sheaf associated to `R` is the structure sheaf, so the image of `R[0]` is `𝒪_{Spec R}[0]`.

*`Lj^*𝒪_Y ≅ 𝒪_X` for an open immersion.* Both `Lj^*` and restriction `j^*` are left adjoints of
`Rj_*` — the first by `Stacks.Duality.derivedAdjunction`, the second by
`Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction` — so they are isomorphic.
Restriction is exact, hence carries a module in degree zero to that module's restriction in
degree zero, and the restriction of `𝒪_Y` is `𝒪_X`
(`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`).

## Main definitions

* `Stacks.Duality.DerivedPushforward.derivedPullbackIsoDerivedRestrict` — `Lj^* ≅ j^*` for an
  open immersion of schemes.
* `Stacks.Duality.DerivedPushforward.quasiCoherentDerivedPullbackDerivedStructureSheafIso` —
  `Lj^*𝒪_Y ≅ 𝒪_X` in `D_QCoh`, for an open immersion.
* `Stacks.Duality.DerivedPushforward.derivedTildeObjUnitIso` — derived sheafification carries
  `R[0]` to `𝒪_{Spec R}[0]`.

## Main results

* `Stacks.Duality.DerivedPushforward.isWeakTriangulatedGenerator_derivedStructureSheaf_spec` —
  `𝒪_{Spec R}` is a weak generator of `D_QCoh(𝒪_{Spec R})`.
* `isWeakTriangulatedGenerator_derivedStructureSheaf_of_isQuasiAffine`, in the namespace
  `Stacks.Duality.DerivedPushforward` — **[Stacks, Tag 0BQT]**, the consequence for a quasi-affine
  scheme.

## Implementation notes

*The model of the derived categories* is the locally small one throughout, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/PullbackGenerator.lean`; both the
affine derived Spec–Γ equivalence and the open-immersion adjunction are available there.

## References

* [Stacks Project, Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Tag 01P9](https://stacks.math.columbia.edu/tag/01P9)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality.DerivedPushforward

/-! ### `Lj^*` is restriction, and it fixes the structure sheaf -/

section OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- **`Lj^* ≅ j^*` for an open immersion of schemes.** Derived pullback and restriction are both
left adjoint to `Rj_*`, by `Stacks.Duality.derivedAdjunction` and
`Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction`, so they are isomorphic. -/
def derivedPullbackIsoDerivedRestrict :
    Stacks.Duality.derivedPullback j ≅ Stacks.Duality.OpenImmersion.derivedRestrict j :=
  (Stacks.Duality.derivedAdjunction j).leftAdjointUniq
    (Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction j)

/-- **The restriction of the structure sheaf along an open immersion is the structure sheaf.**
Restriction is isomorphic to pullback (`restrictFunctorIsoPullback`) and the pullback of the
structure sheaf is the structure sheaf (`pullbackUnitIso`). -/
def restrictFunctorObjUnitIso :
    (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app (Scheme.unitModule Y) ≪≫
    Scheme.Modules.pullbackUnitIso j

/-- **`Lj^*𝒪_Y ≅ 𝒪_X` in `D_QCoh`, for an open immersion of schemes.** `Lj^*` is restriction,
restriction is exact so it carries a module in degree zero to its restriction in degree zero, and
the restriction of `𝒪_Y` is `𝒪_X`. -/
def quasiCoherentDerivedPullbackDerivedStructureSheafIso :
    (Stacks.Duality.quasiCoherentDerivedPullback' j).obj (derivedStructureSheaf Y) ≅
      derivedStructureSheaf X :=
  (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).isoMk
    ((derivedPullbackIsoDerivedRestrict j).app (derivedStructureSheaf Y).obj ≪≫
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).app
        (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      (DerivedCategory.singleFunctor X.Modules 0).mapIso (restrictFunctorObjUnitIso j))

end OpenImmersion

/-! ### The affine case -/

/-- **Derived sheafification carries `R[0]` to `𝒪_{Spec R}[0]`.** Sheafification is exact, so it
carries a module in degree zero to its associated sheaf in degree zero, and the sheaf associated
to `R` is the structure sheaf (`AlgebraicGeometry.tildeSelf`). -/
def derivedTildeObjUnitIso (R : CommRingCat.{u}) :
    (AlgebraicGeometry.derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      derivedStructureSheaf (Spec R) :=
  (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).isoMk
    (((AlgebraicGeometry.tilde.functor R).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of R R) ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso
        (AlgebraicGeometry.tildeSelf (R := R)))

/-- **The structure sheaf generates on an affine scheme.** `R` in degree zero is a weak generator
of `D(R)`, derived sheafification is an equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` commuting with
the shift ([Stacks, Tag 06Z0]), and it carries `R[0]` to `𝒪_{Spec R}[0]`. -/
theorem isWeakTriangulatedGenerator_derivedStructureSheaf_spec (R : CommRingCat.{u}) :
    (ObjectProperty.singleton (derivedStructureSheaf (Spec R))).IsWeakTriangulatedGenerator := by
  have hM : (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).IsWeakTriangulatedGenerator :=
    StacksDraft.Perfect.isWeakTriangulatedGenerator_regularModule
  have hE := CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_obj_of_equivalence
    (AlgebraicGeometry.derivedTildeQuasicoherentEquivalence R) _ hM
  exact isWeakTriangulatedGenerator_of_iso (derivedTildeObjUnitIso R) hE

/-! ### The consequence for a quasi-affine scheme -/

/-- **[Stacks, Tag 0BQT]: if `X` is a quasi-affine scheme then `𝒪_X` generates
`D_QCoh(𝒪_X)`.** This is the first consequence the source draws from its remark.

A quasi-affine scheme is quasi-compact, quasi-separated, and its canonical morphism
`j : X ⟶ Spec Γ(X, 𝒪_X)` is an open immersion; the target is affine, hence quasi-compact and
quasi-separated. The remark's clause for an open immersion therefore applies to `j`, and `𝒪` is
a generator on the affine target by
`isWeakTriangulatedGenerator_derivedStructureSheaf_spec`, so `Lj^*𝒪` is a generator — and
`Lj^*𝒪` is `𝒪_X`. -/
@[stacks 0BQT "the first consequence drawn from the remark: if X is a quasi-affine scheme then \
  the structure sheaf O_X is a generator for D_QCoh(O_X)"]
theorem isWeakTriangulatedGenerator_derivedStructureSheaf_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    (ObjectProperty.singleton (derivedStructureSheaf X)).IsWeakTriangulatedGenerator := by
  have : IsOpenImmersion X.toSpecΓ := inferInstance
  have : CompactSpace X := inferInstance
  have : QuasiSeparatedSpace X := inferInstance
  have hOpen := isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isOpenImmersion
    X.toSpecΓ (derivedStructureSheaf (Spec Γ(X, ⊤)))
    (isWeakTriangulatedGenerator_derivedStructureSheaf_spec Γ(X, ⊤))
  exact isWeakTriangulatedGenerator_of_iso
    (quasiCoherentDerivedPullbackDerivedStructureSheafIso X.toSpecΓ) hOpen

end Stacks.Duality.DerivedPushforward

end
