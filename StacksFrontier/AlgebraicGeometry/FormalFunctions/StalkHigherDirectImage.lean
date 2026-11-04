module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdeal
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientCohomologyBound
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk

/-!
# The stalk of a higher direct image is the cohomology of the base change

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes, `ℱ` a quasi-coherent
`𝒪_X`-module and `y` a point of `Y`. Writing `A = 𝒪_{Y, y}`, `X' = X ×_Y Spec A` with its two
projections `g' : X' ⟶ X` and `f' : X' ⟶ Spec A`, and `ℱ' = (g')^* ℱ`, this file proves

`(R ᵖ f_* ℱ)_y ≅ H ᵖ (X', ℱ')`

as `A`-modules, in every degree. This is the left-hand side of [Stacks, Tag 02OD] put in the
shape the affine theorem on formal functions consumes, and it is the only place where flat base
change in positive degrees is used.

Three steps. Flat base change for the higher direct images,
`Stacks.FormalFunctions.nonempty_pullbackHigherDirectImageIso`, identifies the pullback of
`R ᵖ f_* ℱ` to `Spec A` with `R ᵖ f'_* ℱ'`; `Spec A` is affine, so taking global sections of the
right-hand side gives `H ᵖ (X', ℱ')` by [Stacks, Tag 01XK]; and taking global sections of the
left-hand side gives the stalk, by
`AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv`, since `R ᵖ f_* ℱ` is quasi-coherent
([Stacks, Tag 01XJ]).

## Main definitions

* `Stacks.FormalFunctions.stalkBaseChangeModule`: the module `ℱ'` on `X'`.
* `Stacks.FormalFunctions.higherDirectImageStalk`: the stalk `(R ᵖ f_* ℱ)_y`, as an `A`-module.

## Main results

* `Stacks.FormalFunctions.nonempty_higherDirectImageStalkLinearEquiv`:
  **`(R ᵖ f_* ℱ)_y ≅ H ᵖ (X', ℱ')` as `𝒪_{Y, y}`-modules**, in every degree.

## Implementation notes

Every comparison below is only an `A`-module isomorphism and none is identified with a canonical
map: the flat base change it rests on is itself only available as an isomorphism, not as the
invertibility of the canonical base-change morphism, so the statements are `Nonempty`.

The three module structures that have to be made to agree are all restrictions of scalars along
ring maps out of `A`, and they are all spelled with `Module.compHom`: `compHomEquiv` reads an
`R`-linear equivalence as an `A`-linear one for a ring map `A ⟶ R`, and `Mathlib`'s
`ModuleCat.restrictScalars` has the same `smul`, by
`ModuleCat.smul_restrictScalars`. The ring map on the side of the stalk is
`Scheme.ΓSpecIso`, and on the side of the cohomology it is
`Stacks.Cohomology.FormalFunctions.baseRingHom`, which is `Scheme.ΓSpecIso` followed by the
structure morphism of `X'` over `Spec A` — the two meet because global sections on `Spec A` of
`R ᵖ f'_* ℱ'` are the cohomology of `ℱ'` with scalars restricted along that structure morphism.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **An `R`-linear equivalence read as an `A`-linear one**, for the module structures obtained
by restricting scalars along a ring map `σ : A ⟶ R`. -/
public def compHomEquiv {A R : Type*} [CommRing A] [CommRing R] (σ : A →+* R)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) :
    letI := Module.compHom M σ
    letI := Module.compHom N σ
    M ≃ₗ[A] N :=
  letI := Module.compHom M σ
  letI := Module.compHom N σ
  { e.toAddEquiv with map_smul' := fun a x => e.map_smul (σ a) x }

variable {X Y : Scheme.{u}}

/-- **The module `ℱ' = (g')^* ℱ` on the base change `X' = X ×_Y Spec 𝒪_{Y, y}`.** -/
public abbrev stalkBaseChangeModule (f : X ⟶ Y) (F : X.Modules) (y : Y) :
    (stalkBaseChange f y).Modules :=
  (Scheme.Modules.pullback (stalkBaseChangeι f y)).obj F

/-- The pullback `ℱ'` of a quasi-coherent `ℱ` to `X'` is quasi-coherent. -/
public instance isQuasicoherent_stalkBaseChangeModule (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] (y : Y) : (stalkBaseChangeModule f F y).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F

/-- **The stalk `(R ᵖ f_* ℱ)_y` of a higher direct image at a point of the base.** -/
public abbrev higherDirectImageStalk (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) : Type u :=
  (((Scheme.Modules.pushforward f).rightDerived p).obj F).presheaf.stalk y

/-- The stalk of a higher direct image is a module over the local ring of the base. -/
public instance moduleHigherDirectImageStalk (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    Module (Y.presheaf.stalk y) (higherDirectImageStalk f F y p) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) (((Scheme.Modules.pushforward f).rightDerived p).obj F).val y

/-- **`(R ᵖ f_* ℱ)_y ≅ H ᵖ (X ×_Y Spec 𝒪_{Y, y}, ℱ')` as `𝒪_{Y, y}`-modules.** -/
public theorem nonempty_higherDirectImageStalkLinearEquiv (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (y : Y) (p : ℕ) :
    Nonempty (higherDirectImageStalk f F y p ≃ₗ[Y.presheaf.stalk y]
      cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
        (stalkBaseChangeModule f F y)) := by
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (U := ⊤) (TopologicalSpace.Opens.mem_top y)
  -- Flat base change in degree `p` along `Spec 𝒪_{Y,y} ⟶ Y`.
  obtain ⟨bc⟩ := nonempty_pullbackHigherDirectImageIso
    (IsPullback.of_hasPullback f (Y.fromSpecStalk y)) F p
  exact ⟨(AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv
      (((Scheme.Modules.pushforward f).rightDerived p).obj F) y hU hyU).symm ≪≫ₗ
    compHomEquiv (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
      ((AlgebraicGeometry.moduleGlobalSections
        (Spec (Y.presheaf.stalk y))).mapIso bc).toLinearEquiv ≪≫ₗ
    compHomEquiv (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
      (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso
          (stalkBaseChangeStructure f y)
          (stalkBaseChangeModule f F y) p).symm.toLinearEquiv⟩

end Stacks.FormalFunctions

end
