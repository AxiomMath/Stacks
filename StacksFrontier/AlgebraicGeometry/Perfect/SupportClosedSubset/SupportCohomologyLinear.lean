module

public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetEndofunctorSpelling

/-!
# Local cohomology acts additively and `Γ(X, ⊤)`-linearly on morphisms

Let `T` be a closed subset of a scheme `X`. The functor `ℱ ↦ i_*ℋ ⁿ_T(ℱ)` of the coefficient
module, `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, is additive on
morphisms and linear over the ring `Γ(X, ⊤)` of global functions:

`i_*ℋ ⁿ_T(φ + ψ) = i_*ℋ ⁿ_T(φ) + i_*ℋ ⁿ_T(ψ)`,  `i_*ℋ ⁿ_T(a • φ) = a • i_*ℋ ⁿ_T(φ)`.

**Why this is worth proving.** A pairing with the local cohomology sheaf in the second variable,
`ℳ × i_*ℋ ⁿ_T(𝒩) ⟶ i_*ℋ ⁿ_T(𝒫)`, is additive and `𝒪`-homogeneous in its *first* variable as
soon as the functorial action on "multiply by a section of `ℳ`" is; and the only route to those
two laws in the tree runs through
`Stacks.Perfect.CechPairing.supportPair`, which is descended from the extended alternating Čech
complex of a family of `c = d + 1` equations and so does not exist when `c = 0`. These two
statements give the laws with no equations and at every degree.

## The route

`Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso` identifies
the functor with `CategoryTheory.Functor.rightDerived` of the supported-sections endofunctor
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor`. That endofunctor is a
subfunctor of the identity — it acts on a section by acting on it — so it is linear, which is
`supportedSectionsFunctor_linear` below; `Stacks.DerivedLinear.rightDerived_linear` and
`Stacks.DerivedLinear.rightDerived_additive` carry both properties to the derived functors, and
the identification transports them.

## Main results

* `Stacks.Perfect.SupportCohomologyLinear.supportedSectionsFunctor_map_globalSmul`: the
  supported-sections endofunctor carries multiplication by a global function to multiplication by
  that function.
* `Stacks.Perfect.SupportCohomologyLinear.supportedSectionsFunctor_linear`: it is
  `Γ(X, ⊤)`-linear.
* `Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_additive`,
  `Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_linear`: `i_*ℋ ⁿ_T` is
  additive and `Γ(X, ⊤)`-linear on morphisms.

## Implementation notes

The ambient category has two spellings, `X.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)`, which agree only up to unfolding, and
`CategoryTheory.Functor.Additive` and `CategoryTheory.Functor.Linear` carry the categories as
arguments. `supportCohomologySheafFunctor` is declared at the first spelling and
`supportedSectionsFunctor` at the second, so the transport is written as a chain of
`Eq.trans` and `congrArg` rather than with `rw` or `simp`, which find no occurrence of their
patterns across the two spellings; and `CategoryTheory.Linear.smul_comp` and
`CategoryTheory.Linear.comp_smul` are applied with their category given explicitly, for the same
reason. `CategoryTheory.Functor.additive_iff_of_iso` is used in place of
`CategoryTheory.Functor.additive_of_iso` because it takes the additivity of the source as a term
rather than looking for it as an instance.

## References

* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Perfect.SupportedFraction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportCohomologyLinear

variable {X : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- Sheaves of modules on the ringed space underlying a scheme form a `Γ(X, ⊤)`-linear category,
in the spelling that unfolds `structureSheafRing`.  Instance search does not find
`AlgebraicGeometry.linearModules` through that unfolding, and it is needed to say that the
supported-sections endofunctor, whose declared type uses that spelling, is linear. -/
local instance linear_sheafOfModules_ringSheaf (Y : Scheme.{u}) :
    Linear ↥Γ(Y, ⊤) (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
  AlgebraicGeometry.linearModules

/-- **Taking the sections supported on `T` carries multiplication by a global function to
multiplication by that function.**  The functor acts on a supported section by acting on the
section it is, and multiplication by a global function acts by the restriction of that function;
so both sides restrict `a` to the open and multiply. -/
theorem supportedSectionsFunctor_map_globalSmul (T : Set X) (a : Γ(X, ⊤)) (M : X.Modules) :
    (supportedSectionsFunctor X.toRingedSpace T).map (AlgebraicGeometry.globalSmul a M) =
      AlgebraicGeometry.globalSmul a
        ((supportedSectionsFunctor X.toRingedSpace T).obj M) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext s
  refine Subtype.ext ?_
  refine Eq.trans (supportedSectionsMap_val_app T (AlgebraicGeometry.globalSmul a M) U s) ?_
  refine Eq.trans (AlgebraicGeometry.globalSmul_app a M U.unop s.1) ?_
  exact congrArg Subtype.val (AlgebraicGeometry.globalSmul_app a
    ((supportedSectionsFunctor X.toRingedSpace T).obj M) U.unop s).symm

/-- **The supported-sections endofunctor of [Stacks, Tag 0G6N] is `Γ(X, ⊤)`-linear.**  A scalar
acts on a morphism by precomposition with multiplication by it, which the functor carries to
multiplication by it again. -/
instance supportedSectionsFunctor_linear (T : Set X) :
    Functor.Linear ↥Γ(X, ⊤) (supportedSectionsFunctor X.toRingedSpace T) where
  map_smul {M _} φ a :=
    Eq.trans ((supportedSectionsFunctor X.toRingedSpace T).map_comp
        (AlgebraicGeometry.globalSmul a M) φ)
      (congrArg (fun ψ => ψ ≫ (supportedSectionsFunctor X.toRingedSpace T).map φ)
        (supportedSectionsFunctor_map_globalSmul T a M))

/-- **`i_*ℋ ⁿ_T` is additive on morphisms of the coefficient module.**  It is the degree-`n` right
derived functor of the supported-sections endofunctor, by
`Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso`, and the
right derived functors of an additive functor are additive by
`Stacks.DerivedLinear.rightDerived_additive`. -/
theorem supportCohomologySheafFunctor_additive {T : Set X} (hT : IsClosed T) (n : ℕ) :
    (supportCohomologySheafFunctor hT (n : ℤ)).Additive :=
  (Functor.additive_iff_of_iso
      (Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso
        hT n)).mpr
    (Stacks.DerivedLinear.rightDerived_additive
      (supportedSectionsFunctor X.toRingedSpace T) n)

/-- **`i_*ℋ ⁿ_T` is `Γ(X, ⊤)`-linear on morphisms of the coefficient module**: for a global
function `a`, `i_*ℋ ⁿ_T(a • φ) = a • i_*ℋ ⁿ_T(φ)`.

It is enough to check this on `a • 𝟙`, by `CategoryTheory.Functor.linear_iff`.  There the derived
functor of the supported-sections endofunctor gives the equation, by
`Stacks.DerivedLinear.rightDerived_linear` and `supportedSectionsFunctor_linear`, and the
identification of the two spellings of the functor transports it: the scalar passes through the
two components of the identification and the identification cancels. -/
theorem supportCohomologySheafFunctor_linear {T : Set X} (hT : IsClosed T) (n : ℕ) :
    Functor.Linear ↥Γ(X, ⊤) (supportCohomologySheafFunctor hT (n : ℤ)) := by
  let : (supportCohomologySheafFunctor hT (n : ℤ)).Additive :=
    supportCohomologySheafFunctor_additive hT n
  have hlin := Stacks.DerivedLinear.rightDerived_linear
    (R := ↥Γ(X, ⊤)) (supportedSectionsFunctor X.toRingedSpace T) n
  refine (Functor.linear_iff ↥Γ(X, ⊤) (supportCohomologySheafFunctor hT (n : ℤ))).mpr
    fun M a => ?_
  set e := Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso
    hT n with he
  refine Eq.trans (NatIso.naturality_2 e (a • 𝟙 M)).symm ?_
  refine Eq.trans (congrArg (fun φ => e.hom.app M ≫ φ ≫ e.inv.app M)
    (Eq.trans (hlin.map_smul (𝟙 M) a)
      (congrArg (fun ψ => a • ψ)
        (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).map_id M)))) ?_
  refine Eq.trans (congrArg (fun ψ => e.hom.app M ≫ ψ)
    (Eq.trans (Linear.smul_comp (R := ↥Γ(X, ⊤)) (C := X.Modules) _ _ _ a (𝟙 _) (e.inv.app M))
      (congrArg (fun ψ => a • ψ) (Category.id_comp (e.inv.app M))))) ?_
  exact Eq.trans
    (Linear.comp_smul (R := ↥Γ(X, ⊤)) (C := X.Modules) _ _ _ (e.hom.app M) a (e.inv.app M))
    (congrArg (fun ψ => a • ψ) (e.hom_inv_id_app M))

end Stacks.Perfect.SupportCohomologyLinear

end
