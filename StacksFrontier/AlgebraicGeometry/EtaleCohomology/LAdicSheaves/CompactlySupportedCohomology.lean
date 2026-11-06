module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
import StacksCore.Tactic.StacksAttribute

/-!
# Compactly supported ℓ-adic cohomology

Let `X` be a separated scheme of finite type over a field `k` and let `F = {Fₙ}` be an ℓ-adic
sheaf on `X`. Each finite level `Fₙ` is a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules, hence of `ℤ_[ℓ]`-modules
through the reduction `ℤ_[ℓ] → ℤ/ℓⁿ⁺¹ℤ`, and the transition maps of the inverse system are
`ℤ_[ℓ]`-linear for these structures. Compactly supported cohomology through a compactification
of `X` therefore gives an inverse system `n ↦ Hⁱ_c(X, Fₙ)` of `ℤ_[ℓ]`-modules, and the
compactly supported ℓ-adic cohomology of `F` is its inverse limit
`Hⁱ_c(X, F) = limₙ Hⁱ_c(X, Fₙ)`. For rational coefficients `F ⊗ Q_ℓ` one tensors up:
`Hⁱ_c(X, F ⊗ Q_ℓ) = Hⁱ_c(X, F) ⊗_{ℤ_[ℓ]} ℚ_[ℓ]`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.padicLevel` is a finite level of an ℓ-adic sheaf read as a
  sheaf of `ℤ_[ℓ]`-modules, and `Stacks.EtaleCohomology.LAdicSheaf.padicTransition` is the
  transition map of the system between two consecutive ones.
* `Stacks.EtaleCohomology.compactlySupportedPadicCohomology` is compactly supported étale
  cohomology of a sheaf of `ℤ_[ℓ]`-modules on the small étale site of Stacks 021B, through a
  compactification.
* `Stacks.EtaleCohomology.LAdicSheaf.compactlySupportedCohomologySystem` is the inverse system
  `n ↦ Hⁱ_c(X, Fₙ)`, and `Stacks.EtaleCohomology.LAdicSheaf.compactlySupportedCohomology` is
  its limit `Hⁱ_c(X, F)`, with projections
  `Stacks.EtaleCohomology.LAdicSheaf.compactlySupportedCohomologyπ`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalCompactlySupportedCohomology` is
  `Hⁱ_c(X, F ⊗ Q_ℓ) = Hⁱ_c(X, F) ⊗_{ℤ_[ℓ]} ℚ_[ℓ]`.

## Main results

* `Stacks.EtaleCohomology.toZModPow_succ_comp`: the reduction `ℤ_[ℓ] → ℤ/ℓⁿ⁺¹ℤ` factors through
  the next one, which is what makes the transition maps `ℤ_[ℓ]`-linear.
* `Stacks.EtaleCohomology.LAdicSheaf.compactlySupportedCohomologySystem_obj` identifies the
  `n`-th term of the inverse system with `Hⁱ_c(X, Fₙ)`, and
  `Stacks.EtaleCohomology.LAdicSheaf.compactlySupportedCohomologySystem_map_succ` identifies its
  map from level `n + 1` to level `n` with the one induced by the transition map of `F`.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTransition_val_app_apply`: the transition map of the
  system of `ℤ_[ℓ]`-module sheaves has the same sections as the transition map of `F`.

## Implementation notes

The coefficients are `ℤ_[ℓ]`-modules rather than abelian groups, so that the limit carries the
`ℤ_[ℓ]`-module structure that the rational clause tensors away. A level and its restriction of
scalars to the coefficient ring of the previous level have the same underlying sheaf, and the
two reductions of `ℤ_[ℓ]` differ by exactly that restriction of scalars, so the transition maps
of the ℓ-adic sheaf are already `ℤ_[ℓ]`-linear; `Mathlib.ModuleCat.restrictScalarsComp'`
supplies the identification of the two coefficient functors.

Compactly supported cohomology is `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup`,
which is stated for Mathlib's small étale site and takes a compactification of `X` over
`Spec k` as an explicit argument; `AlgebraicGeometry.SmallEtale.sheafEquiv` identifies the
sheaves of Stacks 021B, on which ℓ-adic sheaves live, with the sheaves on Mathlib's site. The
compactification stays an explicit argument here too, so these definitions have a genuine
construction as their body; Stacks Tag 0F7I is the statement that different compactifications
give canonically isomorphic functors.

Only the hypotheses that the construction uses are assumed: `X` separated of finite type over
a field, with a compactification. Algebraic closedness of `k`, under which the source states
the definition, is not needed to form the limit, exactly as for the ordinary variant
`Stacks.EtaleCohomology.LAdicSheaf.cohomology`.

## References

* [Stacks Project, Tag 03UT](https://stacks.math.columbia.edu/tag/03UT)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

/-- The reduction `ℤ_[ℓ] → ℤ/ℓⁿ⁺¹ℤ` is the next one followed by the quotient map of coefficient
rings. -/
public theorem toZModPow_succ_comp [Fact ℓ.Prime] (n : ℕ) :
    PadicInt.toZModPow (p := ℓ) (n + 1) =
      (finiteLevelRingHom ℓ n).comp (PadicInt.toZModPow (n + 2)) :=
  (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (by omega)).symm

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-! ### The finite levels as sheaves of `ℤ_[ℓ]`-modules -/

/-- The level `n` of an ℓ-adic sheaf, read as a sheaf of `ℤ_[ℓ]`-modules through the reduction
`ℤ_[ℓ] → ℤ/ℓⁿ⁺¹ℤ`. -/
public def LAdicSheaf.padicLevel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  (sheafCompose (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (n + 1)))).obj (F.level n)

/-- The transition map of an ℓ-adic sheaf, read on the levels as sheaves of `ℤ_[ℓ]`-modules:
restricting the scalars of a level to the coefficient ring of the previous one leaves the
`ℤ_[ℓ]`-module structure unchanged, so the transition goes from level `n + 1` to level `n`. -/
public def LAdicSheaf.padicTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.padicLevel B X ℓ F (n + 1) ⟶ LAdicSheaf.padicLevel B X ℓ F n :=
  (sheafCompose (SmallEtale.topology B X.1 X.property)
        (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (n + 2)))).map
      (F.transition n) ≫
    (sheafCompose_map (SmallEtale.topology B X.1 X.property)
      (ModuleCat.restrictScalarsComp'.{u + 1} (PadicInt.toZModPow (n + 2))
        (finiteLevelRingHom ℓ n) (PadicInt.toZModPow (n + 1))
        (toZModPow_succ_comp ℓ n)).inv).app (F.level n)

/-- On sections the transition map of the system of `ℤ_[ℓ]`-module sheaves is the transition map
of the ℓ-adic sheaf. -/
@[simp]
public theorem LAdicSheaf.padicTransition_hom_app_apply (F : LAdicSheaf B X ℓ) (n : ℕ)
    (V : (SmallEtale B X.1 X.property)ᵒᵖ) (x : (F.level (n + 1)).obj.obj V) :
    ((LAdicSheaf.padicTransition B X ℓ F n).hom.app V).hom x =
      ((F.transition n).hom.app V).hom x :=
  rfl

/-! ### Compactly supported cohomology of the finite levels -/

variable (k : Type u) [Field k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

/-- **Stacks Project, Tag 0GJZ.** Compactly supported étale cohomology `Hⁱ_c(X, -)` of a sheaf
of `ℤ_[ℓ]`-modules on the small étale site of Stacks 021B of a separated finite type
`k`-scheme `X`, through a compactification `j`. -/
@[sga "7 XXII 3.4"]
public def compactlySupportedPadicCohomology (i : ℤ) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
      ModuleCat.{u + 1} ℤ_[ℓ] :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor ⋙
    DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ_[ℓ] X.1) 0 ⋙
    compactlySupportedCohomologyGroup.{u, 0} k f j ℤ_[ℓ] i

/-! ### Compactly supported ℓ-adic cohomology -/

/-- The inverse system `n ↦ Hⁱ_c(X, Fₙ)` of the compactly supported étale cohomology of the
finite levels of an ℓ-adic sheaf, with the maps induced by its transition maps. -/
public def LAdicSheaf.compactlySupportedCohomologySystem (F : LAdicSheaf B X ℓ) (i : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
  Functor.ofOpSequence
    (X := fun n => (compactlySupportedPadicCohomology B X ℓ k f j i).obj
      (LAdicSheaf.padicLevel B X ℓ F n))
    (fun n => (compactlySupportedPadicCohomology B X ℓ k f j i).map
      (LAdicSheaf.padicTransition B X ℓ F n))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The `n`-th term of the inverse system is the compactly supported cohomology of the `n`-th
level. -/
@[simp]
public theorem LAdicSheaf.compactlySupportedCohomologySystem_obj (F : LAdicSheaf B X ℓ) (i : ℤ)
    (n : ℕ) :
    (LAdicSheaf.compactlySupportedCohomologySystem B X ℓ k f j F i).obj (op n) =
      (compactlySupportedPadicCohomology B X ℓ k f j i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) :=
  rfl

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The map of the inverse system from level `n + 1` to level `n` is the one induced on
compactly supported cohomology by the transition map of the ℓ-adic sheaf. -/
@[simp]
public theorem LAdicSheaf.compactlySupportedCohomologySystem_map_succ (F : LAdicSheaf B X ℓ)
    (i : ℤ) (n : ℕ) :
    (LAdicSheaf.compactlySupportedCohomologySystem B X ℓ k f j F i).map
        (homOfLE (n.le_add_right 1)).op =
      (compactlySupportedPadicCohomology B X ℓ k f j i).map
        (LAdicSheaf.padicTransition B X ℓ F n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The compactly supported ℓ-adic cohomology of an ℓ-adic sheaf.** For an ℓ-adic sheaf
`F = {Fₙ}` on `X` and a degree `i`, this is `Hⁱ_c(X, F) = limₙ Hⁱ_c(X, Fₙ)`. -/
@[stacks 03UT "H^i_c(X, F) = lim_n H^i_c(X, F_n)"]
public def LAdicSheaf.compactlySupportedCohomology (F : LAdicSheaf B X ℓ) (i : ℤ) :
    ModuleCat.{u + 1} ℤ_[ℓ] :=
  limit (LAdicSheaf.compactlySupportedCohomologySystem B X ℓ k f j F i)

/-- The projection of the compactly supported ℓ-adic cohomology onto the compactly supported
cohomology of a finite level. -/
public def LAdicSheaf.compactlySupportedCohomologyπ (F : LAdicSheaf B X ℓ) (i : ℤ) (n : ℕ) :
    LAdicSheaf.compactlySupportedCohomology B X ℓ k f j F i ⟶
      (compactlySupportedPadicCohomology B X ℓ k f j i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) :=
  limit.π (LAdicSheaf.compactlySupportedCohomologySystem B X ℓ k f j F i) (op n)

/-! ### Rational coefficients -/

/-- **The compactly supported ℓ-adic cohomology with `ℚ_[ℓ]`-coefficients.** For the rational
ℓ-adic sheaf `F ⊗ Q_ℓ` attached to an ℓ-adic sheaf `F`, this is the extension of scalars of
`Hⁱ_c(X, F)` along `ℤ_[ℓ] → ℚ_[ℓ]`, that is `Hⁱ_c(X, F ⊗ Q_ℓ) = Hⁱ_c(X, F) ⊗_{ℤ_[ℓ]} ℚ_[ℓ]`. -/
@[stacks 03UT "H^i_c(X, F' ⊗ Q_ell) = H^i_c(X, F') ⊗_{Z_ell} Q_ell",
  sga "4½ Rapport 2.10",
  sga "7 I 0.1" "more general"]
public def LAdicSheaf.rationalCompactlySupportedCohomology (F : LAdicSheaf B X ℓ) (i : ℤ) :
    ModuleCat.{u + 1} ℚ_[ℓ] :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (LAdicSheaf.compactlySupportedCohomology B X ℓ k f j F i)

end Stacks.EtaleCohomology

end
