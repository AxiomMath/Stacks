module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullUnit
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.IdealMultipleKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent

/-!
# The kernel of `A ⟶ i_* i^* A` is `ℐ · A` in every degree

Let `v : V ⟶ X` be a closed immersion of schemes and `A` a sheaf of graded `𝒪_X`-algebras. The
canonical homomorphism of sheaves of graded algebras `A ⟶ v_* v^* A` is the unit of
`Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction`
(`Stacks.PushforwardGradedAlgebra.gradedUnit`), and its degree-`n` component is the unit of
`f^* ⊣ f_*` on sheaves of modules at `A_n`
(`Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction_unit_app_app`).

This file reads the sectionwise kernel off that.
`Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple` computes the kernel of
the module-level unit at a quasi-coherent module as the subsheaf cut out by the ideal sheaf of
`v`, over *every* open and with no quasi-compactness or affineness; so the graded unit has
sectionwise kernel `ℐ · A_n` in degree `n`, which is the realization of
`⨁_n ℐ ⊗ A_n` as the kernel of `⨁_n A_n ⟶ ⨁_n v_* v^* A_n` that the graded arguments of
[Stacks Project, Tag 09MS] use.

**The two adjunctions are the same adjunction.** The degreewise kernel result is stated over
Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` for a morphism of
schemes, and the graded one over
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` for a morphism of ringed spaces.
No bridge is needed: the two are **definitionally equal** at `v.toLRSHom.toShHom`
(`Stacks.AmpleThickeningDevissage.schemeAdjunction_eq_ringedSpaceAdjunction` below, proved by
`rfl`), exactly as `AlgebraicGeometry.Scheme.Modules.pullback` and
`RingedSpaceModuleAdjunction.modulePullback` are
(`AlgebraicGeometry.pullback_scheme_eq`,
`../DerivedAcyclic/Pushforward.lean:101`), and `X.ringCatSheaf` is `structureRingSheaf` of the
underlying ringed space on the nose.

## Main results

* `Stacks.AmpleThickeningDevissage.schemeAdjunction_eq_ringedSpaceAdjunction`: the scheme-level and
  ringed-space-level adjunctions `v^* ⊣ v_*` on sheaves of modules are equal.
* `Stacks.AmpleThickeningDevissage.kernelSubmodule_gradedUnit_app`: **`ker (A_n ⟶ (v_* v^* A)_n) =
  ℐ · A_n`** for a closed immersion of schemes and a quasi-coherent degree-`n` piece.
* `Stacks.AmpleThickeningDevissage.kernelSubmodule_gradedUnit_app_symmetricAlgebra`: the same at
  `A = Sym(L)`, whose nonnegative pieces are quasi-coherent whenever `L` is
  (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece`), so the hypothesis is
  discharged rather than carried.

## Scope

**No `stacks` attribute is attached.** The statements are about the pieces of a graded algebra,
which is the spelling the twisted Čech argument of
`StacksFrontier/AlgebraicGeometry/TwistedThickeningLift/` runs in. For a closed immersion the
degree-`n` component of the graded unit is moreover an epimorphism with no hypothesis on the piece
(`Stacks.AmpleThickeningDevissage.epi_gradedUnit_app_of_isClosedImmersion`,
`GradedUnitClosedSurjective.lean`).

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open Stacks.Algebraization (idealPowerMultiple kernelSubmodule)

universe u

namespace Stacks.AmpleThickeningDevissage

/-! ### The scheme-level and ringed-space-level adjunctions coincide -/

/-- **`v^* ⊣ v_*` on sheaves of modules has one value under two names.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` for a morphism of schemes and
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` for the underlying morphism of
ringed spaces are the same adjunction, both being
`CategoryTheory.SheafOfModules.pullbackPushforwardAdjunction` at the same morphism of sheaves of
rings. This is the module-level counterpart of `AlgebraicGeometry.pullback_scheme_eq`
(`../DerivedAcyclic/Pushforward.lean:101`). -/
theorem schemeAdjunction_eq_ringedSpaceAdjunction {V X : Scheme.{u}} (v : V ⟶ X) :
    Scheme.Modules.pullbackPushforwardAdjunction v =
      modulePullbackPushforwardAdjunction v.toLRSHom.toShHom :=
  rfl

/-! ### The degreewise kernel of the graded unit -/

/-- **`ker (A_n ⟶ (v_* v^* A)_n) = ℐ · A_n`.** For a closed immersion of schemes `v : V ⟶ X` with
ideal sheaf `ℐ` and a sheaf of graded `𝒪_X`-algebras `A` whose degree-`n` piece is quasi-coherent,
a local section of `A_n` dies in degree `n` of `v_* v^* A` exactly when it lies in `ℐ · A_n`.

The kernel is the *sectionwise* one, `Stacks.Algebraization.kernelSubmodule`, whose value over `U`
is the kernel of the map on sections (`Stacks.Algebraization.kernelSubmodule_toSubmodule_obj`). -/
theorem kernelSubmodule_gradedUnit_app {V X : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (n : ℤ)
    [(A.piece n).IsQuasicoherent] :
    kernelSubmodule
        ((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom A).app n) =
      idealPowerMultiple v.ker 1 (A.piece n) := by
  rw [Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction_unit_app_app
    v.toLRSHom.toShHom A n, ← schemeAdjunction_eq_ringedSpaceAdjunction v]
  exact Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple (A.piece n) v

/-- **The same at the symmetric algebra of a quasi-coherent module**, where the quasi-coherence of
the piece is not a hypothesis but a theorem
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece`, the degreewise half of
[Stacks Project, Tag 01CL]).

At an invertible `L` the pieces are the tensor powers `L^{⊗ n}`
(`Stacks.LineBundle.Situation.symmetricPieceIsoTensorPower`), so this is
`ker (L^{⊗ n} ⟶ i_* i^* L^{⊗ n}) = ℐ ⊗ L^{⊗ n}` for every `n ≥ 0` at once, over every open — the
left-hand term of the graded square-zero extension of [Stacks Project, Tag 09MS]. -/
theorem kernelSubmodule_gradedUnit_app_symmetricAlgebra {V X : Scheme.{u}} (v : V ⟶ X)
    [IsClosedImmersion v] (L : X.Modules) [L.IsQuasicoherent] (n : ℕ) :
    kernelSubmodule
        ((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom
          (Scheme.Modules.symmetricAlgebra X L)).app (n : ℤ)) =
      idealPowerMultiple v.ker 1 ((Scheme.Modules.symmetricAlgebra X L).piece (n : ℤ)) :=
  have := Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece X L n
  kernelSubmodule_gradedUnit_app v (Scheme.Modules.symmetricAlgebra X L) (n : ℤ)

end Stacks.AmpleThickeningDevissage

end
