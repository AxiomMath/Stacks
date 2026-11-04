module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal

/-!
# The difference map of [Stacks Project, Tag 04FL] read in the category `X.Modules`

`Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf` is
[Stacks Project, Tag 04FL]: the transpose of `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` sends the universal
differential `d_{Y/S} s` to the conormal class of `(a')^♯ s - (b')^♯ s`. It is stated in the
ringed-space vocabulary of `RingedSpaceModuleAdjunction`: the conormal sheaf is
`Stacks.Conormal.conormalSheaf i`, an object of
`SheafOfModules (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)`, and the adjunction
is `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction a.toLRSHom.toShHom`.

This file states the same equation in the scheme vocabulary: the conormal sheaf is
`Stacks.Thickenings.conormalModules i`, an object of `AlgebraicGeometry.Scheme.Modules X`, and
the adjunction is `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction a`. The two
vocabularies name the same objects — `conormalModules i = Stacks.Conormal.conormalSheaf i` and
`Scheme.Modules.pullback a = modulePullback a.toLRSHom.toShHom` both hold by `rfl` — so
`Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d_modules` is proved by handing the
original term to the restated type, and nothing mathematical happens here.

## Why the restatement exists

The crossing between the two vocabularies is a `rfl` that the kernel can afford **only while
`a` is a variable**. Elaborating each case as a single declaration in a file of
its own:

* the statement below, with `a` a variable: checked, 5.2s;
* the same statement with `a := i` substituted — that is, the pullback and pushforward taken
  along the immersion `i` whose conormal sheaf is the target, which is the instance
  [Stacks Project, Tag 0D14] part (2) needs — proved directly from
  `homEquiv_diagonalConormalSheafMap_d`: **`(deterministic) timeout at `isDefEq``, 13.8s to
  fail** (the same statement with the section taken by `.val.app (op V)` instead of
  `AlgebraicGeometry.Scheme.Modules.Hom.app` times out at `whnf` instead, at the same cost);
* that same `a := i` statement proved instead by substitution into the statement below:
  checked, **0.8s**.

With `a` a variable the crossing is a first-order unification of two spellings of one ring
sheaf. With `a := i` the two sides of the same crossing both mention `i`, the elaborator has to
unfold `AlgebraicGeometry.Scheme.Modules.pushforward i` against
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom` inside a term of the size of
04FL's, and it does not finish. Instantiating an already-crossed statement costs nothing,
because substitution is not a defeq check; so the crossing is paid once, here, at the generic
`a`, and every consumer gets its instance for free.

This is therefore not a wrapper to be inlined: deleting it and using
`homEquiv_diagonalConormalSheafMap_d` directly at `a := i` is the timeout above, and
the only other way past it is to raise `maxHeartbeats`.

## Main results

* `Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d_modules`: [Stacks Project, Tag 04FL]
  with the conormal sheaf read as an object of `AlgebraicGeometry.Scheme.Modules X` and the
  transpose taken along `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

## References

* [Stacks Project, Tag 04FL](https://stacks.math.columbia.edu/tag/04FL)
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Opposite

universe u

namespace Stacks.Thickenings

open Stacks.Conormal Stacks.Diagonal

variable {S X X' Y : Scheme.{u}}
variable {i : X ⟶ X'} {a : X ⟶ Y} {a' b' : X' ⟶ Y} {q : Y ⟶ S}

/-- **The difference of two maps to a fixed scheme, through the diagonal**,
[Stacks Project, Tag 04FL], with the conormal sheaf read as an object of
`AlgebraicGeometry.Scheme.Modules X` and the transpose of `θ` taken along
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

This is `Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d` at the other of the two
definitionally equal spellings of the category of `𝒪_X`-modules; see the module docstring for
why both spellings are stated, and for the measurement that forbids crossing between them at a
non-variable `a`. -/
theorem homEquiv_diagonalConormalSheafMap_d_modules [IsImmersion i] (hq : b' ≫ q = a' ≫ q)
    (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) (s : Γ(Y, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials q) (conormalModules i)
          (diagonalConormalSheafMap hq comm_a comm_b)) V).hom
        (q.universalRelativeDerivation.d s) =
      conormalClass i (liftPairOpen a' b' V) (le_preimage_liftPairOpen comm_a comm_b V)
        (liftDiffSection a' b' V s) (app_liftDiffSection comm_a comm_b V s) :=
  homEquiv_diagonalConormalSheafMap_d hq comm_a comm_b V s

end Stacks.Thickenings

end
