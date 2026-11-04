module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward of the cycle of a coherent sheaf, Stacks 02R6

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be proper over `S`.

1. For a closed subscheme `i : Z ⟶ X` with `dim_δ(Z) ≤ k`, `f_* [Z]_k = [f_* 𝒪_Z]_k`.
2. For a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`, `f_* [F]_k = [f_* F]_k`.

The right-hand sides make sense because `f_* F` and `f_* 𝒪_Z` are coherent `𝒪_Y`-modules: `Y`
is locally Noetherian, being locally of finite type over the locally Noetherian `S`, and the
direct image of a coherent module under a proper morphism to a locally Noetherian scheme is
coherent ([Stacks, Tag 02O5], `Stacks.Chow.properDirectImageIsCoherent`). That coherence is
supplied inside the statements below, and the cycle identities are then
`Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf` and
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme` at that instance. Here `𝒪_Z`
is read as the coherent `𝒪_X`-module `i_* 𝒪_Z`.

## Main results

* `Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf_eq_directImage` — part (2).
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_eq_directImage` — part (1).

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-- **Stacks 02R6, part (2).** Let `f : X ⟶ Y` be a proper morphism of schemes locally of finite
type over the base `S` of chapter 42, and let `F` be a coherent `𝒪_X`-module whose support has
delta-dimension at most `k`. Then `f_* [F]_k = [f_* F]_k`, where `f_* F` is coherent by
[Stacks, Tag 02O5] since `Y` is locally Noetherian. -/
@[stacks 02R6 "part (2)"]
theorem properPushforward_cycleAssociatedToCoherentSheaf_eq_directImage (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent := properDirectImageIsCoherent f F
    properPushforward C sX sY f hf k (cycleAssociatedToCoherentSheaf C sX F k hFk) =
      cycleAssociatedToCoherentSheaf C sY ((Scheme.Modules.pushforward f).obj F) k
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf F hFk) :=
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent := properDirectImageIsCoherent f F
  properPushforward_cycleAssociatedToCoherentSheaf C sX sY f hf F k hFk

/-- **Stacks 02R6, part (1).** Let `f : X ⟶ Y` be a proper morphism of schemes locally of finite
type over the base `S` of chapter 42, and let `i : Z ⟶ X` be a closed subscheme with
`dim_δ(Z) ≤ k`. Then `f_* [Z]_k = [f_* 𝒪_Z]_k`, where `𝒪_Z` is the coherent `𝒪_X`-module
`i_* 𝒪_Z` and its direct image `f_* 𝒪_Z` is coherent by [Stacks, Tag 02O5] since `Y` is locally
Noetherian. -/
@[stacks 02R6 "part (1)"]
theorem properPushforward_cycleAssociatedToClosedSubscheme_eq_directImage (C : ChowSituation.{u})
    {Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
      properDirectImageIsCoherent f _
    properPushforward C sX sY f hf k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToCoherentSheaf C sY
        ((Scheme.Modules.pushforward f).obj
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))) k
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
          (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hZ)) :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
    properDirectImageIsCoherent f _
  properPushforward_cycleAssociatedToClosedSubscheme C sX sY f hf i k hZ

end Stacks.Chow

end
