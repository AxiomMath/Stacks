module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward of the cycle of a coherent sheaf, with no coherence hypothesis

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be proper over `S`. This file states
[Stacks, Tag 02R6] with no hypothesis beyond those:

* for a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`, `f_* [F]_k = [f_* F]_k`;
* for a closed subscheme `i : Z ⟶ X` with `dim_δ(Z) ≤ k`, `f_* [Z]_k = [f_* 𝒪_Z]_k`.

Both equations are between `k`-cycles on `Y`, so the right-hand side only makes sense once the
direct image is known to be coherent. That is the proper mapping theorem, [Stacks, Tag 02O5],
which this repository proves with no hypothesis as
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`; it is read here through
`Stacks.Chow.properDirectImageIsCoherent`, whose locally Noetherian target is `Y`, locally of
finite type over the locally Noetherian base `S`. So the coherence of `f_* F` is produced by a
term inside the statement rather than carried as an instance binder, and the two theorems below
assume exactly what the source assumes.

`StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardCoherent/Basic.lean` proves the same two
equations with the coherence of the direct image taken as an instance hypothesis — the shape the
rest of the chapter consumes, since a proof that already has that instance in hand should not
have to produce it again. These are those theorems with the hypothesis discharged, and they
carry the tag.

## Main results

* `Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf_unconditional` — [Stacks, Tag
  02R6] part (2), with no coherence hypothesis.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_unconditional` — [Stacks, Tag
  02R6] part (1), with no coherence hypothesis.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-- **[Stacks, Tag 02R6], part (2).** Let `f : X ⟶ Y` be a proper morphism of schemes locally of
finite type over the base `S` of chapter 42, and let `F` be a coherent `𝒪_X`-module whose support
has delta-dimension at most `k`. Then proper pushforward of `k`-cycles carries the cycle of `F`
to the cycle of the direct image: `f_* [F]_k = [f_* F]_k`.

The coherence of `f_* F`, which is what lets the right-hand cycle be formed, is the proper
mapping theorem [Stacks, Tag 02O5] in the form `Stacks.Chow.properDirectImageIsCoherent`: `Y` is
locally Noetherian because it is locally of finite type over the locally Noetherian base. The
equation itself is
`Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf`. -/
@[stacks 02R6 "part (2)"]
theorem properPushforward_cycleAssociatedToCoherentSheaf_unconditional (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsProper f] (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) :
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      properDirectImageIsCoherent f F
    properPushforward C sX sY f hf k (cycleAssociatedToCoherentSheaf C sX F k hFk) =
      cycleAssociatedToCoherentSheaf C sY ((Scheme.Modules.pushforward f).obj F) k
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf F hFk) :=
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent := properDirectImageIsCoherent f F
  properPushforward_cycleAssociatedToCoherentSheaf C sX sY f hf F k hFk

/-- **[Stacks, Tag 02R6], part (1).** Let `f : X ⟶ Y` be a proper morphism of schemes locally of
finite type over the base `S` of chapter 42, and let `i : Z ⟶ X` be a closed subscheme with
`dim_δ(Z) ≤ k`. Then proper pushforward of `k`-cycles carries the cycle of `Z` to the cycle of
the direct image of its structure sheaf: `f_* [Z]_k = [f_* 𝒪_Z]_k`.

Here `𝒪_Z` is read as the coherent `𝒪_X`-module `i_* 𝒪_Z`, and the coherence of its direct image
along `f` is again [Stacks, Tag 02O5]. The equation is
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme`. -/
@[stacks 02R6 "part (1)"]
theorem properPushforward_cycleAssociatedToClosedSubscheme_unconditional (C : ChowSituation.{u})
    {Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      properDirectImageIsCoherent f ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
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
    properDirectImageIsCoherent f ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
  properPushforward_cycleAssociatedToClosedSubscheme C sX sY f hf i k hZ

end Stacks.Chow

end
