module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic along a closed immersion

For a closed immersion `i : Z ⟶ X` and a structure morphism `f : X ⟶ Spec k` the cohomology of
`𝒢` on `Z` and of `i_*𝒢` on `X` are isomorphic as `k`-vector spaces
(`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`). This file draws the
numerical consequences: equal dimensions in every degree, hence equal Euler characteristics,
and — composing with the projection formula of
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` — the identity

`χ(X, i_*𝒢 ⊗ ℰ) = χ(Z, 𝒢 ⊗ i^*ℰ)`

which is how a computation on `X` involving a sheaf supported on a closed subscheme is moved to
that subscheme. It is the closed-immersion case of [Stacks, Tag 089W] at the level of Euler
characteristics, together with the closed-immersion case of the projection formula of
[Stacks, Tag 01E8].

Both are used by the induction on the ideal of the reduction in the proof of [Stacks, Tag 0AYW]:
there the short exact sequence `0 → ℐ^e → 𝒪_X → 𝒪_{X'} → 0` has its outer terms pushed forward
from the reduction `C` and from `X'`, and every Euler characteristic of a tensor product with
`ℰ` that the computation needs is read off on `C` or on `X'` by the identity above.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `finrank_cohomologyOverField_pushforward_of_isClosedImmersion`: `Hⁿ(Z, 𝒢)` and `Hⁿ(X, i_*𝒢)`
  have the same dimension over `k`.
* `eulerCharacteristic_pushforward_of_isClosedImmersion`: `χ(X, i_*𝒢) = χ(Z, 𝒢)`.
* `isFiniteLocallyFreeOfRank_pullback`: the pullback of a finite locally free sheaf of constant
  rank along an arbitrary morphism of schemes is again finite locally free of that rank.
* `eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion`:
  `χ(X, i_*𝒢 ⊗ ℰ) = χ(Z, 𝒢 ⊗ i^*ℰ)`.
* `eulerCharacteristic_unit_tensorSheaf`: `χ(X, 𝒪_X ⊗ ℰ) = χ(X, ℰ)`, the left-hand companion of
  `AlgebraicGeometry.eulerCharacteristic_tensor_unit`.
* `eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion`:
  `χ(X, i_*𝒪_Z ⊗ ℰ) = χ(Z, i^*ℰ)`, the previous identity at `𝒢 = 𝒪_Z`.

## Implementation notes

**Coherence is passed explicitly, not by instance search.** The types of the statements mention
`AlgebraicGeometry.eulerCharacteristic`, whose coherence argument is an instance; a caller
typically holds a coherence witness as a term (produced, for instance, by
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` or by
`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`) rather than as an instance in
scope. The statements therefore take the witnesses as ordinary arguments and apply
`eulerCharacteristic` to them with `@`, which is the idiom of
`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/Devissage.lean`.

**No spelling bridge was needed for the projection formula.** It is stated over
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace` with
`Stacks.RingedSpace.tensorSheaf`, `Stacks.RingedSpace.pushforwardFunctor` and
`Stacks.RingedSpace.pullbackFunctor`, while this file's consumers use `X.Modules`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`,
  `AlgebraicGeometry.Scheme.Modules.pushforward` and
`AlgebraicGeometry.Scheme.Modules.pullback`. All four pairs are equal by `rfl`, so
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` is usable at the second
spelling with no transport and no transparency option.

**`isFiniteLocallyFreeOfRank_pullback` generalizes a declaration that existed only at one
morphism.** The declaration
`isFiniteLocallyFreeOfRank_pullback_reducedComponentι` of
`Stacks.AlgebraicGeometry.ComponentDegrees`
is the same statement for the closed immersion of a reduced component; its proof uses nothing
about that morphism, so the general form is the same two lines over
`Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData`. The special case is left in place.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The pullback of a finite locally free sheaf of constant rank is finite locally free of the
same rank**, along an arbitrary morphism of schemes. -/
theorem isFiniteLocallyFreeOfRank_pullback {Y X : Scheme.{u}} (g : Y ⟶ X) (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r :=
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData g.base g.toRingCatSheafHom E r
    inferInstance

variable (k : Type u) [Field k] {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k))

/-- **Cohomology along a closed immersion has the same dimension upstairs and downstairs.** -/
theorem finrank_cohomologyOverField_pushforward_of_isClosedImmersion [IsClosedImmersion i]
    (G : Z.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (i ≫ f) G n) =
      Module.finrank k
        (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n) :=
  (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f G n).toLinearEquiv.finrank_eq

/-- **The Euler characteristic is unchanged by pushing forward along a closed immersion**:
`χ(X, i_*𝒢) = χ(Z, 𝒢)`. This is [Stacks, Tag 089W] at the level of Euler characteristics, for a
closed immersion. -/
theorem eulerCharacteristic_pushforward_of_isClosedImmersion [IsClosedImmersion i] [IsProper f]
    (G : Z.Modules) (hG : SheafOfModules.IsCoherent G)
    (hpush : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj G)) :
    @eulerCharacteristic k _ X f _ ((Scheme.Modules.pushforward i).obj G) hpush =
      @eulerCharacteristic k _ Z (i ≫ f) _ G hG := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_congr fun n => by
    rw [finrank_cohomologyOverField_pushforward_of_isClosedImmersion k i f G n]

/-- **The Euler characteristic of a tensor product with a module pushed forward from a closed
subscheme is computed on that subscheme**: `χ(X, i_*𝒢 ⊗ ℰ) = χ(Z, 𝒢 ⊗ i^*ℰ)`. The projection
formula identifies the module on `X` with the direct image of the module on `Z`, and
`AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion` moves the Euler
characteristic across. -/
@[sga "6 X 4.4" "(4.4.2), special case"]
theorem eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion [IsClosedImmersion i]
    [IsProper f] [IsLocallyNoetherian X] (G : Z.Modules) (E : X.Modules)
    (hG : SheafOfModules.IsCoherent G) (hE : SheafOfModules.IsCoherent E)
    (hpushG : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj G))
    (hpullE : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E)) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pushforward i).obj G))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hpushG hE) =
      @eulerCharacteristic k _ Z (i ≫ f) _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
              (G)).obj (((Scheme.Modules.pullback i).obj E))))
        (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace G _ hG hpullE) := by
  have hT := @SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace G _ hG hpullE
  have hZ := @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ hT
  refine Eq.trans ?_ (eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hT hZ)
  exact @eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hpushG hE) hZ
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i G E)

/-- **Tensoring with the structure sheaf on the left does not change the Euler
characteristic**: `χ(X, 𝒪_X ⊗ ℰ) = χ(X, ℰ)`. The companion on the other side is
`AlgebraicGeometry.eulerCharacteristic_tensor_unit`. -/
theorem eulerCharacteristic_unit_tensorSheaf [IsProper f] (E : X.Modules)
    (hE : SheafOfModules.IsCoherent E)
    (hunit : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((SheafOfModules.unit X.ringCatSheaf))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hunit hE) =
      @eulerCharacteristic k _ X f _ E hE :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hunit hE) hE
    (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace E)

/-- **The Euler characteristic of `ℰ` tensored with the structure sheaf of a closed subscheme is
the Euler characteristic of the restriction of `ℰ` to that subscheme**:
`χ(X, i_*𝒪_Z ⊗ ℰ) = χ(Z, i^*ℰ)`.

This is the identity by which the right-hand term of the short exact sequence
`0 → ℐ^e → 𝒪_X → 𝒪_{X'} → 0`, tensored with `ℰ`, is read off on `X'` in the induction of
[Stacks, Tag 0AYW]. -/
theorem eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion
    [IsClosedImmersion i] [IsProper f] [IsLocallyNoetherian X] (E : X.Modules)
    (hE : SheafOfModules.IsCoherent E)
    (hunitZ : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (hpushunit : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hpullE : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E)) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hpushunit hE) =
      @eulerCharacteristic k _ Z (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hpullE := by
  refine Eq.trans
    (eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i f
      (SheafOfModules.unit Z.ringCatSheaf) E hunitZ hE hpushunit hpullE) ?_
  exact eulerCharacteristic_unit_tensorSheaf k (i ≫ f) _ hpullE hunitZ

end AlgebraicGeometry

end
