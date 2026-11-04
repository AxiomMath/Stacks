module

public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula

/-!
# The pullback of an invertible module along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `L` be an invertible
`𝒪_Y`-module. [Stacks, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L) asserts that `f^*L`
is an invertible `𝒪_X`-module, and its proof is exactly two lemmas: by Tag 0B8K choose `N` with
`L ⊗_{𝒪_Y} N ≅ 𝒪_Y`; by Tag 01CD the pullback of that pairing is
`f^*L ⊗_{𝒪_X} f^*N ≅ f^*𝒪_Y ≅ 𝒪_X`; by Tag 0B8K again `f^*L` is invertible. That is the proof
taken here, with no detour.

Tag 01CD enters through `Stacks.RingedSpace.tensorIsoUnitPullback` and the instance
`Stacks.RingedSpace.isIso_comparison`. The predicate that
`StacksFrontier/AlgebraicGeometry/PullbackTensor/Basic.lean` reduces Tag 01CD to,
`Stacks.RingedSpace.PullbackStalkFormula f` — the stalk formula of Tag 0098 for the
adjunction-defined pullback — is a theorem in
`StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean`, so both statements below
are unconditional and no hypothesis of 01CD's shape is coined locally.

For a morphism of **schemes** the same conclusion is already available unconditionally, by a
different route that avoids Tag 01CD altogether:
`Stacks.Modules.isInvertible_pullback` in
`StacksFrontier/AlgebraicGeometry/PullbackInvertible/Basic.lean`. The statement here is the
ringed-space statement that Tag 0B8L actually makes, which that one does not imply.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.RingedSpace.isInvertible_modulePullback`: Tag 0B8L for
  `Stacks.SheafOfModules.IsInvertible`. This is the registration carrier for the tag.
* `Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback`: the same statement for
  `AlgebraicGeometry.SheafOfModules.IsInvertible`, the other of the repository's two
  Tag 01CS predicates, obtained from the first across an iff and carrying no attribute.

## Implementation notes

**Which `IsInvertible`.** The repository carries two classes with the same body,
`Stacks.SheafOfModules.IsInvertible`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`) and
`AlgebraicGeometry.SheafOfModules.IsInvertible`
(`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`), and neither discharges the other by
instance search. Tag 0B8K is stated for the first, so the argument is run there and carried
across once by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; nothing is restated
on either side.

**Where the tag sits.** The two theorems below assert the same thing — Tag 0B8L — and differ
only in which of the two provably equivalent Tag 01CS invertibility predicates it is spelled
with; the second is the first transported along
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. That is one result in two
spellings and not two parts of the tag, so the Tag 0B8L attribute sits on
`isInvertible_modulePullback` alone. The second theorem stays, with no attribute, because the
downstream divisor and ampleness files state invertibility in its class and use it directly.

## References

* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.RingedSpace

variable {X Y : RingedSpace.{u, u}}

/-- **Stacks Project, Tag 0B8L.** The pullback `f^*L` of an invertible `𝒪_Y`-module along a
morphism of ringed spaces `f : X ⟶ Y` is an invertible `𝒪_X`-module.

The proof is the one the Stacks Project gives. Tag 0B8K produces an `𝒪_Y`-module `N` with
`L ⊗_{𝒪_Y} N ≅ 𝒪_Y`; `Stacks.RingedSpace.tensorIsoUnitPullback` pulls that pairing back, which
is where Tag 01CD enters; and Tag 0B8K read in the other direction concludes. -/
@[stacks 0B8L]
theorem isInvertible_modulePullback (f : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureSheafRing Y).property L] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheafRing X).property
      ((modulePullback f).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := Y.sheaf.obj) (hO := (structureSheafRing Y).property) L).mp inferInstance
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.sheaf.obj) (hO := (structureSheafRing X).property) _).mpr
      ⟨(modulePullback f).obj N, ⟨?_⟩⟩
  exact tensorIsoUnitPullback f L N e (isIso_comparison f L N)

/-- **Stacks Project, Tag 0B8L** for `AlgebraicGeometry.SheafOfModules.IsInvertible`, the other
of the repository's two Tag 01CS invertibility predicates. This is the spelling in which the
chapter-31 divisor arguments state invertibility; it is
`isInvertible_modulePullback` carried across
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` once.

No attribute: this is Tag 0B8L in the second spelling of one invertibility predicate, not a
second part of the tag, so the registration sits on `isInvertible_modulePullback`. -/
theorem algebraicGeometryIsInvertible_modulePullback (f : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
      ((modulePullback f).obj L) :=
  have : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureSheafRing Y).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (isInvertible_modulePullback f L)

end Stacks.RingedSpace

end
