module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# The pullback of an invertible module is invertible

Let `f : X ⟶ Y` be a morphism of schemes and let `L` be an invertible `𝒪_Y`-module. This file
proves that `f^*L` is an invertible `𝒪_X`-module, **without** [Stacks, Tag 01CD] — that is,
without knowing that pullback commutes with the tensor product.

## Main definitions

* `Stacks.Modules.restrictPullbackIso`: for `V ≤ f⁻¹(U)` the restriction to `V` of a pullback
  along `f` is the pullback along `f|_V : V ⟶ U` of the restriction to `U`.
* `Stacks.Modules.overIsoUnitOfRestrictIsoUnit`: a trivialization of `L` restricted to the open
  subscheme `U`, read as a trivialization of `L` over the localized site `Over U`. This is the
  direction missing from `StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Restriction.lean`,
  whose `restrictIsoUnitOfOverIsoUnit` is the other one and is reused here rather than
  re-derived.

## Main results

* `Stacks.Modules.isInvertible_pullback`, and the same in instance form: the pullback of an
  invertible module sheaf along an arbitrary morphism of schemes is invertible.
* `Stacks.Modules.exists_restrict_iso_unit_of_isInvertible`: an invertible module on a scheme
  has an open cover on each member of which it restricts to the structure sheaf.

## Implementation notes

The usual proof of this statement is the one Tag 01CT takes: a tensor inverse `N` of `L` pulls
back to a tensor inverse of `f^*L`, because `f^*(L ⊗ N) ≅ f^*L ⊗ f^*N` by Tag 01CD and
`f^*𝒪_Y ≅ 𝒪_X`. Tag 01CD is not available —
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean` constructs the
comparison morphism and leaves its invertibility open, and
`StacksFrontier/AlgebraicGeometry/InvertibleDual/Evaluation.lean` records that the pulled-back
*pairing* therefore cannot be built. **For invertibility of the pullback itself that note is
too pessimistic:** both halves of [Stacks, Tag 0B8M] are now available, and together they
replace Tag 01CD here. The route is

* `Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`, the converse half of Tag 0B8M,
  trivializes `L` on a cover `{U_y}` of `Y`;
* `restrictPullbackIso` identifies `(f^*L)|_{f^{-1}(U_y)}` with the pullback of `L|_{U_y}` along
  `f|_{f^{-1}(U_y)} : f^{-1}(U_y) ⟶ U_y`, so it is the pullback of the structure sheaf, hence
  the structure sheaf by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`;
* `Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit`, clause 1 of Tag 0B8M,
  concludes invertibility from those trivializations.

No `Tag 01CD` component is used, and no tensor product is formed at any point.

`restrictPullbackIso` is the connection the pullback functor was missing. `Scheme.Modules.pullback`
is defined as a left adjoint with no description of its sections, so "check it on a trivializing
cover and glue" has no foothold; what it *does* have is Mathlib's pseudofunctoriality
(`Scheme.Modules.pullbackComp`, `pullbackCongr`) and the explicit `restrictFunctor` for open
immersions, with `restrictFunctorIsoPullback` between them. Composing those along the square
`V ⟶ U`, `V ⟶ X`, `U ⟶ Y` — which commutes by `Scheme.Hom.resLE_comp_ι` — turns the
pseudofunctoriality into the localization statement, and that is the foothold.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class in which both
halves of Tag 0B8M are stated. The repository also carries
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`, with the same body; nothing here
identifies the two.

**Which triviality.** Two spellings of "trivial over `U`" occur and have to be converted into
one another: `L.over U ≅ 𝒪|_U` on the localized site `Over U`, which is what both halves of Tag
0B8M speak, and `L.restrict U.ι ≅ 𝒪_U` on the open subscheme `U`, which is what the pullback
calculus speaks. Mathlib's `Scheme.Modules.overFunctorEquiv` and
`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit` are the two ingredients of the conversion.
One direction is already available as
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit` (for Tag 01MU)
and is used here unchanged; the other, `overIsoUnitOfRestrictIsoUnit`, is obtained below from
full faithfulness of `Scheme.Modules.overEquiv`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Modules

/-! ### Localizing the pullback functor -/

variable {X Y : Scheme.{u}}

/-- **The restriction of a pullback is the pullback of a restriction.** For `f : X ⟶ Y` and opens
`V ≤ f⁻¹(U)`, restricting `f^*(-)` to `V` is pulling back along the induced morphism
`f|_V : V ⟶ U` the restriction to `U`.

This is Mathlib's pseudofunctoriality of `Scheme.Modules.pullback` applied to the commuting
square `V.ι ≫ f = f|_V ≫ U.ι`, read through `restrictFunctorIsoPullback`. -/
noncomputable def restrictPullbackIso (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f.resLE U V e) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
    Scheme.Modules.pullbackComp V.ι f ≪≫
    Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι f e).symm ≪≫
    (Scheme.Modules.pullbackComp (f.resLE U V e) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm _

/-- `restrictPullbackIso` at a single module. -/
noncomputable def restrictPullbackObjIso (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (M : Y.Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj M) V.ι ≅
      (Scheme.Modules.pullback (f.resLE U V e)).obj (Scheme.Modules.restrict M U.ι) :=
  (restrictPullbackIso f e).app M

/-! ### The two spellings of a trivialization over an open -/

/-- A trivialization of the restriction of `L` to the open subscheme `U`, read as a
trivialization of `L` over the localized site `Over U`.

This is the passage inverse to
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`, which is in the library and
not re-derived here; the two together are what lets the trivializations produced by the pullback
calculus be fed to Tag 0B8M's descent step, which speaks the localized site. -/
noncomputable def overIsoUnitOfRestrictIsoUnit (L : Y.Modules) (U : Y.Opens)
    (e : Scheme.Modules.restrict L U.ι ≅ SheafOfModules.unit (U.toScheme.ringCatSheaf)) :
    L.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app L ≪≫ e ≪≫
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U Y.ringCatSheaf).symm)

/-! ### Invertibility of the pullback -/

/-- **An invertible module on a scheme is trivial on an open cover**, in the `restrict`
spelling: there is a family of opens covering the scheme on each member of which the restriction
of `L` is isomorphic to the structure sheaf of that open subscheme.

This is the converse half of Tag 0B8M (`exists_bijective_smul_of_isInvertible`) together with
`isoUnitOver` and
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`. -/
theorem exists_restrict_iso_unit_of_isInvertible (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    ∃ U : Y → Y.Opens, (⨆ y, U y) = ⊤ ∧
      ∀ y, Nonempty (Scheme.Modules.restrict L (U y).ι ≅
        SheafOfModules.unit ((U y).toScheme.ringCatSheaf)) := by
  have : ∀ z : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose U hyU a ha using
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L
  refine ⟨U, ?_, fun y => ⟨Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit
    (U y) L (Stacks.SheafOfModules.isoUnitOver L (U y) (a y) (ha y))⟩⟩
  refine top_le_iff.1 fun y _ => ?_
  exact Opens.mem_iSup.2 ⟨y, hyU y⟩

/-- **The pullback of an invertible module sheaf is invertible**, for an arbitrary morphism of
schemes and with no use of Tag 01CD. -/
theorem isInvertible_pullback (f : X ⟶ Y) (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) := by
  obtain ⟨U, hU, hiso⟩ := exists_restrict_iso_unit_of_isInvertible L
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit
    X.presheaf (structureSheafRing X.toRingedSpace).property _
    (X := fun y : Y => f ⁻¹ᵁ U y) ?_ fun y => ⟨overIsoUnitOfRestrictIsoUnit _ _ ?_⟩
  · refine (Opens.coversTop_iff _ _).2 (IsOpenCover.mk (top_le_iff.1 fun x _ => ?_))
    have hx : f.base x ∈ (⨆ y, U y) := by rw [hU]; exact Opens.mem_top _
    obtain ⟨y, hy⟩ := Opens.mem_iSup.1 hx
    exact Opens.mem_iSup.2 ⟨y, hy⟩
  · exact restrictPullbackObjIso f (U := U y) (V := f ⁻¹ᵁ U y) le_rfl L ≪≫
      (Scheme.Modules.pullback (f.resLE (U y) (f ⁻¹ᵁ U y) le_rfl)).mapIso (hiso y).some ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso _

/-- `isInvertible_pullback` in instance form. -/
instance (priority := 100) instIsInvertiblePullbackObj (f : X ⟶ Y) (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  isInvertible_pullback f L

end Stacks.Modules

end
