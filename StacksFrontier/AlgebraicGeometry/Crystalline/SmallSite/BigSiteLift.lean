module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift

/-!
# Lifting a sheaf of modules from `Cris(X/S)` to `CRIS(X/S)`, and the universe it is possible at

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The inclusion
`i : Cris(X/S) ⥤ CRIS(X/S)` of [Stacks, Tag 07IJ] is continuous, cocontinuous and fully faithful,
and on sheaves of `𝒪_{X/S}`-modules the restriction `i^{-1}` has a right adjoint `i_*` whose
counit is invertible, `...SmallSite.moduleDirectImageιCounitIso`.  So **`i^{-1}` is essentially
surjective**: every sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` is the restriction of one on
`CRIS(X/S)`, namely of its own direct image.

This module records that, and records exactly **at which module universe** it holds and why it
does not descend.

## The universe, stated precisely

`i_*` is `Stacks.SheafOfModules.directImage`, whose value over an object `B` of `CRIS(X/S)` is the
module of compatible families of sections indexed by the objects of `Cris(X/S)` over `B` — a limit
over a category whose objects form a `Type (u + 1)`, the objects of `CRIS(X/S)` being
`Crystalline.GlobalCrystallineSituation.Thickening`, a structure on `Scheme.{u}`.  The sections of
`i_* ℱ` therefore live in `Type (u + 1)` and `...SmallSite.moduleDirectImageι` goes between
`...SmallSite.ModuleSheaf` and `...SmallSite.BigModuleSheaf`, the sheaves of modules with sections
there.  The same holds of the lower shriek `...SmallSite.moduleLowerShriek`, whose value is a
colimit over a category of the same size, and the module-level `i_!` is in any case not exact
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`).

The chapter's crystal and quasi-coherence predicates, and the base-change maps of
[Stacks, Tag 07J6] and [Stacks, Tag 07JG], are stated for sheaves of modules with sections in
`Type u`: the affine computation reads the restriction `ℱ_T` as an
`AlgebraicGeometry.Scheme.Modules`, and the modules on a `Scheme.{u}` have sections in `Type u`.
So what those statements would need is a lift with sections in `Type u`, and that is **not** what
either functor produces.

`essSurj_moduleRestrictι` is the lift at module universe `u + 1`, unconditionally.
`nonempty_restrictSheafOfModules_iso_iff` then says exactly what the lift at module universe `u`
is: the universe lift `...SmallSite.moduleULift` is full and faithful, and
`...SmallSite.moduleULift_obj_restrictSheafOfModules` is an equality, so a sheaf `N` on
`CRIS(X/S)` with sections in `Type u` restricts to `ℱ` precisely when its universe lift restricts
to the universe lift of `ℱ`.  Hence

> the lift at module universe `u` holds for `ℱ` if and only if **some** `u + 1`-level lift of the
> universe lift of `ℱ` lies in the essential image of `...SmallSite.bigModuleULift`,

which is `exists_restrictSheafOfModules_iso_iff`.  A `u + 1`-level lift always exists, by
`essSurj_moduleRestrictι`; what is not available is one with essentially small sections, and the
limit computing `i_* ℱ` gives no reason for its sections to be small.

The route taken in the chapter is therefore not to lift.  `SmallSite`
`/CrysFirstOrderAffineBaseChange.lean` proves the affine statement of [Stacks, Tag 07J6] on
`Cris(X/S)` directly, and `SmallSite/LevelBaseChangeAffineLevels.lean` discharges with it the
base-change input of [Stacks, Tag 07JG] that
`SmallSite/LevelBaseChangeFromBigSite.lean` had reduced to a lift.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `essSurj_moduleRestrictι` — **`i^{-1}` on sheaves of `𝒪_{X/S}`-modules is essentially
  surjective**, at the module universe `u + 1`.
* `exists_moduleRestrictι_obj_iso_moduleULift` — hence every sheaf of `𝒪_{X/S}`-modules on
  `Cris(X/S)` with sections in `Type u` has its universe lift restricted from `CRIS(X/S)`.
* `nonempty_restrictSheafOfModules_iso_iff` — for a sheaf of modules on `CRIS(X/S)` with sections
  in `Type u`, restricting to `ℱ` is the same as having its universe lift restrict to the universe
  lift of `ℱ`.
* `exists_restrictSheafOfModules_iso_iff` — **the exact content of the missing lift**: it is the
  question whether a `u + 1`-level lift can be found in the essential image of the universe lift.

**No `@[stacks]` attribute is placed**: [Stacks, Tag 07IJ] is registered where the morphism of
topoi and its adjunctions are built.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The lift at module universe `u + 1` -/

/-- **`i^{-1}` on sheaves of `𝒪_{X/S}`-modules is essentially surjective.**  The direct image
`i_*` is a right adjoint of it whose counit is invertible — the inclusion of sites being fully
faithful, so that over an object of the image the index category of the right Kan extension has
the identity index as an initial object — and `i^{-1} i_* 𝒢 ≅ 𝒢` exhibits `𝒢` as a restriction.

This is the lift at the module universe `u + 1` of `...SmallSite.ModuleSheaf`, which is the
universe `i_*` exists at; see the module documentation. -/
instance essSurj_moduleRestrictι : (moduleRestrictι S).EssSurj where
  mem_essImage G :=
    ⟨(moduleDirectImageι S).obj G, ⟨(moduleDirectImageιCounitIso S).app G⟩⟩

/-- **The universe lift of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` with sections in `Type u`
is the restriction of a sheaf of modules on `CRIS(X/S)`** with sections in `Type (u + 1)`. -/
theorem exists_moduleRestrictι_obj_iso_moduleULift (F : SheafOfModules.{u} (structureSheaf S)) :
    ∃ N : BigModuleSheaf S, Nonempty ((moduleRestrictι S).obj N ≅ (moduleULift S).obj F) :=
  Functor.EssSurj.mem_essImage (F := moduleRestrictι S) _

/-! ### What the lift at module universe `u` is -/

/-- **A sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` with sections in `Type u` restricts to `ℱ` if
and only if its universe lift restricts to the universe lift of `ℱ`.**

The forward direction applies the universe lift to the isomorphism and rewrites along
`...SmallSite.moduleULift_obj_restrictSheafOfModules`, which is an equality; the backward
direction takes the preimage of the isomorphism under `...SmallSite.moduleULift`, which is full
and faithful. -/
theorem nonempty_restrictSheafOfModules_iso_iff
    (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (F : SheafOfModules.{u} (structureSheaf S)) :
    Nonempty (restrictSheafOfModules N ≅ F) ↔
      Nonempty ((moduleRestrictι S).obj ((bigModuleULift S).obj N) ≅ (moduleULift S).obj F) :=
  ⟨fun ⟨α⟩ ↦ ⟨eqToIso (moduleULift_obj_restrictSheafOfModules S N).symm ≪≫
      (moduleULift S).mapIso α⟩,
    fun ⟨α⟩ ↦ ⟨(Functor.FullyFaithful.ofFullyFaithful (moduleULift S)).preimageIso
      (eqToIso (moduleULift_obj_restrictSheafOfModules S N) ≪≫ α)⟩⟩

/-- **The exact content of the big-site lift at module universe `u`.**

A sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` is isomorphic to the restriction of one on
`CRIS(X/S)` with sections in `Type u` if and only if its universe lift is isomorphic to the
restriction of a sheaf of modules on `CRIS(X/S)` **of the form `bigModuleULift N`** — that is, one
whose sections are essentially small.

A restriction of *some* sheaf of modules on `CRIS(X/S)` at universe `u + 1` always exists, by
`exists_moduleRestrictι_obj_iso_moduleULift`.  So this isolates the whole of the obstruction: it
is the smallness of the sections of the lift, and nothing else. -/
theorem exists_restrictSheafOfModules_iso_iff (F : SheafOfModules.{u} (structureSheaf S)) :
    (∃ N : SheafOfModules.{u} (crystallineStructureSheaf S),
        Nonempty (restrictSheafOfModules N ≅ F)) ↔
      ∃ N : SheafOfModules.{u} (crystallineStructureSheaf S),
        Nonempty ((moduleRestrictι S).obj ((bigModuleULift S).obj N) ≅
          (moduleULift S).obj F) :=
  exists_congr fun N ↦ nonempty_restrictSheafOfModules_iso_iff S N F

end Crystalline.GlobalCrystallineSituation.SmallSite

end
