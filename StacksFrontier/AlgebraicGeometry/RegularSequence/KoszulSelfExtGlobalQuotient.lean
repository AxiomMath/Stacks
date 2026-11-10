module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentSitePushforward
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalGeneration
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafRecognition

/-!
# The restriction of a quotient of the structure sheaf to the slice site over an open

Let `X` be a ringed space, `𝓘 ⊆ O_X` a sheaf of ideals and `f₁, …, f_r` sections of `O_X` over an
open `U` generating `𝓘` there.  The gluing of the local statements of [Stacks, Tag 0BQY] asks, at
each member of its cover, for an identification of the quotient of the slice structure sheaf by
the sheaf of ideals the `fᵢ` generate with the restriction to the slice site of the global
quotient `O_X/𝓘`, compatible with the two quotient maps.

This file supplies it.  The restriction of the quotient map to the slice site is locally
surjective, and its kernel over a slice object is the ideal of sections of `𝓘` over the
underlying open, which is what the `fᵢ` generate there
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.sectionIdeal_sliceIdealOfSections_eq_obj`); so
`Stacks.Sites.quotientRingSheafIso` recognises the restricted quotient as the quotient by that
sheaf of ideals, and `Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafIso_hom` says it
carries one quotient map to the other.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.sliceQuotientHom`: the quotient map
  `O_X ⟶ O_X/𝓘`, restricted to `Opens X / U`.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.sliceQuotientRingHom`: **the identification `θ`**,
  as a morphism of the underlying sheaves of rings — the shape the gluing consumes.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.ker_sliceQuotientHom`: the kernel of the restricted
  quotient map over a slice object is the ideal of sections the `fᵢ` generate there.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isLocallySurjective_sliceQuotientRingHom` and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.quotientRingHom_comp_sliceQuotientRingHom`: the two
  hypotheses the gluing carries alongside `θ`.

## Implementation notes

**The recognition is `CommRingCat`-valued and the gluing is `RingCat`-valued.**
`Stacks.Sites.quotientRingSheafIso` identifies two sheaves of *commutative* rings, while the
descent of a sheaf of graded algebras runs over a bare sheaf of rings; the passage between them
is `CategoryTheory.sheafCompose` along `forget₂ CommRingCat RingCat`, applied to the isomorphism.
That the restriction to the slice site of the underlying sheaf of rings is the underlying sheaf
of rings of the restriction is definitional — both are the structure presheaf precomposed with
`Over.forget U` and postcomposed with the forgetful functor — so the ascriptions below are what
pin the spelling, and nothing transports along an equality of sheaves of rings.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace
open _root_.SheafOfModules.GradedAlgebra

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (J : (structureSheafModule X).Submodule)
  [HasWeakSheafify (Opens.grothendieckTopology X.carrier) CommRingCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}]

/-- The quotient map `O_X ⟶ O_X/𝓘` of sheaves of commutative rings, restricted to the slice site
over `U`. -/
abbrev sliceQuotientHom : X.sheaf.over U ⟶ (quotientRingSheaf J).over U :=
  ((Opens.grothendieckTopology X.carrier).overPullback CommRingCat.{u} U).map
    (toQuotientRingSheaf J)

/-- The restriction to the slice site over `U` of the quotient map `O_X ⟶ O_X/𝓘` is locally
surjective. -/
instance isLocallySurjective_sliceQuotientHom :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U)
      (sliceQuotientHom U J).hom :=
  haveI := isLocallySurjective_toQuotientRingSheaf J
  Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) (Over.forget U) (toQuotientRingSheaf J).hom

variable {r : ℕ} (f : Fin r → X.presheaf.obj (op U))

omit [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}] in
/-- The kernel of the restricted quotient map over a slice object is the ideal the `fᵢ` generate
there. -/
theorem ker_sliceQuotientHom (hJ : IsGeneratedByOn X J U f) (V : (Over U)ᵒᵖ) :
    RingHom.ker ((sliceQuotientHom U J).hom.app V).hom =
      sectionIdeal (sliceIdealOfSections U f) V := by
  rw [sectionIdeal_sliceIdealOfSections_eq_obj U f J hJ V]
  refine SetLike.ext fun a => ?_
  have h := (SheafOfModules.mem_kerIdeal (quotientRingHom J) (op V.unop.left) a).symm
  rw [kerIdeal_quotientRingHom J] at h
  exact Iff.trans (RingHom.mem_ker.trans (Iff.symm RingHom.mem_ker)) h

/-- **The identification of the two quotients of the structure sheaf over `U`.**  The restriction
to the slice site of the global quotient is the quotient of the slice structure sheaf by the
sheaf of ideals the `fᵢ` generate. -/
def sliceQuotientIso (hJ : IsGeneratedByOn X J U f) :
    quotientRingSheaf.{u, u, u} (sliceIdealOfSections U f) ≅
      (quotientRingSheaf.{u, u, u} J).over U :=
  quotientRingSheafIso (sliceQuotientHom U J) (sliceIdealOfSections U f)
    (ker_sliceQuotientHom U J f hJ)

/-- The identification `sliceQuotientIso` of the two quotients of the structure sheaf over `U`,
as a morphism of the underlying sheaves of rings. -/
abbrev sliceQuotientRingHom (hJ : IsGeneratedByOn X J U f) :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (quotientRingSheaf.{u, u, u} (sliceIdealOfSections U f)) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (quotientRingSheaf.{u, u, u} J)).over U :=
  (sheafCompose ((Opens.grothendieckTopology X.carrier).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (sliceQuotientIso U J f hJ).hom

/-- The morphism `sliceQuotientRingHom` of sheaves of rings is an isomorphism. -/
instance isIso_sliceQuotientRingHom (hJ : IsGeneratedByOn X J U f) :
    IsIso (sliceQuotientRingHom U J f hJ) :=
  inferInstanceAs (IsIso ((sheafCompose _ _).map (sliceQuotientIso U J f hJ).hom))

/-- The morphism `sliceQuotientRingHom` of sheaves of rings is locally surjective. -/
theorem isLocallySurjective_sliceQuotientRingHom (hJ : IsGeneratedByOn X J U f) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U)
      (sliceQuotientRingHom U J f hJ).hom :=
  have : IsIso (sliceQuotientRingHom U J f hJ).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (sliceQuotientRingHom U J f hJ)))
  inferInstance

/-- **The identification carries the quotient map by the generated sheaf of ideals to the
restriction of the global quotient map.** -/
theorem quotientRingHom_comp_sliceQuotientRingHom (hJ : IsGeneratedByOn X J U f) :
    quotientRingHom (sliceIdealOfSections U f) ≫ sliceQuotientRingHom U J f hJ =
      overRingHom (quotientRingHom J) U := by
  have h : toQuotientRingSheaf (sliceIdealOfSections U f) ≫ (sliceQuotientIso U J f hJ).hom =
      sliceQuotientHom U J :=
    toQuotientRingSheaf_comp_quotientRingSheafIso_hom (sliceQuotientHom U J)
      (sliceIdealOfSections U f) (ker_sliceQuotientHom U J f hJ)
  refine Eq.trans ((Functor.map_comp
    (sheafCompose ((Opens.grothendieckTopology X.carrier).over U)
      (forget₂ CommRingCat.{u} RingCat.{u}))
    (toQuotientRingSheaf (sliceIdealOfSections U f))
    (sliceQuotientIso U J f hJ).hom).symm) ?_
  rw [h]
  rfl

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
