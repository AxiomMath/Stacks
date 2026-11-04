module

public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Stacks Tag 05P2, the implication (1) ⟹ (4)

Entry (1) of Stacks Tag 05P2 is "flat and of finite presentation" and entry (4) is "finite
locally free". This file proves that implication for a sheaf of modules on a scheme.

The stalk of a finite type sheaf of modules is a finite module over the local ring
(`Stacks.StalkFiniteType.finite_stalk`), flatness of the sheaf gives flatness of the stalk
(Tag 05NE, `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`), and a finite flat module
over a local ring is free (`Module.free_of_flat_of_isLocalRing`, Tag 00NZ). In particular no
finite presentation of the stalk is needed.

## Main results

* `Stacks.StalkFiniteType.free_stalk_of_flat`: the stalk of a finite type sheaf of modules on a
  scheme which is flat over the local ring is free over it — finite plus flat over a local ring.
* `Stacks.StalkFiniteType.exists_nhd_iso_free_of_flat_stalk`: a finitely presented sheaf of
  modules with flat stalk at `x` is free on a neighbourhood of `x`, with finite index type. This
  is Tag 0B8J fed through `Stacks.StalkFiniteType.basisRingCatStalk`.
* `Stacks.StalkFiniteType.isFiniteLocallyFree_of_isFinitePresentation_of_flat_stalk`: assembling
  those neighbourhoods over all points gives finite locally free local generators data.
* `Stacks.StalkFiniteType.flat_stalk_of_isFlat`: Tag 05NE read at a scheme.
* `Stacks.StalkFiniteType.isFiniteLocallyFree_of_isFlat_of_isFinitePresentation`: **Stacks Tag
  05P2, the implication (1) ⟹ (4).**

## Implementation notes

**Generating sections from a free chart.** Tag 0B8J returns an isomorphism
`M.over U ≅ SheafOfModules.free ρ`, and what the covering data wants is
`(M.over U).GeneratingSections` whose structure map is an isomorphism. Mathlib's route —
`SheafOfModules.GeneratingSections.equivOfIso` applied to `SheafOfModules.free.generatingSections`
— leaves the structure map as `𝟙 (free ρ) ≫ g.hom` at the type
`free (free.generatingSections ρ).I ⟶ _`, and neither `rw` nor `simp` can cancel the identity
there: the index type is `ρ` only up to unfolding, so the rewrite produces an ill-typed motive.
Mathlib's own corresponding instance works around this with
the `backward.isDefEq.respectTransparency` pragma set to `false`.
`generatingSectionsOfFreeIso` below
avoids the problem instead of working around it, by taking `I := ρ` and `s := freeHomEquiv g.hom`
outright, so that its structure map is `g.hom` by `Equiv.symm_apply_apply` with both sides at the
same type.

**Spelling of the hypotheses.** `AlgebraicGeometry.SheafOfModules.IsFlat` takes the Grothendieck
topology as an implicit argument which cannot be recovered from `X.sheaf`: `TopCat.Sheaf` is a
definition that does not unfold during unification, so `(O := X.sheaf)` alone leaves the topology
an unsolved metavariable. It is given explicitly.

Instance search also does not derive `M.IsFiniteType` from `M.IsFinitePresentation` for
`M : X.Modules`, because `AlgebraicGeometry.Scheme.Modules` is a `def` that search will not
unfold; the Mathlib instance applies perfectly well when named, which is
`isFiniteType_of_isFinitePresentation`.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite

universe v' u' u

namespace Stacks.StalkFiniteType

section Site

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {Rr : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The generating sections of a sheaf of modules exhibited as a free one: the index type is the
index type of the free sheaf and the sections are the images of its basis sections. -/
def generatingSectionsOfFreeIso {N : SheafOfModules.{u} Rr} {ρ : Type u}
    (g : SheafOfModules.free ρ ≅ N) : N.GeneratingSections where
  I := ρ
  s := N.freeHomEquiv g.hom
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

/-- The structure map of `generatingSectionsOfFreeIso g` is `g.hom`. -/
@[simp]
lemma generatingSectionsOfFreeIso_π {N : SheafOfModules.{u} Rr} {ρ : Type u}
    (g : SheafOfModules.free ρ ≅ N) : (generatingSectionsOfFreeIso g).π = g.hom :=
  N.freeHomEquiv.symm_apply_apply g.hom

/-- The structure map of `generatingSectionsOfFreeIso g` is an isomorphism. -/
instance isIso_generatingSectionsOfFreeIso_π {N : SheafOfModules.{u} Rr} {ρ : Type u}
    (g : SheafOfModules.free ρ ≅ N) : IsIso (generatingSectionsOfFreeIso g).π := by
  rw [generatingSectionsOfFreeIso_π]
  exact g.isIso_hom

end Site

section OnAScheme

variable {X : Scheme.{u}}

/-- A finitely presented sheaf of modules on a scheme is of finite type. -/
theorem isFiniteType_of_isFinitePresentation (M : X.Modules) [M.IsFinitePresentation] :
    M.IsFiniteType :=
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M

/-- **The stalk of a finite type sheaf of modules which is flat at a point is free there.** The
local ring of a scheme is local and the stalk is a finite module over it by
`Stacks.StalkFiniteType.finite_stalk`, so `Module.free_of_flat_of_isLocalRing` applies. Note that
no finite presentation of the stalk is involved. -/
theorem free_stalk_of_flat (M : X.Modules) [M.IsFiniteType] (x : X)
    (hflat : Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    Module.Free (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  have := finite_stalk M x
  have := hflat
  Module.free_of_flat_of_isLocalRing

/-- A finitely presented sheaf of modules on a scheme whose stalk at `x` is flat over the local
ring is isomorphic to a free sheaf of modules of finite rank on a neighbourhood of `x`.

The stalk is finite and flat, hence free of finite rank; its basis is transported to the
`RingCat`-valued stalk by `Stacks.StalkFiniteType.basisRingCatStalk` and fed to Stacks Tag
0B8J. -/
theorem exists_nhd_iso_free_of_flat_stalk (M : X.Modules) [M.IsFinitePresentation] (x : X)
    (hflat : Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ (U : X.Opens) (ρ : Type u) (_ : Finite ρ), x ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) ρ) := by
  have := isFiniteType_of_isFinitePresentation M
  have := finite_stalk M x
  have := free_stalk_of_flat M x hflat
  obtain ⟨U, hxU, hU⟩ := exists_over_iso_free_of_stalk_basis M x
    (Module.Free.chooseBasis (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)))
  exact ⟨U, _, inferInstance, hxU, hU⟩

/-- **Stacks Tag 05P2, the implication (1) ⟹ (4), with flatness taken at the stalks.** A
finitely presented sheaf of modules on a scheme all of whose stalks are flat over the local ring
is finite locally free.

The covering family is indexed by the points of `X`: each point has a neighbourhood on which `M`
is free of finite rank, and those neighbourhoods cover because each contains its own point. -/
theorem isFiniteLocallyFree_of_isFinitePresentation_of_flat_stalk (M : X.Modules)
    [M.IsFinitePresentation]
    (hflat : ∀ x : X, Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M := by
  choose U ρ hρ hxU hiso using fun x : X => exists_nhd_iso_free_of_flat_stalk M x (hflat x)
  have e : ∀ y : X, M.over (U y) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U y)) (ρ y) :=
    fun y => (hiso y).some
  have hcov : (Opens.grothendieckTopology ((X : TopCat.{u}) : Type u)).CoversTop U := by
    refine (Opens.coversTop_iff _ _).2 (IsOpenCover.mk (eq_top_iff.2 (SetLike.le_def.2 ?_)))
    intro y _
    exact Opens.mem_iSup.2 ⟨y, hxU y⟩
  constructor
  refine ⟨{ I := (X : TopCat.{u}), X := U, coversTop := hcov
            generators := fun y => generatingSectionsOfFreeIso (e y).symm }, ?_, ?_⟩
  · constructor
    intro y
    infer_instance
  · constructor
    intro y
    exact ⟨hρ y⟩

/-- **Stacks Tag 05NE at a scheme.** A flat sheaf of modules on a scheme has flat stalks over the
local rings. The Grothendieck topology is passed explicitly because `TopCat.Sheaf` does not
unfold during unification. -/
theorem flat_stalk_of_isFlat (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat
      (J := Opens.grothendieckTopology ((X : TopCat.{u}) : Type u)) (O := X.sheaf) M) (x : X) :
    Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf M).1 hM x

/-- **Stacks Tag 05P2, the implication (1) ⟹ (4).** A flat, finitely presented sheaf of modules
on a scheme is finite locally free. -/
theorem isFiniteLocallyFree_of_isFlat_of_isFinitePresentation (M : X.Modules)
    [M.IsFinitePresentation]
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat
      (J := Opens.grothendieckTopology ((X : TopCat.{u}) : Type u)) (O := X.sheaf) M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
  isFiniteLocallyFree_of_isFinitePresentation_of_flat_stalk M (flat_stalk_of_isFlat M hM)

/-- Tag 05P2 (1) ⟹ (4) for the repository's second, untagged copy of finite local freeness. -/
theorem finiteLocallyFree_of_isFlat_of_isFinitePresentation (M : X.Modules)
    [M.IsFinitePresentation]
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat
      (J := Opens.grothendieckTopology ((X : TopCat.{u}) : Type u)) (O := X.sheaf) M) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
  have := isFiniteLocallyFree_of_isFlat_of_isFinitePresentation M hM
  StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree M

end OnAScheme

end Stacks.StalkFiniteType

end
