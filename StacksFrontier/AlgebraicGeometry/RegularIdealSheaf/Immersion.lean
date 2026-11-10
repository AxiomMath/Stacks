module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Regular
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular, Koszul-regular, `H₁`-regular and quasi-regular immersions

Let `i : Z ⟶ X` be an immersion of schemes.  Stacks tag 063J calls `i` *regular*,
*Koszul-regular*, *`H₁`-regular* or *quasi-regular* when there is an open `U ⊆ X` with
`i(Z) ⊆ U` closed in `U` such that the defining ideal sheaf of the closed immersion `Z ⟶ U` has
the corresponding property of Stacks tag 063D.

This file supplies the defining ideal sheaf and the four conditions.  The open neighbourhood is
taken to be the canonical one: an immersion factors as the closed immersion `i.liftCoborder` into
the open subscheme `i.coborderRange`, and `i.coborderRange` is the largest open of `X` in which
the image of `i` is closed, so every admissible `U` is an open of it.

## Main definitions

* `kernelSubmodule f`: the sectionwise kernel of a morphism of sheaves of modules, as an
  embedded submodule of its source.
* `definingIdealOfHom j`: for `j : Z ⟶ U` a morphism of schemes, the kernel of
  `O_U ⟶ j_* O_Z` as an ideal subsheaf of `O_U`.  For a closed immersion this is its defining
  ideal sheaf.
* `definingIdeal i`: the defining ideal sheaf `definingIdealOfHom i.liftCoborder` of the
  canonical closed factor of an immersion, an ideal subsheaf of `O_{i.coborderRange}`.
* `IsRegularImmersion i`, `IsKoszulRegularImmersion i`, `IsH1RegularImmersion i`,
  `IsQuasiRegularImmersion i`: parts (1), (2), (3) and (4) of Stacks tag 063J.

## Main results

* `mem_definingIdealOfHom` and `eq_definingIdealOfHom_of_mem_iff`: the defining ideal is
  characterized, sectionwise and uniquely, by vanishing in the pushforward structure sheaf.
* `le_coborderRange_of_isClosedImmersion`: every open in which the immersion is closed is an open
  of `i.coborderRange`, so the canonical choice is the largest admissible one.
* `isRegularImmersion_iff`, `isKoszulRegularImmersion_iff`, `isH1RegularImmersion_iff`,
  `isQuasiRegularImmersion_iff`: the four conditions may be checked against any ideal subsheaf
  of `O_{i.coborderRange}` identified with the defining ideal, which is how a construction of
  that ideal by other means is fed to them.

## Implementation notes

The ideal sheaf is the *sectionwise* kernel of `O_U ⟶ j_* O_Z` rather than the categorical
kernel of that map in `SheafOfModules`, because the four conditions of Stacks tag 063D are
stated for a `SheafOfModules.Submodule` of the structure sheaf module, i.e. for an ideal
subsheaf presented as a family of ideals of the rings of sections.  `kernelSubmodule` builds
exactly that: the sheaf condition on the family is the separatedness of the target, since a
section whose restrictions along a cover all vanish vanishes.

The map `O_U ⟶ j_* O_Z` is `SheafOfModules.unitToPushforwardObjUnit` applied to
`RingedSpaceModuleAdjunction.structureSheafHom`, the comparison map `j^♯` read as the datum that
`SheafOfModules.pushforward` consumes.  This is why `U` and `Z` are schemes in a single universe:
that pushforward is only available for `RingedSpace.{u, u}`.

Stacks tag 063J also asserts that the four conditions do not depend on the choice of `U`.  That
independence is not proved here but in
`StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence`, for parts (2), (3) and (4) and
with the ideal sheaf on `U` spelled as the restriction of `definingIdealOfHom i` to `U`.  What is
proved here is the weaker statement that each condition may be read off any ideal subsheaf of
`O_{i.coborderRange}` that has been identified with `definingIdeal i`.

## References

* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.21.3 (Tag 063E)](https://stacks.math.columbia.edu/tag/063E)
* [SGA 6, Exposé VII, Definition 1.4]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

section Kernel

/-- **The sectionwise kernel of a morphism of sheaves of modules**, as an embedded submodule of
its source: over each object of the site it is the kernel of the component of the morphism.  The
family is stable under restriction by naturality, and is local because the target is a sheaf, so
a section all of whose restrictions along a covering vanish already vanishes. -/
def kernelSubmodule {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N) : M.Submodule where
  toSubmodule :=
    { obj U := LinearMap.ker (f.val.app U).hom
      map {U V} g := by
        intro s hs
        change f.val.app V (M.val.map g s) = 0
        rw [PresheafOfModules.naturality_apply, show f.val.app U s = 0 from hs]
        exact map_zero _ }
  isSheaf := by
    intro U s hs
    change f.val.app U s = 0
    have hN : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{u}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf)
    refine (hN _ hs).isSeparatedFor.ext fun V g hg => ?_
    change N.val.map g.op (f.val.app U s) = N.val.map g.op 0
    rw [← PresheafOfModules.naturality_apply, map_zero]
    exact hg

/-- A section lies in the sectionwise kernel exactly when the morphism kills it. -/
theorem mem_kernelSubmodule {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (s : M.val.obj U) : s ∈ (kernelSubmodule f).obj U ↔ f.val.app U s = 0 :=
  Iff.rfl

end Kernel

section DefiningIdeal

/-- **The defining ideal sheaf of a morphism of schemes.** The ideal subsheaf of `O_U` of those
sections that die in the pushforward `j_* O_Z`.  For a closed immersion `j : Z ⟶ U` this is the
ideal sheaf cutting out `Z`, which is the ideal sheaf Stacks tag 063J refers to. -/
noncomputable abbrev definingIdealOfHom {Z U : Scheme.{u}} (j : Z ⟶ U) :
    (structureSheafModule U.toLocallyRingedSpace.toRingedSpace).Submodule :=
  kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom))

/-- A section lies in the defining ideal sheaf of `j` exactly when its image in the pushforward
structure sheaf vanishes. -/
theorem mem_definingIdealOfHom {Z U : Scheme.{u}} (j : Z ⟶ U)
    (V : Opens U.toLocallyRingedSpace.toRingedSpace)
    (s : (structureSheafModule U.toLocallyRingedSpace.toRingedSpace).val.obj (op V)) :
    s ∈ (definingIdealOfHom j).obj (op V) ↔
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom j.toLRSHom.toShHom)).val.app (op V) s = 0 :=
  Iff.rfl

/-- That sectionwise kernel description determines the defining ideal sheaf of `j`: any ideal
subsheaf of `O_U` whose sections are cut out by vanishing in `j_* O_Z` equals it. -/
theorem eq_definingIdealOfHom_of_mem_iff {Z U : Scheme.{u}} (j : Z ⟶ U)
    (J : (structureSheafModule U.toLocallyRingedSpace.toRingedSpace).Submodule)
    (h : ∀ (V : Opens U.toLocallyRingedSpace.toRingedSpace)
      (s : (structureSheafModule U.toLocallyRingedSpace.toRingedSpace).val.obj (op V)),
      s ∈ J.obj (op V) ↔
        (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom j.toLRSHom.toShHom)).val.app (op V) s = 0) :
    J = definingIdealOfHom j := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V =>
    Submodule.ext fun s => ?_)
  exact (h V.unop s).trans (mem_definingIdealOfHom j V.unop s).symm

/-- **The defining ideal sheaf of an immersion.** An immersion `i : Z ⟶ X` factors as the closed
immersion `i.liftCoborder` into the open subscheme `i.coborderRange`; this is the defining ideal
sheaf of that closed factor, an ideal subsheaf of `O_{i.coborderRange}`. -/
noncomputable abbrev definingIdeal {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    (structureSheafModule
      i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace).Submodule :=
  definingIdealOfHom i.liftCoborder

/-- A section lies in the defining ideal sheaf of an immersion exactly when its image in the
pushforward structure sheaf of the canonical closed factor vanishes. -/
theorem mem_definingIdeal {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : Opens i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace)
    (s : (structureSheafModule
      i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace).val.obj (op U)) :
    s ∈ (definingIdeal i).obj (op U) ↔
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom)).val.app (op U) s = 0 :=
  Iff.rfl

/-- The sectionwise kernel description determines the defining ideal sheaf of an immersion. -/
theorem eq_definingIdeal_of_mem_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (J : (structureSheafModule
      i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace).Submodule)
    (h : ∀ (U : Opens i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace)
      (s : (structureSheafModule
        i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace).val.obj (op U)),
      s ∈ J.obj (op U) ↔
        (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.liftCoborder.toLRSHom.toShHom)).val.app (op U) s = 0) :
    J = definingIdeal i :=
  eq_definingIdealOfHom_of_mem_iff i.liftCoborder J h

end DefiningIdeal

section CanonicalOpen

/-- **The canonical open is the largest admissible one.** If the immersion `i : Z ⟶ X` factors
through an open `U ⊆ X` as a closed immersion `j : Z ⟶ U`, then `U ≤ i.coborderRange`.

Concretely: `i.coborderRange` is the complement of `closure (range i) \ range i`, and a point of
`U` in the closure of `range i` already lies in `range i`, because `U.ι` is an open map, so
pulling the closure back to `U` gives the closure of `range j`, which is closed. This is why the
four conditions of Stacks tag 063J may be stated on `i.coborderRange` with no loss: every
admissible open is an open subset of it. -/
theorem le_coborderRange_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (j : Z ⟶ U.toScheme) [IsClosedImmersion j] (hij : j ≫ U.ι = i) :
    U ≤ i.coborderRange := by
  have hrange : Set.range i.base = U.ι.base '' Set.range j.base := by
    rw [← hij, Scheme.Hom.comp_base]
    simp [Set.range_comp]
  have hpre : U.ι.base ⁻¹' closure (Set.range i.base) = Set.range j.base := by
    rw [(U.ι.isOpenEmbedding.isOpenMap).preimage_closure_eq_closure_preimage
      U.ι.base.hom.continuous, hrange,
      Set.preimage_image_eq _ U.ι.isOpenEmbedding.injective,
      j.isClosedEmbedding.isClosed_range.closure_eq]
  intro x hx
  change x ∈ coborder (Set.range i.base)
  rw [mem_coborder_iff_imp]
  intro hxc
  obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι.base := by rwa [U.range_ι]
  exact hrange ▸ Set.mem_image_of_mem _ (hpre ▸ hxc)

end CanonicalOpen

section Immersions

variable {Z X : Scheme.{u}}

/-- **Stacks tag 063J, part (1).** The immersion `i` is regular when the defining ideal sheaf of
its canonical closed factor is a regular ideal sheaf. -/
@[stacks 063J "part (1): regular immersion"]
def IsRegularImmersion (i : Z ⟶ X) [IsImmersion i] : Prop :=
  IsRegularIdealSheaf i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace
    (definingIdeal i)

/-- **Stacks tag 063J, part (2).** The immersion `i` is Koszul-regular when the defining ideal
sheaf of its canonical closed factor is a Koszul-regular ideal sheaf. -/
@[stacks 063J "part (2): Koszul-regular immersion", sga "6 VII 1.4" "regular immersion"]
def IsKoszulRegularImmersion (i : Z ⟶ X) [IsImmersion i] : Prop :=
  IsKoszulRegularIdealSheaf i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace
    (definingIdeal i)

/-- **Stacks tag 063J, part (3).** The immersion `i` is `H₁`-regular when the defining ideal
sheaf of its canonical closed factor is an `H₁`-regular ideal sheaf. -/
@[stacks 063J "part (3): H₁-regular immersion"]
def IsH1RegularImmersion (i : Z ⟶ X) [IsImmersion i] : Prop :=
  IsH1RegularIdealSheaf i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace
    (definingIdeal i)

/-- **Stacks tag 063J, part (4).** The immersion `i` is quasi-regular when the defining ideal
sheaf of its canonical closed factor is a quasi-regular ideal sheaf. -/
@[stacks 063J "part (4): quasi-regular immersion", ega "IV 16.9.2" "quasi-regular"]
def IsQuasiRegularImmersion (i : Z ⟶ X) [IsImmersion i] : Prop :=
  IsQuasiRegularIdealSheaf i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace
    (definingIdeal i)

variable (i : Z ⟶ X) [IsImmersion i]
  (J : (structureSheafModule
    i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace).Submodule)
  (hJ : J = definingIdeal i)

include hJ

/-- Regularity of an immersion may be read off any ideal subsheaf of the structure sheaf of the
canonical open that has been identified with the defining ideal sheaf. -/
theorem isRegularImmersion_iff :
    IsRegularImmersion i ↔
      IsRegularIdealSheaf
        i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace J := by
  subst hJ
  rfl

/-- Koszul-regularity of an immersion may be read off any identified defining ideal sheaf. -/
theorem isKoszulRegularImmersion_iff :
    IsKoszulRegularImmersion i ↔
      IsKoszulRegularIdealSheaf
        i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace J := by
  subst hJ
  rfl

/-- `H₁`-regularity of an immersion may be read off any identified defining ideal sheaf. -/
theorem isH1RegularImmersion_iff :
    IsH1RegularImmersion i ↔
      IsH1RegularIdealSheaf
        i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace J := by
  subst hJ
  rfl

/-- Quasi-regularity of an immersion may be read off any identified defining ideal sheaf. -/
theorem isQuasiRegularImmersion_iff :
    IsQuasiRegularImmersion i ↔
      IsQuasiRegularIdealSheaf
        i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace J := by
  subst hJ
  rfl

end Immersions

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
