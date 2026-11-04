module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobal
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalGeneration

/-!
# The sheaf of ideals annihilates the composition-product algebra of a global resolution

Let `Y` be a ringed space, `𝓘 ⊆ O_Y` a Koszul-regular sheaf of ideals and `Q` a K-injective
complex of `O_Y`-modules presenting the quotient `O_Y/𝓘`.  The descent of the
composition-product algebra of `Q` along the quotient map exists exactly because `𝓘` annihilates
every homogeneous piece of that algebra, and this file proves that it does.

The statement is **not** unconditional in `Q`: it uses the presentation `e`, and the morphism `Φ`
whose cokernel the resolution presents, through the comparison of models over an open.  What
makes it provable is that annihilation of a section of a sheaf is local on the space: over the
open of a Koszul presentation of `𝓘` the comparison of the two models identifies the pieces of
the composition-product algebra of `Q` with those of the Koszul algebra, where the annihilation
is `Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`, and the opens carrying a
Koszul presentation cover `Y`.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_globalHomologyPiece_eq_zero_of_le`: the
  annihilation over an open contained in the open of a Koszul presentation.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_globalHomologyPiece_eq_zero`: **the
  hypothesis `hAglob` of the gluing of [Stacks, Tag 0BQY]** — the annihilation over every open of
  `Y`, for the quotient map by a Koszul-regular sheaf of ideals.

## Implementation notes

**Where the restriction to an open subspace is crossed.** The annihilation available over a
member `U` of the cover is stated on the site `Opens ↥U` of the open subspace, so its reading at
an object is about the sections of the piece over the *image* in `Y` of an open of `↥U`.  Over an
open `W ⊆ U` of `Y` that image is `W` again, but only after an equality of opens, not
definitionally; `smul_globalHomologyPiece_eq_zero_of_eq_open` is the one place that equality is
substituted, and everything downstream of it is about opens of `Y`.

**Why the slice site needs no crossing at all.** The sections of the restriction to `Opens Y / U`
of a sheaf of graded algebras over a slice object *are* its sections over the underlying open —
`SheafOfModules.GradedAlgebra.smul_over_eq_zero` is proved by applying the global statement — so
nothing here has to move between `Opens Y` and `Opens Y / U`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace
open _root_.SheafOfModules.GradedAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {Y : RingedSpace.{u, u}} (J : (structureSheafModule Y).Submodule)
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}]
  (Q : CochainComplex (_root_.SheafOfModules.{u}
    (structureSheafRing Y)) ℤ) (hQ : Q.IsKInjective)
  (e : DerivedCategory.Q.obj
      ((single (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ) 0).obj (cokernel J.ι)) ≅
    DerivedCategory.Q.obj Q)

omit [∀ V : Opens Y.carrier,
    HasSheafify ((Opens.grothendieckTopology Y.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    ((Opens.grothendieckTopology Y.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasSheafify (Opens.grothendieckTopology ↥V) AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier,
    (Opens.grothendieckTopology ↥V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y.carrier, HasWeakSheafify (Opens.grothendieckTopology ↥V) CommRingCat.{u}]
  [∀ V : Opens Y.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over V) CommRingCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **Annihilation of a homogeneous piece over an open is carried along an equality of opens.**
The one place the image in `Y` of an open of an open subspace is identified with that open. -/
theorem smul_globalHomologyPiece_eq_zero_of_eq_open (n : ℤ) {A W : Opens Y.carrier}
    (hAW : A = W)
    (h : ∀ b : (structureSheafRing Y).obj.obj (op A), b ∈ J.obj (op A) →
      ∀ m : ((globalHomologyGradedAlgebra Q).piece n).val.obj (op A), b • m = 0)
    (b : (structureSheafRing Y).obj.obj (op W)) (hb : b ∈ J.obj (op W))
    (m : ((globalHomologyGradedAlgebra Q).piece n).val.obj (op W)) : b • m = 0 := by
  subst hAW
  exact h b hb m

include hQ e in
omit [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}] in
/-- **Over an open contained in the open of a Koszul presentation, the sheaf of ideals
annihilates every homogeneous piece of the composition-product algebra of `Q`.**

Over the open of the presentation the chain of presentations identifies the pieces of the
composition-product algebra of `Q` with those of the Koszul algebra of the presentation's own
sequence, where the annihilation is
`Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`; that identification is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_openSubspaceGradedAlgebra_piece_eq_zero`, whose
generation hypothesis is the presentation's own, read on the slice site by
`sectionIdeal_sliceIdealOfSections_eq`.

The statement there is read on the site of the open subspace, so what it annihilates are the
sections over the image in `Y` of an open of `↥U`; `smul_globalHomologyPiece_eq_zero_of_eq_open`
carries that back to an open `W ⊆ U` of `Y`, the image of the preimage of `W` being `W`. -/
theorem smul_globalHomologyPiece_eq_zero_of_le (d : KoszulPresentation Y J) (n : ℤ)
    (W : Opens Y.carrier) (hW : W ≤ d.U)
    (b : (structureSheafRing Y).obj.obj (op W)) (hb : b ∈ J.obj (op W))
    (m : ((globalHomologyGradedAlgebra Q).piece n).val.obj (op W)) : b • m = 0 := by
  have : QuasiIso (koszulChainData (koszulHomOfSections (openSubspace d.U).sheaf
      fun j => sectionOnRestriction Y d.U (d.f j))).augmentation :=
    quasiIso_koszulChainData_augmentation _
      (quasiIso_koszulAugmentation_restrict Y d.U d.f d.koszulExact)
  refine smul_globalHomologyPiece_eq_zero_of_eq_open J Q n
    (A := (d.U.overEquivalence.inverse.obj
      (d.U.overEquivalence.functor.obj (Over.mk (homOfLE hW)))).left) ?_ ?_ b hb m
  · ext x
    refine ⟨fun hx => ?_, fun hx => ⟨⟨x, hW hx⟩, hx, rfl⟩⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact hy
  · intro c hc t
    refine smul_openSubspaceGradedAlgebra_piece_eq_zero d.U d.f
      (koszulChainData (koszulHomOfSections (openSubspace d.U).sheaf
        fun j => sectionOnRestriction Y d.U (d.f j)))
      J.ι (sectionIdeal_sliceIdealOfSections_eq d.U d.f J d.generated) Q hQ e n
      (op (d.U.overEquivalence.functor.obj (Over.mk (homOfLE hW)))) c ?_ t
    have hker := kerIdeal_quotientRingHom (koszulOpenSubspaceIdeal d.U d.f)
    refine (SheafOfModules.mem_kerIdeal (quotientRingHom (koszulOpenSubspaceIdeal d.U d.f))
      (op (d.U.overEquivalence.functor.obj (Over.mk (homOfLE hW)))) c).mp ?_
    rw [hker]
    refine (sectionIdeal_idealOfHom_koszulHomOfSections d.U d.f
      (op (d.U.overEquivalence.functor.obj (Over.mk (homOfLE hW))))).ge ?_
    rw [sectionIdeal_sliceIdealOfSections_eq_obj d.U d.f J d.generated]
    exact hc

include hQ e in
/-- **The sheaf of ideals annihilates every homogeneous piece of the composition-product algebra
of `Q`, over every open of `Y`.**  This is the hypothesis `hAglob` of the gluing of
[Stacks, Tag 0BQY], for the quotient map by a Koszul-regular sheaf of ideals.

Annihilation of a section of a sheaf of modules is local on the space
(`Stacks.SheafOfModules.eq_zero_of_locally_eq_zero`), and the opens contained in the open of some
Koszul presentation form a covering sieve of every open, the presentations covering `Y`
(`iSup_koszulPresentation_eq_top`); over such an open the annihilation is
`smul_globalHomologyPiece_eq_zero_of_le`. -/
theorem smul_globalHomologyPiece_eq_zero (hJ : IsKoszulRegularIdealSheaf Y J) (n : ℤ)
    (W : (Opens Y.carrier)ᵒᵖ)
    (b : (structureSheafRing Y).obj.obj W)
    (hb : b ∈ RingHom.ker ((quotientRingHom J).hom.app W).hom)
    (m : ((globalHomologyGradedAlgebra Q).piece n).val.obj W) : b • m = 0 := by
  have hbJ : b ∈ J.obj W := by
    have h := (SheafOfModules.mem_kerIdeal (quotientRingHom J) W b).mpr hb
    rwa [kerIdeal_quotientRingHom J] at h
  refine eq_zero_of_locally_eq_zero (b • m)
    (S := { arrows := fun V _ => ∃ d : KoszulPresentation Y J, V ≤ d.U
            downward_closed := fun {_ _ _} hd g => hd.imp fun _ h => le_trans (leOfHom g) h })
    ((Opens.mem_grothendieckTopology _).mpr fun y hy => ?_) (fun {V} g hg => ?_)
  · obtain ⟨d, hyd⟩ :=
      Opens.mem_iSup.mp ((iSup_koszulPresentation_eq_top J hJ).ge (Opens.mem_top y))
    exact ⟨W.unop ⊓ d.U, homOfLE inf_le_left, ⟨d, inf_le_right⟩, ⟨hy, hyd⟩⟩
  · obtain ⟨d, hVd⟩ := hg
    rw [PresheafOfModules.map_smul]
    exact smul_globalHomologyPiece_eq_zero_of_le J Q hQ e d n V hVd _
      (J.toSubmodule.map_mem g.op hbJ) _

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
