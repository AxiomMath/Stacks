module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFlatDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSupportDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The direct image of the structure sheaf along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `g : X ⟶ T` be a morphism of algebraic spaces.  This file reads the two
properties of the `𝒪_X`-module `i_*𝒪_Z` that a closed subspace of `X` is meant to record off
the geometry of `Z`:

* `i_*𝒪_Z` is flat over `T` at the geometric points of `X` in the image of `i` exactly when the
  composite `Z ⟶ T` is a flat morphism;
* the image of `|Z|` is contained in the support of `i_*𝒪_Z`.

Both rest on the identification of the geometric stalk of a structure sheaf with an étale local
ring, `AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`, which turns a statement about
the `𝒪_Z`-module `𝒪_Z` into a statement about the morphism `Z ⟶ T` itself: flatness of the
stalk becomes flatness of the homomorphism of étale local rings of Stacks 04NG, which is
flatness of the morphism at that point by Stacks 04NG, and nonvanishing of the stalk becomes
the nontriviality of a local ring, so that `Supp(𝒪_Z) = |Z|`.

The direct image is `AlgebraicGeometry.Space.chartDirectImage`; see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_structureSheafModule_iff`: flatness of
  `𝒪_X` over `Y` at a geometric point, in the sense of Stacks 05VU(2), is flatness of the
  morphism at that point in the sense of Stacks 03ML(2).
* `AlgebraicGeometry.Space.isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule`:
  **a morphism of algebraic spaces is flat exactly when its structure sheaf is flat over the
  target at every geometric point.**
* `AlgebraicGeometry.Space.isFlat_comp_iff_isFlatOverAtGeometricPoint_chartDirectImage`:
  **`Z ⟶ T` is flat exactly when `i_*𝒪_Z` is flat over `T` at every geometric point of `X` in
  the image of `i`.**  No hypothesis beyond the closed immersion.
* `AlgebraicGeometry.Space.isFlat_comp_of_isFlatOver_chartDirectImage`: if `i_*𝒪_Z` is flat
  over `T` in the sense of Stacks 05VV, then `Z ⟶ T` is a flat morphism.
* `AlgebraicGeometry.Space.range_subset_supportOfSheaf_chartDirectImage_structureSheafModule`:
  **`|i|(|Z|) ⊆ Supp(i_*𝒪_Z)`.**

## Implementation notes

The pointwise flatness equivalence is unconditional: the comparison of stalks underlying
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_chartDirectImage_iff` needs no
quasi-coherence, and neither does
`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`.  Quasi-coherence enters only in
the two results that speak about `AlgebraicGeometry.Space.IsFlatOver` and about the support,
where it is the hypothesis of Stacks 05VU and of Stacks 07TZ respectively.  For `𝒪_Z` itself it
is automatic (`SheafOfModules.isQuasicoherentOnSite_unit`), so the only quasi-coherence hypothesis
is that of the direct image `i_*𝒪_Z`: quasi-coherence of a direct image is Stacks 03M9,
and the closed-immersion case available in this development,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_pushforwardStructureSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceQuotientQuasicoherent.lean`, is stated for
the other direct image (see below).

The comparison of `AlgebraicGeometry.Space.IsFlatAt`, which is a condition on germs in étale
scheme charts, with flatness of the stalk is Stacks 04NG in the form
`AlgebraicGeometry.Space.isFlatAt_iff_etaleLocalRingMap_flat`.  The module structure on the
étale local ring that `RingHom.Flat` uses is the one induced by the ring homomorphism through
`RingHom.toAlgebra`, and the one that `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint` uses
is `Module.compHom` along the same homomorphism; the two are the same scalar multiplication, so
the two flatness statements are interchangeable without a transport.

**The direct image.**  `AlgebraicGeometry.Space.chartDirectImage` is
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, whose sections over an étale chart
`V` of `X` are the sections of the module over the base-changed chart `Z ×_X V`.  It is not
identified in this development with `AlgebraicGeometry.Space.modulePushforward`, the
realization of Stacks 03LU; the comparisons that identification needs are listed in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean`.  So the results
here do not apply verbatim to `AlgebraicGeometry.Space.pushforwardStructureSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean`, which is built from
`AlgebraicGeometry.Space.structureSharp`.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RingedSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flatness of the structure sheaf is flatness of the morphism -/

section StructureSheafFlat

variable {X Y : AlgebraicSpaces B S hS}

/-- **Flatness of the structure sheaf over the target at a geometric point is flatness of the
morphism at that point.**  For a morphism `f : X ⟶ Y` of algebraic spaces and a geometric point
`x̄` of `X`, the `𝒪_X`-module `𝒪_X` is flat over `Y` at `x̄` in the sense of Stacks 05VU(2)
exactly when `f` is flat at the image of `x̄` in the germ sense of Stacks 03ML(2).

The stalk of `𝒪_X` at `x̄` is `𝒪_{X, x̄}`, and the scalars are restricted along the same
homomorphism `𝒪_{Y, ȳ} → 𝒪_{X, x̄}` of Stacks 04NG whose flatness is flatness of `f` at the
point. -/
theorem isFlatOverAtGeometricPoint_structureSheafModule_iff (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1) :
    IsFlatOverAtGeometricPoint B S hS f (structureSheafModule B S hS X) x ↔
      IsFlatAt B S hS f.hom x.image := by
  refine Iff.trans ?_ (isFlatAt_iff_etaleLocalRingMap_flat X.2 Y.2 f.hom x).symm
  set Rt := etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x) with hRt
  set R := etaleLocalRing B S hS X.1 x with hR
  set M := geometricModuleStalk B S hS X x (structureSheafModule B S hS X) with hM
  set γ := etaleLocalRingMap X.2 f.hom x with hγ
  let e : M ≃ₗ[R] R := structureSheafGeometricStalkEquiv B S hS X x
  let _ : Module Rt M := Module.compHom M γ
  let _ : Module Rt R := Module.compHom R γ
  let Ψ : M ≃ₗ[Rt] R :=
    AddEquiv.toLinearEquiv e.toAddEquiv fun c z => map_smul e (γ c) z
  exact Module.Flat.equiv_iff Ψ

/-- **A morphism of algebraic spaces is flat exactly when its structure sheaf is flat over the
target at every geometric point of the source.**  This is the dictionary between flatness of a
morphism, Stacks 03ML(2) at every point, and relative flatness of the `𝒪_X`-module `𝒪_X`,
Stacks 05VU(2) at every geometric point.

Every point of `|X|` is the image of a geometric point by
`AlgebraicGeometry.Space.exists_geometricRepresentative`, and at a geometric point the two
conditions agree. -/
theorem isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule (f : X ⟶ Y) :
    IsFlat B S hS f.hom ↔ ∀ x : GeometricPoint B S hS X.1,
      IsFlatOverAtGeometricPoint B S hS f (structureSheafModule B S hS X) x := by
  refine Iff.trans (isFlat_iff_forall_isFlatAt B S hS f.hom) ⟨fun h x => ?_, fun h pt => ?_⟩
  · exact (isFlatOverAtGeometricPoint_structureSheafModule_iff B S hS f x).2 (h x.image)
  · obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X.1 pt
    subst hxbar
    exact (isFlatOverAtGeometricPoint_structureSheafModule_iff B S hS f xbar).1 (h xbar)

end StructureSheafFlat

/-! ### Flatness of the direct image of the structure sheaf -/

section DirectImage

variable {Z X T : AlgebraicSpaces B S hS}

/-- **The direct image of the structure sheaf along a closed immersion is flat over `T` at the
image of a geometric point exactly when the composite is flat there.**  For a closed immersion
`i : Z ⟶ X` and a morphism `g : X ⟶ T`, and for a geometric point `z̄` of `Z`, the `𝒪_X`-module
`i_*𝒪_Z` is flat over `T` at `i(z̄)` exactly when `i ≫ g` is flat at the image of `z̄`.

The stalk of `i_*𝒪_Z` at `i(z̄)` is the stalk of `𝒪_Z` at `z̄`, which is `𝒪_{Z, z̄}`.  No
hypothesis beyond the closed immersion. -/
theorem isFlatOverAtGeometricPoint_chartDirectImage_structureSheafModule_iff (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T) (zbar : GeometricPoint B S hS Z.1) :
    IsFlatOverAtGeometricPoint B S hS g
        (chartDirectImage B S hS i hi (structureSheafModule B S hS Z))
        (geometricPointMap i.hom zbar) ↔
      IsFlatAt B S hS (i ≫ g).hom zbar.image :=
  (isFlatOverAtGeometricPoint_chartDirectImage_iff B S hS i hi g
      (structureSheafModule B S hS Z) zbar).trans
    (isFlatOverAtGeometricPoint_structureSheafModule_iff B S hS (i ≫ g) zbar)

/-- **The composite `Z ⟶ T` is flat exactly when `i_*𝒪_Z` is flat over `T` at every geometric
point of `X` in the image of the closed immersion.**  This is the dictionary entry which reads
flatness of a closed subspace over a base off the direct image of its structure sheaf.

No hypothesis beyond the closed immersion: the stalk comparison needs none, and neither does
the identification of the stalk of a structure sheaf with an étale local ring. -/
theorem isFlat_comp_iff_isFlatOverAtGeometricPoint_chartDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T) :
    IsFlat B S hS (i ≫ g).hom ↔ ∀ zbar : GeometricPoint B S hS Z.1,
      IsFlatOverAtGeometricPoint B S hS g
        (chartDirectImage B S hS i hi (structureSheafModule B S hS Z))
        (geometricPointMap i.hom zbar) := by
  refine Iff.trans
    (isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule B S hS (i ≫ g))
    (forall_congr' fun zbar => ?_)
  exact ((isFlatOverAtGeometricPoint_chartDirectImage_iff B S hS i hi g
    (structureSheafModule B S hS Z) zbar)).symm

/-- **Flatness of `i_*𝒪_Z` over `T` makes `Z ⟶ T` a flat morphism.**  If the direct image of
the structure sheaf of a closed subspace is flat over `T` in the sense of Stacks 05VV, then the
composite `Z ⟶ T` is flat in the sense of Stacks 03ML.

Stacks 05VV for `i_*𝒪_Z` descends to `𝒪_Z` by
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_chartDirectImage`, and relative flatness of
`𝒪_Z` at every geometric point is flatness of `Z ⟶ T` at every point.

Quasi-coherence of `i_*𝒪_Z` is the hypothesis of Stacks 05VU on the ambient space; for `𝒪_Z`
itself it is automatic. -/
theorem isFlat_comp_of_isFlatOver_chartDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T)
    [(chartDirectImage B S hS i hi (structureSheafModule B S hS Z)).IsQuasicoherentOnSite]
    (h : IsFlatOver B S hS X.2 g.hom
      (chartDirectImage B S hS i hi (structureSheafModule B S hS Z))) :
    IsFlat B S hS (i ≫ g).hom := by
  have h2 : IsFlatOver B S hS Z.2 (i ≫ g).hom (structureSheafModule B S hS Z) :=
    isFlatOver_of_isFlatOver_chartDirectImage B S hS i hi g
      (structureSheafModule B S hS Z) h
  refine (isFlat_comp_iff_isFlatOverAtGeometricPoint_chartDirectImage B S hS i hi g).2
    fun zbar => ?_
  exact isFlatOverAtGeometricPoint_chartDirectImage_of_isFlatOver B S hS i hi g
    (structureSheafModule B S hS Z) h2 zbar

/-! ### The support of the direct image of the structure sheaf -/

/-- **The image of `|Z|` lies in the support of `i_*𝒪_Z`.**  For a closed immersion
`i : Z ⟶ X` of algebraic spaces whose direct image of the structure sheaf is quasi-coherent,
`|i|(|Z|) ⊆ Supp(i_*𝒪_Z)`.

The support of `𝒪_Z` is all of `|Z|`
(`AlgebraicGeometry.Space.supportOfSheaf_structureSheafModule`), and the image of the support
of a module is contained in the support of its direct image.

Quasi-coherence of `i_*𝒪_Z` is the hypothesis of Stacks 07TZ on the ambient space; for `𝒪_Z`
itself it is automatic. -/
theorem range_subset_supportOfSheaf_chartDirectImage_structureSheafModule (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    [(chartDirectImage B S hS i hi (structureSheafModule B S hS Z)).IsQuasicoherentOnSite] :
    Set.range (pointsMap B S hS Z.1 i.hom) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (chartDirectImage B S hS i hi (structureSheafModule B S hS Z))) := by
  refine Set.Subset.trans (le_of_eq ?_)
    (image_supportOfSheaf_subset_supportOfSheaf_chartDirectImage B S hS i hi
      (structureSheafModule B S hS Z))
  refine Eq.trans (Set.image_univ (f := pointsMap B S hS Z.1 i.hom)).symm ?_
  exact congrArg (fun A => pointsMap B S hS Z.1 i.hom '' A)
    (supportOfSheaf_structureSheafModule B S hS Z).symm

/-- **The support of `i_*𝒪_Z` meets the image of `|Z|` exactly in that image.**  The
restatement of
`AlgebraicGeometry.Space.range_subset_supportOfSheaf_chartDirectImage_structureSheafModule` in
the shape of `AlgebraicGeometry.Space.supportOfSheaf_chartDirectImage_inter_range`. -/
theorem supportOfSheaf_chartDirectImage_structureSheafModule_inter_range (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    [(chartDirectImage B S hS i hi (structureSheafModule B S hS Z)).IsQuasicoherentOnSite] :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
          (chartDirectImage B S hS i hi (structureSheafModule B S hS Z))) ∩
        Set.range (pointsMap B S hS Z.1 i.hom) =
      Set.range (pointsMap B S hS Z.1 i.hom) :=
  Set.inter_eq_self_of_subset_right
    (range_subset_supportOfSheaf_chartDirectImage_structureSheafModule B S hS i hi)

end DirectImage

end AlgebraicGeometry.Space

end
