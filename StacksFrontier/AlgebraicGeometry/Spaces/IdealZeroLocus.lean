module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# The zero locus of a sheaf of ideals on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site, that is, a sheaf submodule of the unit
module of the structure sheaf.  This file defines the point set `|V(ℐ)|` of the closed subspace
cut out by `ℐ`, shows it is closed, and uses it to state the third condition of Stacks 0855.

The point set is defined directly, as the complement of the *unit locus*: the set of points of
`X` lying in the image of an étale chart `V` on which `ℐ` is the whole structure sheaf,
`ℐ(V) = 𝒪_X(V)`.  For a sheaf of ideals on a scheme this is the familiar description
`V(ℐ) = {x ∣ ℐ_x ≠ 𝒪_x}`, since the Zariski opens form a basis and `ℐ_x = 𝒪_x` exactly when
`1 ∈ ℐ(U)` for some open `U ∋ x`; on the small étale site of an algebraic space the étale charts
play the part of the basis, and their images are open by clause (3) of Stacks 03BX.

The *closed subspace* `V(ℐ)` itself is not constructed here, and nothing below asserts that the
point set defined here is the point set of a closed subspace.  Producing the closed subspace from
`ℐ` is the surjectivity direction of Stacks 03MB, which is unavailable; see the section "What is
not proved" of `StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection`.  The whole
point of taking the point set as the primitive notion is that it needs none of that: the
statement of Stacks 0855(3) only ever refers to `|V(ℐ)|`.

## Main definitions

* `AlgebraicGeometry.Space.idealUnitLocus` is the open set of points of `X` at which the sheaf of
  ideals is the whole structure sheaf, and `AlgebraicGeometry.Space.idealZeroLocus` is its
  complement `|V(ℐ)|`.
* `AlgebraicGeometry.Space.IsFiniteTypeQuasicoherentIdeal` is the property of a sheaf of ideals
  on `X` of being quasi-coherent and of finite type, in the senses of Stacks 03DL(6) and
  03DL(5).
* `AlgebraicGeometry.Space.HasFiniteTypeQuasicoherentIdealZeroLocus` is condition (3) of
  Stacks 0855: the complement of the point set of an open subspace is the zero locus of some
  finite type quasi-coherent sheaf of ideals.

## Main results

* `AlgebraicGeometry.Space.isOpen_idealUnitLocus` and
  `AlgebraicGeometry.Space.isClosed_idealZeroLocus`: the unit locus is open and the zero locus is
  closed.
* `AlgebraicGeometry.Space.mem_idealUnitLocus_iff_exists_over` and
  `AlgebraicGeometry.Space.mem_idealZeroLocus_iff_forall_over`: **both loci are read on a chart
  by the charts over it.** This is the form in which they are tested chart by chart, and it needs
  no comparison between the small étale site of `X` and the Zariski site of a chart.
* `AlgebraicGeometry.Space.idealZeroLocus_antitone`: a larger sheaf of ideals has a smaller zero
  locus.
* `AlgebraicGeometry.Space.idealZeroLocus_top`: the zero locus of `𝒪_X` is empty.
* `SheafOfModules.Submodule.top_obj`: the sections of the top sheaf submodule are everything, and
  `SheafOfModules.Submodule.unit_obj_eq_top_of_map`: a sheaf of ideals which is the whole
  structure sheaf on an object is so on every object below it.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite` and finite type is
`SheafOfModules.IsFiniteTypeOnSite`, the forms of Stacks 03DL(6) and 03DL(5) which need no
sheafification instance; they are applied to the sheaf of modules
`SheafOfModules.Submodule.toSheafOfModules` associated with the sheaf of ideals.  Before this
file no sheaf of ideals on an algebraic space had been asserted quasi-coherent at all, not even
hypothetically: the only ideal sheaf in the library is
`AlgebraicGeometry.Space.definingIdealSheaf`, which lands in the sheaf submodules of `𝒪_X` and
whose quasi-coherence is explicitly not claimed.

A sheaf of ideals is recorded as a `SheafOfModules.Submodule` of
`SheafOfModules.unit (structureRingSheaf B S hS X)` rather than as an `𝒪_X`-module with a
monomorphism into `𝒪_X`, because that is the form `definingIdealSheaf` already takes and because
the condition `ℐ(V) = 𝒪_X(V)` defining the unit locus is then literally an equality of
submodules, needing no comparison of two subobjects.

Openness of the unit locus is clause (3) of Stacks 03BX in the form
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale`: the structure morphism of an
étale chart is presheaf-étale by definition of the small étale site, hence open on points, so the
unit locus is a union of open ranges.  This is the same argument as for
`AlgebraicGeometry.Space.isOpen_zeroImages`, the difference being that the condition selecting
the charts is `ℐ(V) = 𝒪_X(V)` rather than the vanishing of a prescribed section, and that the
union is taken in the point set of `X` itself rather than in that of a fixed chart.

The two chart criteria are what makes the point-set definition workable: the chart witnessing
membership in the unit locus can be replaced by its fibre product with a prescribed chart `V`,
which is again an étale chart of `X` because the structure morphism of a chart is relatively
representable and étale after every represented base change, and a point of each factor with the
same image in `X` lifts to the fibre product by
`AlgebraicGeometry.Space.exists_points_of_isPullback`. The sheaf of ideals stays the whole
structure sheaf after restriction because restriction carries `1` to `1`; that is
`SheafOfModules.Submodule.unit_obj_eq_top_of_map`, stated for an arbitrary site.

`idealZeroLocus_top` is where the atlas enters: every point of an algebraic space lies in the
image of an étale chart, namely of the atlas of
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, whose structure morphism is surjective on
points by `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`.  The atlas is
itself an object of the small étale site, since `exists_atlas` already asserts the presheaf-étale
property that membership in the site requires.

## References

* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules.Submodule

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}

/-- The family of full submodules of a sheaf of modules is a sheaf submodule: membership is
vacuously local because every section belongs to it. -/
private def topAux (M : SheafOfModules.{u} R) : M.Submodule where
  toSubmodule := ⊤
  isSheaf _ _ := by simp

/-- The sections of the top sheaf submodule of a sheaf of modules are the whole module: the
family of full submodules is itself a sheaf submodule, and is therefore below the top one. -/
theorem top_obj (X : Cᵒᵖ) : (⊤ : M.Submodule).obj X = ⊤ := by
  refine top_le_iff.1 ?_
  have h := PresheafOfModules.Submodule.le_iff.1
    (SheafOfModules.Submodule.le_iff.1 (le_top (a := topAux M))) X
  rwa [show (topAux M).obj X = ⊤ from PresheafOfModules.Submodule.top_obj X] at h

/-- **A sheaf of ideals which is the whole structure sheaf on an object is the whole structure
sheaf on every object below it.** Restriction carries `1` to `1`, and every section of the unit
module is a multiple of `1`. -/
theorem unit_obj_eq_top_of_map (I : (SheafOfModules.unit R).Submodule) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : I.obj X = ⊤) : I.obj Y = ⊤ := by
  refine eq_top_iff.2 fun s _ ↦ ?_
  have h1 : SheafOfModules.unitOf (1 : ToType (R.obj.obj X)) ∈ I.obj X :=
    h ▸ _root_.Submodule.mem_top
  have h2 : SheafOfModules.unitOf (1 : ToType (R.obj.obj Y)) ∈ I.obj Y := by
    have hm := I.map_mem f h1
    rwa [show ((SheafOfModules.unit R).val.map f)
        (SheafOfModules.unitOf (1 : ToType (R.obj.obj X))) =
        SheafOfModules.unitOf (1 : ToType (R.obj.obj Y)) from
      PresheafOfModules.unit_map_one R.obj f] at hm
  have h3 := _root_.Submodule.smul_mem (I.obj Y) (SheafOfModules.unitVal s) h2
  rwa [show SheafOfModules.unitVal s • SheafOfModules.unitOf (1 : ToType (R.obj.obj Y)) = s from
    mul_one (SheafOfModules.unitVal s)] at h3

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### The zero locus of a sheaf of ideals -/

/-- The sieve on an étale chart of `X` consisting of the charts over it on which `ℐ` is the
whole structure sheaf. -/
def unitSieve (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (P : SmallEtale B S hS X.1) : Sieve P where
  arrows Y _ := I.obj (op Y) = ⊤
  downward_closed hg k := SheafOfModules.Submodule.unit_obj_eq_top_of_map I k.op hg

/-- The **unit locus** of a sheaf of ideals `ℐ ⊆ 𝒪_X` on an algebraic space: the set of points of
`X` lying in the image of an étale chart `V` on which `ℐ` is the whole structure sheaf.  It is the
complement of `AlgebraicGeometry.Space.idealZeroLocus`, and it is open. -/
def idealUnitLocus (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    Set (points B S hS X.1) :=
  {x | ∃ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ ∧
    x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom)}

/-- A point lies in the unit locus exactly when some étale chart on which the sheaf of ideals is
the whole structure sheaf has it in its image. -/
theorem mem_idealUnitLocus_iff (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (x : points B S hS X.1) :
    x ∈ idealUnitLocus B S hS X I ↔
      ∃ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom) :=
  Iff.rfl

/-- **The unit locus of a sheaf of ideals is open.** It is the union, over the étale charts on
which the sheaf of ideals is the whole structure sheaf, of their images, and the image of an étale
chart is open by clause (3) of Stacks 03BX. -/
theorem isOpen_idealUnitLocus (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    IsOpen (idealUnitLocus B S hS X I) := by
  have hrw : idealUnitLocus B S hS X I =
      ⋃ V : SmallEtale B S hS X.1,
        {x | I.obj (op V) = ⊤ ∧ x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom)} := by
    ext x
    simp only [mem_idealUnitLocus_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hrw]
  refine isOpen_iUnion fun V ↦ ?_
  by_cases hV : I.obj (op V) = ⊤
  · simp only [hV, true_and]
    exact (isOpenMap_pointsMap_of_presheafEtale B S hS V.1.hom V.property).isOpen_range
  · simp only [hV, false_and, Set.ofPred_false]
    exact isOpen_empty

/-- **The unit locus is read on a chart by the charts over it.** A point of an étale chart `V` of
`X` maps into the unit locus of a sheaf of ideals exactly when it lies in the image of an étale
chart *over* `V` on which the sheaf of ideals is the whole structure sheaf.

The chart witnessing membership can be moved over `V` by replacing it with its fibre product with
`V`, which is again an étale chart of `X`; a point of each factor with the same image in `X`
lifts to the fibre product by `AlgebraicGeometry.Space.exists_points_of_isPullback`, and the
sheaf of ideals stays the whole structure sheaf under restriction. -/
theorem mem_idealUnitLocus_iff_exists_over (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (V : SmallEtale B S hS X.1)
    (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom y ∈
        idealUnitLocus B S hS X I ↔
      ∃ (W : SmallEtale B S hS X.1) (g : W ⟶ V), I.obj (op W) = ⊤ ∧
        y ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map g))) := by
  constructor
  · rintro ⟨V', hV', y', hy'⟩
    have hrep : yoneda.relativelyRepresentable V'.1.hom := V'.property.rep
    have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd V.1.hom)) :=
      V'.property.property V.1.hom (hrep.fst V.1.hom) (hrep.snd V.1.hom)
        (hrep.isPullback V.1.hom)
    have hsq : IsPullback (yoneda.map (hrep.fst' V.1.hom)) (yoneda.map (hrep.snd V.1.hom))
        V'.1.hom V.1.hom := hrep.isPullback' V.1.hom
    let W : SmallEtale B S hS X.1 :=
      ⟨CostructuredArrow.mk (yoneda.map (hrep.snd V.1.hom) ≫ V.1.hom),
        etale_comp_of_scheme B S hS (hrep.snd V.1.hom) V.1.hom hqEtale V.property⟩
    refine ⟨W, ObjectProperty.homMk (CostructuredArrow.homMk (hrep.snd V.1.hom) rfl),
      SheafOfModules.Submodule.unit_obj_eq_top_of_map I
        (ObjectProperty.homMk (CostructuredArrow.homMk (hrep.fst' V.1.hom) hsq.w) : W ⟶ V').op hV',
      ?_⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS hsq y' y hy'
    exact ⟨w, hw⟩
  · rintro ⟨W, g, hW, z, hz⟩
    refine ⟨W, hW, z, ?_⟩
    rw [← hz, ← pointsMap_comp_apply]
    exact congrArg (fun α ↦ pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) α z)
      (CostructuredArrow.w g.hom).symm

/-- The point set `|V(ℐ)|` of the closed subspace cut out by a sheaf of ideals `ℐ ⊆ 𝒪_X` on an
algebraic space: the complement of `AlgebraicGeometry.Space.idealUnitLocus`, that is, the set of
points at which `ℐ` is not the whole structure sheaf.

The closed subspace `V(ℐ)` itself is not constructed; see the module documentation. -/
def idealZeroLocus (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    Set (points B S hS X.1) :=
  (idealUnitLocus B S hS X I)ᶜ

/-- A point lies in the zero locus of a sheaf of ideals exactly when no étale chart whose image
contains it has the sheaf of ideals equal to the whole structure sheaf. -/
theorem mem_idealZeroLocus_iff (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (x : points B S hS X.1) :
    x ∈ idealZeroLocus B S hS X I ↔
      ∀ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ →
        x ∉ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom) := by
  simp only [idealZeroLocus, Set.mem_compl_iff, mem_idealUnitLocus_iff, not_exists, not_and]

/-- **The zero locus is read on a chart by the charts over it.** A point of an étale chart `V` of
`X` maps into the zero locus of a sheaf of ideals exactly when the sheaf of ideals is not the
whole structure sheaf on any chart over `V` whose image contains that point.

This is the contrapositive of
`AlgebraicGeometry.Space.mem_idealUnitLocus_iff_exists_over`, and is the form in which the zero
locus of a sheaf of ideals is tested chart by chart. -/
theorem mem_idealZeroLocus_iff_forall_over (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (V : SmallEtale B S hS X.1)
    (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom y ∈
        idealZeroLocus B S hS X I ↔
      ∀ (W : SmallEtale B S hS X.1) (g : W ⟶ V), I.obj (op W) = ⊤ →
        y ∉ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map g))) := by
  simp only [idealZeroLocus, Set.mem_compl_iff, mem_idealUnitLocus_iff_exists_over, not_exists,
    not_and]

/-- **The zero locus of a sheaf of ideals is closed.** -/
theorem isClosed_idealZeroLocus (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    IsClosed (idealZeroLocus B S hS X I) :=
  (isOpen_idealUnitLocus B S hS X I).isClosed_compl

/-- A larger sheaf of ideals has a larger unit locus. -/
theorem idealUnitLocus_mono (X : AlgebraicSpaces B S hS)
    {I J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule} (hIJ : I ≤ J) :
    idealUnitLocus B S hS X I ⊆ idealUnitLocus B S hS X J := by
  rintro x ⟨V, hV, hx⟩
  exact ⟨V, top_le_iff.1 (hV.ge.trans (hIJ (op V))), hx⟩

/-- A larger sheaf of ideals has a smaller zero locus. -/
theorem idealZeroLocus_antitone (X : AlgebraicSpaces B S hS)
    {I J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule} (hIJ : I ≤ J) :
    idealZeroLocus B S hS X J ⊆ idealZeroLocus B S hS X I :=
  Set.compl_subset_compl.2 (idealUnitLocus_mono B S hS X hIJ)

/-- The unit locus of the structure sheaf itself is everything: every point of an algebraic space
lies in the image of its atlas, which is an étale chart. -/
theorem idealUnitLocus_top (X : AlgebraicSpaces B S hS) :
    idealUnitLocus B S hS X ⊤ = Set.univ := by
  obtain ⟨U, a, haS, haE⟩ := X.2.exists_atlas
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U a).1 haS
  refine Set.eq_univ_of_forall fun x ↦ ?_
  exact ⟨⟨CostructuredArrow.mk a, haE⟩, SheafOfModules.Submodule.top_obj _, hsurj x⟩

/-- **The zero locus of the structure sheaf is empty.** This is the side of the degenerate case
of Stacks 0855(3) — the open subspace being the whole space — which concerns the zero locus; that
`𝒪_X` is itself quasi-coherent and of finite type is *not* proved here, so the degenerate case of
`AlgebraicGeometry.Space.HasFiniteTypeQuasicoherentIdealZeroLocus` does not follow. -/
theorem idealZeroLocus_top (X : AlgebraicSpaces B S hS) :
    idealZeroLocus B S hS X ⊤ = ∅ := by
  rw [idealZeroLocus, idealUnitLocus_top, Set.compl_univ]

/-! ### Condition (3) of Stacks 0855 -/

/-- A sheaf of ideals `ℐ ⊆ 𝒪_X` on an algebraic space is a **finite type quasi-coherent sheaf of
ideals** when the associated `𝒪_X`-module is quasi-coherent and of finite type, in the senses of
Stacks 03DL(6) and 03DL(5). -/
def IsFiniteTypeQuasicoherentIdeal (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) : Prop :=
  I.toSheafOfModules.IsQuasicoherentOnSite ∧ I.toSheafOfModules.IsFiniteTypeOnSite

/-- **Condition (3) of Stacks 0855.** A subfunctor `U` of an algebraic space `X` has the property
that the complement of its point set in `|X|` is the zero locus of a finite type quasi-coherent
sheaf of ideals `ℐ ⊆ 𝒪_X`.

The zero locus is `AlgebraicGeometry.Space.idealZeroLocus`, the point set of `V(ℐ)` taken as a
primitive; see the module documentation for why the closed subspace `V(ℐ)` is not formed. -/
def HasFiniteTypeQuasicoherentIdealZeroLocus (X : AlgebraicSpaces B S hS)
    (U : Subfunctor X.1) : Prop :=
  ∃ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
    IsFiniteTypeQuasicoherentIdeal B S hS X I ∧
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ = idealZeroLocus B S hS X I

end AlgebraicGeometry.Space

end
