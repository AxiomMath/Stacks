module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFiniteSingularities
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperOverSchemeFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The singular locus of a family of curves and the open locus in the base (Stacks 0DZW)

Stacks 0DZW produces the open substack `Curves⁺ ⊂ Curves` of families of curves whose singular
locus is finite over the base. Its proof: for a family of curves `f : X → S` the locus
`T ⊂ |X|` of points where `f` is not smooth is closed; let `Z ⊂ X` be the reduced induced
closed subspace on it (Stacks 047X); the set of points of `S` over which `Z` is finite is open
(Stacks 0A4Y), and its formation commutes with base change. This file proves all of that, and
the "any/some closed subspace structure" clause of part (1).

## Main definitions

* `AlgebraicGeometry.CurveFamily.nonSmoothLocus`: the singular locus `T ⊂ |X|`.
* `AlgebraicGeometry.CurveFamily.singularSubspace`: the reduced induced closed subspace `Z ⊂ X`
  on it.
* `AlgebraicGeometry.CurveFamily.finiteSingularBaseLocus`: the set of points of `|S|` over which
  the singular locus is finite.

## Main results

* `AlgebraicGeometry.CurveFamily.isClosed_nonSmoothLocus`: the singular locus is closed.
* `AlgebraicGeometry.CurveFamily.isFinite_iff_forall_finite_nonSmoothLocus_fibre`: for *any*
  closed subspace structure `Z` on the singular locus, `Z → S` is finite exactly when the singular
  locus meets every fibre of `|X| → |S|` in a finite set — a condition independent of `Z`.
* `AlgebraicGeometry.CurveFamily.isFiniteNonSmoothLocus_iff_forall_isClosedSubspace` and
  `AlgebraicGeometry.CurveFamily.isFiniteNonSmoothLocus_iff_exists_isClosedSubspace`:
  **Stacks 0DZW**, part (1), condition (b) with "any" and with "some".
* `AlgebraicGeometry.CurveFamily.isOpen_finiteSingularBaseLocus`: the locus in the base is open.
* `AlgebraicGeometry.CurveFamily.preimage_finiteSingularBaseLocus`: its formation commutes with
  arbitrary base change.

The open substack itself and parts (1) and (2) of the source are assembled in
`StacksFrontier/AlgebraicGeometry/Quot/CurvesPlusOpenSubstack.lean`.

## Implementation notes

The locus in the base is defined by finiteness of the fibres of the singular locus, which is the
form in which it does not depend on a closed subspace structure. Openness and base change are read
on a closed subspace structure `Z` through Stacks 0ACZ: since `Z → S` is proper and the base is a
scheme (hence decent, Stacks 0ABT), a fibre of `|Z| → |S|` is finite exactly when `Z → S` is
quasi-finite at each of its points; the quasi-finite locus of `Z` is open (Stacks 0ABM, part (1))
and commutes with base change (Stacks 0ABM, part (2)), and `Z → S` is universally closed. Base
change is computed on the inverse image of the reduced singular locus of the target family, which
is a closed subspace structure — possibly non-reduced — on the singular locus of the source
family; this is where the independence of the closed subspace structure is used.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The singular locus and its reduced structure -/

/-- The singular locus of a family of curves: the set of points of the total space at which the
structure morphism is not smooth. -/
def CurveFamily.nonSmoothLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ X.total.1) :=
  {x | ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x}

/-- The singular locus of a family of curves is closed: the locus of smoothness of a morphism of
algebraic spaces is open, which is Stacks 0DZI read on algebraic spaces. This is the step the
proof of Stacks 0DZW opens with. -/
theorem CurveFamily.isClosed_nonSmoothLocus (X : CurveFamily B hZ) :
    IsClosed (CurveFamily.nonSmoothLocus B hZ X) :=
  (Space.isOpen_setOf_isSmoothAt B integerBase hZ X.total.property X.toBase.hom).isClosed_compl

/-- The singular locus of a family of curves with its reduced induced algebraic space structure,
the closed subspace `Z ⊂ X` of Stacks 047X built on the closed set of non-smooth points. -/
noncomputable def CurveFamily.singularSubspace (X : CurveFamily B hZ) :
    Subfunctor X.total.1 :=
  Space.reducedClosedSubspace B integerBase hZ X.total.1 X.total.property
    (CurveFamily.nonSmoothLocus B hZ X) (CurveFamily.isClosed_nonSmoothLocus B hZ X)

/-- The reduced induced structure on the singular locus is a closed subspace. -/
theorem CurveFamily.isClosedSubspace_singularSubspace (X : CurveFamily B hZ) :
    Space.IsClosedSubspace B integerBase hZ (CurveFamily.singularSubspace B hZ X) :=
  Space.isClosedSubspace_reducedClosedSubspace B integerBase hZ X.total.1 X.total.property _ _

/-- The points of the reduced induced structure on the singular locus are the non-smooth
points. -/
theorem CurveFamily.range_pointsMap_ι_singularSubspace (X : CurveFamily B hZ) :
    Set.range (Space.pointsMap B integerBase hZ
        (CurveFamily.singularSubspace B hZ X).toFunctor
        (CurveFamily.singularSubspace B hZ X).ι) =
      CurveFamily.nonSmoothLocus B hZ X :=
  Space.range_pointsMap_ι_reducedClosedSubspace B integerBase hZ X.total.1 X.total.property _ _

/-- The reduced induced structure on the singular locus is reduced. -/
theorem CurveFamily.hasEtaleLocalProperty_isReduced_singularSubspace (X : CurveFamily B hZ) :
    Space.HasEtaleLocalProperty B integerBase hZ
      (CurveFamily.singularSubspace B hZ X).toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B integerBase hZ X.total.1
    X.total.property _ _

/-- A closed subspace of the total space of a family of curves is proper over the base: it is a
closed immersion into the total space, which is proper by Stacks 04XZ, followed by the structure
morphism of the family, which is proper by definition (Stacks 04XY). -/
theorem CurveFamily.isProper_of_isClosedSubspace (X : CurveFamily B hZ)
    (Z : Subfunctor X.total.1) (hZc : Space.IsClosedSubspace B integerBase hZ Z) :
    Space.IsProper B integerBase hZ (Z.ι ≫ X.toBase.hom) :=
  Space.isProper_comp B integerBase hZ hZc.1 X.total.property (schemeSpace X.base).property _ _
    (Space.isProper_of_isClosedImmersion B integerBase hZ hZc.1 X.total.property _ hZc.2)
    X.proper

/-- The singular locus with its reduced structure is proper over the base. -/
theorem CurveFamily.isProper_singularSubspace_toBase (X : CurveFamily B hZ) :
    Space.IsProper B integerBase hZ
      ((CurveFamily.singularSubspace B hZ X).ι ≫ X.toBase.hom) :=
  CurveFamily.isProper_of_isClosedSubspace B hZ X _
    (CurveFamily.isClosedSubspace_singularSubspace B hZ X)

/-! ### Part (1), condition (b): any/some closed subspace structure -/

/-- **Any closed subspace structure on the singular locus.** For a closed subspace `Z` of the total
space of a family of curves whose set of points is the singular locus, `Z → S` is finite exactly
when the singular locus meets every fibre of `|X| → |S|` in a finite set. The right-hand side does
not mention `Z`, so finiteness of `Z → S` does not depend on the closed subspace structure. -/
theorem CurveFamily.isFinite_iff_forall_finite_nonSmoothLocus_fibre (X : CurveFamily B hZ)
    (Z : Subfunctor X.total.1) (hZc : Space.IsClosedSubspace B integerBase hZ Z)
    (hZs : Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      CurveFamily.nonSmoothLocus B hZ X) :
    Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) ↔
      ∀ y : Space.points B integerBase hZ (schemeSpace X.base).obj,
        {x : Space.points B integerBase hZ X.total.1 |
          x ∈ CurveFamily.nonSmoothLocus B hZ X ∧
            Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x = y}.Finite := by
  have h := Space.isFinite_comp_iff_forall_finite_fibre_of_isClosedSubspace B integerBase hZ
    X.total.property X.toBase.hom X.proper Z hZc
  rwa [hZs] at h

/-- **Stacks 0DZW, part (1)**, the singular locus with its *reduced* structure: the defining
condition of `Curves⁺` is finiteness over the base of the reduced induced structure on the
singular locus. By the uniqueness half of Stacks 047X there is only one reduced closed subspace
with the non-smooth points as its point set, so the existential of
`AlgebraicGeometry.IsFiniteNonSmoothLocus` may be discharged against it. -/
theorem CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_singularSubspace (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      Space.IsFinite B integerBase hZ
        ((CurveFamily.singularSubspace B hZ X).ι ≫ X.toBase.hom) := by
  constructor
  · rintro ⟨W, hWclosed, hWsupport, hWreduced, hWfinite⟩
    obtain rfl := Space.eq_of_isAlgebraicSpaceStructure_isReduced B integerBase hZ X.total.1
      X.total.property (CurveFamily.nonSmoothLocus B hZ X)
      (CurveFamily.isClosed_nonSmoothLocus B hZ X) W ⟨hWclosed, hWsupport⟩ hWreduced
    exact hWfinite
  · exact fun hfinite => ⟨CurveFamily.singularSubspace B hZ X,
      CurveFamily.isClosedSubspace_singularSubspace B hZ X,
      CurveFamily.range_pointsMap_ι_singularSubspace B hZ X,
      CurveFamily.hasEtaleLocalProperty_isReduced_singularSubspace B hZ X, hfinite⟩

/-- A family of curves lies in `Curves⁺` exactly when its singular locus meets every fibre of
`|X| → |S|` in a finite set. Over the spectrum of a field, whose point space is a single point,
this is the condition that `X → Spec(k)` be smooth except at finitely many points. -/
theorem CurveFamily.isFiniteNonSmoothLocus_iff_forall_finite_nonSmoothLocus_fibre
    (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      ∀ y : Space.points B integerBase hZ (schemeSpace X.base).obj,
        {x : Space.points B integerBase hZ X.total.1 |
          x ∈ CurveFamily.nonSmoothLocus B hZ X ∧
            Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x = y}.Finite :=
  (CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_singularSubspace B hZ X).trans
    (CurveFamily.isFinite_iff_forall_finite_nonSmoothLocus_fibre B hZ X _
      (CurveFamily.isClosedSubspace_singularSubspace B hZ X)
      (CurveFamily.range_pointsMap_ι_singularSubspace B hZ X))

/-- A family of curves lies in `Curves⁺` exactly when a given closed subspace structure `Z` on its
singular locus is finite over the base: the condition reads the same for every closed subspace
structure. -/
theorem CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_of_isClosedSubspace
    (X : CurveFamily B hZ) (Z : Subfunctor X.total.1)
    (hZc : Space.IsClosedSubspace B integerBase hZ Z)
    (hZs : Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      CurveFamily.nonSmoothLocus B hZ X) :
    IsFiniteNonSmoothLocus B hZ X ↔ Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) :=
  (CurveFamily.isFiniteNonSmoothLocus_iff_forall_finite_nonSmoothLocus_fibre B hZ X).trans
    (CurveFamily.isFinite_iff_forall_finite_nonSmoothLocus_fibre B hZ X Z hZc hZs).symm

/-- **Stacks 0DZW, part (1), condition (b) with "any".** A family of curves `X → S` lies in
`Curves⁺` exactly when *every* closed subspace `Z ⊂ X` whose set of points is the singular locus
of `X → S` is finite over `S`. -/
@[stacks 0DZW "part (1), condition (b) with 'any': every closed subspace structure on the \
singular locus is finite over the base"]
theorem CurveFamily.isFiniteNonSmoothLocus_iff_forall_isClosedSubspace (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      ∀ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z →
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          CurveFamily.nonSmoothLocus B hZ X →
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) :=
  ⟨fun h Z hZc hZs =>
      (CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_of_isClosedSubspace B hZ X Z hZc hZs).mp h,
    fun h => (CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_singularSubspace B hZ X).mpr
      (h _ (CurveFamily.isClosedSubspace_singularSubspace B hZ X)
        (CurveFamily.range_pointsMap_ι_singularSubspace B hZ X))⟩

/-- **Stacks 0DZW, part (1), condition (b) with "some".** A family of curves `X → S` lies in
`Curves⁺` exactly when *some* closed subspace `Z ⊂ X` whose set of points is the singular locus of
`X → S` is finite over `S`. -/
@[stacks 0DZW "part (1), condition (b) with 'some': some closed subspace structure on the \
singular locus is finite over the base"]
theorem CurveFamily.isFiniteNonSmoothLocus_iff_exists_isClosedSubspace (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      ∃ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z ∧
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          CurveFamily.nonSmoothLocus B hZ X ∧
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) :=
  ⟨fun h => ⟨_, CurveFamily.isClosedSubspace_singularSubspace B hZ X,
      CurveFamily.range_pointsMap_ι_singularSubspace B hZ X,
      (CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_singularSubspace B hZ X).mp h⟩,
    fun ⟨Z, hZc, hZs, hfin⟩ =>
      (CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_of_isClosedSubspace B hZ X Z hZc hZs).mpr
        hfin⟩

/-! ### The locus in the base, its openness and its base change -/

/-- The locus of points of the base of a family of curves over which the singular locus is
finite: those points `s` of `|S|` such that the singular locus meets the fibre over `s` in a finite
set. -/
def CurveFamily.finiteSingularBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  {y | {x : Space.points B integerBase hZ X.total.1 |
    x ∈ CurveFamily.nonSmoothLocus B hZ X ∧
      Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x = y}.Finite}

/-- Membership of the locus in the base, read on any closed subspace structure `Z` on the singular
locus: the singular locus is finite over `s` exactly when `Z → S` is quasi-finite at every point of
`|Z|` over `s` (Stacks 0ACZ). -/
theorem CurveFamily.mem_finiteSingularBaseLocus_iff (X : CurveFamily B hZ)
    (Z : Subfunctor X.total.1) (hZc : Space.IsClosedSubspace B integerBase hZ Z)
    (hZs : Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      CurveFamily.nonSmoothLocus B hZ X)
    (y : Space.points B integerBase hZ (schemeSpace X.base).obj) :
    y ∈ CurveFamily.finiteSingularBaseLocus B hZ X ↔
      ∀ z : Space.points B integerBase hZ Z.toFunctor,
        Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ X.toBase.hom) z = y →
          Space.IsQuasiFiniteAt B integerBase hZ (Z.ι ≫ X.toBase.hom) z := by
  show {x : Space.points B integerBase hZ X.total.1 |
    x ∈ CurveFamily.nonSmoothLocus B hZ X ∧
      Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x = y}.Finite ↔ _
  rw [← hZs, Space.finite_fibre_range_iff_of_isClosedSubspace B integerBase hZ Z hZc]
  exact Space.finite_fibre_iff_forall_isQuasiFiniteAt_of_isProper B integerBase hZ hZc.1 _
    (CurveFamily.isProper_of_isClosedSubspace B hZ X Z hZc) y

/-- **Stacks 0DZW.** The locus of points of the base of a family of curves over which the
singular locus is finite is open.

The set of points of the singular locus `Z` at which `Z → S` is quasi-finite is open by part (1)
of Stacks 0ABM, so its complement is closed; `Z → S` is proper, so the image of that complement,
which is the complement of the locus, is closed. -/
theorem CurveFamily.isOpen_finiteSingularBaseLocus (X : CurveFamily B hZ) :
    IsOpen (CurveFamily.finiteSingularBaseLocus B hZ X) := by
  set Z := CurveFamily.singularSubspace B hZ X
  have hcompl : (CurveFamily.finiteSingularBaseLocus B hZ X)ᶜ =
      Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ X.toBase.hom) ''
        {z : Space.points B integerBase hZ Z.toFunctor |
          Space.IsQuasiFiniteAt B integerBase hZ (Z.ι ≫ X.toBase.hom) z}ᶜ := by
    ext y
    rw [Set.mem_compl_iff, CurveFamily.mem_finiteSingularBaseLocus_iff B hZ X Z
      (CurveFamily.isClosedSubspace_singularSubspace B hZ X)
      (CurveFamily.range_pointsMap_ι_singularSubspace B hZ X)]
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    exact ⟨fun ⟨z, hz, hq⟩ => ⟨z, hq, hz⟩, fun ⟨z, hq, hz⟩ => ⟨z, hz, hq⟩⟩
  rw [← isClosed_compl_iff, hcompl]
  exact Space.isClosed_of_universallyClosed B integerBase hZ (schemeSpace X.base).property _
    (CurveFamily.isProper_singularSubspace_toBase B hZ X).2.2 _
    (Space.isOpen_setOf_isQuasiFiniteAt B integerBase hZ _).isClosed_compl

/-- The singular locus of a family of curves is the inverse image of the singular locus of any
family it maps to: smoothness at a point is compatible with the cartesian square of a morphism of
families (the flat case of Stacks 02V4 at a point). -/
theorem CurveFamily.nonSmoothLocus_eq_preimage {F G : CurveFamily B hZ} (a : F ⟶ G) :
    CurveFamily.nonSmoothLocus B hZ F =
      Space.pointsMap B integerBase hZ F.total.1 a.totalMap.hom ⁻¹'
        CurveFamily.nonSmoothLocus B hZ G := by
  ext x
  exact not_congr (CurveFamily.isSmoothAt_iff_hom B hZ a x)

/-- The inverse image of the reduced singular locus of `G` along the morphism of total spaces of
a morphism of families `F ⟶ G`: a closed subspace of the total space of `F`. -/
theorem CurveFamily.isClosedSubspace_preimage_singularSubspace {F G : CurveFamily B hZ}
    (a : F ⟶ G) :
    Space.IsClosedSubspace B integerBase hZ
      ((CurveFamily.singularSubspace B hZ G).preimage a.totalMap.hom) :=
  Space.isClosedSubspace_preimage B integerBase hZ a.totalMap.hom _ G.total.property
    F.total.property (CurveFamily.isClosedSubspace_singularSubspace B hZ G)

/-- The points of the inverse image of the singular locus of `G` along a morphism of families
`F ⟶ G` are the singular locus of `F`: the inverse image subfunctor is the fibre product, whose
points surject onto the fibre product of point sets (Stacks 03H4). -/
theorem CurveFamily.range_pointsMap_ι_preimage_singularSubspace {F G : CurveFamily B hZ}
    (a : F ⟶ G) :
    Set.range (Space.pointsMap B integerBase hZ
        ((CurveFamily.singularSubspace B hZ G).preimage a.totalMap.hom).toFunctor
        ((CurveFamily.singularSubspace B hZ G).preimage a.totalMap.hom).ι) =
      CurveFamily.nonSmoothLocus B hZ F := by
  set Z := CurveFamily.singularSubspace B hZ G
  have sq := Subfunctor.isPullback_preimage a.totalMap.hom Z
  rw [CurveFamily.nonSmoothLocus_eq_preimage B hZ a,
    ← CurveFamily.range_pointsMap_ι_singularSubspace B hZ G]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, Space.pointsMap_apply_comm B integerBase hZ sq.w w⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ := Space.exists_points_of_isPullback B integerBase hZ sq z x hz
    exact ⟨w, hw⟩

/-- **The locus in the base commutes with arbitrary base change.** For a morphism of families of
curves `F ⟶ G` (a cartesian square over a morphism of base schemes `S' → S`), the locus of `F` in
`S'` is the inverse image of the locus of `G` in `S`.

The inverse image `Z'` of the reduced singular locus `Z` of `G` is a closed subspace structure on
the singular locus of `F`, and `Z' → S'` is the base change of `Z → S`; quasi-finiteness at a point
commutes with base change by part (2) of Stacks 0ABM, and the points of `Z'` over a point of `S'`
surject onto the points of `Z` over its image by Stacks 03H4. -/
theorem CurveFamily.preimage_finiteSingularBaseLocus {F G : CurveFamily B hZ} (a : F ⟶ G) :
    Space.pointsMap B integerBase hZ (schemeSpace F.base).obj (schemeSpaceMap a.baseMap).hom ⁻¹'
        CurveFamily.finiteSingularBaseLocus B hZ G =
      CurveFamily.finiteSingularBaseLocus B hZ F := by
  set Z := CurveFamily.singularSubspace B hZ G
  set Z' := Z.preimage a.totalMap.hom
  have hZc := CurveFamily.isClosedSubspace_singularSubspace B hZ G
  have sq : IsPullback (Z'.ι ≫ F.toBase.hom) (Z.fromPreimage a.totalMap.hom)
      (schemeSpaceMap a.baseMap).hom (Z.ι ≫ G.toBase.hom) :=
    ((Subfunctor.isPullback_preimage a.totalMap.hom Z).paste_vert
      (AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian)).flip
  have hqf := Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback' B integerBase hZ sq
    hZc.1 (schemeSpace G.base).property (schemeSpace F.base).property
    (CurveFamily.isProper_singularSubspace_toBase B hZ G).2.1.1
  ext y
  rw [Set.mem_preimage, CurveFamily.mem_finiteSingularBaseLocus_iff B hZ G Z hZc
      (CurveFamily.range_pointsMap_ι_singularSubspace B hZ G),
    CurveFamily.mem_finiteSingularBaseLocus_iff B hZ F Z'
      (CurveFamily.isClosedSubspace_preimage_singularSubspace B hZ a)
      (CurveFamily.range_pointsMap_ι_preimage_singularSubspace B hZ a)]
  constructor
  · intro h z' hz'
    refine (Set.ext_iff.mp hqf z').2 (h _ ?_)
    rw [← Space.pointsMap_apply_comm B integerBase hZ sq.w z', hz']
  · intro h z hz
    obtain ⟨w, hw₁, hw₂⟩ := Space.exists_points_of_isPullback B integerBase hZ sq y z hz.symm
    rw [← hw₂]
    exact (Set.ext_iff.mp hqf w).1 (h w hw₁)

/-- A family of curves lies in `Curves⁺` exactly when the locus in its base over which the
singular locus is finite is the whole base. -/
theorem CurveFamily.isFiniteNonSmoothLocus_iff_finiteSingularBaseLocus_eq_univ
    (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      CurveFamily.finiteSingularBaseLocus B hZ X = Set.univ := by
  rw [CurveFamily.isFiniteNonSmoothLocus_iff_forall_finite_nonSmoothLocus_fibre,
    Set.eq_univ_iff_forall]
  rfl

/-- A family of curves mapping to a family in `Curves⁺` lies in `Curves⁺`: membership is stable
under arbitrary base change. -/
theorem CurveFamily.isFiniteNonSmoothLocus_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (hG : IsFiniteNonSmoothLocus B hZ G) : IsFiniteNonSmoothLocus B hZ F := by
  rw [CurveFamily.isFiniteNonSmoothLocus_iff_finiteSingularBaseLocus_eq_univ] at hG ⊢
  rw [← CurveFamily.preimage_finiteSingularBaseLocus B hZ a, hG, Set.preimage_univ]

end AlgebraicGeometry

end
