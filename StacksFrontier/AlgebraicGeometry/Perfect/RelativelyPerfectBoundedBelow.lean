module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCertificate
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections

/-!
# Local boundedness below, and relative perfectness

An object `E` of `D(𝒪_X)` on a ringed space is *locally bounded below* when every point of `X`
has an open neighbourhood `U` and an integer `N` with `H^i(E|_U) = 0` for all `i < N`. This is the
condition appearing in both clauses of the fibrewise criterion for relative perfectness,
Stacks 0GEH: there it is asked of `E` itself and of the derived restriction
`L(X_s ⟶ X)^*E` of `E` to each fibre of `f : X ⟶ S`.

For a flat, locally finitely presented `f : X ⟶ S`, an `S`-perfect object is locally bounded
below. Relative perfectness (Stacks 0DI0) asks `E` to have locally finite Tor dimension over
`f⁻¹𝒪_S`, and the structure sheaf of a ringed space is the unit of its tensor product, so a Tor
amplitude interval for `E|_U` over `f⁻¹𝒪_S` already bounds the cohomology of `E|_U` itself.

## Main definitions

* `AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow`: local boundedness below.

## Main results

* `AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_iff_forall_exists_isBoundedBelow`: local
  boundedness below is boundedness below of the restrictions `E|_U` in `D(𝒪_{X|U})`.
* `AlgebraicGeometry.RingedSpace.isZero_homology_of_hasTorAmplitudeIn`: an object with Tor
  amplitude in `[a, b]` for the genuine tensor product has cohomology concentrated in `[a, b]`.
* `AlgebraicGeometry.isLocallyBoundedBelow_of_isPerfectRelativeTo`: an `S`-perfect object is
  locally bounded below, the first clause of condition (2) of Stacks 0GEH.

## Implementation notes

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product on the inverse-image ringed space is a hypothesis — a family of certificates
indexed by the opens of that space, since part (3) of Stacks 08CG restricts to an open covering.
The family is pinned by the hypothesis that its underived tensor product is the genuine
`- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU; by
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` that hypothesis determines the
predicate, and without it the Tor clause carries no information about the cohomology of `E`: at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` it holds for
every object.

The cohomology sheaves of `E|_U` are the restrictions to `U` of the cohomology sheaves of `E`,
restriction to an open subspace being exact, and
`AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_iff_forall_exists_isBoundedBelow` records
the two readings as one statement.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry

/-! ### Exact functors and cohomology -/

/-- For an exact additive functor `G`, the `i`-th cohomology of `G(E)` vanishes exactly when `G`
carries the `i`-th cohomology of `E` to a zero object. -/
theorem isZero_homology_mapDerivedCategory_iff {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (E : DerivedCategory A)
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor B i).obj (G.mapDerivedCategory.obj E)) ↔
      IsZero (G.obj ((DerivedCategory.homologyFunctor A i).obj E)) :=
  ⟨fun h => h.of_iso ((G.mapDerivedCategoryHomologyIso i).app E).symm,
    fun h => h.of_iso ((G.mapDerivedCategoryHomologyIso i).app E)⟩

/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` reflects zero objects after restriction to an
open subspace: it does not change the underlying sheaf of abelian groups. -/
private theorem isZero_restrictModules_of_isZero_scalarRestriction {X S : Scheme.{u}}
    (f : X ⟶ S) (U : Opens X.carrier) (M : OXMod.{u, u} X.toRingedSpace)
    (hM : IsZero ((RingedSpace.restrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) U).obj
      ((Scheme.Hom.scalarRestriction f).obj M))) :
    IsZero ((RingedSpace.restrictModules X.toRingedSpace U).obj M) := by
  refine isZero_of_faithful (SheafOfModules.toSheaf
    (structureSheafOfRings (X.toRingedSpace.restrict U.isOpenEmbedding))) ?_
  exact Functor.map_isZero (SheafOfModules.toSheaf
    (structureSheafOfRings ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
      U.isOpenEmbedding))) hM

namespace RingedSpace

/-! ### Local boundedness below -/

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **Locally bounded below.** An object `E` of `D(𝒪_X)` is locally bounded below when every
point of `X` has an open neighbourhood `U` and an integer `N` such that the cohomology sheaves
`H^i(E)` restricted to `U` vanish for all `i < N`.

This is the condition occurring twice in condition (2) of Stacks 0GEH. -/
public def IsLocallyBoundedBelow (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ N : ℤ, ∀ i : ℤ, i < N →
    IsZero ((restrictModules X U).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E))

/-- Local boundedness below says that every point has a neighbourhood `U` with `E|_U` bounded
below in `D(𝒪_{X|U})`: restriction to an open subspace is exact, so the cohomology sheaves of
`E|_U` are the restrictions of those of `E`. -/
public theorem isLocallyBoundedBelow_iff_forall_exists_isBoundedBelow
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) :
    IsLocallyBoundedBelow X E ↔
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        DerivedCategoryB.IsBoundedBelow ((derivedRestrictModules X U).obj E) := by
  refine forall_congr' fun x => exists_congr fun U => and_congr_right fun _ =>
    exists_congr fun N => forall_congr' fun i => imp_congr_right fun _ => ?_
  exact (isZero_homology_mapDerivedCategory_iff (restrictModules X U) E i).symm

/-! ### Tor amplitude bounds the cohomology -/

/-- **An object of Tor amplitude in `[a, b]` is concentrated in `[a, b]`.** Tensoring with the
structure sheaf is the identity, and the structure sheaf is a flat module, so the derived
tensor product of the certificate with it is the object itself.

The certificate is pinned by its underived tensor product; by
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_congr` that is
all the pinning Tor amplitude admits. -/
public theorem isZero_homology_of_hasTorAmplitudeIn (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (hD : D.tensor = Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) (hE : D.HasTorAmplitudeIn E a b) (i : ℤ)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) := by
  set F := Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.structureSheafModule X
    with hFdef
  have hunit : D.tensor.flip.obj F ≅ 𝟭 (OXMod.{u, u} X) := by
    rw [hD, hFdef]
    exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.tensorStructureSheafIso X
  have hex : PreservesFiniteLimits (D.tensor.flip.obj F) ∧
      PreservesFiniteColimits (D.tensor.flip.obj F) := by
    rw [← exactFunctor_iff, hD]
    exact Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat X.sheaf F
      (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule X)
  let _ := D.additive F
  obtain ⟨_, _⟩ := hex
  let _ := D.isLeftDerived F
  let _ : ((D.tensor.flip.obj F).mapDerivedCategory).IsLeftDerivedFunctor
      (D.tensor.flip.obj F).mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  exact (((CertifiedDerivedSheafTensoring.isZero_homology_iff_of_isLeftDerived
    _ _ (D.comparison F) (D.tensor.flip.obj F).mapDerivedCategoryFactors.hom E i).trans
    (isZero_homology_mapDerivedCategory_iff (D.tensor.flip.obj F) E i)).1
      (hE F i hi)).of_iso (hunit.app _).symm

end RingedSpace

/-! ### Relatively perfect objects are locally bounded below -/

section Objective

/-- **Stacks 0GEH, condition (1) implies the first clause of condition (2).** Let `f : X ⟶ S` be
flat and locally of finite presentation. An object of `D(𝒪_X)` perfect relative to `S` is locally
bounded below.

Relative perfectness gives an open covering of `X` on each member of which `E`, read over
`f⁻¹𝒪_S`, has Tor amplitude in some interval `[a, b]`. The structure sheaf of the inverse-image
ringed space is the unit of its tensor product, so that interval already bounds the cohomology
of `E|_U` read over `f⁻¹𝒪_S`, and restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` leaves the
underlying sheaves unchanged.

The derived tensor product is a family of certificates, one on each open subspace of the
inverse-image ringed space, pinned by the hypothesis that its underived tensor product is the
genuine `- ⊗_{f⁻¹𝒪_S} -`. -/
@[stacks 0GEH "condition (1) implies the first clause of condition (2): an `S`-perfect object \
is locally bounded below"]
public theorem isLocallyBoundedBelow_of_isPerfectRelativeTo {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
    [∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      HasDerivedCategory.{d'}
        (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
          U.isOpenEmbedding))]
    (D : ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding).sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo D E) :
    RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E := by
  obtain ⟨I, U, hU, hTor⟩ := hE.2
  intro x
  have hx : x ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  obtain ⟨a, b, hab⟩ := hTor j
  refine ⟨U j, hj, a, fun i hi => ?_⟩
  have hamp := RingedSpace.isZero_homology_of_hasTorAmplitudeIn _ (D (U j)) (hD (U j)) _ a b hab i
    fun h => absurd h.1 (by omega)
  have h1 := (isZero_homology_mapDerivedCategory_iff
    (RingedSpace.restrictModules (RingedSpace.inverseImage S.toRingedSpace f.base) (U j))
    ((Scheme.Hom.derivedScalarRestriction f).obj E) i).1 hamp
  refine isZero_restrictModules_of_isZero_scalarRestriction f (U j)
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) ?_
  exact h1.of_iso ((RingedSpace.restrictModules
      (RingedSpace.inverseImage S.toRingedSpace f.base) (U j)).mapIso
    (((Scheme.Hom.scalarRestriction f).mapDerivedCategoryHomologyIso i).app E)).symm

end Objective

end AlgebraicGeometry

end
