module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The derived pullback on a ringed space commutes with the shift and is exact

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f`
is `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`, available unconditionally by
`StacksDraft.Ch20.Sec28.Tag079WKFlat`.  This file proves the two clauses of Stacks 06YJ that say
`Lf^*` is a morphism of triangulated categories: it commutes with the shift, and it carries
distinguished triangles to distinguished triangles.

## Main results

* `Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`: **`Lf^*` commutes with the
  shift.**  A total left
  derived functor does, by `StacksDraft.PseudoCoherence.leftDerivedCommShift`.
* `Stacks.Cohomology.KFlatDerivedPullback.derivedPullbackComparison_commShift`: the canonical
  comparison
  `Qh ⋙ Lf^* ⟶ K(f^*)` is compatible with that commutation.
* `Stacks.Cohomology.KFlatDerivedPullback.isKFlat_obj₃_of_distTriang`: the third vertex of a
  distinguished triangle of
  `K(𝒪_Y)` is K-flat if the first two are.
* `Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated`: **`Lf^*` is exact**,
  i.e. triangulated.

## Implementation notes

*The two clauses are not independent.*  `Functor.IsTriangulated` takes the commutation with the
shift as an instance argument — `F.mapTriangle` is built from it — so the exactness statement is
*about* the structure `derivedPullback_commShift` provides.  That structure is therefore seated
as an instance here, and the exactness statement is the plain
`(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).IsTriangulated` read against
  it.

*Route to exactness.*  `CategoryTheory.Functor.isTriangulated_of_rightExtension` needs every
morphism of `D(𝒪_Y)` to be, up to isomorphism of arrows, the image of a morphism *between
K-flat complexes*, together with a distinguished triangle on it whose three vertices all carry
an invertible comparison.  The three ingredients are: the K-flat complexes resolve every
complex (`Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat`), so the inclusion of the
  K-flat objects is a
localized equivalence and is essentially surjective on *arrows*
(`CategoryTheory.LeftDerivedByResolutions`); the comparison is invertible at every K-flat
object (`CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions`, with
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat` discharging
  exactness of `f^*` there); and
K-flatness passes to the cone, which is `isKFlat_obj₃_of_distTriang` below.  This is the
ringed-space counterpart of the argument carried out for extension of scalars in
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`.

*An instance that is found and then rejected for size.*
  `(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy
f).IsTriangulated` does **not** synthesize, and the cause is neither a missing instance nor a
heartbeat budget: the trace ends `[Meta.synthInstance.answer] ❌ … (size: 215 ≥ 128)`, i.e. the
solution *was* assembled and then rejected against `synthInstance.maxSize`.  Both halves —
`((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated` and
`DerivedCategory.Qh.IsTriangulated` — synthesize on their own, so the remedy is to apply
`Functor.IsTriangulated.instComp` with its two functors written out, which makes each half a
separate synthesis problem.  No option is needed.

*Named instances.*  The instance hypotheses of `CochainComplex.KFlatBifunctor.KFlat` are not
found by synthesis: at a ringed space the site `Opens Y` has its object universe equal to its
morphism universe, so the general instances present search with `max ?u ?v =?= u` with both
unknown, which is *stuck* rather than failing, and pinning
`J := Opens.grothendieckTopology Y.carrier` is what solves it.
`StacksDraft.Ch20.Sec27Pullback.Tag06YJ` already seats them so pinned, as
`Stacks.Cohomology.KFlatDerivedPullback.sheafTensorAdditive`,
  `Stacks.Cohomology.KFlatDerivedPullback.sheafTensorObjAdditive` and
`Stacks.Cohomology.KFlatDerivedPullback.hasMapBifunctorSheafTensor`; those three are re-activated
  below with
`attribute [local instance]` rather than declared again.

*Why `StacksFrontier.Homology.PseudoCoherent.BaseChange` is imported.*  That file is the only place
in the tree where the generic facts "a total left derived functor commutes with the shift" and
"its counit is compatible with that commutation" are *public*; the same two facts exist as
`private` declarations in `StacksFrontier.Homology.Tor.DerivedExtensionScalars`, which is upstream
of it.  Relocating the generic `Op` and `Shift` sections out of
`StacksFrontier.Homology.PseudoCoherent.BaseChange` into a module of their own, and deleting the
private copies, is a dedup target; it is not done here because it would rewrite two other files.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.KFlatDerivedPullback

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Space

variable (Y : RingedSpace.{u, u})

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  hasMapBifunctorSheafTensor

/-- **K-flatness passes to the cone.**  In a distinguished triangle of `K(𝒪_Y)`, the third
vertex is K-flat as soon as the first two are.  This is the bifunctor statement
`CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang` read at `⊗_{𝒪_Y}`: the functor
`Tot(G ⊗_{𝒪_Y} -)` descended to `K(𝒪_Y)` is triangulated, and the acyclic objects form a
triangulated subcategory, so two acyclic vertices force the third. -/
theorem isKFlat_obj₃_of_distTriang
    (T : Triangle
      (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)))
    (hT : T ∈ distTriang _) (h₁ : IsKFlat Y T.obj₁) (h₂ : IsKFlat Y T.obj₂) :
    IsKFlat Y T.obj₃ :=
  CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ T.mor₁ T.mor₂ T.mor₃ hT h₁ h₂

end Space

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Degreewise pullback followed by localization is triangulated.

Each half is an instance of Mathlib's, but the composite is *not* found by synthesis: the search
assembles the answer and then rejects it for exceeding `synthInstance.maxSize`.  Applying the
composition instance with its two functors written out turns each half into a synthesis problem
of its own. -/
instance pullbackOnHomotopy_isTriangulated :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).IsTriangulated :=
  Functor.IsTriangulated.instComp
    (F := (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
    (G := DerivedCategory.Qh)

/-- **The derived pullback commutes with the shift.**  `Lf^*` is the total left derived functor
of degreewise pullback along `Qh`; degreewise pullback and `Qh` both commute with the shift, and
the quasi-isomorphisms of `K(𝒪_Y)` are stable under it, so the derived functor does too. -/
@[instance_reducible, stacks 06YJ "compatibility with shifts"]
instance derivedPullback_commShift :
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ

/-- The canonical comparison `Qh ⋙ Lf^* ⟶ K(f^*)` is compatible with the commutation with the
shift of `derivedPullback_commShift`.  This is what makes the exactness argument below run. -/
instance derivedPullbackComparison_commShift :
    NatTrans.CommShift (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f) ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ

/-- The canonical comparison of `Lf^*` is invertible at every K-flat object of `K(𝒪_Y)`.

This is `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` with
  the object left
arbitrary rather than presented as the image of a complex, which is the form the exactness
argument consumes. -/
theorem isIso_derivedPullbackComparison_app_of_isKFlat
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (hK : IsKFlat Y K) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app K) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (IsKFlat Y) (hasResolutions_isKFlat Y)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat f)
      DerivedCategory.Qh
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f) K hK

/-- **The derived pullback is exact**: `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` carries distinguished triangles
to distinguished triangles.

Every morphism of `D(𝒪_Y)` is, up to isomorphism of arrows, the image of a morphism between
K-flat complexes: the K-flat objects resolve every object, so their inclusion is a localized
equivalence and the induced functor is essentially surjective on arrows.  Completing such a
morphism to a distinguished triangle of `K(𝒪_Y)` leaves all three vertices K-flat, the third by
`isKFlat_obj₃_of_distTriang`, and the comparison of `Lf^*` is invertible at each of them.  That
is exactly the input of `CategoryTheory.Functor.isTriangulated_of_rightExtension`. -/
@[stacks 06YJ "exactness"]
instance derivedPullback_isTriangulated :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).IsTriangulated := by
  have hP := hasResolutions_isKFlat Y
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (IsKFlat Y)).HasLeftResolutions := fun M => by
    obtain ⟨K, hK, s, hs⟩ := hP M
    exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (IsKFlat Y)
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (IsKFlat Y)
  have : ((IsKFlat Y).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).inverseImage (IsKFlat Y).ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
        (IsKFlat Y)) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((IsKFlat Y).ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)).inverseImage (IsKFlat Y).ι)
  refine Functor.isTriangulated_of_rightExtension
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f) (fun {A B} g =>
      ?_)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((IsKFlat Y).ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  obtain ⟨Z, u, v, hT⟩ := distinguished_cocone_triangle ((IsKFlat Y).ι.map a.hom)
  have h₁ : IsKFlat Y (Triangle.mk ((IsKFlat Y).ι.map a.hom) u v).obj₁ := a.left.property
  have h₂ : IsKFlat Y (Triangle.mk ((IsKFlat Y).ι.map a.hom) u v).obj₂ := a.right.property
  exact ⟨Triangle.mk ((IsKFlat Y).ι.map a.hom) u v, hT,
    isIso_derivedPullbackComparison_app_of_isKFlat f _ h₁,
    isIso_derivedPullbackComparison_app_of_isKFlat f _ h₂,
    isIso_derivedPullbackComparison_app_of_isKFlat f _
      (isKFlat_obj₃_of_distTriang Y _ hT h₁ h₂), ⟨ea⟩⟩

end

end Stacks.Cohomology.KFlatDerivedPullback

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived pushforward commutes with the shift.**  `Rf_*` is the right adjoint in the
derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W], and its left adjoint commutes with the
shift by `derivedPullback_commShift` ([Stacks, Tag 06YJ]), so the shift datum transports across
the adjunction.

Not an instance: it is a datum rather than a property, so a consumer must seat it, typically by
`letI` or `attribute [local instance]`. -/
@[instance_reducible]
def derivedPushforwardCommShift : (derivedPushforward f).CommShift ℤ :=
  (derivedAdjunction f).rightAdjointCommShift ℤ

/-- **The derived pushforward is exact**: it is the right adjoint of the exact functor `Lf^*`.
Stated against the particular shift datum `derivedPushforwardCommShift`, which has to be seated
before the statement even typechecks. -/
theorem derivedPushforward_isTriangulated :
    letI := derivedPushforwardCommShift f
    (derivedPushforward f).IsTriangulated :=
  let := derivedPushforwardCommShift f
  let : (derivedAdjunction f).CommShift ℤ := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
  (derivedAdjunction f).isTriangulated_rightAdjoint

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end

