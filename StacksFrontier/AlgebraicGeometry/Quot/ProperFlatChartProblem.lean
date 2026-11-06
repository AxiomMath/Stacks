module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartConormalTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeRepresentable
public import StacksFrontier.Cotangent.Spaces.EtaleRestriction
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblemRebase
public import StacksFrontier.Deformation.ToposThickening.CanonicalCotangentObstruction

/-!
# The extension problem of a lift at a chart, posed over `Spec A`

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart, and let
`D` be a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX, with ideal `I`. The extension
problem of [Stacks, Section 08V3] attached to `x` and `D`
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problem`) lives over the closed subspace
`Z ⊆ Spec A'` cut out by `Spec A`, a base that changes with `D`. This file poses the same problem
over `Spec A` itself, on the `Type u` model of the small étale site of `X`:

* the morphism is `X → Spec A` (`AlgebraicGeometry.Space.ProperFlatLift.chartStructureMap`), so the
  middle ring `f⁻¹𝒪_{Spec A}` of the lower row is the same sheaf for every `D`;
* the thickened base is the extension `0 → 𝒞 → 𝒪' → 𝒪_{Spec A} → 0` of `Z ⊂ Spec A'`, restricted
  to `Spec A` along the isomorphism `ρ : Spec A ≅ Z`;
* the prescribed module is `𝒪_X ⊗_A I` (the module whose `Ext` groups are the functors `T¹`, `T²`
  of [Stacks, Remark 0D1P]).

Its isomorphism classes of solutions are those of the original problem, so that `x` lifts along
`D` exactly when it has a solution, and [Stacks, Tag 08V5] then reads the obstruction in
`Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`.

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartBaseExtension`: the thickening of `Spec A` attached
  to `D`.
* `AlgebraicGeometry.Space.ProperFlatLift.problemOnChart`: the problem over `Spec A`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.problemOnChartIsomorphismClassesEquiv`: the isomorphism
  classes of solutions of the problem of `x` along `D` on the model
  (`AlgebraicGeometry.Space.ProperFlatLift.chartModelProblem`), and of `problemOnChart`,
  correspond.
* `AlgebraicGeometry.Space.ProperFlatLift.nonempty_lift_iff_nonempty_problemOnChart`: `x` lifts
  along `D` exactly when `problemOnChart x hx D` has a solution.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.ToposPullback (inverseImageCommRingRestrictionIso
  inverseImageCommRingRestrictionIso_naturality)

universe t u

namespace AlgebraicGeometry.Space

/-! ### Restriction along an isomorphism and inverse images -/

section RestrictionInverseImage

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (ρ : Y ≅ Z)

/-- Restriction of sheaves of rings along the isomorphism `ρ : Y ≅ Z` of small étale sites. -/
abbrev isoRingRes :=
  Deformation.AlgebraExtension.ringRes (J := SmallEtale.topology B S hS Z.1)
    (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Restriction of sheaves of sets along the isomorphism `ρ : Y ≅ Z` of small étale sites
preserves finite products (found once here, so that later uses do not repeat the search). -/
local instance preservesFiniteProducts_isoSheafRes_properFlatChartProblem :
    PreservesFiniteProducts ((smallEtalePostcomp B S hS ρ.hom
      (isEtale_hom_of_iso B S hS ρ)).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1)) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- `ρ⁻¹F ≅ F|_Y` for the isomorphism `ρ : Y ≅ Z`: the inverse image along an étale morphism is
restriction (Stacks 03LV). -/
abbrev isoInverseImageRestrictionIso (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS ρ.hom).obj F ≅ (isoRingRes ρ).obj F :=
  (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Z.1) (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) F :)

/-- **`(g ≫ ρ)⁻¹F ≅ g⁻¹(F|_Y)`** on the small étale site of `X`, for `ρ : Y ≅ Z`: the composition
law of inverse images followed by `g⁻¹` of `ρ⁻¹F ≅ F|_Y`. -/
def inverseImageRestrictionIsoOfCompIso
    (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS (g ≫ ρ.hom)).obj F ≅
      (smallEtaleInverseImageRing B S hS g).obj ((isoRingRes ρ).obj F) :=
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).app F).symm ≪≫
    (smallEtaleInverseImageRing B S hS g).mapIso (isoInverseImageRestrictionIso ρ F)

set_option synthInstance.maxHeartbeats 400000 in
/-- The identification `inverseImageRestrictionIsoOfCompIso` is compatible with a map
`m : F ⟶ 𝒪_Z` and its restriction followed by `𝒪_Z|_Y ≅ 𝒪_Y`, against
`(g ≫ ρ)⁻¹𝒪_Z ≅ g⁻¹𝒪_Y`. -/
theorem inverseImageRestrictionIsoOfCompIso_hom_comp_map
    {F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (m : F ⟶ (smallEtaleRingedTopos B S hS Z).O) :
    (inverseImageRestrictionIsoOfCompIso g ρ F).hom ≫
        (smallEtaleInverseImageRing B S hS g).map ((isoRingRes ρ).map m ≫
          (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).hom) =
      (smallEtaleInverseImageRing B S hS (g ≫ ρ.hom)).map m ≫
        (inverseImageRingIsoOfCompIso g ρ).hom := by
  have hR := inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Z.1) (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) m
  have hc := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).inv.naturality m
  simp only [Functor.comp_map] at hc
  have key : (isoInverseImageRestrictionIso ρ F).hom ≫ (isoRingRes ρ).map m ≫
      (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).hom =
      (smallEtaleInverseImageRing B S hS ρ.hom).map m ≫
        (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage := by
    rw [← Category.assoc, ← hR, Category.assoc]
    exact congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc (isoInverseImageRestrictionIso ρ _) _)
  show ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).inv.app F ≫
      (smallEtaleInverseImageRing B S hS g).map (isoInverseImageRestrictionIso ρ F).hom) ≫
      (smallEtaleInverseImageRing B S hS g).map ((isoRingRes ρ).map m ≫
        (etaleRestrictionStructureSheafIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).hom) =
    (smallEtaleInverseImageRing B S hS (g ≫ ρ.hom)).map m ≫
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).inv.app _ ≫
      (smallEtaleInverseImageRing B S hS g).map
        (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage
  rw [Category.assoc, ← Functor.map_comp, key, Functor.map_comp, ← Category.assoc, ← hc,
    Category.assoc]

end RestrictionInverseImage

namespace ProperFlatLift

open Deformation.Artin Deformation.ToposThickening

attribute [local instance] restrictedFirstOrderExtension_isContinuous

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- `ρ : Spec A ≅ Z`, the identification of `Spec A` with the closed subspace of `Spec A'` it
cuts out. -/
abbrev chartRangeIso : schemeSpace (algebraOver A B S hS toS hA) ≅
    (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
      (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS) :=
  rangeSpaceIso B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1

/-- **The thickening of `Spec A` attached to `D`**: the extension
`0 → 𝒞 → 𝒪' → 𝒪_Z → 0` of the first-order thickening `Z ⊂ Spec A'` (`Z` the closed subspace cut
out by `Spec A`), restricted to the small étale site of `Spec A` along `ρ : Spec A ≅ Z`. -/
abbrev chartBaseExtension :=
  restrictedFirstOrderExtension B S hS (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D))
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))
    (chartRangeIso D) (𝟙 _)

/-- The problem of `x` along `D` with the morphism `X → Spec A ≅ Z` written as a composite, on the
model of the small étale site of `X`. -/
abbrev chartModelProblem :=
  (FlatThickeningDeformation.problem (chartStructureMap x hx ≫ (chartRangeIso D).hom)
      (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow
        (isSquareZeroClosedImmersion_arrow D))).siteTransport
    (smallEtaleModelTopology B S hS x.obj.obj.left.1) (smallEtaleModelEquiv B S hS x.obj.obj.left)

/-- `f₁⁻¹𝒪' ≅ f⁻¹(𝒪'|_{Spec A})` on the model, for `f₁ = X → Spec A ≅ Z` and `f = X → Spec A`. -/
def chartThickenedBaseIso :
    (inverseImageCommRingFunctor (chartModelProblem x hx D).f.toToposHom).obj
        (chartModelProblem x hx D).baseExtension ≅
      (inverseImageCommRingFunctor (modelRingedToposHom (chartStructureMap x hx)).toToposHom).obj
        (chartBaseExtension D).extension :=
  siteTransportInverseImageRingIso (X := smallEtaleRingedTopos B S hS x.obj.obj.left)
    (smallEtaleModelTopology B S hS x.obj.obj.left.1) (smallEtaleModelEquiv B S hS x.obj.obj.left)
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx ≫ (chartRangeIso D).hom))
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx))
    (inverseImageRestrictionIsoOfCompIso (chartStructureMap x hx) (chartRangeIso D) _)

/-- `chartThickenedBaseIso` intertwines the reductions: followed by `f⁻¹` of the reduction
`𝒪' → 𝒪_{Spec A}`, it is `f₁⁻¹` of the reduction `𝒪' → 𝒪_Z` followed by
`f₁⁻¹𝒪_Z ≅ f⁻¹𝒪_{Spec A}`. -/
theorem chartThickenedBaseIso_hom_comp_map :
    (chartThickenedBaseIso x hx D).hom ≫
        (inverseImageCommRingFunctor (modelRingedToposHom (chartStructureMap x hx)).toToposHom).map
          (chartBaseExtension D).reduction =
      (inverseImageCommRingFunctor (chartModelProblem x hx D).f.toToposHom).map
          (chartModelProblem x hx D).baseReduction ≫
        (modelInverseImageRingIsoOfCompIso (chartStructureMap x hx) (chartRangeIso D)).hom :=
  siteTransportInverseImageRingIso_hom_comp_map (X := smallEtaleRingedTopos B S hS x.obj.obj.left)
    (smallEtaleModelTopology B S hS x.obj.obj.left.1) (smallEtaleModelEquiv B S hS x.obj.obj.left)
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx ≫ (chartRangeIso D).hom))
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)) _ _ _ _
    (inverseImageRestrictionIsoOfCompIso_hom_comp_map (chartStructureMap x hx) (chartRangeIso D) _)

/-- The prescribed module of the problem of `x` along `D`, on the model, is `𝒪_X ⊗_A I`
(`AlgebraicGeometry.Space.ProperFlatLift.thickeningModelConormalIso`, read at `X → Spec A ≅ Z`). -/
def chartModelProblemGIso :
    (chartModelProblem x hx D).G ≅ (modelTensorFunctor (chartBaseRingHom x hx)).obj D.kernel :=
  eqToIso (congrArg (fun h => (Deformation.AlgebraExtension.moduleRes
      (smallEtaleModelTopology B S hS x.obj.obj.left.1)
      (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
      (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        (FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace D.arrow
          (isSquareZeroClosedImmersion_arrow D)) h))
      (specialMap_arrow_eq x hx D).symm) ≪≫
    thickeningModelConormalIso x hx D

/-- **The extension problem of a lift of `x` along `D`, posed over `Spec A`** ([Stacks, Section
08V3] for `X → Spec A ⊂ Spec A'`), on the model of the small étale site of `X`: the morphism is
`f = X → Spec A`, the thickened base is `chartBaseExtension D`, the prescribed module is
`𝒪_X ⊗_A I` (`I = D.kernel`), and the ideal and the prescribed map are those of the problem of
`x` along `D` (`chartModelProblem`), read through `f₁⁻¹𝒪' ≅ f⁻¹𝒪'`, `f₁⁻¹𝒪_Z ≅ f⁻¹𝒪_{Spec A}` and
`f^*𝒞 ≅ 𝒪_X ⊗_A I` (`RingedToposExtensionProblem.rebase`).

The base ring `f⁻¹𝒪_{Spec A}` of its lower row is the same sheaf for every thickening `D`. -/
def problemOnChart :
    RingedToposExtensionProblem (modelTopos x.obj.obj.left)
      (smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA))) :=
  RingedToposExtensionProblem.rebase
    (X := modelTopos x.obj.obj.left)
    (B₁ := smallEtaleRingedTopos B S hS
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS))
    (B₂ := smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA)))
    (chartModelProblem x hx D) (modelRingedToposHom (chartStructureMap x hx))
    (chartBaseExtension D).reduction (chartThickenedBaseIso x hx D)
    (modelInverseImageRingIsoOfCompIso (chartStructureMap x hx) (chartRangeIso D))
    (chartThickenedBaseIso_hom_comp_map x hx D)
    (modelInverseImageRingIsoOfCompIso_hom_fSharpInverseImage (chartStructureMap x hx)
      (chartRangeIso D))
    (chartModelProblemGIso x hx D) (chartBaseExtension D).locallySurjective
    (chartBaseExtension D).squareZero

/-- The morphism of `problemOnChart x hx D` is `f = X → Spec A`. -/
@[simp]
theorem problemOnChart_f :
    (problemOnChart x hx D).f = modelRingedToposHom (chartStructureMap x hx) := rfl

/-- The prescribed module of `problemOnChart x hx D` is `𝒪_X ⊗_A I`, for `I = D.kernel`. -/
@[simp]
theorem problemOnChart_G :
    (problemOnChart x hx D).G = (modelTensorFunctor (chartBaseRingHom x hx)).obj D.kernel := rfl

/-- The thickened base ring of `problemOnChart x hx D` is that of `chartBaseExtension D`. -/
theorem problemOnChart_baseExtension :
    (problemOnChart x hx D).baseExtension = (chartBaseExtension D).extension := rfl

/-- The reduction of the base of `problemOnChart x hx D` is that of `chartBaseExtension D`. -/
theorem problemOnChart_baseReduction :
    (problemOnChart x hx D).baseReduction = (chartBaseExtension D).reduction := rfl

/-- **The solutions of the problem of `x` along `D` on the model and those of `problemOnChart`
correspond**, up to isomorphism (`RingedToposExtensionProblem.rebaseIsomorphismClassesEquiv`). -/
def problemOnChartIsomorphismClassesEquiv :
    RingedToposExtensionProblem.CompatibleFirstOrderThickening.IsomorphismClasses
        (X := modelTopos x.obj.obj.left)
        (B := smallEtaleRingedTopos B S hS
          (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
            (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
              AlgebraicSpaces B S hS))
        (chartModelProblem x hx D) ≃
      RingedToposExtensionProblem.CompatibleFirstOrderThickening.IsomorphismClasses
        (X := modelTopos x.obj.obj.left)
        (B := smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA)))
        (problemOnChart x hx D) :=
  RingedToposExtensionProblem.rebaseIsomorphismClassesEquiv (X := modelTopos x.obj.obj.left)
    (B₁ := smallEtaleRingedTopos B S hS
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS))
    (B₂ := smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA)))
    _ _ _ _ _ _ _ _ _ _

/-- `problemOnChart x hx D` has a solution exactly when the problem of `x` along `D` on the model
has one. -/
theorem nonempty_problemOnChart_iff :
    Nonempty (problemOnChart x hx D).CompatibleFirstOrderThickening ↔
      Nonempty (chartModelProblem x hx D).CompatibleFirstOrderThickening :=
  RingedToposExtensionProblem.nonempty_rebase_iff (X := modelTopos x.obj.obj.left)
    (B₁ := smallEtaleRingedTopos B S hS
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS))
    (B₂ := smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA)))
    _ _ _ _ _ _ _ _ _ _

/-- **`x` lifts along `D` exactly when `problemOnChart x hx D` has a solution.** A lift is a
solution of the extension problem of [Stacks, Section 08V3] over the closed subspace of `Spec A'`
cut out by `Spec A` (`nonempty_lift_iff_nonempty_solution`); restricting to the model of the small
étale site of `X` (`siteTransportIsomorphismClassesEquiv`) and posing the problem over `Spec A`
(`nonempty_problemOnChart_iff`) does not change whether it has one. -/
theorem nonempty_lift_iff_nonempty_problemOnChart :
    Nonempty ((Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D.arrow))) ↔
      Nonempty (problemOnChart x hx D).CompatibleFirstOrderThickening := by
  refine (nonempty_lift_iff_nonempty_solution x hx D).trans
    (Iff.trans ?_ (nonempty_problemOnChart_iff x hx D).symm)
  rw [specialMap_arrow_eq x hx D]
  have e := RingedToposExtensionProblem.siteTransportIsomorphismClassesEquiv
    (smallEtaleModelTopology B S hS x.obj.obj.left.1) (smallEtaleModelEquiv B S hS x.obj.obj.left)
    (FlatThickeningDeformation.problem (chartStructureMap x hx ≫ (chartRangeIso D).hom)
      (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow
        (isSquareZeroClosedImmersion_arrow D)))
  exact ⟨fun ⟨P⟩ => ⟨(e (Quotient.mk _ P)).out⟩, fun ⟨Q⟩ => ⟨(e.symm (Quotient.mk _ Q)).out⟩⟩

/-! ### The obstruction class at a chart -/

section Obstruction

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The obstruction class `o(D) ∈ T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of `x` along `D`**:
the class of [Stacks, Tag 08V5] of `problemOnChart x hx D`
(`RingedToposExtensionProblem.canonicalObstructionClass`, formed on the connecting morphism of the
fundamental triangle of `f⁻¹𝒪_{Spec A'} → f⁻¹𝒪_{Spec A} → 𝒪_X`, with the sign `o = −(δ.comp γ)`),
read in the `A`-module `T²(I)` through `AlgebraicGeometry.Space.cotangentExtFunctorObjEquiv`. -/
def chartObstruction :
    (cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).obj D.kernel :=
  (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2 D.kernel).symm
    (problemOnChart x hx D).canonicalObstructionClass

/-- `chartObstruction x hx D`, read in the Ext group through
`AlgebraicGeometry.Space.cotangentExtFunctorObjEquiv`, is the canonical obstruction class of
`problemOnChart x hx D`. -/
theorem cotangentExtFunctorObjEquiv_chartObstruction :
    cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2 D.kernel
        (chartObstruction x hx D) = (problemOnChart x hx D).canonicalObstructionClass :=
  AddEquiv.apply_symm_apply _ _

/-- **Condition (i)/(iii) of Situation 07YX at a chart**: `x` lifts along `D` exactly when
`o(D) = 0`. A lift is a solution of `problemOnChart x hx D`
(`nonempty_lift_iff_nonempty_problemOnChart`), and a solution exists exactly when the class of
[Stacks, Tag 08V5] (1) vanishes (`nonempty_iff_canonicalObstructionClass_eq_zero`). -/
theorem nonempty_lift_iff_chartObstruction_eq_zero :
    Nonempty ((Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D.arrow))) ↔ chartObstruction x hx D = 0 := by
  refine (nonempty_lift_iff_nonempty_problemOnChart x hx D).trans
    ((problemOnChart x hx D).nonempty_iff_canonicalObstructionClass_eq_zero.trans ?_)
  have hc := cotangentExtFunctorObjEquiv_chartObstruction x hx D
  have he := (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2
    D.kernel).map_eq_zero_iff (x := chartObstruction x hx D)
  exact (Iff.of_eq (congrArg (· = 0) hc.symm)).trans he

end Obstruction

end ProperFlatLift

end AlgebraicGeometry.Space

end
