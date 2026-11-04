module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorAnyModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Coproducts
public import StacksFrontier.Homology.Devissage.NatTransOnDerivedModulesByShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDirectSums
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08EU] over an affine base of the form `Spec R`

Let `p : V ⟶ Spec R` be a quasi-compact and quasi-separated morphism of schemes and let `E` be an
object of `D_QCoh(𝒪_V)`.  Then the projection-formula morphism of [Stacks, Tag 0B53]

`R p_* E ⊗^𝐋_{𝒪_{Spec R}} A ⟶ R p_*(E ⊗^𝐋_{𝒪_V} L p^* A)`

is an isomorphism for every `A` in `D_QCoh(𝒪_{Spec R})`.  This is the heart of the source's proof
of [Stacks, Tag 08EU]: the dévissage in `A`.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_spec`: the statement
  above.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_app_of_devissage`: the dévissage of
  [Stacks, Tag 09PB] in the shape used here — a morphism of exact functors, precomposed with a
  functor out of `D(R)` under which the two composites commute with direct sums, is invertible
  on the whole image of that functor as soon as it is invertible at the shifts of `R`.

## Implementation notes

The two sides are the functors
`Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaSource` and
`projectionFormulaTarget` of `A`, and the morphism between them is
`projectionFormulaTransformation`.  The dévissage is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_shifts_of_regularModule`
([Stacks, Tag 09PB]), entered through `isIso_app_of_devissage`, and it is run not on
`D_QCoh(𝒪_{Spec R})` but along the functor

`Φ = (tilde R).mapDerivedCategory : D(R) ⥤ D(𝒪_{Spec R})`

of [Stacks, Tag 06Z0].  Every object of `D_QCoh(𝒪_{Spec R})` is in the image of `Φ` up to
isomorphism — `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, which is the
essential surjectivity half of Tag 06Z0 at the standard model of the derived category — and
invertibility of the projection-formula morphism depends on its target only through its
isomorphism class, so running the dévissage along `Φ` is enough.  Doing it this way means the
quasi-coherent subcategory never has to carry a triangulated structure: it appears only inside
the proof that `Φ` commutes with direct sums.

*Exactness.*  `Φ` is `Functor.mapDerivedCategory` of an exact functor, and the exactness of the
two sides is `Stacks.Cohomology.ProjectionFormulaPerfect`'s `projectionFormulaTargetCommShift`
and `projectionFormulaTarget_isTriangulated` together with the shift compatibility and exactness
of tensoring with a fixed object ([Stacks, Tag 06YU]).

*Commutation with arbitrary direct sums.*  `Φ` commutes with them because it is the equivalence
of Tag 06Z0 followed by the inclusion of `D_QCoh(𝒪_{Spec R})`, which is closed under direct sums
([Stacks, Tag 08DT]).  For the source side the remaining factor is the derived tensor product's,
`Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor`.
For the target side the three factors are taken in turn: `L p^*` is a left adjoint;
`E ⊗^𝐋_{𝒪_V} -` again commutes with direct sums; and `R p_*` does so on `D_QCoh(𝒪_V)` by
[Stacks, Tag 08DZ].  The last step is why the middle of the composite is corestricted to
`D_QCoh(𝒪_V)`, which is legitimate because `L p^*` preserves quasi-coherent cohomology
([Stacks, Tag 08DW] part (1)) and so does the derived tensor product ([Stacks, Tag 08DX]
part (1), at the standard model by
`Stacks.Duality.isQuasicoherent_homology_derivedTensor_anyModel`).

*The base case* is the one the source calls clear: at `A = 𝒪_{Spec R}[0]⟦n⟧` the morphism is
invertible with no hypothesis at all, by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`.
Derived sheafification carries the regular module in degree zero to the structure sheaf in degree
zero — `AlgebraicGeometry.tildeSelf` is the identity — and carries shifts to shifts, which is
`tildeDUnitShiftIso` below.

**Why the dévissage and the plumbing are entered through explicit-argument wrappers.**
`projectionFormulaSource` and `projectionFormulaTarget` are `abbrev`s whose arguments include the
`HasSheafify` instances of the two spaces, and a local instance declared at the folded spelling
is not found by instance search against a goal that prints identically.  Inside
`isIso_app_of_devissage` and
`preservesColimitsOfShape_comp'` the functors are plain variables, so there is nothing to unfold
and every instance is found on the nose; the caller supplies the exactness and direct-sum data as
terms, which are checked by conversion rather than by instance search.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.DerivedTensor.RingedSite

universe w u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Explicit-argument forms of two pieces of plumbing -/

section Plumbing

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  {J : Type*} [Category J]

/-- Composition of two functors preserving `J`-indexed colimits, with the two preservations as
explicit arguments.  See the module docstring for why the instance form will not do. -/
theorem preservesColimitsOfShape_comp' (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (hF : PreservesColimitsOfShape J F) (hG : PreservesColimitsOfShape J G) :
    PreservesColimitsOfShape J (F ⋙ G) :=
  let := hF
  let := hG
  comp_preservesColimitsOfShape F G

/-- A functor preserves `J`-indexed colimits as soon as its composite with a functor reflecting
them does, with both inputs as explicit arguments. -/
theorem preservesColimitsOfShape_of_reflects' (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (hG : ReflectsColimitsOfShape J G) (hFG : PreservesColimitsOfShape J (F ⋙ G)) :
    PreservesColimitsOfShape J F :=
  let := hG
  let := hFG
  preservesColimitsOfShape_of_reflects_of_preserves F G

end Plumbing

/-- **The dévissage of [Stacks, Tag 09PB], along a functor out of `D(R)`, with every input
explicit.**  Let `Φ : D(R) ⥤ 𝒞` and `α : F ⟶ G` with `F, G : 𝒞 ⥤ D` be exact, and suppose the
two composites `Φ ⋙ F` and `Φ ⋙ G` commute with direct sums indexed by any type of the module
universe.  If `α` is invertible at `Φ(R[0]⟦n⟧)` for every integer `n`, then it is invertible at
`Φ(M)` for every `M` in `D(R)`.

This is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_shifts_of_regularModule` applied
to `α` whiskered by `Φ`, with the exactness and direct-sum data taken as explicit arguments
rather than as instances. -/
theorem isIso_app_of_devissage
    {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory.{w} C₀]
    {A : Type u} [Ring A] [Small.{u} A]
    (Φ : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory C₀) (cΦ : Φ.CommShift ℤ)
    (tΦ : letI := cΦ; Φ.IsTriangulated)
    (F G : DerivedCategory C₀ ⥤ DerivedCategory C₀) (cF : F.CommShift ℤ) (cG : G.CommShift ℤ)
    (tF : letI := cF; F.IsTriangulated) (tG : letI := cG; G.IsTriangulated)
    (pF : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (Φ ⋙ F))
    (pG : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (Φ ⋙ G))
    (α : F ⟶ G)
    (h : ∀ n : ℤ, IsIso (α.app (Φ.obj
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Shrink.{u} A)))⟦n⟧))))
    (M : DerivedCategory (ModuleCat.{u} A)) : IsIso (α.app (Φ.obj M)) := by
  let := cΦ
  let := tΦ
  let := cF
  let := cG
  let := tF
  let := tG
  let := pF
  let := pG
  let : (Φ ⋙ F).CommShift ℤ := Functor.CommShift.comp _ _
  let : (Φ ⋙ G).CommShift ℤ := Functor.CommShift.comp _ _
  have : (Φ ⋙ F).IsTriangulated := inferInstance
  have : (Φ ⋙ G).IsTriangulated := inferInstance
  exact Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_shifts_of_regularModule
    (Functor.whiskerLeft Φ α) h M

/-! ### The quasi-coherent subcategory -/

/-- `D_QCoh(𝒪_W)` for a scheme `W`, as a property of objects of `D(𝒪_W)`: the objects all of
whose cohomology sheaves are quasi-coherent.  The ambient category is left to be inferred, which
is the spelling the standard-model instances are stated at. -/
abbrev derivedQCoh (W : Scheme.{u}) :=
  DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)

/-- **`D_QCoh(𝒪_W)` is closed under `I`-indexed direct sums**, [Stacks, Tag 08DT]. -/
theorem derivedQCoh_isClosedUnderCoproducts (W : Scheme.{u}) (I : Type u) :
    (derivedQCoh W).IsClosedUnderColimitsOfShape (Discrete I) :=
  Stacks.Cohomology.SupportedComplexes.quasicoherentDerivedProperty_isClosedUnderCoproducts W I

/-- The inclusion of `D_QCoh(𝒪_W)` in `D(𝒪_W)` preserves `I`-indexed direct sums, `D_QCoh(𝒪_W)`
being closed under them. -/
theorem preservesColimitsOfShape_discrete_derivedQCoh_ι (W : Scheme.{u}) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (derivedQCoh W).ι := by
  have := derivedQCoh_isClosedUnderCoproducts W I
  infer_instance

/-- The inclusion of `D_QCoh(𝒪_W)` in `D(𝒪_W)` reflects `I`-indexed direct sums. -/
theorem reflectsColimitsOfShape_discrete_derivedQCoh_ι (W : Scheme.{u}) (I : Type u) :
    ReflectsColimitsOfShape (Discrete I) (derivedQCoh W).ι := by
  have := derivedQCoh_isClosedUnderCoproducts W I
  infer_instance

/-! ### Derived sheafification at the standard model -/

variable (R : CommRingCat.{u})

/-- **Derived sheafification `D(R) ⥤ D(𝒪_{Spec R})`** at the standard model of the derived
category: the functor induced on derived categories by the exact functor `M ↦ M^~` of
[Stacks, Tag 01I7], with its target read in the spelling of `𝒪_{Spec R}`-modules that the
projection-formula morphism of [Stacks, Tag 0B53] is stated at. -/
abbrev tildeD : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) :=
  (tilde.functor R).mapDerivedCategory

/-- **Derived sheafification commutes with `I`-indexed direct sums.**  It is the equivalence
`D(R) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0] followed by the inclusion of
`D_QCoh(𝒪_{Spec R})`, and the latter is closed under direct sums. -/
theorem preservesColimitsOfShape_discrete_tildeD (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (tildeD R) :=
  preservesColimitsOfShape_comp' (derivedTilde R) (derivedQCoh (Spec R)).ι inferInstance
    (preservesColimitsOfShape_discrete_derivedQCoh_ι (Spec R) I)

/-- **Derived sheafification carries the regular module in degree zero to the structure sheaf in
degree zero.**  The shrunken copy of `R` is identified with `R` by `Shrink.linearEquiv`, the
single functors are exchanged by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, and
`AlgebraicGeometry.tildeSelf` — which is the identity — identifies the sheaf associated to `R`
with the structure sheaf. -/
def tildeDUnitIso :
    (tildeD R).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of (R : Type u) (Shrink.{u} (R : Type u)))) ≅
      singleUnit (Spec R).toRingedSpace :=
  (tildeD R).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (Shrink.linearEquiv (R : Type u) (R : Type u)).toModuleIso) ≪≫
    ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of (R : Type u) (R : Type u)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso AlgebraicGeometry.tildeSelf

/-- **Derived sheafification carries every shift of the regular module in degree zero to the
corresponding shift of the structure sheaf in degree zero**, sheafification being exact. -/
def tildeDUnitShiftIso (n : ℤ) :
    (tildeD R).obj (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of (R : Type u) (Shrink.{u} (R : Type u))))⟦n⟧) ≅
      (singleUnit (Spec R).toRingedSpace)⟦n⟧ :=
  (((tilde.functor R).mapDerivedCategory).commShiftIso n).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of (R : Type u) (Shrink.{u} (R : Type u)))) ≪≫
    (shiftFunctor _ n).mapIso (tildeDUnitIso R)

/-! ### The dévissage over an affine base -/

section Main

variable {V : Scheme.{u}} (p : V ⟶ Spec R) [QuasiCompact p] [QuasiSeparated p]
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing V.toRingedSpace)))
  (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing V.toRingedSpace)) j).obj E).IsQuasicoherent)

omit [QuasiCompact p] [QuasiSeparated p] in
/-- `L p^*` commutes with direct sums, being a left adjoint. -/
theorem preservesColimitsOfShape_discrete_derivedPullback (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (derivedPullback p.toLRSHom.toShHom) := by
  have : (derivedPullback p.toLRSHom.toShHom).IsLeftAdjoint :=
    (derivedAdjunction p.toLRSHom.toShHom).isLeftAdjoint
  infer_instance

/-- The middle of the target functor, `A ↦ E ⊗^𝐋_{𝒪_V} L p^* A`, corestricted to `D_QCoh(𝒪_V)`.
It lands there because `L p^*` preserves quasi-coherent cohomology ([Stacks, Tag 08DW] part (1))
and so does the derived tensor product with an object of `D_QCoh(𝒪_V)` ([Stacks, Tag 08DX]
part (1)). -/
def targetLift :
    (derivedQCoh (Spec R)).FullSubcategory ⥤ (derivedQCoh V).FullSubcategory :=
  ObjectProperty.lift _
    ((derivedQCoh (Spec R)).ι ⋙ derivedPullback p.toLRSHom.toShHom ⋙
      (derivedTensorProductFunctor V.toRingedSpace.sheaf).obj E)
    (fun A j => Stacks.Duality.isQuasicoherent_homology_derivedTensor_anyModel V E
      ((derivedPullback p.toLRSHom.toShHom).obj A.obj) hE
      (fun k => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel p A.obj
        (fun m => A.property m) k) j)

include hE

omit [QuasiCompact p] [QuasiSeparated p] in
/-- `A ↦ E ⊗^𝐋_{𝒪_V} L p^* A`, corestricted to `D_QCoh(𝒪_V)`, preserves `I`-indexed direct
sums: its composite with the inclusion of `D_QCoh(𝒪_V)` is the inclusion of `D_QCoh(𝒪_{Spec R})`
followed by `L p^*` and by `E ⊗^𝐋_{𝒪_V} -`, all three of which do, and the inclusion of
`D_QCoh(𝒪_V)` reflects them. -/
theorem preservesColimitsOfShape_discrete_targetLift (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (targetLift R p E hE) :=
  preservesColimitsOfShape_of_reflects' (targetLift R p E hE) (derivedQCoh V).ι
    (reflectsColimitsOfShape_discrete_derivedQCoh_ι V I)
    (preservesColimitsOfShape_comp' (derivedQCoh (Spec R)).ι
      (derivedPullback p.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor V.toRingedSpace.sheaf).obj E)
      (preservesColimitsOfShape_discrete_derivedQCoh_ι (Spec R) I)
      (preservesColimitsOfShape_comp' (derivedPullback p.toLRSHom.toShHom)
        ((derivedTensorProductFunctor V.toRingedSpace.sheaf).obj E)
        (preservesColimitsOfShape_discrete_derivedPullback R p I)
        (preservesColimitsOfShape_discrete_derivedTensorProductFunctor
          V.toRingedSpace.sheaf I E)))

/-- Derived sheafification followed by the target functor of the projection-formula morphism
preserves `I`-indexed direct sums.  Sheafification factors through `D_QCoh(𝒪_{Spec R})`, where
the target functor is the corestriction above followed by `R p_*` on `D_QCoh(𝒪_V)`, which
commutes with direct sums by [Stacks, Tag 08DZ]. -/
theorem preservesColimitsOfShape_discrete_tildeD_comp_projectionFormulaTarget (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (tildeD R ⋙ projectionFormulaTarget p.toLRSHom.toShHom E) :=
  preservesColimitsOfShape_comp' (derivedTilde R)
    (targetLift R p E hE ⋙ (derivedQCoh V).ι ⋙ derivedPushforward p.toLRSHom.toShHom)
    inferInstance
    (preservesColimitsOfShape_comp' (targetLift R p E hE)
      ((derivedQCoh V).ι ⋙ derivedPushforward p.toLRSHom.toShHom)
      (preservesColimitsOfShape_discrete_targetLift R p E hE I)
      (SupportedComplexes.preservesColimitsOfShape_discrete_ι_comp_derivedPushforward
        p I))

omit hE

omit [QuasiCompact p] [QuasiSeparated p] in
/-- Derived sheafification followed by the source functor of the projection-formula morphism
preserves `I`-indexed direct sums: both factors do. -/
theorem preservesColimitsOfShape_discrete_tildeD_comp_projectionFormulaSource (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (tildeD R ⋙ projectionFormulaSource p.toLRSHom.toShHom E) :=
  preservesColimitsOfShape_comp' (tildeD R) (projectionFormulaSource p.toLRSHom.toShHom E)
    (preservesColimitsOfShape_discrete_tildeD R I)
    (preservesColimitsOfShape_discrete_derivedTensorProductFunctor
      (Spec R).toRingedSpace.sheaf I ((derivedPushforward p.toLRSHom.toShHom).obj E))

include hE

/-- **[Stacks, Tag 08EU] at every derived sheafification over `Spec R`.**  For a quasi-compact
and quasi-separated `p : V ⟶ Spec R`, an `E` in `D_QCoh(𝒪_V)` and an arbitrary `M` in `D(R)`, the
projection-formula morphism of [Stacks, Tag 0B53] is invertible at `M^~`. -/
theorem isIso_projectionFormulaMap_tildeD_obj (M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso (projectionFormulaMap p.toLRSHom.toShHom E ((tildeD R).obj M)) := by
  refine isIso_app_of_devissage (tildeD R)
    (inferInstance : ((tilde.functor R).mapDerivedCategory).CommShift ℤ)
    (inferInstance : ((tilde.functor R).mapDerivedCategory).IsTriangulated)
    (projectionFormulaSource p.toLRSHom.toShHom E)
    (projectionFormulaTarget p.toLRSHom.toShHom E)
    ((canonicalDerivedTensorProduct (Spec R).toRingedSpace.sheaf).commShift_right _)
    (projectionFormulaTargetCommShift p.toLRSHom.toShHom E)
    ((canonicalDerivedTensorProduct (Spec R).toRingedSpace.sheaf).exact_right _)
    (projectionFormulaTarget_isTriangulated p.toLRSHom.toShHom E)
    (fun I => preservesColimitsOfShape_discrete_tildeD_comp_projectionFormulaSource R p E I)
    (fun I => preservesColimitsOfShape_discrete_tildeD_comp_projectionFormulaTarget R p E hE I)
    (projectionFormulaTransformation p.toLRSHom.toShHom E) (fun n => ?_) M
  exact isIso_projectionFormulaMap_of_iso_right p.toLRSHom.toShHom E
    (tildeDUnitShiftIso R n).symm
    (isIso_projectionFormulaMap_unitShift_unconditional p.toLRSHom.toShHom E n)

/-- **[Stacks, Tag 08EU] over an affine base of the form `Spec R`.**  For a quasi-compact and
quasi-separated morphism of schemes `p : V ⟶ Spec R`, an object `E` of `D_QCoh(𝒪_V)` and an
object `A` of `D_QCoh(𝒪_{Spec R})`, the projection-formula morphism of [Stacks, Tag 0B53]

`R p_* E ⊗^𝐋_{𝒪_{Spec R}} A ⟶ R p_*(E ⊗^𝐋_{𝒪_V} L p^* A)`

is an isomorphism.

This is the source's dévissage in `A`: both sides are exact functors of `A` commuting with
arbitrary direct sums, every object of `D_QCoh(𝒪_{Spec R})` is a derived sheafification by
[Stacks, Tag 06Z0], and at the shifts of the structure sheaf the morphism is invertible with no
hypothesis. -/
theorem isIso_projectionFormulaMap_of_spec
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)))
    (hA : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) j).obj
        A).IsQuasicoherent) :
    IsIso (projectionFormulaMap p.toLRSHom.toShHom E A) := by
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R A
    (fun j => hA j)
  exact isIso_projectionFormulaMap_of_iso_right p.toLRSHom.toShHom E eM
    (isIso_projectionFormulaMap_tildeD_obj R p E hE M)

end Main

end Stacks.Cohomology.DerivedProjectionFormula

end
