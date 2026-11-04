module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts

/-!
# Tensoring on the right in `D_QCoh(𝒪_X)` is exact and commutes with direct sums

Let `X` be a scheme and `M` an object of `D_QCoh(𝒪_X)`. The functor `K ↦ K ⊗ᴸ_{𝒪_X} M` of
`D_QCoh(𝒪_X)`, which is `tensorRight M` for the monoidal structure
`Stacks.Duality.quasiCoherentDerivedMonoidal`, commutes with the shift, carries distinguished
triangles to distinguished triangles, and commutes with direct sums indexed by the universe of
`X`. The source uses all three facts without comment ("the functors `Lf^*` and `⊗ᴸ` preserve
direct sums by construction", proof of [Stacks, Tag 08EU]; "compatible with distinguished
triangles", Equation 48.8.0.1 of [Stacks, Tag 0A9S]).

## Main results

* `Stacks.Duality.commShift_quasiCoherentDerivedTensorFlipObj`,
  `Stacks.Duality.isTriangulated_quasiCoherentDerivedTensorFlipObj` and
  `Stacks.Duality.preservesColimitsOfShape_quasiCoherentDerivedTensorFlipObj` — the three facts.

## Implementation notes

The functor is the restriction of `K ↦ K ⊗ᴸ_{𝒪_X} M` on `D(𝒪_X)` to the full subcategory, and
composing it with the inclusion gives the inclusion followed by the ambient functor, with
identity components (`quasiCoherentDerivedTensorFlipObjCompιIso`). On `D(𝒪_X)` the commutation
with the shift and the exactness are the fields `commShift₂` and `exact_left` of the derived
tensor product of [Stacks, Tag 06YU], and the commutation with direct sums is
`Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft`, read in the
first variable through the symmetry of [Stacks, Tag 0FPT]. All three pass to `D_QCoh` along the
fully faithful inclusion, which commutes with the shift and with direct sums.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable (X : Scheme.{u}) (M : quasiCoherentDerivedCategory X)

/-- Tensoring with `M` on the right, followed by the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, is the
inclusion followed by tensoring with `M` on the right in `D(𝒪_X)`; the components are
identities. -/
def quasiCoherentDerivedTensorFlipObjCompιIso :
    (quasiCoherentDerivedTensor X).flip.obj M ⋙
        (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        (derivedTensor X).flip.obj M.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} g =>
    (Category.comp_id _).trans ((quasiCoherentDerivedTensor_map_app_hom X g M).trans
      (Category.id_comp _).symm))

/-- `K ↦ K ⊗ᴸ M` on `D(𝒪_X)` commutes with the shift: the `commShift₂` field of the derived
tensor product of [Stacks, Tag 06YU]. -/
@[instance_reducible]
def commShiftDerivedTensorFlipObj (L : DerivedCategory X.Modules) :
    ((derivedTensor X).flip.obj L).CommShift ℤ :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).commShift_left L

/-- `K ↦ K ⊗ᴸ M` on `D(𝒪_X)` is exact: the `exact_left` field of the derived tensor product of
[Stacks, Tag 06YU]. -/
theorem isTriangulated_derivedTensorFlipObj (L : DerivedCategory X.Modules) :
    letI := commShiftDerivedTensorFlipObj X L
    ((derivedTensor X).flip.obj L).IsTriangulated :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).exact_left L

/-- **Tensoring on the right in `D_QCoh(𝒪_X)` commutes with the shift.** -/
instance commShift_quasiCoherentDerivedTensorFlipObj :
    ((quasiCoherentDerivedTensor X).flip.obj M).CommShift ℤ :=
  letI := commShiftDerivedTensorFlipObj X M.obj
  Functor.CommShift.ofComp (quasiCoherentDerivedTensorFlipObjCompιIso X M) ℤ

/-- **Tensoring on the right in `D_QCoh(𝒪_X)` is an exact functor.** -/
instance isTriangulated_quasiCoherentDerivedTensorFlipObj :
    ((quasiCoherentDerivedTensor X).flip.obj M).IsTriangulated := by
  let := commShiftDerivedTensorFlipObj X M.obj
  have : NatTrans.CommShift (quasiCoherentDerivedTensorFlipObjCompιIso X M).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have := isTriangulated_derivedTensorFlipObj X M.obj
  rw [Functor.isTriangulated_iff_comp_right (quasiCoherentDerivedTensorFlipObjCompιIso X M)]
  infer_instance

/-- `K ↦ K ⊗ᴸ L` on `D(𝒪_X)` commutes with direct sums indexed by the universe of `X`: the
monoidal structure of [Stacks, Tag 0FPT] is symmetric, and `L ⊗ᴸ -` commutes with direct sums. -/
theorem preservesColimitsOfShape_derivedTensorFlipObj (L : DerivedCategory X.Modules)
    (J : Type u) : PreservesColimitsOfShape (Discrete J) ((derivedTensor X).flip.obj L) := by
  let := Scheme.Modules.derivedMonoidal X
  let := Scheme.Modules.derivedSymmetric X
  have : PreservesColimitsOfShape (Discrete J) (tensorLeft L) :=
    Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft X.sheaf L J
  have : PreservesColimitsOfShape (Discrete J) (tensorRight L) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L)
  have e : curriedTensor (DerivedCategory X.Modules) ≅ derivedTensor X :=
    Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf
  have e' : tensorRight L ≅ (derivedTensor X).flip.obj L := ((flipFunctor _ _ _).mapIso e).app L
  exact preservesColimitsOfShape_of_natIso e'

/-- **Tensoring on the right in `D_QCoh(𝒪_X)` commutes with direct sums** indexed by the universe
of `X`. -/
instance preservesColimitsOfShape_quasiCoherentDerivedTensorFlipObj (J : Type u) :
    PreservesColimitsOfShape (Discrete J) ((quasiCoherentDerivedTensor X).flip.obj M) := by
  have := DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X J
  have := preservesColimitsOfShape_derivedTensorFlipObj X M.obj J
  have : PreservesColimitsOfShape (Discrete J) ((quasiCoherentDerivedTensor X).flip.obj M ⋙
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι) :=
    preservesColimitsOfShape_of_natIso (quasiCoherentDerivedTensorFlipObjCompιIso X M).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι

/-! ### The same, for `tensorRight M` of the monoidal category `D_QCoh(𝒪_X)` -/

/-- `tensorRight M` in the monoidal category `D_QCoh(𝒪_X)` commutes with the shift. -/
instance commShift_tensorRight_quasiCoherentDerivedMonoidal :
    (@MonoidalCategory.tensorRight _ _ (quasiCoherentDerivedMonoidal X) M).CommShift ℤ :=
  commShift_quasiCoherentDerivedTensorFlipObj X M

/-- **`tensorRight M` in the monoidal category `D_QCoh(𝒪_X)` is exact.** -/
instance isTriangulated_tensorRight_quasiCoherentDerivedMonoidal :
    (@MonoidalCategory.tensorRight _ _ (quasiCoherentDerivedMonoidal X) M).IsTriangulated :=
  isTriangulated_quasiCoherentDerivedTensorFlipObj X M

/-- **`tensorRight M` in the monoidal category `D_QCoh(𝒪_X)` commutes with direct sums** indexed
by the universe of `X`. -/
instance preservesColimitsOfShape_tensorRight_quasiCoherentDerivedMonoidal (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (@MonoidalCategory.tensorRight _ _ (quasiCoherentDerivedMonoidal X) M) :=
  preservesColimitsOfShape_quasiCoherentDerivedTensorFlipObj X M J

end Stacks.Duality
