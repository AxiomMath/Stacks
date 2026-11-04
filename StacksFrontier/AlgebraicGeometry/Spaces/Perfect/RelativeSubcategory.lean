module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocalDistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
import StacksCore.Tactic.StacksAttribute

/-!
# The objects of `D(𝒪_X)` perfect relative to a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally
of finite presentation.  The `Y`-perfect objects of `D(𝒪_X)` of Stacks 0DKN, packaged as a
property of the objects of `D(𝒪_X)`, form a strictly full, saturated, triangulated
subcategory.  This is Stacks 0DKR.

## Main definitions

* `AlgebraicGeometry.Space.isPerfectRelativeTo`: relative perfectness as a property of the
  objects of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`: the family of derived tensor
  products on the slices of the small étale site that the Tor clause is measured against,
  constructed by Stacks 06YU.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical`: relative perfectness measured against
  that family, so a property of `f` alone.

## Main results

* `AlgebraicGeometry.Space.isClosedUnderIsomorphisms_isPerfectRelativeTo`: relative
  perfectness is invariant under isomorphism in `D(𝒪_X)`, so the `Y`-perfect objects form a
  strictly full subcategory.
* `AlgebraicGeometry.Space.isSaturated_isPerfectRelativeTo`: both summands of a `Y`-perfect
  biproduct are `Y`-perfect, so the subcategory is saturated (thick).
* `AlgebraicGeometry.Space.containsZero_isPerfectRelativeTo` and
  `AlgebraicGeometry.Space.isStableUnderShift_isPerfectRelativeTo`: the subcategory contains a
  zero object and is stable under every shift.
* `AlgebraicGeometry.Space.isTriangulated_isPerfectRelativeTo`: the subcategory is
  triangulated, i.e. also closed under extensions.
* `AlgebraicGeometry.Space.isClosedUnderIsomorphisms_isPerfectRelativeToCanonical`,
  `isSaturated_`, `containsZero_`, `isStableUnderShift_` and
  `isTriangulated_isPerfectRelativeToCanonical`: the same five clauses for `f` itself, with the
  family of derived tensor products on the slices discharged.

## Implementation notes

Each closure property splits along the two clauses of relative perfectness.  Isomorphism
invariance transports the pseudo-coherent witness and, for the Tor clause, uses
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.of_iso` with the same covering and
interval.  Saturation is Stacks 08FW in the form
`AlgebraicGeometry.RingedSite.isPseudoCoherent_left_of_biprod_general`, with independent
universes since the small étale ringed site of `X` is `RingedSite.{u + 1, u, u}`, and a retract
argument for the Tor clause.  Triangulatedness is two-out-of-three in a distinguished triangle:
Stacks 08FV via `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_distinguished_general` and
Stacks 08G2 via
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_distinguished`.
Closure under extensions needs a common refinement of two coverings, and so the transport of
finite Tor dimension along an arrow of the site,
`Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.finiteTorDimensionRestricts`,
available because the small étale site is essentially `u`-small.

Finite Tor dimension on a slice is measured against a derived tensor product datum on it, so
every clause first takes the family `T` of Stacks 0DKN; the clauses are then restated at
`AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`, built by Stacks 06YU.  Saturation
needs, in addition, sheafification and a derived category on each slice of the small étale site
for `𝒪_X`-modules; these are hypotheses of the statement.

## References

* [Stacks Project, Tag 0DKR](https://stacks.math.columbia.edu/tag/0DKR)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 05RB](https://stacks.math.columbia.edu/tag/05RB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.ToposPushforward
open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

/-- An object property of a pretriangulated category which contains the zero object, is closed
under isomorphisms, and satisfies the first and third two-out-of-three rules *for triangles
whose middle vertex is a zero object*, is stable under all integer shifts. -/
private theorem isStableUnderShift_of_twoOutOfThree_isZero_obj₂ {C : Type*} [Category* C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (h₁ : ∀ T : Triangle C, T ∈ distinguishedTriangles → IsZero T.obj₂ →
      P T.obj₂ → P T.obj₃ → P T.obj₁)
    (h₃ : ∀ T : Triangle C, T ∈ distinguishedTriangles → IsZero T.obj₂ →
      P T.obj₁ → P T.obj₂ → P T.obj₃) :
    P.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro E hE
    induction n using Int.induction_on with
    | zero => exact P.prop_of_iso ((shiftFunctorZero C ℤ).symm.app E) hE
    | succ n hn =>
        exact P.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).symm.app E)
          (h₃ _ (contractible_distinguished₂ (E⟦(n : ℤ)⟧)) (isZero_zero C) hn P.prop_zero)
    | pred n hn =>
        apply h₁ (Triangle.mk (0 : E⟦-(n : ℤ) - 1⟧ ⟶ (0 : C)) 0
            (𝟙 ((E⟦-(n : ℤ) - 1⟧)⟦(1 : ℤ)⟧)))
          (contractible_distinguished₂ (E⟦-(n : ℤ) - 1⟧)) (isZero_zero C) P.prop_zero
        exact P.prop_of_iso
          ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app E) hn⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space

universe u d e

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

variable (f : X ⟶ Y)
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

variable
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over U) AddCommGrpCat.{u}]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- The objects of `D(𝒪_X)` perfect relative to `Y` (Stacks 0DKN), viewed as a property of the
objects of `D(𝒪_X)`. -/
def isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  fun E => IsPerfectRelativeTo B S hS f hflat hlfp T E

/-- An object of `D(𝒪_X)` satisfies `AlgebraicGeometry.Space.isPerfectRelativeTo` exactly when
it is perfect relative to `Y`. -/
theorem isPerfectRelativeTo_iff
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    isPerfectRelativeTo B S hS f hflat hlfp T E ↔
      IsPerfectRelativeTo B S hS f hflat hlfp T E :=
  Iff.rfl

/-- Pseudo-coherence of an object of `D(𝒪_X)` transports along an isomorphism. -/
private theorem isPseudoCoherent_of_iso
    {E E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (ε : E ≅ E')
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E' := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := h
  exact ⟨K, hK, ⟨eK ≪≫ ε⟩⟩

omit [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)] in
/-- Locally finite Tor dimension of an object of `D(f⁻¹𝒪_Y)` transports along an
isomorphism. -/
private theorem locallyHasFiniteTorDimension_of_iso
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    {F F' : RingedSite.DerivedModules.{u + 1, u, u, e} (inverseImageRingedSite B S hS f)}
    (ε : F ≅ F')
    (h : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T F) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T F' := by
  intro U
  obtain ⟨P, hP, hdata⟩ := h U
  refine ⟨P, hP, fun {V} g hg => ?_⟩
  obtain ⟨a, b, hab⟩ := hdata g hg
  exact ⟨a, b, hab.of_iso
    ((RingedSite.derivedRestriction.{u + 1, u, u, e}
      (inverseImageRingedSite B S hS f) V).mapIso ε)⟩

/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *strictly full* subcategory:
relative perfectness is invariant under isomorphism in `D(𝒪_X)`. -/
@[stacks 0DKR "isomorphism closure"]
theorem isClosedUnderIsomorphisms_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    (isPerfectRelativeTo B S hS f hflat hlfp T).IsClosedUnderIsomorphisms :=
  ⟨fun ε h => ⟨isPseudoCoherent_of_iso B S hS ε h.1,
    locallyHasFiniteTorDimension_of_iso B S hS f T
      ((derivedScalarRestriction B S hS f).mapIso ε) h.2⟩⟩

variable
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
    [hDerX : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasDerivedCategory.{d}
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).over U))]

/-- Pseudo-coherence passes to both summands of a pseudo-coherent biproduct in `D(𝒪_X)`
(Stacks 08FW). -/
private theorem isPseudoCoherent_of_biprod
    (K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) [HasBinaryBiproduct K L]
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent (K ⊞ L)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K ∧
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent L :=
  ⟨RingedSite.isPseudoCoherent_left_of_biprod_general _ K L h,
    RingedSite.isPseudoCoherent_right_of_biprod_general _ K L h⟩

omit [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)] hDerX in
/-- Locally finite Tor dimension passes to both summands of a biproduct of `D(f⁻¹𝒪_Y)`. -/
private theorem locallyHasFiniteTorDimension_of_biprod
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (F G : RingedSite.DerivedModules.{u + 1, u, u, e} (inverseImageRingedSite B S hS f))
    [HasBinaryBiproduct F G]
    (h : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T (F ⊞ G)) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T F ∧
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T G := by
  constructor <;> intro U <;> obtain ⟨P, hP, hdata⟩ := h U <;>
      refine ⟨P, hP, fun {V} g hg => ?_⟩ <;>
    · obtain ⟨a, b, hamp⟩ := hdata g hg
      refine ⟨a, b, fun N i hi => ?_⟩
      set R := RingedSite.derivedRestriction.{u + 1, u, u, e}
        (inverseImageRingedSite B S hS f) V with hR
      first
        | exact Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
            ((T V).tensorModule N ⋙
              DerivedCategory.homologyFunctor
                (RingedSite.Modules.{u + 1, u, u}
                  ((inverseImageRingedSite B S hS f).over V)) i)
            (R.map biprod.inl) (R.map biprod.fst)
            (by rw [← R.map_comp, biprod.inl_fst]; exact CategoryTheory.Functor.map_id _ _)
            (hamp N i hi)
        | exact Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
            ((T V).tensorModule N ⋙
              DerivedCategory.homologyFunctor
                (RingedSite.Modules.{u + 1, u, u}
                  ((inverseImageRingedSite B S hS f).over V)) i)
            (R.map biprod.inr) (R.map biprod.snd)
            (by rw [← R.map_comp, biprod.inr_snd]; exact CategoryTheory.Functor.map_id _ _)
            (hamp N i hi)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *saturated* (thick) subcategory: both
summands of a `Y`-perfect biproduct are `Y`-perfect. -/
@[stacks 0DKR "saturation"]
theorem isSaturated_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    (isPerfectRelativeTo B S hS f hflat hlfp T).IsSaturated := by
  let _ := isClosedUnderIsomorphisms_isPerfectRelativeTo B S hS f hflat hlfp T
  have key (K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) [HasBinaryBiproduct K L]
      (h : IsPerfectRelativeTo B S hS f hflat hlfp T (K ⊞ L)) :
      IsPerfectRelativeTo B S hS f hflat hlfp T K ∧
        IsPerfectRelativeTo B S hS f hflat hlfp T L := by
    have hpc := isPseudoCoherent_of_biprod B S hS K L h.1
    have hpres : PreservesBinaryBiproducts (derivedScalarRestriction B S hS f) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    have htor := locallyHasFiniteTorDimension_of_biprod B S hS f T
      ((derivedScalarRestriction B S hS f).obj K) ((derivedScalarRestriction B S hS f).obj L)
      (locallyHasFiniteTorDimension_of_iso B S hS f T
        ((derivedScalarRestriction B S hS f).mapBiprod K L) h.2)
    exact ⟨⟨hpc.1, htor.1⟩, ⟨hpc.2, htor.2⟩⟩
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
  · exact (key _ _ h).1
  · exact (key _ _ h).2

open Stacks.SheafOfModules.DerivedTensorProduct

omit hDerX in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` contain a zero object. -/
@[stacks 0DKR "contains a zero object"]
theorem containsZero_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    (isPerfectRelativeTo B S hS f hflat hlfp T).ContainsZero :=
  ⟨⟨0, isZero_zero _,
    ⟨RingedSite.isPseudoCoherent_of_isZero_general (smallEtaleRingedSite B S hS X.1 X.2) 0
        (isZero_zero _),
      Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_isZero T
        ((derivedScalarRestriction B S hS f).map_isZero (isZero_zero _))⟩⟩⟩

omit hDerX in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` are stable under every shift `E ↦ E[n]`. -/
@[stacks 0DKR "closure under the shifts"]
theorem isStableUnderShift_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    (isPerfectRelativeTo B S hS f hflat hlfp T).IsStableUnderShift ℤ := by
  let _ := isClosedUnderIsomorphisms_isPerfectRelativeTo B S hS f hflat hlfp T
  let _ := containsZero_isPerfectRelativeTo B S hS f hflat hlfp T
  have hzeroTor (tri : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
      (hzero : IsZero tri.obj₂) (V : (inverseImageRingedSite B S hS f).C) :
      Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension (T V)
        ((RingedSite.derivedRestriction.{u + 1, u, u, e}
          (inverseImageRingedSite B S hS f) V).obj
            (((derivedScalarRestriction B S hS f).mapTriangle.obj tri).obj₂)) :=
    Stacks.SheafOfModules.DerivedTensorProduct.forall_hasFiniteTorDimension_of_isZero T
      ((derivedScalarRestriction B S hS f).map_isZero hzero) V
  refine ObjectProperty.isStableUnderShift_of_twoOutOfThree_isZero_obj₂ _ ?_ ?_
  · intro tri htri hzero h₂ h₃
    refine ⟨(RingedSite.isPseudoCoherent_of_distinguished_general _ tri htri).2.2 h₂.1 h₃.1, ?_⟩
    exact (locallyHasFiniteTorDimension_of_distinguished_obj₂_forall T _
      (Functor.map_distinguished (derivedScalarRestriction B S hS f) tri htri)
      (hzeroTor tri hzero)).2 h₃.2
  · intro tri htri hzero h₁ h₂
    refine ⟨(RingedSite.isPseudoCoherent_of_distinguished_general _ tri htri).1 h₁.1 h₂.1, ?_⟩
    exact (locallyHasFiniteTorDimension_of_distinguished_obj₂_forall T _
      (Functor.map_distinguished (derivedScalarRestriction B S hS f) tri htri)
      (hzeroTor tri hzero)).1 h₁.2

variable
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).obj M).Additive]
    [∀ (K L : CochainComplex
        (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
        (ComplexShape.up ℤ)]

/-- The small étale site of `X` is essentially `u`-small (Stacks 03ED), restated for the
projection of `AlgebraicGeometry.Space.inverseImageRingedSite`, which instance search does not
unfold. -/
local instance essentiallySmall_inverseImageRingedSite :
    EssentiallySmall.{u} (inverseImageRingedSite B S hS f).C :=
  inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS X.1))

omit hDerX in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *triangulated* subcategory: the
property contains a zero object, is stable under all shifts, and is closed under extensions,
for a given family `T` of derived tensor products on the slices. -/
@[stacks 0DKR "closure under cones: the Y-perfect objects form a triangulated subcategory. \
The zero object and the shifts are `containsZero_isPerfectRelativeTo` and \
`isStableUnderShift_isPerfectRelativeTo`", sga "6 I 5.8.4" "5.8.4 a), special case"]
theorem isTriangulated_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U)) :
    (isPerfectRelativeTo B S hS f hflat hlfp T).IsTriangulated := by
  have hres : Stacks.SheafOfModules.DerivedTensorProduct.FiniteTorDimensionRestricts T :=
    Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.finiteTorDimensionRestricts
      (inverseImageRingedSite B S hS f) T
  let _ := isClosedUnderIsomorphisms_isPerfectRelativeTo B S hS f hflat hlfp T
  let _ := containsZero_isPerfectRelativeTo B S hS f hflat hlfp T
  let _ := isStableUnderShift_isPerfectRelativeTo B S hS f hflat hlfp T
  have key (tri : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
      (htri : tri ∈ distinguishedTriangles)
      (h₁ : IsPerfectRelativeTo B S hS f hflat hlfp T tri.obj₁)
      (h₃ : IsPerfectRelativeTo B S hS f hflat hlfp T tri.obj₃) :
      IsPerfectRelativeTo B S hS f hflat hlfp T tri.obj₂ := by
    refine ⟨(RingedSite.isPseudoCoherent_of_distinguished_general _ tri htri).2.1 h₁.1 h₃.1, ?_⟩
    exact (locallyHasFiniteTorDimension_of_distinguished T hres _
      (Functor.map_distinguished (derivedScalarRestriction B S hS f) tri htri)).2.1 h₁.2 h₃.2
  exact { ext₂' := fun tri htri h₁ h₃ =>
    ObjectProperty.le_isoClosure _ _ (key tri htri h₁ h₃) }

/-! ### The five clauses for an actual morphism `f : X ⟶ Y`, with no parameter left -/

/-- The canonical family of derived tensor products on the slices of
`AlgebraicGeometry.Space.inverseImageRingedSite`: on the slice over `U` it is
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU. -/
def canonicalSliceDerivedTensorProduct :
    ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U) :=
  fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
    ((inverseImageRingedSite B S hS f).over U)

/-- An object `E` of `D(𝒪_X)` is *perfect relative to `Y`* (Stacks 0DKN) when it is
pseudo-coherent and, read through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, locally has
finite Tor dimension, measured against
`AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`. -/
abbrev IsPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  IsPerfectRelativeTo B S hS f hflat hlfp (canonicalSliceDerivedTensorProduct B S hS f) E

/-- The `Y`-perfect objects of `D(𝒪_X)`, as a property of the objects of `D(𝒪_X)`, with the
family of derived tensor products on the slices discharged by Stacks 06YU. -/
def isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  isPerfectRelativeTo B S hS f hflat hlfp (canonicalSliceDerivedTensorProduct B S hS f)

omit hDerX [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
      (ComplexShape.up ℤ)] in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *strictly full* subcategory. -/
@[stacks 0DKR "isomorphism closure, for an actual f"]
theorem isClosedUnderIsomorphisms_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    (isPerfectRelativeToCanonical B S hS f hflat hlfp).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_isPerfectRelativeTo B S hS f hflat hlfp _

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
      (ComplexShape.up ℤ)] in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *saturated* (thick) subcategory. -/
@[stacks 0DKR "saturation, for an actual f"]
theorem isSaturated_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    (isPerfectRelativeToCanonical B S hS f hflat hlfp).IsSaturated :=
  isSaturated_isPerfectRelativeTo B S hS f hflat hlfp _

omit hDerX [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
      (ComplexShape.up ℤ)] in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` contain a zero object. -/
@[stacks 0DKR "contains a zero object, for an actual f"]
theorem containsZero_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    (isPerfectRelativeToCanonical B S hS f hflat hlfp).ContainsZero :=
  containsZero_isPerfectRelativeTo B S hS f hflat hlfp _

omit hDerX [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (inverseImageRingedSite B S hS f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
      (ComplexShape.up ℤ)] in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` are stable under every shift. -/
@[stacks 0DKR "closure under the shifts, for an actual f"]
theorem isStableUnderShift_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    (isPerfectRelativeToCanonical B S hS f hflat hlfp).IsStableUnderShift ℤ :=
  isStableUnderShift_isPerfectRelativeTo B S hS f hflat hlfp _

omit hDerX in
/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, the `Y`-perfect objects of `D(𝒪_X)` form a *triangulated* subcategory: the
property contains a zero object, is stable under all shifts, and is closed under extensions. -/
@[stacks 0DKR "closure under cones for an actual f: the Y-perfect objects of D(O_X) form a \
triangulated subcategory. The zero object and the shifts are \
`containsZero_isPerfectRelativeToCanonical` and \
`isStableUnderShift_isPerfectRelativeToCanonical`"]
theorem isTriangulated_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    (isPerfectRelativeToCanonical B S hS f hflat hlfp).IsTriangulated :=
  isTriangulated_isPerfectRelativeTo B S hS f hflat hlfp _

end AlgebraicGeometry.Space

end
