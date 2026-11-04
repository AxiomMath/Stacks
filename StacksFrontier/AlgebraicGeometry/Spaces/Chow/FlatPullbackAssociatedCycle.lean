module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackClosedSubspaceMultiplicity
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion

/-!
# Flat pullback of the cycle of a closed subspace and of a coherent module

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be flat of relative
dimension `r`. This file proves **Stacks 0EPB**:

1. for a closed subspace `Z ⊆ Y` with `dim_δ(Z) ≤ k` one has `dim_δ(f^{-1}(Z)) ≤ k + r` and
   `[f^{-1}(Z)]_{k+r} = f^*[Z]_k` in `Z_{k+r}(X)`;
2. for a coherent `𝒪_Y`-module `F` with `dim_δ(Supp(F)) ≤ k` one has
   `dim_δ(Supp(f^*F)) ≤ k + r` and `f^*[F]_k = [f^*F]_{k+r}` in `Z_{k+r}(X)`.

## Main results

* `AlgebraicGeometry.Space.geometricLength_unit_preimage_eq_mul`: for a closed subspace
  `Z ⊆ Y` and a geometric point `z̄` of `f^{-1}(Z)` lying over `x̄` in `X`, the length of
  `𝒪_{f^{-1}(Z)}` at `z̄` is the length of `𝒪_Z` at the image of `z̄` times the length of
  `𝒪_{X, x̄}/𝔪_{f(x̄)}𝒪_{X, x̄}`.
* `AlgebraicGeometry.Space.flatPullback_closedSubspaceCycle_preimage`: **Stacks 0EPB, part (1)**.
* `AlgebraicGeometry.Space.flatPullback_associatedCycle_modulePullback`:
  **Stacks 0EPB, part (2)**.

## Implementation notes

The source compares, at an integral closed subspace `W' ⊆ X` lying over the generic point of a
component `W` of the support, the coefficients of the two cycles as lengths of local rings at a
pair of points of étale charts, and concludes with Algebra, Lemma 10.52.13 (Stacks 02M1). Here
the same comparison is made at a geometric point `x̄` of `X` over the generic point of `W'`,
whose étale local ring `𝒪_{X, x̄}` is flat and local over `𝒪_{Y, f(x̄)}` (Stacks 04NG).

* For a module the comparison is
  `AlgebraicGeometry.Space.geometricLength_mul_length_quotient_extendedMaximalIdeal`, Stacks 02M1
  read through the base-change formula of Stacks 05VQ for the geometric stalk of `f^*F`.
* For a closed subspace `Z` the étale local ring of `f^{-1}(Z)` at a geometric point `z̄` is the
  tensor product `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Z, z̄}`: the canonical homomorphism from the tensor
  product is flat by `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat` (the square
  `f^{-1}(Z) → Z, X → Y` is cartesian by Stacks 083Q), surjective because
  `𝒪_{X, x̄} → 𝒪_{f^{-1}(Z), z̄}` is (a closed immersion), and a flat surjective local
  homomorphism of local rings is bijective. Then Stacks 02M1 applies to the `𝒪_{Y, ȳ}`-module
  `𝒪_{Z, z̄}`. This is the fact `f^*𝒪_Z = 𝒪_{f^{-1}(Z)}` used by the source, read at a geometric
  point.

For `W` integral and `ȳ` over its generic point the length of `𝒪_W` at the image of `z̄` is one,
`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_one_of_isIntegralSpace`, so the
multiplicity of `W'` in `f^{-1}(W)`, which is the coefficient of `W'` in `f^*[W]` by
part (1) of Stacks 0EP8, is the length of `𝒪_{X, x̄}/𝔪_{ȳ}𝒪_{X, x̄}`. Both cycle identities then
follow coefficientwise; the sum defining the flat pullback has at most one nonzero term, at the
component of the support through the image of the generic point of `W'`.

## References

* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Space

/-! ### The length of the structure sheaf of an inverse image -/

/-- The image of a geometric point under a composite is the image of its image. -/
private theorem geometricPointMap_comp_aux {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    (z : GeometricPoint B S hS F) :
    geometricPointMap (α ≫ β) z = geometricPointMap β (geometricPointMap α z) :=
  rfl

section Algebra

/-- **The length of a flat quotient of a base change.** Let `A → R` be a flat local homomorphism
of local rings, let `C` be a quotient of `A` and let `R'` be a quotient of `R`. If a ring
homomorphism `φ : R ⊗_A C → R'` restricting to the quotient map on `R` is flat, then

`length_{R'}(R') = length_C(C) · length_R(R/𝔪_A R)`.

The tensor product is a quotient of `R`, hence local, and `φ` is surjective, so `φ` is a flat
surjective local homomorphism of local rings, hence bijective; the identity is then Stacks 02M1
for the `A`-module `C`. -/
@[ega "IV 2.5.5.3" "Case M = A/I (cyclic)"]
theorem length_self_eq_length_mul_of_tensor_flat {A R C R' : Type v} [CommRing A] [CommRing R]
    [CommRing C] [CommRing R'] [Algebra A R] [Algebra A C] [Algebra R R'] [IsLocalRing A]
    [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hC : Function.Surjective (algebraMap A C)) (hR' : Function.Surjective (algebraMap R R'))
    (φ : R ⊗[A] C →+* R') (hφ : ∀ a : R, φ (a ⊗ₜ 1) = algebraMap R R' a) (hflat : φ.Flat) :
    Module.length R' R' =
      Module.length C C * Module.length R (R ⧸ extendedMaximalIdeal A R) := by
  have hL : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[A] C) :=
    Algebra.TensorProduct.includeLeft_surjective (S := R) _ hC
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a, rfl⟩ := hR' w
    exact ⟨a ⊗ₜ 1, hφ a⟩
  have : Nontrivial (R ⊗[A] C) := hφsurj.nontrivial
  have : IsLocalRing (R ⊗[A] C) := IsLocalRing.of_surjective' _ hL
  have : IsLocalHom φ := IsLocalHom.of_surjective φ hφsurj
  have hbij : Function.Bijective φ := AlgebraicGeometry.bijective_of_flat_of_surjective φ hflat
    hφsurj
  let e : (R ⊗[A] C) ≃ₗ[R] R' :=
    LinearEquiv.ofBijective
      { toFun := φ
        map_add' := map_add φ
        map_smul' := fun a t => by
          show φ (a • t) = a • φ t
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hφ a]
          rfl } hbij
  rw [← Module.length_eq_of_surjective (S := R) (R := R') (M := R') hR', ← e.length_eq,
    ← length_baseChange_eq_length_mul_length_quotient,
    Module.length_eq_of_surjective (S := A) (R := C) (M := C) hC]

end Algebra

section Length

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure sheaf of an inverse image closed subspace, at a geometric point.** Let
`f : X ⟶ Y` be a flat morphism of algebraic spaces, let `Z ⊆ Y` be a closed subspace and let
`z̄` be a geometric point of `f^{-1}(Z)` with image `x̄` in `X`. Then

`length(𝒪_{f^{-1}(Z)} at z̄) = length(𝒪_Z at f(z̄)) · length(𝒪_{X, x̄}/𝔪_{f(x̄)}𝒪_{X, x̄})`.

The square `f^{-1}(Z) → Z, X → Y` is cartesian (Stacks 083Q), so the canonical homomorphism
`𝒪_{X, x̄} ⊗_{𝒪_{Y, f(x̄)}} 𝒪_{Z, f(z̄)} → 𝒪_{f^{-1}(Z), z̄}` is flat
(`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`); both closed immersions are
surjective on étale local rings, and
`AlgebraicGeometry.Space.length_self_eq_length_mul_of_tensor_flat` applies. -/
theorem geometricLength_unit_preimage_eq_mul {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFlat B S hS f) (Z : Subfunctor Y) (hZ : IsClosedSubspace B S hS Z)
    (z : GeometricPoint B S hS (Z.preimage f).toFunctor) (x : GeometricPoint B S hS X)
    (hx : geometricPointMap (Z.preimage f).ι z = x) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Y (geometricPointMap f x)) :=
      isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f x)
    geometricLength B S hS
        ⟨(Z.preimage f).toFunctor, (isClosedSubspace_preimage B S hS f Z hY hX hZ).1⟩ z
        (SheafOfModules.unit _) =
      geometricLength B S hS ⟨Z.toFunctor, hZ.1⟩ (geometricPointMap (Z.fromPreimage f) z)
          (SheafOfModules.unit _) *
        Module.length ↥(etaleLocalRing B S hS X x)
          (↥(etaleLocalRing B S hS X x) ⧸
            Ideal.map (etaleLocalRingMap hX f x)
              (maximalIdeal ↥(etaleLocalRing B S hS Y (geometricPointMap f x)))) := by
  subst hx
  have hP := isClosedSubspace_preimage B S hS f Z hY hX hZ
  have hpb0 : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ.1⟩)
      (ObjectProperty.homMk (Z.preimage f).ι :
        (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f Z)
  have hcart := cartesian_etaleStalk_tensor_flat B S hS _ _ _ _ hpb0.flip z
  dsimp only [IsEtaleStalkTensorFlat] at hcart
  obtain ⟨φ, hφl, -, hφflat⟩ := hcart
  have hw : geometricPointMap f (geometricPointMap (Z.preimage f).ι z) =
      geometricPointMap Z.ι (geometricPointMap (Z.fromPreimage f) z) := by
    rw [← geometricPointMap_comp_aux, ← geometricPointMap_comp_aux,
      Subfunctor.fromPreimage_ι]
  let : IsLocalRing ↥(etaleLocalRing B S hS Y
      (geometricPointMap f (geometricPointMap (Z.preimage f).ι z))) :=
    isLocalRing_etaleLocalRing B S hS Y hY _
  let : IsLocalRing ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z)) :=
    isLocalRing_etaleLocalRing B S hS X hX _
  let : IsLocalRing ↥(etaleLocalRing B S hS (Z.preimage f).toFunctor z) :=
    isLocalRing_etaleLocalRing B S hS _ hP.1 z
  let : Algebra
      ↥(etaleLocalRing B S hS Y (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z)) :=
    (etaleLocalRingMap hX f (geometricPointMap (Z.preimage f).ι z)).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS Z.toFunctor (geometricPointMap (Z.fromPreimage f) z)) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y) hw) ≫
      CommRingCat.ofHom
        (etaleLocalRingMap hZ.1 Z.ι (geometricPointMap (Z.fromPreimage f) z))).hom).toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z))
      ↥(etaleLocalRing B S hS (Z.preimage f).toFunctor z) :=
    (etaleLocalRingMap hP.1 (Z.preimage f).ι z).toAlgebra
  have : Module.Flat
      ↥(etaleLocalRing B S hS Y (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z)) :=
    flat_etaleLocalRingMap B S hS hX hY f hf _
  have : IsLocalHom (algebraMap
      ↥(etaleLocalRing B S hS Y (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z))) :=
    isLocalHom_etaleLocalRingMap B S hS hX hY f _
  have hγsurj : Function.Surjective (algebraMap
      ↥(etaleLocalRing B S hS X (geometricPointMap (Z.preimage f).ι z))
      ↥(etaleLocalRing B S hS (Z.preimage f).toFunctor z)) :=
    surjective_etaleLocalRingMap_of_isClosedImmersion B S hS
      (ObjectProperty.homMk (Z.preimage f).ι :
        (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hP.2 z
  have hβsurj : Function.Surjective (algebraMap
      ↥(etaleLocalRing B S hS Y (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS Z.toFunctor (geometricPointMap (Z.fromPreimage f) z))) := by
    have h1 := surjective_etaleLocalRingMap_of_isClosedImmersion B S hS
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) hZ.2
      (geometricPointMap (Z.fromPreimage f) z)
    have h2 := (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (etaleLocalRing B S hS Y) hw))).2
    exact h1.comp h2
  rw [geometricLength, geometricLength,
    (structureSheafGeometricStalkEquiv B S hS ⟨(Z.preimage f).toFunctor, hP.1⟩ z).length_eq,
    (structureSheafGeometricStalkEquiv B S hS ⟨Z.toFunctor, hZ.1⟩
      (geometricPointMap (Z.fromPreimage f) z)).length_eq]
  exact length_self_eq_length_mul_of_tensor_flat hβsurj hγsurj φ
    (fun a => RingHom.congr_fun hφl a) hφflat

end Length

/-! ### Points over the generic point of an integral closed subspace -/

section Points

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

attribute [local instance] pointTopology

/-- The generic point of an integral closed subspace lies in the set of generic points of its
own point space. -/
theorem IntegralClosedSubspace.genericPoint_mem_genericPoints
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    W.genericPoint D.site D.base D.base_mem ∈
      genericPoints (points D.site D.base D.base_mem W.subspace.toFunctor) := by
  let := W.irreducibleSpace_points D.site D.base D.base_mem
  show closure {W.genericPoint D.site D.base D.base_mem} ∈ irreducibleComponents _
  rw [W.closure_singleton_genericPoint D.site D.base D.base_mem]
  exact ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ => Set.subset_univ _⟩

/-- An integral closed subspace whose generic point lies in a closed set of points is contained
in that set. -/
theorem IntegralClosedSubspace.subspacePointSet_subset_of_ambientGenericPoint_mem
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    {T : Set (points D.site D.base D.base_mem Y)} (hT : IsClosed T)
    (hW : W.ambientGenericPoint D.site D.base D.base_mem ∈ T) :
    subspacePointSet D.site D.base D.base_mem Y W.subspace ⊆ T := by
  rw [← (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY).def]
  exact hT.closure_subset_iff.2 (Set.singleton_subset_iff.2 hW)

/-- The integral closed subspace attached to an irreducible component `C` of a closed set of
points, when `η` is the generic point of `C`, has `η` for its generic point. -/
theorem ambientGenericPoint_closedSetComponent (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T)
    (C : irreducibleComponents T) (η : points D.site D.base D.base_mem Y) (hη : η ∈ T)
    (hC : IsGenericPoint (⟨η, hη⟩ : T) C.1) :
    (closedSetComponent D.site D.base D.base_mem hY hYdec T hT C).ambientGenericPoint
      D.site D.base D.base_mem = η := by
  have hgen : IsGenericPoint η (subspacePointSet D.site D.base D.base_mem Y
      (closedSetComponent D.site D.base D.base_mem hY hYdec T hT C).subspace) := by
    rw [subspacePointSet_closedSetComponent]
    have h := hT.isClosedEmbedding_subtypeVal.closure_image_eq ({⟨η, hη⟩} : Set T)
    rw [Set.image_singleton, hC.def] at h
    exact h
  exact (eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hY _ η hgen).symm

/-- **The component through a generic point is unique.** Let `C` be an irreducible component of
a closed set of points `T` with generic point `η`. An integral closed subspace whose point set is
an irreducible component of `T` and contains `η` is the subspace attached to `C`. -/
theorem eq_closedSetComponent_of_mem (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T)
    (C : irreducibleComponents T) (η : points D.site D.base D.base_mem Y) (hη : η ∈ T)
    (hC : IsGenericPoint (⟨η, hη⟩ : T) C.1)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (C' : irreducibleComponents T)
    (hW : subspacePointSet D.site D.base D.base_mem Y W.subspace = Subtype.val '' (C' : Set T))
    (hηW : η ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace) :
    W = closedSetComponent D.site D.base D.base_mem hY hYdec T hT C := by
  have hmem : (⟨η, hη⟩ : T) ∈ (C' : Set T) := by
    rw [hW] at hηW
    obtain ⟨p, hp, hpe⟩ := hηW
    have : p = ⟨η, hη⟩ := Subtype.ext hpe
    exact this ▸ hp
  have hC'cl : IsClosed (C' : Set T) := isClosed_of_mem_irreducibleComponents _ C'.2
  have hle : (C : Set T) ⊆ (C' : Set T) := by
    rw [← hC.def]
    exact hC'cl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  have hCC : (C : Set T) = (C' : Set T) := le_antisymm hle (C.2.2 C'.2.1 hle)
  refine (eq_closedSetComponent D.site D.base D.base_mem hY hYdec T hT C W ?_).symm
  rw [hW, hCC]

/-- **The image of the generic point of a subspace of dimension `k + r`.** Let `f : X ⟶ Y` be a
morphism of good spaces of relative dimension `r`, let `T ⊆ |Y|` be a closed set of
`δ`-dimension at most `k`, and let `W' ⊆ X` be an integral closed subspace of δ-dimension
`k + r` whose generic point maps into `T`. Then the image `η` of that generic point has
`δ(η) = k`, so it is the generic point of an irreducible component of `T`. -/
theorem exists_isGenericPoint_image (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ)
    (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T)
    (hTk : deltaDimensionClosed D sY hY T hT ≤ (k : EInt))
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW' : deltaDimension D sX W' = k + (r : ℤ))
    (hη : pointsMap D.site D.base D.base_mem X f
      (W'.ambientGenericPoint D.site D.base D.base_mem) ∈ T) :
    inducedDimensionValue D.site D.base D.base_mem D.delta sY
        (pointsMap D.site D.base D.base_mem X f
          (W'.ambientGenericPoint D.site D.base D.base_mem)) = k ∧
      ∃ C : irreducibleComponents T, IsGenericPoint (⟨_, hη⟩ : T) C.1 := by
  have hupper := (deltaDimensionClosed_le_coe_iff D sY hY T hT k).1 hTk _ hη
  have hle := inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr
    (W'.ambientGenericPoint D.site D.base D.base_mem)
  have hval : inducedDimensionValue D.site D.base D.base_mem D.delta sX
      (W'.ambientGenericPoint D.site D.base D.base_mem) = k + (r : ℤ) := hW'
  have heq : inducedDimensionValue D.site D.base D.base_mem D.delta sY
      (pointsMap D.site D.base D.base_mem X f
        (W'.ambientGenericPoint D.site D.base D.base_mem)) = k := by omega
  exact ⟨heq, isGenericPoint_of_deltaDimensionClosed_le D sY hY T hT _ hη k hTk heq⟩

/-- An integral closed subspace of `X` whose generic point lies in a closed subspace `Y' ⊆ X` is
the image of an integral closed subspace of `Y'`. -/
theorem exists_closedSubspaceComponentImage_eq_of_mem (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y' : Subfunctor X) (hY' : IsClosedSubspace D.site D.base D.base_mem Y')
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : W.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X Y') :
    ∃ V : IntegralClosedSubspace D.site D.base D.base_mem Y'.toFunctor,
      closedSubspaceComponentImage D sX hX Y' hY' V = W :=
  IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY'.1
    (D.isDecentSpace_of_isGood sX hX)
    (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sX hX) hY') hY'.2 W
    (W.subspacePointSet_subset_of_ambientGenericPoint_mem D hX.1
      (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y' hY') hW)

/-- The generic point of the image of an integral closed subspace of a closed subspace `Y' ⊆ X`
is the image of its generic point. -/
theorem ambientGenericPoint_closedSubspaceComponentImage (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y' : Subfunctor X) (hY' : IsClosedSubspace D.site D.base D.base_mem Y')
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y'.toFunctor) :
    (closedSubspaceComponentImage D sX hX Y' hY' V).ambientGenericPoint
        D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem Y'.toFunctor Y'.ι
        (V.ambientGenericPoint D.site D.base D.base_mem) :=
  IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hX.1 hY'.1
    (D.isDecentSpace_of_isGood sX hX) hY'.2 V

/-- A point of a closed subspace is determined by its image in the ambient space. -/
theorem pointsMap_ι_injective (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Y' : Subfunctor X) (hY' : IsClosedSubspace D.site D.base D.base_mem Y') :
    Function.Injective (pointsMap D.site D.base D.base_mem Y'.toFunctor Y'.ι) :=
  (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX hY'.2).injective

end Points

/-! ### The cycle of the inverse image of an integral closed subspace -/

section Mult

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **The coefficient of `W'` in `f^*[W]` is a length of an étale local ring.** Let
`W ⊆ Y` be an integral closed subspace, let `V ⊆ f^{-1}(W)` be an integral closed subspace whose
image `W'` in `X` has δ-dimension `dim_δ(W) + r` and whose generic point maps to the generic point
of `W`, and let `z̄` be a geometric point of `f^{-1}(W)` over the generic point of `V`, with image
`x̄` in `X`. Then the coefficient of `W'` in `f^*[W]` is
`length_{𝒪_{X, x̄}}(𝒪_{X, x̄}/𝔪_{f(x̄)}𝒪_{X, x̄})`. -/
theorem flatPullbackMult_eq_toNat_length
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : deltaDimension D sX (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V) =
        deltaDimension D sY W + (r : ℤ))
    (z : GeometricPoint D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hz : z.image = V.ambientGenericPoint D.site D.base D.base_mem)
    (hgen : pointsMap D.site D.base D.base_mem X f
        (pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι
          (V.ambientGenericPoint D.site D.base D.base_mem)) =
      W.ambientGenericPoint D.site D.base D.base_mem) :
    letI : IsLocalRing ↥(etaleLocalRing D.site D.base D.base_mem Y
        (geometricPointMap f (geometricPointMap (W.subspace.preimage f).ι z))) :=
      isLocalRing_etaleLocalRing D.site D.base D.base_mem Y hY.1 _
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W
        (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V) =
      ((Module.length ↥(etaleLocalRing D.site D.base D.base_mem X
          (geometricPointMap (W.subspace.preimage f).ι z))
        (↥(etaleLocalRing D.site D.base D.base_mem X
            (geometricPointMap (W.subspace.preimage f).ι z)) ⧸
          Ideal.map (etaleLocalRingMap hX.1 f (geometricPointMap (W.subspace.preimage f).ι z))
            (maximalIdeal ↥(etaleLocalRing D.site D.base D.base_mem Y
              (geometricPointMap f (geometricPointMap (W.subspace.preimage f).ι z)))))).toNat :
        ℤ) := by
  have hcoeff : flatPullbackMult D sX hX sY hY f hbase r hflat hr W
      (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V) =
      closedSubspaceMultiplicity D (W.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V := by
    unfold flatPullbackMult flatPullbackIntegralCycle
    rw [closedSubspaceCycle_apply_closedSubspaceComponentImage, ite_eq_left hV]
    rfl
  rw [hcoeff, closedSubspaceMultiplicity_eq_toNat_geometricLength D _
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V z hz,
    geometricLength_unit_preimage_eq_mul D.site D.base D.base_mem hX.1 hY.1 f hflat W.subspace
      W.isClosedSubspace z _ rfl]
  have hone : geometricLength D.site D.base D.base_mem ⟨W.subspace.toFunctor,
      W.isClosedSubspace.1⟩ (geometricPointMap (W.subspace.fromPreimage f) z)
        (SheafOfModules.unit _) = 1 := by
    refine geometricLength_structureSheafModule_eq_one_of_isIntegralSpace D.site D.base D.base_mem
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ W.isIntegralSpace _ ?_
    have himg : (geometricPointMap (W.subspace.fromPreimage f) z).image =
        W.genericPoint D.site D.base D.base_mem := by
      refine (IntegralClosedSubspace.isClosedEmbedding_pointsMap D.site D.base D.base_mem hY.1
        W).injective ?_
      have e : pointsMap D.site D.base D.base_mem _ W.subspace.ι
          (geometricPointMap (W.subspace.fromPreimage f) z).image =
          W.ambientGenericPoint D.site D.base D.base_mem := by
        rw [geometricPointMap_image, hz, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι,
          pointsMap_comp_apply, hgen]
      exact e
    rw [himg]
    exact W.genericPoint_mem_genericPoints D
  rw [hone, one_mul]

end Mult

/-! ### Stacks 0EPB -/

section Main

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A term of the sum defining `f^*α` vanishes when the δ-dimension of the subspace of `X` is not
`m + r`. -/
private theorem flatPullbackTerm_eq_zero_of_deltaDimension_ne (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (m : ℤ) (α : CycleGroup D sY m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T ≠ m + (r : ℤ))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  exact hT (by rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat
    hr W T h2, α.2.2 W h1])

/-- The sum defining `f^*α` at `T` vanishes when the image of the generic point of `T` lies
outside a set `S` containing the point set of every `W` with a nonzero coefficient. -/
private theorem finsum_flatPullbackMult_eq_zero_of_not_mem (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (S : Set (points D.site D.base D.base_mem Y))
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (hc : ∀ W, c W ≠ 0 → subspacePointSet D.site D.base D.base_mem Y W.subspace ⊆ S)
    (hη : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∉ S) :
    ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      c W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  exact hη (hc W h1 (mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
    hflat hr W T h2))

/-- The sum defining `f^*α` at `T` has a single term, at the component `W₀` of a closed set `S`
through the image of the generic point of `T`, when the point set of every `W` with a nonzero
coefficient is an irreducible component of `S`. -/
private theorem finsum_flatPullbackMult_eq_single (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (S : Set (points D.site D.base D.base_mem Y)) (hS : IsClosed S)
    (C : irreducibleComponents S)
    (hη : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈ S)
    (hC : IsGenericPoint (⟨_, hη⟩ : S) C.1)
    (W₀ : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW₀ : W₀ = closedSetComponent D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) S hS C)
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (hc : ∀ W, c W ≠ 0 → ∃ C' : irreducibleComponents S,
      subspacePointSet D.site D.base D.base_mem Y W.subspace = Subtype.val '' (C' : Set S)) :
    ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      c W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T =
    c W₀ * flatPullbackMult D sX hX sY hY f hbase r hflat hr W₀ T := by
  refine finsum_eq_single _ W₀ fun W hW => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  obtain ⟨C', hC'⟩ := hc W h1
  exact hW (hW₀ ▸ eq_closedSetComponent_of_mem D hY.1 (D.isDecentSpace_of_isGood sY hY) S hS C _
    hη hC W C' hC' (mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r
      hflat hr W T h2))

/-- **The component through the image of a generic point.** Let `T` be an integral closed subspace
of `X` of δ-dimension `k + r` whose generic point maps into a closed set `S` of `δ`-dimension at
most `k`. Then there is an irreducible component `C` of `S` whose generic point is that image, the
corresponding integral closed subspace `W₀` has δ-dimension `k` and that generic point, and `T` is
the image of an integral closed subspace `T₀` of `f^{-1}(W₀)` whose generic point maps to the
generic point of `T`. -/
private theorem exists_closedSetComponent_preimage (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (k : ℤ) (S : Set (points D.site D.base D.base_mem Y)) (hS : IsClosed S)
    (hSk : deltaDimensionClosed D sY hY S hS ≤ (k : EInt))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T = k + (r : ℤ))
    (hη : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈ S) :
    ∃ C : irreducibleComponents S, IsGenericPoint (⟨_, hη⟩ : S) C.1 ∧
      ∃ W₀ : IntegralClosedSubspace D.site D.base D.base_mem Y,
        W₀ = closedSetComponent D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) S hS C ∧
        W₀.ambientGenericPoint D.site D.base D.base_mem =
          pointsMap D.site D.base D.base_mem X f
            (T.ambientGenericPoint D.site D.base D.base_mem) ∧
        deltaDimension D sY W₀ = k ∧
        ∃ T₀ : IntegralClosedSubspace D.site D.base D.base_mem (W₀.subspace.preimage f).toFunctor,
          closedSubspaceComponentImage D sX hX (W₀.subspace.preimage f)
            (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W₀) T₀ = T ∧
          pointsMap D.site D.base D.base_mem _ (W₀.subspace.preimage f).ι
            (T₀.ambientGenericPoint D.site D.base D.base_mem) =
            T.ambientGenericPoint D.site D.base D.base_mem := by
  obtain ⟨hηk, C, hC⟩ := exists_isGenericPoint_image D sX hX sY hY f hbase r hr k S hS hSk T hT hη
  have hW₀gen := ambientGenericPoint_closedSetComponent D hY.1 (D.isDecentSpace_of_isGood sY hY) S
    hS C _ hη hC
  set W₀ := closedSetComponent D.site D.base D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) S
    hS C with hW₀
  have hW₀dim : deltaDimension D sY W₀ = k := by
    change inducedDimensionValue D.site D.base D.base_mem D.delta sY
      (W₀.ambientGenericPoint D.site D.base D.base_mem) = k
    rw [hW₀gen]
    exact hηk
  have hξW₀ : T.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X (W₀.subspace.preimage f) := by
    rw [subspacePointSet_preimage]
    change pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈
        subspacePointSet D.site D.base D.base_mem Y W₀.subspace
    rw [← hW₀gen]
    exact ⟨_, rfl⟩
  obtain ⟨T₀, hT₀⟩ := exists_closedSubspaceComponentImage_eq_of_mem D sX hX _
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W₀) T hξW₀
  exact ⟨C, hC, W₀, hW₀, hW₀gen, hW₀dim, T₀, hT₀, by
    rw [← hT₀, ambientGenericPoint_closedSubspaceComponentImage]⟩

/-- **Stacks 0EPB, part (1).** In Situation 0EDT let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be a morphism over the base which is flat of relative dimension `r`. Let `Z ⊆ Y` be
a closed subspace with `dim_δ(Z) ≤ k`. Then `dim_δ(f^{-1}(Z)) ≤ k + r` and

`[f^{-1}(Z)]_{k+r} = f^*[Z]_k` in `Z_{k+r}(X)`.

The cycle of a closed subspace is `AlgebraicGeometry.Space.closedSubspaceCycle` (Stacks 0EE9)
and the flat pullback is `AlgebraicGeometry.Space.flatPullbackMap` (Stacks 0EP8). -/
@[stacks 0EPB "part (1)"]
theorem flatPullback_closedSubspaceCycle_preimage (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ) (Z : Subfunctor Y)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (hZk : deltaDimensionSubspace D sY hY Z hZ ≤ (k : EInt)) :
    ∃ hdim : deltaDimensionSubspace D sX hX (Z.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Z hY.1 hX.1 hZ) ≤
          ((k + (r : ℤ) : ℤ) : EInt),
      closedSubspaceCycle D sX hX (Z.preimage f)
          (isClosedSubspace_preimage D.site D.base D.base_mem f Z hY.1 hX.1 hZ) (k + (r : ℤ))
          hdim =
        flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (closedSubspaceCycle D sY hY Z hZ k hZk) := by
  classical
  refine ⟨deltaDimensionSubspace_preimage_le D sX hX sY hY f hbase r hflat hr k Z hZ hZk, ?_⟩
  have hZ' := isClosedSubspace_preimage D.site D.base D.base_mem f Z hY.1 hX.1 hZ
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hZcl := isClosed_subspacePointSet_of_isClosedSubspace D hY.1 Z hZ
  refine Subtype.ext (funext fun T => ?_)
  show (closedSubspaceCycle D sX hX (Z.preimage f) hZ' (k + (r : ℤ)) _).1 T =
    ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (closedSubspaceCycle D sY hY Z hZ k hZk).1 W *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W T
  -- off the δ-dimension `k + r` both sides vanish
  by_cases hTdim : deltaDimension D sX T ≠ k + (r : ℤ)
  · rw [closedSubspaceCycle_coe, cycleCoeffOfClosedSubspace, ite_eq_right hTdim]
    exact (finsum_eq_zero_of_forall_eq_zero fun W =>
      flatPullbackTerm_eq_zero_of_deltaDimension_ne D sX hX sY hY f hbase r hflat hr k _ T
        hTdim W).symm
  rw [not_not] at hTdim
  set ξ := T.ambientGenericPoint D.site D.base D.base_mem with hξ
  set η := pointsMap D.site D.base D.base_mem X f ξ with hη
  -- off the inverse image of `|Z|` both sides vanish
  by_cases hηZ : η ∉ subspacePointSet D.site D.base D.base_mem Y Z
  · rw [closedSubspaceCycle_apply_eq_zero_of_forall_ne]
    · exact (finsum_flatPullbackMult_eq_zero_of_not_mem D sX hX sY hY f hbase r hflat hr T _ _
        (fun W h1 => subspacePointSet_subset_of_closedSubspaceCycle_ne_zero D sY hY Z hZ k hZk W
          h1) hηZ).symm
    · intro V hV
      apply hηZ
      have hmem : ξ ∈ subspacePointSet D.site D.base D.base_mem X (Z.preimage f) := by
        rw [hξ, ← hV, ambientGenericPoint_closedSubspaceComponentImage]
        exact ⟨_, rfl⟩
      rw [subspacePointSet_preimage] at hmem
      exact hmem
  rw [not_not] at hηZ
  -- the component of `|Z|` through `η`
  obtain ⟨C, hC, W₀, hW₀, hW₀gen, hW₀dim, T₀, hT₀, hξ₀⟩ := exists_closedSetComponent_preimage D
    sX hX sY hY f hbase r hr k _ hZcl hZk T hTdim hηZ
  have hW₀sub : subspacePointSet D.site D.base D.base_mem Y W₀.subspace ⊆
      subspacePointSet D.site D.base D.base_mem Y Z := by
    rw [hW₀, subspacePointSet_closedSetComponent]
    exact Subtype.coe_image_subset _ _
  have hW₀le : W₀.subspace ≤ Z := le_of_subspacePointSet_subset_of_integral D hY.1 Z hZ W₀ hW₀sub
  have hpre_le : W₀.subspace.preimage f ≤ Z.preimage f := fun U a ha => hW₀le U ha
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X (Z.preimage f) := by
    rw [subspacePointSet_preimage]
    exact hηZ
  obtain ⟨T₁, hT₁⟩ := exists_closedSubspaceComponentImage_eq_of_mem D sX hX _ hZ' T hξZ
  -- `W₀` is carried by `Z`
  obtain ⟨V, hV⟩ := exists_closedSubspaceComponentImage_eq_of_mem D sY hY Z hZ W₀
    (hW₀sub (show W₀.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem Y W₀.subspace from ⟨_, rfl⟩))
  -- the geometric points
  set z₀ := canonicalGeometricPoint D.site D.base D.base_mem (W₀.subspace.preimage f).toFunctor
    (T₀.ambientGenericPoint D.site D.base D.base_mem) with hz₀
  set z := geometricPointMap (Subfunctor.homOfLe hpre_le) z₀ with hz
  have hzx : geometricPointMap (Z.preimage f).ι z =
      geometricPointMap (W₀.subspace.preimage f).ι z₀ := by
    rw [hz, ← geometricPointMap_comp_aux, Subfunctor.homOfLe_ι]
  have e2 : pointsMap D.site D.base D.base_mem _ (Z.preimage f).ι z.image = ξ := by
    rw [← geometricPointMap_image, hzx, geometricPointMap_image, hz₀,
      canonicalGeometricPoint_image, hξ₀]
  have hz₁ : z.image = T₁.ambientGenericPoint D.site D.base D.base_mem := by
    refine pointsMap_ι_injective D hX.1 _ hZ' ?_
    have e1 : pointsMap D.site D.base D.base_mem _ (Z.preimage f).ι
        (T₁.ambientGenericPoint D.site D.base D.base_mem) = ξ := by
      rw [← ambientGenericPoint_closedSubspaceComponentImage D sX hX _ hZ', hT₁]
    rw [e1, e2]
  have hzV : (geometricPointMap (Z.fromPreimage f) z).image =
      V.ambientGenericPoint D.site D.base D.base_mem := by
    refine pointsMap_ι_injective D hY.1 Z hZ ?_
    have e3 : pointsMap D.site D.base D.base_mem _ Z.ι
        (V.ambientGenericPoint D.site D.base D.base_mem) = η := by
      rw [← ambientGenericPoint_closedSubspaceComponentImage D sY hY Z hZ, hV, hW₀gen]
    have e4 : pointsMap D.site D.base D.base_mem _ Z.ι
        (geometricPointMap (Z.fromPreimage f) z).image = η := by
      rw [geometricPointMap_image, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι,
        pointsMap_comp_apply, e2]
    rw [e3, e4]
  -- the left-hand side
  have hL : (closedSubspaceCycle D sX hX (Z.preimage f) hZ' (k + (r : ℤ))
      (deltaDimensionSubspace_preimage_le D sX hX sY hY f hbase r hflat hr k Z hZ hZk)).1 T =
      ((geometricLength D.site D.base D.base_mem ⟨(Z.preimage f).toFunctor, hZ'.1⟩ z
        (SheafOfModules.unit _)).toNat : ℤ) := by
    rw [← hT₁, closedSubspaceCycle_apply_closedSubspaceComponentImage,
      ite_eq_left (by rw [hT₁]; exact hTdim)]
    exact closedSubspaceMultiplicity_eq_toNat_geometricLength D _ hZ' T₁ z hz₁
  -- the right-hand side has one term
  have hR : ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (closedSubspaceCycle D sY hY Z hZ k hZk).1 W *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W T =
      (closedSubspaceCycle D sY hY Z hZ k hZk).1 W₀ *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W₀ T := by
    exact finsum_flatPullbackMult_eq_single D sX hX sY hY f hbase r hflat hr T _ hZcl C hηZ hC W₀
      hW₀ _ fun W h1 => exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero D sY hY
        Z hZ k _ hZk W h1
  have hZW₀ : (closedSubspaceCycle D sY hY Z hZ k hZk).1 W₀ =
      ((geometricLength D.site D.base D.base_mem ⟨Z.toFunctor, hZ.1⟩
        (geometricPointMap (Z.fromPreimage f) z) (SheafOfModules.unit _)).toNat : ℤ) := by
    rw [← hV, closedSubspaceCycle_apply_closedSubspaceComponentImage,
      ite_eq_left (by rw [hV]; exact hW₀dim)]
    exact closedSubspaceMultiplicity_eq_toNat_geometricLength D Z hZ V _ hzV
  have hM := flatPullbackMult_eq_toNat_length D sX hX sY hY f hbase r hflat hr W₀ T₀
    (by rw [hT₀, hTdim, hW₀dim]) z₀ (canonicalGeometricPoint_image _ _ _ _ _)
    (by rw [hξ₀, hW₀gen])
  rw [hT₀] at hM
  rw [hL, hR, hZW₀, hM, geometricLength_unit_preimage_eq_mul D.site D.base D.base_mem hX.1 hY.1 f
    hflat Z hZ z _ hzx, ENat.toNat_mul, Nat.cast_mul]

/-- **Stacks 0EPB, part (2).** In Situation 0EDT let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be a morphism over the base which is flat of relative dimension `r`. Let `F` be a
coherent `𝒪_Y`-module with `dim_δ(Supp(F)) ≤ k`. Then `dim_δ(Supp(f^*F)) ≤ k + r` and

`f^*[F]_k = [f^*F]_{k+r}` in `Z_{k+r}(X)`.

The cycle of a coherent module is `AlgebraicGeometry.Space.associatedCycle` (Stacks 0EEB), read at
any choice `γ_X`, `γ_Y` of geometric points over the points of `X` and `Y`; the pullback `f^*F`
is coherent by `AlgebraicGeometry.Space.isCoherent_modulePullback`, `X` being locally
Noetherian. -/
@[stacks 0EPB "part (2)"]
theorem flatPullback_associatedCycle_modulePullback (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    [IsCoherent D.site D.base D.base_mem Y hY.1 F] (k : ℤ)
    (hFk : deltaDimensionClosed D sY hY (moduleSupport D.site D.base D.base_mem hY.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hY.1 F) ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x) :
    letI : IsCoherent D.site D.base D.base_mem X hX.1
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk f :
            (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F) :=
      haveI : Fact (HasEtaleLocalProperty D.site D.base D.base_mem X
          (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
        ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
          D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian⟩
      isCoherent_modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f :
          (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) F inferInstance
    ∃ hdim : deltaDimensionClosed D sX hX
        (moduleSupport D.site D.base D.base_mem hX.1
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F))
        (isClosed_moduleSupport D.site D.base D.base_mem hX.1 _) ≤
          ((k + (r : ℤ) : ℤ) : EInt),
      flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (associatedCycle D sY hY F k γY hγY hFk) =
        associatedCycle D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F)
          (k + (r : ℤ)) γX hγX hdim := by
  classical
  let : IsCoherent D.site D.base D.base_mem X hX.1
      ((modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f :
          (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F) :=
    have : Fact (HasEtaleLocalProperty D.site D.base D.base_mem X
        (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
      ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
        D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian⟩
    isCoherent_modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk f :
        (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) F inferInstance
  refine ⟨deltaDimensionClosed_supportOfSheaf_modulePullback_le D sX hX sY hY f hbase r hflat hr
    F k hFk, ?_⟩
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hScl := isClosed_moduleSupport D.site D.base D.base_mem hY.1 F
  refine Subtype.ext (funext fun T => ?_)
  show ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (associatedCycle D sY hY F k γY hγY hFk).1 W *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W T = _
  rw [associatedCycle_apply]
  by_cases hTdim : deltaDimension D sX T ≠ k + (r : ℤ)
  · rw [ite_eq_right hTdim]
    exact finsum_eq_zero_of_forall_eq_zero fun W =>
      flatPullbackTerm_eq_zero_of_deltaDimension_ne D sX hX sY hY f hbase r hflat hr k _ T
        hTdim W
  rw [not_not] at hTdim
  rw [ite_eq_left hTdim, moduleMultiplicity]
  set ξ := T.ambientGenericPoint D.site D.base D.base_mem with hξ
  set η := pointsMap D.site D.base D.base_mem X f ξ with hη
  -- the length of `f^*F` at a geometric point over `ξ`
  have hpull : ∀ x : GeometricPoint D.site D.base D.base_mem X, x.image = ξ →
      geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γX ξ)
          ((modulePullback D.site D.base D.base_mem (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F) =
        geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩ (geometricPointMap f x) F *
          (let : IsLocalRing ↥(etaleLocalRing D.site D.base D.base_mem Y
              (geometricPointMap f x)) :=
            isLocalRing_etaleLocalRing D.site D.base D.base_mem Y hY.1 (geometricPointMap f x)
          Module.length ↥(etaleLocalRing D.site D.base D.base_mem X x)
            (↥(etaleLocalRing D.site D.base D.base_mem X x) ⧸
              Ideal.map (etaleLocalRingMap hX.1 f x)
                (maximalIdeal ↥(etaleLocalRing D.site D.base D.base_mem Y
                  (geometricPointMap f x))))) := by
    intro x hx
    rw [geometricLength_eq_of_image_eq D.site D.base D.base_mem hX.1 (γX ξ) x
      ((hγX ξ).trans hx.symm)
      ((modulePullback D.site D.base D.base_mem (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj F)]
    exact (geometricLength_mul_length_quotient_extendedMaximalIdeal D.site D.base D.base_mem
      (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) hflat x F).symm
  by_cases hηS : η ∉ moduleSupport D.site D.base D.base_mem hY.1 F
  · -- off the support both sides vanish
    have hzero : geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩
        (geometricPointMap f (γX ξ)) F = 0 := by
      rw [geometricLength, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton]
      exact fun h => hηS ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver
        D.site D.base D.base_mem ⟨Y, hY.1⟩ F _ η
        (by rw [GeometricPoint.LiesOver, geometricPointMap_image, hγX ξ])).2 h)
    rw [hpull (γX ξ) (hγX ξ), hzero, zero_mul, ENat.toNat_zero, Nat.cast_zero]
    refine finsum_flatPullbackMult_eq_zero_of_not_mem D sX hX sY hY f hbase r hflat hr T _ _
      (fun W h1 => ?_) hηS
    obtain ⟨C', hC'⟩ := exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero D sY hY F k γY
      hγY hFk W h1
    rw [hC']
    exact Subtype.coe_image_subset _ _
  rw [not_not] at hηS
  -- the component of the support through `η`
  obtain ⟨C, hC, W₀, hW₀, hW₀gen, hW₀dim, T₀, hT₀, hξ₀⟩ := exists_closedSetComponent_preimage D
    sX hX sY hY f hbase r hr k _ hScl hFk T hTdim hηS
  set z₀ := canonicalGeometricPoint D.site D.base D.base_mem (W₀.subspace.preimage f).toFunctor
    (T₀.ambientGenericPoint D.site D.base D.base_mem) with hz₀
  have hx₀ : (geometricPointMap (W₀.subspace.preimage f).ι z₀).image = ξ := by
    rw [geometricPointMap_image, hz₀, canonicalGeometricPoint_image, hξ₀]
  -- the right-hand side has one term
  have hR : ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (associatedCycle D sY hY F k γY hγY hFk).1 W *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W T =
      (associatedCycle D sY hY F k γY hγY hFk).1 W₀ *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr W₀ T := by
    exact finsum_flatPullbackMult_eq_single D sX hX sY hY f hbase r hflat hr T _ hScl C hηS hC W₀
      hW₀ _ fun W h1 => exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero D sY hY F k γY
        hγY hFk W h1
  have hFW₀ : (associatedCycle D sY hY F k γY hγY hFk).1 W₀ =
      ((geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩
        (geometricPointMap f (geometricPointMap (W₀.subspace.preimage f).ι z₀)) F).toNat :
          ℤ) := by
    rw [associatedCycle_apply_eq_geometricLength D sY hY F k γY hγY hFk hW₀dim, hW₀gen,
      geometricLength_eq_of_image_eq D.site D.base D.base_mem hY.1 (γY η)
        (geometricPointMap f (geometricPointMap (W₀.subspace.preimage f).ι z₀))
        ((hγY η).trans (by rw [geometricPointMap_image, hx₀]))]
  have hM := flatPullbackMult_eq_toNat_length D sX hX sY hY f hbase r hflat hr W₀ T₀
    (by rw [hT₀, hTdim, hW₀dim]) z₀ (canonicalGeometricPoint_image _ _ _ _ _)
    (by rw [hξ₀, hW₀gen])
  rw [hT₀] at hM
  rw [hR, hFW₀, hM, hpull _ hx₀, ENat.toNat_mul, Nat.cast_mul]

end Main

end AlgebraicGeometry.Space

end
