module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityFromSizeBound
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsLocalizing
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange

/-!
# Quasi-coherent objects in the derived category of a fibred category (Stacks 0H0H)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category over the big fppf category of a scheme `S`, and let
`𝒳_{affine}` be its associated affine site (Stacks 0H09): the full subcategory of the objects
lying over an affine scheme, with the chaotic topology. Restricting the structure sheaf of
Stacks 06TV to `𝒳_{affine}` gives the sheaf of rings `O` of Stacks 0H08, a functor
`(𝒳_{affine})ᵒᵖ ⥤ RingCat`. This file defines

  `QC(𝒳) = QC(𝒳_{affine}, O)`,

the full subcategory of `D(O)` of Stacks 0GYV: the objects `K` for which, for every arrow `U → V`
of `𝒳_{affine}`, the canonical comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an
isomorphism in `D(O(U))`.

## Main definitions

* `AlgebraicGeometry.Stack.affineStructurePresheaf`: the sheaf of rings `O` of Stacks 0H08, the
  restriction of the structure sheaf to the associated affine site.
* `AlgebraicGeometry.Stack.affineBaseChangeData`: the derived base changes
  `- ⊗^L_{O(V)} O(U)` along the restriction homomorphisms of `O`, each characterized as the left
  adjoint of derived restriction of scalars.
* `AlgebraicGeometry.Stack.IsQuasiCoherentObject`: the condition of Stacks 0GYV at this site.
* `AlgebraicGeometry.Stack.quasiCoherentDerived`: the triangulated category `QC(𝒳)` of
  quasi-coherent objects in the derived category.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCoherentObject_iff` and
  `AlgebraicGeometry.Stack.comparison_eq_homEquiv_symm_restrictionMap`: membership in `QC(𝒳)` is
  the invertibility of the comparison maps, each the adjoint transpose of the canonical derived
  restriction map.
* `AlgebraicGeometry.Stack.isQuasiCoherentObject_iff_of_baseChangeData`: the condition, hence
  `QC(𝒳)`, does not depend on which derived base-change datum is used.
* The four assertions of Stacks 0GYW at this site — `QC(𝒳)` is a strictly full, saturated,
  triangulated subcategory of `D(O)` closed under arbitrary direct sums — are the general
  instances `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated`,
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isSaturated`,
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms` and
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderColimitsOfShape`, which
  apply because `AlgebraicGeometry.Stack.IsQuasiCoherentObject` is an abbreviation of `IsQC`.
* `AlgebraicGeometry.Stack.quasiCoherentDerivedPretriangulated`: `QC(𝒳)` is a triangulated
  category.
* `AlgebraicGeometry.Stack.isZero_quasiCoherentDerived_iff`: an object of `QC(𝒳)` is zero
  exactly when it is zero in `D(O)`.

## Implementation notes

`O` is the underlying presheaf of the structure sheaf of Stacks 06TV restricted along the affine
inclusion, which depends neither on the topology `τ` nor on the proof that `p` is fibred in
groupoids; `AlgebraicGeometry.Stack.affineStructurePresheaf_eq_restriction` identifies it with
the restriction of the structure sheaf for every such choice.

The derived base change `- ⊗^L_{O(V)} O(U)` is a chosen total left derived functor of extension
of scalars (`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`); the
condition defining `QC(𝒳)` does not depend on that choice.

`S` and the big fppf site are at the universe `u`, the fibred category is `𝒳 : Type v` with
`Category.{w} 𝒳`, the section rings of `O` are in `RingCat.{u}`, and the coefficient module
universe of `D(O)` is `max v w u t` for a free parameter `t`.

## References

* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 0H09](https://stacks.math.columbia.edu/tag/0H09)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The commutative-ring-valued structure presheaf of the associated affine site: an object of
`𝒳_{affine}` is sent to the ring of global functions on the scheme it lies over. This is the
underlying presheaf of the structure sheaf of Stacks 06TV, restricted along the inclusion of the
affine subcategory. -/
def affineStructureCommPresheaf : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineCategory.inclusion B S hS p).op ⋙ p.op ⋙
    (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- **The sheaf of rings `O` of Stacks 0H08**: the restriction of the structure sheaf of `𝒳` to
the associated affine site `𝒳_{affine}`, as a functor `(𝒳_{affine})ᵒᵖ ⥤ RingCat`. -/
def affineStructurePresheaf : (AffineCategory B S hS p)ᵒᵖ ⥤ RingCat.{u} :=
  affineStructureCommPresheaf B S hS p ⋙ forget₂ CommRingCat RingCat

/-- The ring `O(x)` is the ring of global functions on the scheme `x` lies over. -/
@[simp]
theorem affineStructurePresheaf_obj (x : (AffineCategory B S hS p)ᵒᵖ) :
    (affineStructurePresheaf B S hS p).obj x =
      (forget₂ CommRingCat RingCat).obj
        (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj (p.obj x.unop.obj)))) :=
  rfl

/-- `O` is the restriction of the structure sheaf of Stacks 06TV to the affine subcategory, for
every topology `τ` coarser than the fppf one and every proof that `p` is fibred in groupoids. -/
theorem affineStructurePresheaf_eq_restriction (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    affineStructurePresheaf B S hS p =
      (AffineCategory.inclusion B S hS p).op ⋙
        (ringStructureSheafCore B S hS p hp τ hτ).obj :=
  rfl

/-- The section rings of `O` are commutative. -/
theorem affineStructurePresheaf_comm (x : (AffineCategory B S hS p)ᵒᵖ)
    (a b : (affineStructurePresheaf B S hS p).obj x) : a * b = b * a :=
  let : CommRing ((affineStructurePresheaf B S hS p).obj x) :=
    inferInstanceAs (CommRing ((affineStructureCommPresheaf B S hS p).obj x))
  mul_comm a b

/-- The derived base-change datum of `O`: for every arrow `U → V` of `𝒳_{affine}` the derived
base change `- ⊗^L_{O(V)} O(U)`, characterized as the left adjoint of derived restriction of
scalars along the restriction homomorphism `O(V) → O(U)`, together with its functoriality
isomorphism. -/
def affineBaseChangeData : BaseChangeData.{t} (affineStructurePresheaf B S hS p) :=
  baseChangeDataOfComm.{u, w, v, t} (affineStructurePresheaf B S hS p)
    (affineStructurePresheaf_comm B S hS p)

/-- An object of `D(O)` is *quasi-coherent* when for every arrow `U → V` of `𝒳_{affine}` the
canonical comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism in `D(O(U))`.
This is the condition of Stacks 0GYV at the associated affine site. -/
abbrev IsQuasiCoherentObject (K : DMod.{t} (affineStructurePresheaf B S hS p)) : Prop :=
  IsQC.{t} (affineBaseChangeData.{u, v, w, t} B S hS p) K

/-- The *triangulated category of quasi-coherent objects in the derived category* of a category
`p : 𝒳 ⥤ (Sch/S)_{fppf}` over the big fppf category of `S`:

  `QC(𝒳) = QC(𝒳_{affine}, O)`,

the full subcategory of `D(𝒳_{affine}, O)` of the objects `K` such that for every arrow `U → V`
of `𝒳_{affine}` the canonical map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism, where
`𝒳_{affine}` is the associated affine site of Stacks 0H09 with its chaotic topology and `O` is
the structure sheaf of `𝒳` restricted to it. -/
@[stacks 0H0H]
abbrev quasiCoherentDerived : Type _ :=
  QC.{t} (affineBaseChangeData.{u, v, w, t} B S hS p)

/-- The inclusion functor `QC(𝒳) ⥤ D(O)`, which is fully faithful. -/
abbrev quasiCoherentDerivedι :
    quasiCoherentDerived.{u, v, w, t} B S hS p ⥤ DMod.{t} (affineStructurePresheaf B S hS p) :=
  QCι.{t} (affineBaseChangeData.{u, v, w, t} B S hS p)

/-- Membership in `QC(𝒳)` is invertibility, for every arrow of `𝒳_{affine}`, of the canonical
base-change comparison map. -/
theorem isQuasiCoherentObject_iff (K : DMod.{t} (affineStructurePresheaf B S hS p)) :
    IsQuasiCoherentObject.{u, v, w, t} B S hS p K ↔
      ∀ {U V : (AffineCategory B S hS p)ᵒᵖ} (a : V ⟶ U),
        IsIso (comparison.{t} (affineBaseChangeData.{u, v, w, t} B S hS p) a K) :=
  Iff.rfl

/-- The comparison map is the adjoint transpose, under `- ⊗^L_{O(V)} O(U) ⊣ DRestrict`, of the
canonical derived restriction map `RΓ(V, K) ⟶ RΓ(U, K)`. -/
theorem comparison_eq_homEquiv_symm_restrictionMap
    {U V : (AffineCategory B S hS p)ᵒᵖ} (a : V ⟶ U)
    (K : DMod.{t} (affineStructurePresheaf B S hS p)) :
    comparison.{t} (affineBaseChangeData.{u, v, w, t} B S hS p) a K =
      (((affineBaseChangeData.{u, v, w, t} B S hS p).baseChangeAdj a).homEquiv _ _).symm
        (restrictionMap.{t} (affineStructurePresheaf B S hS p) a K) :=
  rfl

/-- The quasi-coherence condition, hence `QC(𝒳)`, does not depend on the derived base-change
datum. -/
theorem isQuasiCoherentObject_iff_of_baseChangeData
    (bc : BaseChangeData.{t} (affineStructurePresheaf B S hS p))
    (K : DMod.{t} (affineStructurePresheaf B S hS p)) :
    IsQuasiCoherentObject.{u, v, w, t} B S hS p K ↔ IsQC.{t} bc K :=
  isQC_iff_of_baseChangeData _ _ _ _

/-- The pretriangulated structure of `QC(𝒳)`, with the distinguished triangles inherited from
`D(O)`. -/
@[instance_reducible]
def quasiCoherentDerivedPretriangulated :
    Pretriangulated (quasiCoherentDerived.{u, v, w, t} B S hS p) :=
  inferInstance

/-- An object of `QC(𝒳)` is zero exactly when the underlying object of `D(O)` is zero. -/
theorem isZero_quasiCoherentDerived_iff (K : quasiCoherentDerived.{u, v, w, t} B S hS p) :
    IsZero K ↔ IsZero K.obj :=
  isZero_qc_iff_isZero_obj.{t} (affineBaseChangeData.{u, v, w, t} B S hS p) K

/-- The underlying object in `D(O)` of an object of `QC(𝒳)` is quasi-coherent. -/
theorem isQuasiCoherentObject_obj (K : quasiCoherentDerived.{u, v, w, t} B S hS p) :
    IsQuasiCoherentObject.{u, v, w, t} B S hS p K.obj :=
  K.property

/-- `QC(𝒳)` is nonempty. -/
theorem nonempty_quasiCoherentDerived :
    Nonempty (quasiCoherentDerived.{u, v, w, t} B S hS p) := by
  obtain ⟨K, _, hK⟩ :=
    (isQC_isTriangulated (affineBaseChangeData.{u, v, w, t} B S hS p)).exists_zero
  exact ⟨⟨K, hK⟩⟩

end AlgebraicGeometry.Stack

end
