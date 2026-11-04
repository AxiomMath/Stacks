module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of a category fibred in groupoids

For a category fibred in groupoids over the big fppf category of schemes over `S`, the
structure sheaf on each of its five associated sites is the inverse image of the structure
sheaf of the corresponding big site of schemes.  Concretely its presheaf sends an object of
the fibred category to the ring of global functions on the underlying scheme, and that
presheaf is already a sheaf, so no sheafification occurs.

## Main definitions

* `AlgebraicGeometry.FibredSite.baseStructureSheaf` is the commutative structure sheaf of the
  indicated big site of schemes over `S`, and
  `AlgebraicGeometry.FibredSite.baseRingStructureSheaf` its underlying sheaf of rings.
* `AlgebraicGeometry.FibredSite.structureSheaf` is the commutative structure sheaf on an
  associated site of the fibred category.
* `AlgebraicGeometry.FibredSite.ringStructureSheafCore` is its underlying sheaf of rings.

## Implementation notes

Restriction along the structure functor is the inverse image of the base sheaf, and it
preserves the sheaf condition because the structure functor is a 1-morphism of fibred
categories to the identity fibred category: Stacks 06NW makes it continuous for the inherited
topologies, and a continuous functor pulls sheaves back to sheaves.  The identity's inherited
topology is coarser than the topology it is inherited from, which is what lets the base sheaf
be regarded there.

The underlying presheaf of each construction is definitionally the restricted presheaf; the
`_obj` lemmas record these identifications.

## References

* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the indicated big site of schemes over `S`, obtained by restricting
the fppf structure sheaf to the coarser topology. -/
public noncomputable def baseStructureSheaf (τ : SiteKind) :
    Sheaf (BigFppfOver.baseOverTopology B S hS τ) CommRingCat.{u} :=
  ⟨(BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      ((BigFppfOver.structure_isSheaf B S hS).of_le
        (BigFppfOver.baseOverTopology_le_fppf B S hS τ))⟩

/-- The presheaf underlying `baseStructureSheaf` sends an object over `S` to the ring of global
functions on its underlying scheme. -/
@[simp] public theorem baseStructureSheaf_obj (τ : SiteKind) :
    (baseStructureSheaf B S hS τ).obj =
      (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ := rfl

/-- The underlying sheaf of rings of the structure sheaf of the indicated big site of schemes
over `S`. -/
public noncomputable def baseRingStructureSheaf (τ : SiteKind) :
    Sheaf (BigFppfOver.baseOverTopology B S hS τ) RingCat.{u} :=
  ⟨(baseStructureSheaf B S hS τ).obj ⋙ forget₂ CommRingCat RingCat,
    (BigFppfOver.structure_isSheaf B S hS).of_le
      (BigFppfOver.baseOverTopology_le_fppf B S hS τ)⟩

/-- The presheaf underlying `baseRingStructureSheaf` is that of the fppf structure sheaf
`BigFppfOver.structureSheaf`. -/
@[simp] public theorem baseRingStructureSheaf_obj (τ : SiteKind) :
    (baseRingStructureSheaf B S hS τ).obj =
      (BigFppfOver.structureSheaf B S hS).obj := rfl

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The topology the identity functor inherits from a topology on the big fppf category over
`S` is coarser than that topology, so a sheaf for the latter is one for the former. -/
public theorem identity_inheritedTopology_le (τ : SiteKind) :
    (𝟭 (BigFppfOver B S hS)).inheritedTopology (BigFppfOver.baseOverTopology B S hS τ) ≤
      BigFppfOver.baseOverTopology B S hS τ := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2
  intro X R hR
  simpa using hR.2

/-- The structure sheaf of a category fibred in groupoids on its associated site for the
indicated topology: the inverse image along the structure functor of the structure sheaf of the
big site of schemes. Its sections at an object are the global functions on the underlying
scheme. -/
public noncomputable def structureSheaf (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    Sheaf (BigFppfOver.associatedTopology B S hS p τ) CommRingCat.{u} := by
  let J := BigFppfOver.baseOverTopology B S hS τ
  let Oid : Sheaf ((𝟭 (BigFppfOver B S hS)).inheritedTopology J) CommRingCat.{u} :=
    ⟨(baseStructureSheaf B S hS τ).obj,
      (baseStructureSheaf B S hS τ).property.of_le (identity_inheritedTopology_le B S hS τ)⟩
  letI : p.IsFibered := hp.isFibered
  letI : (𝟭 (BigFppfOver B S hS)).IsFibered :=
    Functor.isFiberedInGroupoids_id.isFibered
  letI := ((Functor.isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology
    J).1
  exact ⟨p.op ⋙ Oid.obj, p.op_comp_isSheaf _ _ Oid⟩

/-- The presheaf underlying `structureSheaf` sends an object of the fibred category to the ring
of global functions on the scheme underlying its image under `p`. -/
@[simp] public theorem structureSheaf_obj (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (structureSheaf B S hS p hp τ).obj =
      p.op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ := rfl

/-- The underlying sheaf of rings of the structure sheaf of a category fibred in groupoids: its
presheaf is the commutative structure presheaf followed by the forgetful functor to rings. -/
public noncomputable def ringStructureSheafCore (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    Sheaf (BigFppfOver.associatedTopology B S hS p τ) RingCat.{u} := by
  let J := BigFppfOver.baseOverTopology B S hS τ
  let Oid : Sheaf ((𝟭 (BigFppfOver B S hS)).inheritedTopology J) RingCat.{u} :=
    ⟨(baseRingStructureSheaf B S hS τ).obj,
      (baseRingStructureSheaf B S hS τ).property.of_le
        (identity_inheritedTopology_le B S hS τ)⟩
  letI : p.IsFibered := hp.isFibered
  letI : (𝟭 (BigFppfOver B S hS)).IsFibered :=
    Functor.isFiberedInGroupoids_id.isFibered
  letI := ((Functor.isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology
    J).1
  exact ⟨p.op ⋙ Oid.obj, p.op_comp_isSheaf _ _ Oid⟩

/-- The presheaf underlying `ringStructureSheafCore` is the composite of `p` with the presheaf
of the fppf structure sheaf `BigFppfOver.structureSheaf`. -/
@[simp] public theorem ringStructureSheafCore_obj (hp : p.IsFiberedInGroupoids)
    (τ : SiteKind) :
    (ringStructureSheafCore B S hS p hp τ).obj =
      p.op ⋙ (BigFppfOver.structureSheaf B S hS).obj := rfl

end AlgebraicGeometry.FibredSite

end
