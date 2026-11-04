module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.GradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistModuleMultiplication
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# The module of twisted global sections on `Proj`

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring, `X = Proj 𝒮`, and let `ℱ` be a sheaf of
`𝒪_X`-modules. Multiplying a global section of `𝒪_X(n)` by a global section of `ℱ(m)` through the
canonical sheaf morphism `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` and extending biadditively gives the pairing

`(⨁_{n ≥ 0} Γ(X, 𝒪_X(n))) × (⨁_{m ∈ ℤ} Γ(X, ℱ(m))) ⟶ ⨁_{m ∈ ℤ} Γ(X, ℱ(m))`,

which raises the degree of a homogeneous section of `ℱ(m)` by the degree of the section of
`𝒪_X(n)` multiplying it. This pairing is the scalar multiplication of a module structure on
`⨁_{m ∈ ℤ} Γ(X, ℱ(m))` over the graded ring `⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` of Tag 01MP.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSections`: the group
  `⨁_{m ∈ ℤ} Γ(X, ℱ(m))` of global sections of all twists of `ℱ`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections`: the product of a
  global section of `𝒪_X(n)` with a global section of `ℱ(m)`, a global section of `ℱ(n + m)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsPairing`: the biadditive pairing of
  the graded ring of twisted global sections on the twisted global sections of `ℱ`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSectionsGCommRing`: the graded ring
  `⨁_{n ≥ 0} Γ(X, 𝒪_X(n))`, with the multiplication of Tag 01MP.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSectionsGmodule` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSectionsModule`: the twisted global
  sections of `ℱ` as a graded module, and as a module, over that graded ring.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsPairing_of_of`: the pairing of two
  homogeneous sections is their product, placed in the degree that is the sum of their degrees.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections_add_left` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections_add_right`: the product
  of homogeneous sections is additive in each variable.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections_one` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections_assoc`: the unit and
  associativity laws of the pairing, the two module axioms that involve the ring structure.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSections_of_smul_of`: the scalar
  multiplication of a homogeneous scalar on a homogeneous section is their canonical product.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.smul_eq_globalSectionsPairing`: the scalar
  multiplication is the pairing.

## Implementation notes

The product of two homogeneous sections is formed by tensoring them into the sheafified tensor
product and applying the multiplication morphism
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap`; biadditivity is
inherited from the tensor product through `twistTensorSections`, the pure tensor of the two
sections.

The pairing is assembled from the homogeneous products by `DirectSum.toAddMonoid` in each
variable separately, so it is biadditive by construction and
`globalSectionsPairing_of_of` records the formula that determines it. The intermediate
`multiplyHomogeneousSectionsRight`, `multiplyDegree` and `multiplyDegreeAddHom` are the
additive maps in one variable at a time.

The two laws that involve the ring structure — the unit law and associativity — are proved not
on sections but on the sheaf morphisms the sections induce: `multiplyByGlobalSection` is
multiplication by a *global* section of `𝒪_X(n)`, as a morphism `ℱ(m) ⟶ ℱ(n + m)`, and both
laws are equalities of such morphisms, checked on the sections of the sheafified tensor product
determined by pairs of sections (`pureTensorSection_hom_ext`, the universal property of
sheafification). On such a section the composite morphism of Tag 03GJ is computed by
`twistSheafMultiplicationMap_pureTensorSection`, from the section-level formulas for the
associator, the braiding and the functoriality of the tensor product; what remains is the
corresponding law for the product `multiplyTwistSections` of two sections of twisting sheaves,
which is pointwise in the module fibers.

The graded ring of Tag 01MP is characterized by its multiplication being the pointwise product
of local fractions, not given as explicit data, so the unit and associativity laws of the
pairing take the relevant global section of a twisting sheaf as a *parameter* together with the
hypothesis that its local values are the pointwise ones; `twistGlobalSections_one_apply` and
`twistGlobalSections_mul_apply` supply that hypothesis for the graded ring.

The degrees of the ring are natural numbers and those of the module are integers, so the
`VAdd ℕ ℤ` action that `DirectSum.Gmodule` asks for is the scoped
`Stacks.GradedLocalization.instVAddNatInt`, and the unit and associativity laws hold only after
reindexing the degree; each is therefore stated as a `HEq` and proved by transporting the
corresponding morphism equality along the equality of degrees (`heq_app_of_comp_eqToHom`).

## References

* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum MonoidalCategory
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.SheafOfModules (tensorSectionsAt tensorSections_associatorAt
  tensorSections_braidingAt)
open Stacks.SheafOfModules.Invertible (tensorProductAssociator tensorProductBraiding)
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open scoped Stacks.GradedLocalization
open scoped TensorProduct

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf ModuleCat.restrictScalars
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- The group `⨁_{m ∈ ℤ} Γ(Proj 𝒮, ℱ(m))` of global sections of all twists of `ℱ`. -/
public abbrev twistedGlobalSections : Type u :=
  ⨁ m : ℤ, (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)

/-- The tensor of a global section of `𝒪(n)` and one of `ℱ(m)`, as a global section of the
sheafified tensor product `𝒪(n) ⊗ ℱ(m)`. -/
public noncomputable def twistTensorSections (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    let O := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
    let J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)
    let hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)
      := by
      exact ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          ((twistingSheaf 𝒮 (n : ℤ)))).obj ((twistSheafOfModules 𝒮 F m)))).val.obj (op ⊤) := by
  let O := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
  let J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)
  let hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)
    := by
    exact ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property
  letI : MonoidalCategory
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
    PresheafOfModules.monoidalCategory (R := O)
  exact (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
    ((twistingSheaf 𝒮 (n : ℤ)).val ⊗ (twistSheafOfModules 𝒮 F m).val)).app (op ⊤)
      (s ⊗ₜ[(O.obj (op ⊤))] t)

private theorem twistTensorSections_add_left (n : ℕ) (m : ℤ)
    (s₁ s₂ : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    twistTensorSections 𝒮 F n m (s₁ + s₂) t =
      twistTensorSections 𝒮 F n m s₁ t + twistTensorSections 𝒮 F n m s₂ t := by
  simp only [twistTensorSections, TensorProduct.add_tmul]
  exact map_add _ _ _

private theorem twistTensorSections_add_right (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n)
    (t₁ t₂ : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    twistTensorSections 𝒮 F n m s (t₁ + t₂) =
      twistTensorSections 𝒮 F n m s t₁ + twistTensorSections 𝒮 F n m s t₂ := by
  simp only [twistTensorSections, TensorProduct.tmul_add]
  exact map_add _ _ _

private theorem twistTensorSections_zero_left (n : ℕ) (m : ℤ)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    twistTensorSections 𝒮 F n m 0 t = 0 := by
  simp only [twistTensorSections, TensorProduct.zero_tmul]
  exact map_zero _

private theorem twistTensorSections_zero_right (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n) :
    twistTensorSections 𝒮 F n m s 0 = 0 := by
  simp only [twistTensorSections, TensorProduct.tmul_zero]
  exact map_zero _

/-- The product of a global section of `𝒪(n)` and a global section of `ℱ(m)`, a global section of
`ℱ(n + m)`, formed by the canonical multiplication morphism `𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`. -/
public noncomputable def multiplyHomogeneousSections (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    (twistSheafOfModules 𝒮 F ((n : ℤ) + m)).val.obj (op ⊤) :=
  ((twistSheafMultiplicationMap 𝒮 F (n : ℤ) m).val.app (op ⊤)).hom
    (twistTensorSections 𝒮 F n m s t)

/-- The product of homogeneous sections is additive in the section of `𝒪(n)`. -/
public theorem multiplyHomogeneousSections_add_left (n : ℕ) (m : ℤ)
    (s₁ s₂ : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    multiplyHomogeneousSections 𝒮 F n m (s₁ + s₂) t =
      multiplyHomogeneousSections 𝒮 F n m s₁ t + multiplyHomogeneousSections 𝒮 F n m s₂ t := by
  unfold multiplyHomogeneousSections
  rw [twistTensorSections_add_left]
  exact map_add ((twistSheafMultiplicationMap 𝒮 F (n : ℤ) m).val.app (op ⊤)).hom _ _

/-- The product of homogeneous sections is additive in the section of `ℱ(m)`. -/
public theorem multiplyHomogeneousSections_add_right (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n)
    (t₁ t₂ : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    multiplyHomogeneousSections 𝒮 F n m s (t₁ + t₂) =
      multiplyHomogeneousSections 𝒮 F n m s t₁ + multiplyHomogeneousSections 𝒮 F n m s t₂ := by
  unfold multiplyHomogeneousSections
  rw [twistTensorSections_add_right]
  exact map_add ((twistSheafMultiplicationMap 𝒮 F (n : ℤ) m).val.app (op ⊤)).hom _ _

/-- The zero section of `𝒪(n)` multiplies every section of `ℱ(m)` to zero. -/
public theorem multiplyHomogeneousSections_zero_left (n : ℕ) (m : ℤ)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    multiplyHomogeneousSections 𝒮 F n m 0 t = 0 := by
  unfold multiplyHomogeneousSections
  rw [twistTensorSections_zero_left]
  exact map_zero ((twistSheafMultiplicationMap 𝒮 F (n : ℤ) m).val.app (op ⊤)).hom

/-- Every section of `𝒪(n)` multiplies the zero section of `ℱ(m)` to zero. -/
public theorem multiplyHomogeneousSections_zero_right (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n) :
    multiplyHomogeneousSections 𝒮 F n m s 0 = 0 := by
  unfold multiplyHomogeneousSections
  rw [twistTensorSections_zero_right]
  exact map_zero ((twistSheafMultiplicationMap 𝒮 F (n : ℤ) m).val.app (op ⊤)).hom

/-- Multiplication by a fixed global section of `𝒪(n)`, as an additive map on the global
sections of `ℱ(m)`. -/
public noncomputable def multiplyHomogeneousSectionsRight (n : ℕ) (m : ℤ)
    (s : twistGlobalSections 𝒮 n) :
    (twistSheafOfModules 𝒮 F m).val.obj (op ⊤) →+
      (twistSheafOfModules 𝒮 F ((n : ℤ) + m)).val.obj (op ⊤) where
  toFun := multiplyHomogeneousSections 𝒮 F n m s
  map_zero' := multiplyHomogeneousSections_zero_right 𝒮 F n m s
  map_add' := multiplyHomogeneousSections_add_right 𝒮 F n m s

/-- Multiplication by a fixed global section of `𝒪(n)`, as an additive map on the twisted global
sections of `ℱ`; it shifts the degree of a homogeneous section by `n`. -/
public noncomputable def multiplyDegree (n : ℕ) (s : twistGlobalSections 𝒮 n) :
    twistedGlobalSections 𝒮 F →+ twistedGlobalSections 𝒮 F :=
  DirectSum.toAddMonoid fun m =>
    (DirectSum.of (fun k : ℤ => (twistSheafOfModules 𝒮 F k).val.obj (op ⊤)) ((n : ℤ) + m)).comp
      (multiplyHomogeneousSectionsRight 𝒮 F n m s)

/-- Multiplication by a global section `s` of `𝒪(n)` sends the homogeneous section `t` of degree
`m` to the homogeneous section `s * t` of degree `n + m`. -/
public theorem multiplyDegree_of (n : ℕ) (m : ℤ) (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    multiplyDegree 𝒮 F n s (DirectSum.of _ m t) =
      DirectSum.of _ ((n : ℤ) + m) (multiplyHomogeneousSections 𝒮 F n m s t) :=
  DirectSum.toAddMonoid_of
    (fun k => (DirectSum.of (fun j : ℤ => (twistSheafOfModules 𝒮 F j).val.obj (op ⊤))
      ((n : ℤ) + k)).comp (multiplyHomogeneousSectionsRight 𝒮 F n k s)) m t

/-- Multiplication of twisted global sections of `ℱ` by the global sections of `𝒪(n)`, additive
in the section of `𝒪(n)`. -/
public noncomputable def multiplyDegreeAddHom (n : ℕ) :
    twistGlobalSections 𝒮 n →+ (twistedGlobalSections 𝒮 F →+ twistedGlobalSections 𝒮 F) where
  toFun := multiplyDegree 𝒮 F n
  map_zero' := DirectSum.addHom_ext fun m t => by
    simp only [AddMonoidHom.zero_apply, multiplyDegree_of,
      multiplyHomogeneousSections_zero_left]
    exact map_zero _
  map_add' := fun s₁ s₂ => DirectSum.addHom_ext fun m t => by
    simp only [AddMonoidHom.add_apply, multiplyDegree_of,
      multiplyHomogeneousSections_add_left]
    exact map_add _ _ _

/-- **The pairing `(⨁_{n ≥ 0} Γ(X, 𝒪_X(n))) × (⨁_{m ∈ ℤ} Γ(X, ℱ(m))) ⟶ ⨁_{m ∈ ℤ} Γ(X, ℱ(m))`**
on `X = Proj 𝒮`: the biadditive extension of the canonical multiplication of a global section of
`𝒪_X(n)` with a global section of `ℱ(m)`. -/
@[stacks 03GK]
public noncomputable def globalSectionsPairing :
    (⨁ n : ℕ, twistGlobalSections 𝒮 n) →+
      (twistedGlobalSections 𝒮 F →+ twistedGlobalSections 𝒮 F) :=
  DirectSum.toAddMonoid (multiplyDegreeAddHom 𝒮 F)

/-- The pairing of a global section of `𝒪(n)` with a global section of `ℱ(m)` is their canonical
product, a global section of `ℱ(n + m)`. -/
@[simp, stacks 03GK]
public theorem globalSectionsPairing_of_of (n : ℕ) (m : ℤ) (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    globalSectionsPairing 𝒮 F (DirectSum.of _ n s) (DirectSum.of _ m t) =
      DirectSum.of _ ((n : ℤ) + m) (multiplyHomogeneousSections 𝒮 F n m s t) := by
  rw [globalSectionsPairing, DirectSum.toAddMonoid_of]
  exact multiplyDegree_of 𝒮 F n m s t

/-! ### The product of two sections of twisting sheaves over an open

The graded ring of Tag 01MP multiplies global sections of `𝒪(n)` and `𝒪(m)` by multiplying
their local fractions pointwise. The same product is computed by the canonical sheaf morphism
`𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` on the image of a pure tensor. -/

/-- The product of a section of `𝒪(n)` and a section of `𝒪(m)` over an open `U`, a section of
`𝒪(n + m)` over `U`: the canonical multiplication morphism applied to their pure tensor. -/
noncomputable def multiplyTwistSections (n m : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (twistingSheaf 𝒮 n).val.obj (op U)) (t : (twistingSheaf 𝒮 m).val.obj (op U)) :
    (twistingSheaf 𝒮 (n + m)).val.obj (op U) :=
  ((twistMultiplicationMap 𝒮 n m).val.app (op U)).hom
    (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (twistingSheaf 𝒮 n) (twistingSheaf 𝒮 m) (op U) (s ⊗ₜ t))

/-- The product of two sections of twisting sheaves has as local values the products of their
local values. -/
theorem multiplyTwistSections_apply (n m : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (twistingSheaf 𝒮 n).val.obj (op U)) (t : (twistingSheaf 𝒮 m).val.obj (op U)) (x : U) :
    (multiplyTwistSections 𝒮 n m U s t).1 x = s.1 x * t.1 x :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul 𝒮 n m U s t x

private theorem twistSectionsOn_ext {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒮)}
    {s t : (twistingSheaf 𝒮 n).val.obj (op U)} (h : ∀ x : U, s.1 x = t.1 x) : s = t :=
  (associatedModuleSheafSectionsEquiv 𝒮 (twistGrading (S := S) 𝒮 n) U).injective
    (Subtype.ext (funext h))

private theorem twistSectionsOn_cast_apply {n m : ℤ} (h : n = m)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 n).val.obj (op U)) (x : U) :
    (cast (congrArg (fun i => ↥((twistingSheaf 𝒮 i).val.obj (op U))) h) s).1 x = s.1 x := by
  cases h
  rfl

private theorem twistSections_restrict_top_apply {k : ℤ}
    (v : (twistingSheaf 𝒮 k).val.obj (op ⊤)) (U : Opens (ProjectiveSpectrum.top 𝒮)) (x : U) :
    ((twistingSheaf 𝒮 k).val.map (homOfLE le_top).op v).1 x =
      v.1 ⟨x.1, show x.1 ∈ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) from trivial⟩ := rfl

/-- Associativity of the product of sections of twisting sheaves, with the first product given
by any section of the right degree whose local values are the pointwise products. -/
private theorem multiplyTwistSections_assoc (a b c : ℤ) {k : ℤ} (hk : k = a + b)
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (twistingSheaf 𝒮 a).val.obj (op U)) (t : (twistingSheaf 𝒮 b).val.obj (op U))
    (u : (twistingSheaf 𝒮 c).val.obj (op U)) (v : (twistingSheaf 𝒮 k).val.obj (op U))
    (hv : ∀ x : U, v.1 x = s.1 x * t.1 x) :
    HEq (multiplyTwistSections 𝒮 k c U v u)
      (multiplyTwistSections 𝒮 a (b + c) U s (multiplyTwistSections 𝒮 b c U t u)) := by
  have hdeg : k + c = a + (b + c) := by rw [hk]; ring
  refine heq_of_cast_eq (congrArg (fun i => ↥((twistingSheaf 𝒮 i).val.obj (op U))) hdeg) ?_
  refine twistSectionsOn_ext 𝒮 fun x => ?_
  rw [twistSectionsOn_cast_apply 𝒮 hdeg, multiplyTwistSections_apply,
    multiplyTwistSections_apply, multiplyTwistSections_apply, hv]
  exact mul_assoc _ _ _

/-- A section of `𝒪(0)` whose local values are all `1` acts as the identity on the sections of
every twisting sheaf. -/
private theorem multiplyTwistSections_one (b : ℤ) {k : ℤ} (hk : k = 0)
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (v : (twistingSheaf 𝒮 k).val.obj (op U)) (hv : ∀ x : U, v.1 x = 1)
    (u : (twistingSheaf 𝒮 b).val.obj (op U)) :
    HEq (multiplyTwistSections 𝒮 k b U v u) u := by
  have hdeg : k + b = b := by rw [hk]; ring
  refine heq_of_cast_eq (congrArg (fun i => ↥((twistingSheaf 𝒮 i).val.obj (op U))) hdeg) ?_
  refine twistSectionsOn_ext 𝒮 fun x => ?_
  rw [twistSectionsOn_cast_apply 𝒮 hdeg, multiplyTwistSections_apply, hv, one_mul]

/-! ### The sheaf multiplication map on pure tensors -/

/-- The presheaf of rings underlying the structure sheaf of `Proj 𝒮`. -/
noncomputable abbrev projStructureRing :
    (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ ⥤ CommRingCat.{u} :=
  (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj

/-- The structure sheaf of `Proj 𝒮` is a sheaf of rings in the form the sheafified tensor
product consumes. -/
theorem projStructureRingIsSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (structureRingPresheaf (projStructureRing 𝒮)) :=
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property

section PureTensors

variable (M N P M' N' : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- The section of `M ⊗ N` over `U` determined by a section of `M` and a section of `N`. -/
noncomputable abbrev pureTensorSection (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
        ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N))).val.obj (op U) :=
  tensorSectionsAt (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) (op U) M N x y

/-- The tensor product `f ⊗ g` of two morphisms sends the section determined by `x` and `y` to
the section determined by `f x` and `g y`. -/
theorem tensorSheafMap_pureTensorSection (f : M ⟶ M') (g : N ⟶ N')
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((AlgebraicGeometry.Proj 𝒮).toRingedSpace).presheaf,
          ((AlgebraicGeometry.Proj 𝒮).toRingedSpace).IsSheaf⟩)).map
        ((f, g) : (_, _) ⟶ (_, _)))).val.app (op U)
        (pureTensorSection 𝒮 M N U x y) =
      pureTensorSection 𝒮 M' N' U (f.val.app (op U) x) (g.val.app (op U) y) :=
  tensorSheafMap_app_toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace M N M' N'
    f g U x y

/-- The associator sends the section determined by `(x ⊗ y) ⊗ z` to the section determined by
`x ⊗ (y ⊗ z)`. -/
theorem tensorProductAssociator_pureTensorSection
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) (z : P.val.obj (op U)) :
    (tensorProductAssociator (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
        M N P).hom.val.app (op U)
        (pureTensorSection 𝒮 ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
            Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
            ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N)))
          P U (pureTensorSection 𝒮 M N U x y) z) =
      pureTensorSection 𝒮 M
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
            Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
            ((projStructureRingIsSheaf 𝒮))⟩).obj (N)).obj (P))) U x
        (pureTensorSection 𝒮 N P U y z) :=
  tensorSections_associatorAt (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
    (op U) M N P x y z

/-- The braiding sends the section determined by `x ⊗ y` to the section determined by
`y ⊗ x`. -/
theorem tensorProductBraiding_pureTensorSection
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
        M N).hom.val.app (op U) (pureTensorSection 𝒮 M N U x y) =
      pureTensorSection 𝒮 N M U y x :=
  tensorSections_braidingAt (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) (op U) M N x y

/-- Two morphisms out of a sheafified tensor product that agree on the sections determined by
pairs of sections of the factors are equal. -/
theorem pureTensorSection_hom_ext
    {f g : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
        ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N)) ⟶ P}
    (h : ∀ (U : Opens (ProjectiveSpectrum.top 𝒮)) (x : M.val.obj (op U)) (y : N.val.obj (op U)),
      f.val.app (op U) (pureTensorSection 𝒮 M N U x y) =
        g.val.app (op U) (pureTensorSection 𝒮 M N U x y)) :
    f = g := by
  apply ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (projStructureRing 𝒮)
    (projStructureRingIsSheaf 𝒮)).homEquiv _ P).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => exact h U.unop x y
  | add z₁ z₂ h₁ h₂ => exact (map_add _ z₁ z₂).trans ((congrArg₂ (· + ·) h₁ h₂).trans
      (map_add _ z₁ z₂).symm)

/-- The inverse associator sends the section determined by `x ⊗ (y ⊗ z)` to the section
determined by `(x ⊗ y) ⊗ z`. -/
theorem tensorProductAssociator_inv_pureTensorSection
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) (z : P.val.obj (op U)) :
    (tensorProductAssociator (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
        M N P).inv.val.app (op U)
        (pureTensorSection 𝒮 M
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
              Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮))
              (forget₂ CommRingCat RingCat) ((projStructureRingIsSheaf 𝒮))⟩).obj (N)).obj (P))) U x
          (pureTensorSection 𝒮 N P U y z)) =
      pureTensorSection 𝒮 ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
          Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N)))
        P U (pureTensorSection 𝒮 M N U x y) z :=
  (congrArg (fun w => (tensorProductAssociator (projStructureRing 𝒮)
        (projStructureRingIsSheaf 𝒮) M N P).inv.val.app (op U) w)
      (tensorProductAssociator_pureTensorSection 𝒮 M N P U x y z)).symm.trans
    (congrArg (fun g => g.val.app (op U)
        (pureTensorSection 𝒮
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
              Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮))
              (forget₂ CommRingCat RingCat) ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N))) P U
          (pureTensorSection 𝒮 M N U x y) z))
      (tensorProductAssociator (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
        M N P).hom_inv_id)

end PureTensors

/-- **The multiplication map `𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` on a pure tensor**: a section of `𝒪(n)`
tensored with a section of `ℱ` tensored with a section of `𝒪(m)` goes to that section of `ℱ`
tensored with the product of the two sections of twisting sheaves. -/
theorem twistSheafMultiplicationMap_pureTensorSection (n m : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : (twistingSheaf 𝒮 n).val.obj (op U)) (b : F.val.obj (op U))
    (c : (twistingSheaf 𝒮 m).val.obj (op U)) :
    (twistSheafMultiplicationMap 𝒮 F n m).val.app (op U)
        (pureTensorSection 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m) U a
          (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b c)) =
      pureTensorSection 𝒮 F (twistingSheaf 𝒮 (n + m)) U b
        (multiplyTwistSections 𝒮 n m U a c) := by
  let L : ℤ → SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) := fun k => twistingSheaf 𝒮 k
  let f₂ := (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((AlgebraicGeometry.Proj 𝒮).toRingedSpace).presheaf,
        ((AlgebraicGeometry.Proj 𝒮).toRingedSpace).IsSheaf⟩)).map
      (((tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) (L n) F).hom,
        (𝟙 (L m))) : (_, _) ⟶ (_, _)))).val.app (op U)
  let f₃ := (tensorProductAssociator (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) F (L n)
    (L m)).hom.val.app (op U)
  let f₄ := (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((AlgebraicGeometry.Proj 𝒮).toRingedSpace).presheaf,
        ((AlgebraicGeometry.Proj 𝒮).toRingedSpace).IsSheaf⟩)).map
      (((𝟙 F), (twistMultiplicationMap 𝒮 n m)) : (_, _) ⟶ (_, _)))).val.app (op U)
  show f₄ (f₃ (f₂ ((tensorProductAssociator (projStructureRing 𝒮)
    (projStructureRingIsSheaf 𝒮) (L n) F (L m)).inv.val.app (op U)
    (pureTensorSection 𝒮 (L n) (twistSheafOfModules 𝒮 F m) U a
      (pureTensorSection 𝒮 F (L m) U b c))))) = _
  refine Eq.trans (congrArg (fun z => f₄ (f₃ (f₂ z)))
    (tensorProductAssociator_inv_pureTensorSection 𝒮 (L n) F (L m) U a b c)) ?_
  refine Eq.trans (congrArg (fun z => f₄ (f₃ z))
    (tensorSheafMap_pureTensorSection 𝒮
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
          Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projStructureRingIsSheaf 𝒮))⟩).obj ((L n))).obj (F))) (L m)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
          Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projStructureRingIsSheaf 𝒮))⟩).obj (F)).obj ((L n)))) (L m)
      (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) (L n) F).hom
      (𝟙 (L m)) U (pureTensorSection 𝒮 (L n) F U a b) c)) ?_
  refine Eq.trans (congrArg (fun z => f₄ (f₃ (pureTensorSection 𝒮
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
          Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
          ((projStructureRingIsSheaf 𝒮))⟩).obj (F)).obj ((L n)))) (L m) U z c)))
    (tensorProductBraiding_pureTensorSection 𝒮 (L n) F U a b)) ?_
  refine Eq.trans (congrArg f₄
    (tensorProductAssociator_pureTensorSection 𝒮 F (L n) (L m) U b a c)) ?_
  exact tensorSheafMap_pureTensorSection 𝒮 F
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
        ((projStructureRingIsSheaf 𝒮))⟩).obj ((L n))).obj ((L m))))
    F (L (n + m)) (𝟙 F) (twistMultiplicationMap 𝒮 n m) U b
    (pureTensorSection 𝒮 (L n) (L m) U a c)

/-! ### Multiplication by a global section, as a morphism of sheaves -/

section GlobalSectionHom

variable (M N : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- A global section of `M`, as a morphism from the unit sheaf of modules to `M`. -/
private noncomputable def globalSectionHom (s : M.val.obj (op ⊤)) :
    SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) ⟶ M :=
  M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op s) (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f =
        (homOfLE (le_top : V.unop ≤ ⊤)).op from Subsingleton.elim _ _]))

private theorem globalSectionHom_app (s : M.val.obj (op ⊤))
    (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    (globalSectionHom 𝒮 M s).val.app (op U) (1 : (projStructureRing 𝒮).obj (op U)) =
      M.val.map (homOfLE le_top).op s :=
  congrArg (fun x : M.sections => x.val (op U))
    (M.unitHomEquiv.apply_symm_apply _)

/-- Tensoring on the left with a global section of `M`, as a morphism `N ⟶ M ⊗ N`. -/
private noncomputable def tensorInsertHom
    (s : SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology
      (ProjectiveSpectrum.top 𝒮)) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) ⟶ M) :
    N ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(projStructureRing 𝒮),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projStructureRing 𝒮)) (forget₂ CommRingCat RingCat)
        ((projStructureRingIsSheaf 𝒮))⟩).obj (M)).obj (N)) :=
  (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor (projStructureRing 𝒮)
      (projStructureRingIsSheaf 𝒮) N).inv ≫
    (Stacks.SheafOfModules.Invertible.tensorProductBifunctor (projStructureRing 𝒮)
      (projStructureRingIsSheaf 𝒮)).map
      (X := (SheafOfModules.unit _, N)) (Y := (M, N)) (s, 𝟙 N)

private theorem tensorInsertHom_apply
    (s : SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology
      (ProjectiveSpectrum.top 𝒮)) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) ⟶ M)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (x : N.val.obj (op U)) :
    (tensorInsertHom 𝒮 M N s).val.app (op U) x =
      pureTensorSection 𝒮 M N U
        (s.val.app (op U) (1 : (projStructureRing 𝒮).obj (op U))) x := by
  have h := Stacks.SheafOfModules.tensorSections_leftUnitorAt (projStructureRing 𝒮)
    (projStructureRingIsSheaf 𝒮) (op U) N x
  have hi := congrArg (fun y => (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor
    (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) N).inv.val.app (op U) y) h
  have hc : (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor (projStructureRing 𝒮)
        (projStructureRingIsSheaf 𝒮) N).inv.val.app (op U)
      ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor (projStructureRing 𝒮)
        (projStructureRingIsSheaf 𝒮) N).hom.val.app (op U)
        (pureTensorSection 𝒮 (SheafOfModules.unit _) N U
          (1 : (projStructureRing 𝒮).obj (op U)) x)) =
      pureTensorSection 𝒮 (SheafOfModules.unit _) N U
        (1 : (projStructureRing 𝒮).obj (op U)) x :=
    congrArg (fun g => g.val.app (op U)
        (pureTensorSection 𝒮 (SheafOfModules.unit _) N U
          (1 : (projStructureRing 𝒮).obj (op U)) x))
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor (projStructureRing 𝒮)
        (projStructureRingIsSheaf 𝒮) N).hom_inv_id
  refine Eq.trans (congrArg (fun y =>
      ((Stacks.SheafOfModules.Invertible.tensorProductBifunctor
        (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)).map
        (X := (SheafOfModules.unit _, N)) (Y := (M, N)) (s, 𝟙 N)).val.app (op U) y)
    (hi.symm.trans hc)) ?_
  exact Stacks.SheafOfModules.tensorSections_tensorMapAt (projStructureRing 𝒮)
    (projStructureRingIsSheaf 𝒮) (op U) (SheafOfModules.unit _) M N N s (𝟙 N)
    (1 : (projStructureRing 𝒮).obj (op U)) x

end GlobalSectionHom

/-! ### Transport along an equality of degrees -/

section Transport

variable {A B C : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

private theorem sheafHom_comp_app_apply (f : A ⟶ B) (g : B ⟶ C)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (x : A.val.obj (op U)) :
    (f ≫ g).val.app (op U) x = g.val.app (op U) (f.val.app (op U) x) := rfl

private theorem sheafHom_id_app_apply (U : Opens (ProjectiveSpectrum.top 𝒮))
    (x : A.val.obj (op U)) : (𝟙 A : A ⟶ A).val.app (op U) x = x := rfl

/-- A morphism that becomes another one after transporting its target along an equality of
sheaves agrees with it on sections, up to the induced equality of section modules. -/
private theorem heq_app_of_comp_eqToHom (f : A ⟶ B) (e : B = C) (g : A ⟶ C)
    (h : f ≫ eqToHom e = g) (U : Opens (ProjectiveSpectrum.top 𝒮)) (x : A.val.obj (op U)) :
    HEq (f.val.app (op U) x) (g.val.app (op U) x) := by
  cases e
  rw [eqToHom_refl, Category.comp_id] at h
  subst h
  exact HEq.rfl

end Transport

private theorem pureTensorSection_heq
    {G G' : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}
    (e : G = G') (U : Opens (ProjectiveSpectrum.top 𝒮)) (b : F.val.obj (op U))
    {c : G.val.obj (op U)} {c' : G'.val.obj (op U)} (h : HEq c c') :
    HEq (pureTensorSection 𝒮 F G U b c) (pureTensorSection 𝒮 F G' U b c') := by
  cases e
  exact heq_of_eq (congrArg (fun z => pureTensorSection 𝒮 F G U b z) (eq_of_heq h))

/-! ### Multiplication by a global section of a twisting sheaf -/

/-- **Multiplication by a global section of `𝒪(n)`, as a morphism `ℱ(m) ⟶ ℱ(n + m)`**: tensor
with the global section and apply the canonical multiplication morphism. -/
private noncomputable def multiplyByGlobalSection (n m : ℤ)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤)) :
    twistSheafOfModules 𝒮 F m ⟶ twistSheafOfModules 𝒮 F (n + m) :=
  tensorInsertHom 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m)
      (globalSectionHom 𝒮 (twistingSheaf 𝒮 n) s) ≫
    twistSheafMultiplicationMap 𝒮 F n m

private theorem multiplyByGlobalSection_pure (n m : ℤ)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤)) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (b : F.val.obj (op U)) (c : (twistingSheaf 𝒮 m).val.obj (op U)) :
    (multiplyByGlobalSection 𝒮 F n m s).val.app (op U)
        (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b c) =
      pureTensorSection 𝒮 F (twistingSheaf 𝒮 (n + m)) U b
        (multiplyTwistSections 𝒮 n m U
          ((twistingSheaf 𝒮 n).val.map (homOfLE le_top).op s) c) := by
  show (twistSheafMultiplicationMap 𝒮 F n m).val.app (op U)
    ((tensorInsertHom 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m)
      (globalSectionHom 𝒮 (twistingSheaf 𝒮 n) s)).val.app (op U)
      (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b c)) = _
  refine Eq.trans (congrArg (fun z => (twistSheafMultiplicationMap 𝒮 F n m).val.app (op U) z)
    (tensorInsertHom_apply 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m)
      (globalSectionHom 𝒮 (twistingSheaf 𝒮 n) s) U
      (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b c))) ?_
  refine Eq.trans (congrArg (fun z => (twistSheafMultiplicationMap 𝒮 F n m).val.app (op U)
      (pureTensorSection 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m) U z
        (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b c)))
    (globalSectionHom_app 𝒮 (twistingSheaf 𝒮 n) s U)) ?_
  exact twistSheafMultiplicationMap_pureTensorSection 𝒮 F n m U _ b c

private theorem multiplyByGlobalSection_top (n m : ℤ)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤))
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    (multiplyByGlobalSection 𝒮 F n m s).val.app (op ⊤) t =
      (twistSheafMultiplicationMap 𝒮 F n m).val.app (op ⊤)
        (pureTensorSection 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m) ⊤ s t) := by
  show (twistSheafMultiplicationMap 𝒮 F n m).val.app (op ⊤)
    ((tensorInsertHom 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m)
      (globalSectionHom 𝒮 (twistingSheaf 𝒮 n) s)).val.app (op ⊤) t) = _
  refine Eq.trans (congrArg (fun z => (twistSheafMultiplicationMap 𝒮 F n m).val.app (op ⊤) z)
    (tensorInsertHom_apply 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m)
      (globalSectionHom 𝒮 (twistingSheaf 𝒮 n) s) ⊤ t)) ?_
  refine congrArg (fun z => (twistSheafMultiplicationMap 𝒮 F n m).val.app (op ⊤)
      (pureTensorSection 𝒮 (twistingSheaf 𝒮 n) (twistSheafOfModules 𝒮 F m) ⊤ z t)) ?_
  refine Eq.trans (globalSectionHom_app 𝒮 (twistingSheaf 𝒮 n) s ⊤) ?_
  rw [show (homOfLE (le_top : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) ≤ ⊤)) = 𝟙 _ from
    Subsingleton.elim _ _, op_id, PresheafOfModules.map_id]
  rfl

private theorem multiplyHomogeneousSections_eq (n : ℕ) (m : ℤ) (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    multiplyHomogeneousSections 𝒮 F n m s t =
      (multiplyByGlobalSection 𝒮 F (n : ℤ) m s).val.app (op ⊤) t :=
  (multiplyByGlobalSection_top 𝒮 F (n : ℤ) m s t).symm

/-- Multiplying by a global section of `𝒪(k)` on a pure tensor, followed by a transport of the
degree, is the pure tensor with the product of twisting sections, up to the degree equality. -/
private theorem heq_multiplyByGlobalSection_pure (k b : ℤ) {l : ℤ} (hdeg : k + b = l)
    (v : (twistingSheaf 𝒮 k).val.obj (op ⊤)) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (p : F.val.obj (op U)) (c : (twistingSheaf 𝒮 b).val.obj (op U)) :
    HEq ((multiplyByGlobalSection 𝒮 F k b v ≫ eqToHom (congrArg (twistSheafOfModules 𝒮 F) hdeg)
        ).val.app (op U) (pureTensorSection 𝒮 F (twistingSheaf 𝒮 b) U p c))
      (pureTensorSection 𝒮 F (twistingSheaf 𝒮 (k + b)) U p
        (multiplyTwistSections 𝒮 k b U ((twistingSheaf 𝒮 k).val.map (homOfLE le_top).op v) c)) :=
  (heq_app_of_comp_eqToHom 𝒮 _ _ _ rfl U _).symm.trans
    (heq_of_eq (multiplyByGlobalSection_pure 𝒮 F k b v U p c))

/-- Multiplying by a global section of `𝒪(0)` whose local values are all `1` is the identity. -/
private theorem multiplyByGlobalSection_one (b : ℤ) {k : ℤ} (hk : k = 0)
    (v : (twistingSheaf 𝒮 k).val.obj (op ⊤))
    (hv : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), v.1 x = 1)
    (hdeg : k + b = b) :
    multiplyByGlobalSection 𝒮 F k b v ≫ eqToHom (congrArg (twistSheafOfModules 𝒮 F) hdeg) =
      𝟙 (twistSheafOfModules 𝒮 F b) := by
  refine pureTensorSection_hom_ext 𝒮 F (twistingSheaf 𝒮 b) _ ?_
  intro U p c
  refine (sheafHom_comp_app_apply 𝒮 _ _ U _).trans
    (Eq.trans ?_ (sheafHom_id_app_apply 𝒮 U _).symm)
  refine eq_of_heq ((heq_multiplyByGlobalSection_pure 𝒮 F k b hdeg v U p c).trans ?_)
  exact pureTensorSection_heq 𝒮 F (congrArg (twistingSheaf 𝒮) hdeg) U p
    (multiplyTwistSections_one 𝒮 b hk U _
      (fun x => (twistSections_restrict_top_apply 𝒮 v U x).trans (hv _)) c)

private theorem multiplyByGlobalSection_pure_comp (n m j : ℤ)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤)) (t : (twistingSheaf 𝒮 m).val.obj (op ⊤))
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (b : F.val.obj (op U))
    (c : (twistingSheaf 𝒮 j).val.obj (op U)) :
    (multiplyByGlobalSection 𝒮 F n (m + j) s).val.app (op U)
        ((multiplyByGlobalSection 𝒮 F m j t).val.app (op U)
          (pureTensorSection 𝒮 F (twistingSheaf 𝒮 j) U b c)) =
      pureTensorSection 𝒮 F (twistingSheaf 𝒮 (n + (m + j))) U b
        (multiplyTwistSections 𝒮 n (m + j) U
          ((twistingSheaf 𝒮 n).val.map (homOfLE le_top).op s)
          (multiplyTwistSections 𝒮 m j U
            ((twistingSheaf 𝒮 m).val.map (homOfLE le_top).op t) c)) :=
  (congrArg (fun z => (multiplyByGlobalSection 𝒮 F n (m + j) s).val.app (op U) z)
    (multiplyByGlobalSection_pure 𝒮 F m j t U b c)).trans
    (multiplyByGlobalSection_pure 𝒮 F n (m + j) s U b _)

/-- Multiplying by a product of global sections of twisting sheaves is multiplying by each in
turn, the product being any global section of the right degree whose local values are the
pointwise products. -/
private theorem multiplyByGlobalSection_assoc (a b j : ℤ) {k : ℤ} (hk : k = a + b)
    (s : (twistingSheaf 𝒮 a).val.obj (op ⊤)) (t : (twistingSheaf 𝒮 b).val.obj (op ⊤))
    (v : (twistingSheaf 𝒮 k).val.obj (op ⊤))
    (hv : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), v.1 x = s.1 x * t.1 x)
    (hdeg : k + j = a + (b + j)) :
    multiplyByGlobalSection 𝒮 F k j v ≫ eqToHom (congrArg (twistSheafOfModules 𝒮 F) hdeg) =
      multiplyByGlobalSection 𝒮 F b j t ≫ multiplyByGlobalSection 𝒮 F a (b + j) s := by
  refine pureTensorSection_hom_ext 𝒮 F (twistingSheaf 𝒮 j) _ ?_
  intro U p c
  refine (sheafHom_comp_app_apply 𝒮 _ _ U _).trans
    (Eq.trans ?_ (sheafHom_comp_app_apply 𝒮 _ _ U _).symm)
  refine eq_of_heq ((heq_multiplyByGlobalSection_pure 𝒮 F k j hdeg v U p c).trans ?_)
  refine HEq.trans ?_
    (heq_of_eq (multiplyByGlobalSection_pure_comp 𝒮 F a b j s t U p c).symm)
  exact pureTensorSection_heq 𝒮 F (congrArg (twistingSheaf 𝒮) hdeg) U p
    (multiplyTwistSections_assoc 𝒮 a b j hk U _ _ c _
      (fun x => (twistSections_restrict_top_apply 𝒮 v U x).trans
        ((hv _).trans (congrArg₂ (· * ·) (twistSections_restrict_top_apply 𝒮 s U x).symm
          (twistSections_restrict_top_apply 𝒮 t U x).symm))))

/-! ### The graded module structure -/

/-- The graded ring `⨁_{n ≥ 0} Γ(Proj 𝒮, 𝒪(n))` of twisted global sections, with the
multiplication of Tag 01MP: the pointwise product of local fractions. -/
public noncomputable instance twistGlobalSectionsGCommRing :
    DirectSum.GCommRing (twistGlobalSections 𝒮) :=
  (globalSectionsRingMap 𝒮).gradedRing

/-- The unit of the graded ring of twisted global sections is the section attached to
`1 ∈ 𝒮 0`. -/
public theorem twistGlobalSections_one_eq_degreeSection :
    (GradedMonoid.GOne.one : twistGlobalSections 𝒮 0) =
      degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩ := by
  apply DirectSum.of_injective 0
  calc
    DirectSum.of (twistGlobalSections 𝒮) 0
        (GradedMonoid.GOne.one : twistGlobalSections 𝒮 0) = 1 := (DirectSum.one_def _).symm
    _ = (globalSectionsRingMap 𝒮).hom 1 := (map_one _).symm
    _ = DirectSum.of (twistGlobalSections 𝒮) 0
        (degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩) :=
      (globalSectionsRingMap 𝒮).map_homogeneous 0 ⟨1, SetLike.one_mem_graded 𝒮⟩

/-- The unit of the graded ring of twisted global sections has local value `1` at every
point. -/
public theorem twistGlobalSections_one_apply (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (GradedMonoid.GOne.one : twistGlobalSections 𝒮 0).1 x = 1 := by
  rw [twistGlobalSections_one_eq_degreeSection]
  refine Eq.trans
    (degreeZeroToGlobalSections_apply 𝒮 (twistGrading (S := S) 𝒮 (0 : ℤ)) _ x) ?_
  simp [LocalizedModule.mk, OreLocalization.one_def]

/-- The product in the graded ring of twisted global sections has as local values the pointwise
products of the local values. -/
public theorem twistGlobalSections_mul_apply (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (GradedMonoid.GMul.mul s t : twistGlobalSections 𝒮 (n + m)).1 x = s.1 x * t.1 x :=
  (globalSectionsRingMap 𝒮).mul_sections n m s t x

/-- The unit of the graded section ring acts as the identity on the twisted global sections of
`ℱ`, up to the shift of the degree by `0`. -/
public theorem multiplyHomogeneousSections_one (m : ℤ) (v : twistGlobalSections 𝒮 0)
    (hv : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), v.1 x = 1)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    HEq (multiplyHomogeneousSections 𝒮 F 0 m v t) t :=
  (heq_of_eq (multiplyHomogeneousSections_eq 𝒮 F 0 m v t)).trans
    ((heq_app_of_comp_eqToHom 𝒮 _ _ _
      (multiplyByGlobalSection_one 𝒮 F m (k := ((0 : ℕ) : ℤ)) rfl v hv
        (Int.zero_add m)) ⊤ t).trans
      (heq_of_eq (sheafHom_id_app_apply 𝒮 ⊤ t)))

/-- **Associativity of the pairing**: multiplying a twisted global section of `ℱ` by a product
of global sections of twisting sheaves is multiplying by each factor in turn, up to the
identification of the degrees. -/
public theorem multiplyHomogeneousSections_assoc (n m : ℕ) (j : ℤ)
    (s : twistGlobalSections 𝒮 n) (t : twistGlobalSections 𝒮 m)
    (v : twistGlobalSections 𝒮 (n + m))
    (hv : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), v.1 x = s.1 x * t.1 x)
    (z : (twistSheafOfModules 𝒮 F j).val.obj (op ⊤)) :
    HEq (multiplyHomogeneousSections 𝒮 F (n + m) j v z)
      (multiplyHomogeneousSections 𝒮 F n ((m : ℤ) + j) s
        (multiplyHomogeneousSections 𝒮 F m j t z)) :=
  (heq_of_eq (multiplyHomogeneousSections_eq 𝒮 F (n + m) j v z)).trans
    ((heq_app_of_comp_eqToHom 𝒮 _ _ _
      (multiplyByGlobalSection_assoc 𝒮 F (n : ℤ) (m : ℤ) j (k := ((n + m : ℕ) : ℤ))
        (by push_cast; ring) s t v hv (by push_cast; ring)) ⊤ z).trans
      (heq_of_eq ((sheafHom_comp_app_apply 𝒮 (multiplyByGlobalSection 𝒮 F (m : ℤ) j t)
        (multiplyByGlobalSection 𝒮 F (n : ℤ) ((m : ℤ) + j) s) ⊤ z).trans
        ((congrArg (fun y => (multiplyByGlobalSection 𝒮 F (n : ℤ) ((m : ℤ) + j) s).val.app
              (op ⊤) y)
            (multiplyHomogeneousSections_eq 𝒮 F m j t z).symm).trans
          (multiplyHomogeneousSections_eq 𝒮 F n ((m : ℤ) + j) s
            (multiplyHomogeneousSections 𝒮 F m j t z)).symm))))

/-- The homogeneous action of the graded section ring on the twisted global sections of `ℱ`,
in the form a graded module asks for. -/
public noncomputable instance twistedGlobalSectionsGSMul :
    GradedMonoid.GSMul (twistGlobalSections 𝒮)
      (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) where
  smul {n m} s t := multiplyHomogeneousSections 𝒮 F n m s t

/-- The unit of the graded section ring acts as the identity, as an equality in the graded
monoid of twisted global sections. -/
public theorem gradedOne_smul
    (b : GradedMonoid (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤))) :
    (1 : GradedMonoid (twistGlobalSections 𝒮)) • b = b := by
  obtain ⟨m, t⟩ := b
  refine Sigma.ext (Int.zero_add m) ?_
  exact multiplyHomogeneousSections_one 𝒮 F m _ (twistGlobalSections_one_apply 𝒮) t

/-- The action of the graded section ring on the twisted global sections is associative, as an
equality in the graded monoid of twisted global sections. -/
public theorem gradedMul_smul (a a' : GradedMonoid (twistGlobalSections 𝒮))
    (b : GradedMonoid (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤))) :
    (a * a') • b = a • a' • b := by
  obtain ⟨n, s⟩ := a
  obtain ⟨m, t⟩ := a'
  obtain ⟨j, z⟩ := b
  refine Sigma.ext (show ((n + m : ℕ) : ℤ) + j = (n : ℤ) + ((m : ℤ) + j) by push_cast; ring) ?_
  exact multiplyHomogeneousSections_assoc 𝒮 F n m j s t _
    (twistGlobalSections_mul_apply 𝒮 n m s t) z

/-- The twisted global sections of `ℱ` form a graded module over the graded ring of twisted
global sections of the structure sheaf. -/
public noncomputable instance twistedGlobalSectionsGmodule :
    DirectSum.Gmodule (twistGlobalSections 𝒮)
      (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) where
  one_smul := gradedOne_smul 𝒮 F
  mul_smul := gradedMul_smul 𝒮 F
  smul_add {n m} s t u := multiplyHomogeneousSections_add_right 𝒮 F n m s t u
  smul_zero {n m} s := multiplyHomogeneousSections_zero_right 𝒮 F n m s
  add_smul {n m} s t u := multiplyHomogeneousSections_add_left 𝒮 F n m s t u
  zero_smul {n m} t := multiplyHomogeneousSections_zero_left 𝒮 F n m t

/-- **The module `⨁_{m ∈ ℤ} Γ(X, ℱ(m))` over the graded ring `⨁_{n ≥ 0} Γ(X, 𝒪_X(n))`** on
`X = Proj 𝒮`, for the pairing that multiplies a global section of `𝒪_X(n)` with a global
section of `ℱ(m)` through the canonical morphism `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`. -/
@[stacks 03GK "the module structure on the twisted global sections"]
public noncomputable instance twistedGlobalSectionsModule :
    Module (⨁ n : ℕ, twistGlobalSections 𝒮 n) (twistedGlobalSections 𝒮 F) :=
  DirectSum.Gmodule.module (twistGlobalSections 𝒮)
    (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤))

/-- A global section of `𝒪(n)` acts on a global section of `ℱ(m)` by their canonical product,
a global section of `ℱ(n + m)`. -/
@[simp]
public theorem twistedGlobalSections_of_smul_of (n : ℕ) (m : ℤ) (s : twistGlobalSections 𝒮 n)
    (t : (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) :
    (DirectSum.of _ n s : ⨁ i : ℕ, twistGlobalSections 𝒮 i) •
        (DirectSum.of _ m t : twistedGlobalSections 𝒮 F) =
      DirectSum.of _ ((n : ℤ) + m) (multiplyHomogeneousSections 𝒮 F n m s t) :=
  DirectSum.Gmodule.of_smul_of (twistGlobalSections 𝒮)
    (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) s t

private theorem globalSectionsPairing_eq_smulAddMonoidHom :
    globalSectionsPairing 𝒮 F =
      DirectSum.Gmodule.smulAddMonoidHom (twistGlobalSections 𝒮)
        (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) := by
  refine DirectSum.addHom_ext fun n s => ?_
  refine DirectSum.addHom_ext fun m t => ?_
  rw [globalSectionsPairing_of_of]
  exact (DirectSum.Gmodule.smulAddMonoidHom_apply_of_of (twistGlobalSections 𝒮)
    (fun m : ℤ => (twistSheafOfModules 𝒮 F m).val.obj (op ⊤)) s t).symm

/-- The module structure is the one given by the pairing: scalar multiplication by an element
of the graded section ring is the value of `globalSectionsPairing` at it. -/
public theorem smul_eq_globalSectionsPairing (r : ⨁ n : ℕ, twistGlobalSections 𝒮 n)
    (x : twistedGlobalSections 𝒮 F) : r • x = globalSectionsPairing 𝒮 F r x :=
  (DFunLike.congr_fun
    (DFunLike.congr_fun (globalSectionsPairing_eq_smulAddMonoidHom 𝒮 F) r) x).symm

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
