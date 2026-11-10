module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Rank
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.TangentSpace.SquareZero

/-!
# Lifting along a small extension

Let `f₂ : A₂ → A` be a small extension in `𝒞_Λ`, let `f₁ : A₁ → A` be another morphism, and
let `Y = A₁ ×_A A₂` be the fibre product, split by a section `h : A₁ → A₂` of `f₂` over `f₁`.
Then `Y` carries a canonical surjection onto the square-zero extension `k[ker f₂]`, namely
`(u, v) ↦ (ū, v - h(u))`. For a predeformation category satisfying Schlessinger's condition
(S2), a morphism from `x₁` into the pushforward of `y` along that surjection produces a lift
`x₁ → x₂` of `f₁` through `f₂` (Stacks 06IT).

The kernel of a small extension is a one-dimensional `k`-vector space: it is a simple module
over the source, its annihilator is the maximal ideal, and the induced module over the residue
field is simple, hence of rank one. So `k[ker f₂]` is the dual numbers after a choice of basis,
and the surjection `Y → k[ker f₂]` is the dual-number projection in coordinates. Condition
(S2) then identifies the existence of a section of `y → x₁` with the existence of a lift across
that projection, which is what the hypothesis supplies.

## Main definitions

* `Deformation.smallExtensionKernelModule`: the `k`-module structure on `ker f₂`.
* `Deformation.SmallExtensionSquareZeroTarget`: an object of `𝒞_Λ` presenting `k[ker f₂]`,
  with its ring coordinates and additive coordinates.
* `Deformation.smallExtensionSquareZeroTarget`: the canonical such presentation.
* `Deformation.infinitesimalCoordinateRingHom`: the coordinate map `Y → k[ker f₂]`.
* `Deformation.InfinitesimalMap`: the canonical surjection onto `k[ker f₂]`, recorded by its
  additive coordinates rather than by a chosen generator of the kernel.
* `Deformation.infinitesimalMap`: its construction, `(u, v) ↦ (ū, v - h(u))`.

## Main results

* `Deformation.isSmallExtension_eqToHom_comp`: being a small extension survives transporting
  the source and the target along equalities of objects of `𝒞_Λ`.
* `Deformation.smallExtension_kernel_annihilated`: the maximal ideal annihilates `ker f₂`.
* `Deformation.smallExtension_kernel_scalar`: scalar multiplication on `ker f₂` factors
  through the residue field.
* `Deformation.smallExtension_kernel_finiteDimensional`: `ker f₂` is finite-dimensional
  over `k`.
* `Deformation.infinitesimal_difference_mem`: `v - h(u)` lies in `ker f₂`.
* `Deformation.exists_lift_of_pushforward_map`: the lift.

## Implementation notes

An object of `𝒞_Λ` with an additive identification with `k × ker f₂` represents the source's
`k[ker f₂]`, and the coordinate equations specify its map directly. This avoids a noncanonical
identification of the kernel with `k`; the presentation is packaged as data because `𝒞_Λ` has
no fixed choice of object for a square-zero extension. The underlying object is the one
produced for Stacks 06IC, transported from complete local algebras to `𝒞_Λ` along the
Artinian structure its coordinates provide.

## References

* [Stacks Project, Tag 06IT](https://stacks.math.columbia.edu/tag/06IT)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Being a small extension is invariant under transporting the source and the target along
equalities of objects of the base category. -/
theorem isSmallExtension_eqToHom_comp
    {B' B A A' : ArtinianLocalAlgCat.{u, v, w} Λ k} (hB : B' = B) (hA : A = A')
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (eqToHom hB ≫ f ≫ eqToHom hA).hom.toRingHom) := by
  cases hB
  cases hA
  simpa using hf

/-- The maximal ideal of the source of a small extension annihilates its kernel: the kernel
is a simple module, so its annihilator is the maximal ideal. -/
theorem smallExtension_kernel_annihilated
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    ∀ a : A₂, a ∈ maximalIdeal A₂ →
      ∀ i : RingHom.ker f₂.hom.toRingHom, a * (i : A₂) = 0 := by
  rcases hsmall with ⟨-, -, -, -, -, hlen⟩
  let I := RingHom.ker f₂.hom.toRingHom
  have hsimp : IsSimpleModule A₂ I := Module.length_eq_one_iff.mp hlen
  have hAnn : (Module.annihilator A₂ I).IsMaximal := IsSimpleModule.annihilator_isMaximal
  have hAnnEq : Module.annihilator A₂ I = maximalIdeal A₂ := IsLocalRing.eq_maximalIdeal hAnn
  intro a ha i
  have hai : a ∈ Module.annihilator A₂ I := by rw [hAnnEq]; exact ha
  have hzero := (Module.mem_annihilator.mp hai) i
  have hzero' : ((a • i : I) : A₂) = 0 := congrArg Subtype.val hzero
  simpa only [Submodule.coe_smul, smul_eq_mul] using hzero'

/-- A section of `f₂` over `f₁` sends each element to one with the same image under `f₂`
as its image under `f₁`. -/
private theorem comp_eq_apply
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    {h : A₁ ⟶ A₂} (hh : h ≫ f₂ = f₁) (a : A₁) : f₂.hom (h.hom a) = f₁.hom a := by
  simpa using congrArg (fun q : A₁ ⟶ A => q.hom a) hh

/-- In a split fibre product over a small extension, the difference between the second
coordinate and the image of the first under the section lies in the kernel. -/
theorem infinitesimal_difference_mem
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁) (t : Y) :
    pr₂.hom t - h.hom (pr₁.hom t) ∈ RingHom.ker f₂.hom.toRingHom := by
  apply RingHom.mem_ker.mpr
  have hpb : f₂.hom.toRingHom (pr₂.hom t) = f₁.hom.toRingHom (pr₁.hom t) := by
    have ht := congrArg (fun q : Y ⟶ A => q.hom t) hPB.w
    simpa using ht
  have hh' : f₂.hom.toRingHom (h.hom (pr₁.hom t)) = f₁.hom.toRingHom (pr₁.hom t) :=
    comp_eq_apply hh _
  change f₂.hom.toRingHom (pr₂.hom t - h.hom (pr₁.hom t)) = 0
  rw [map_sub, hpb, hh']
  exact sub_self _

/-- The kernel of a small extension is a `k`-vector space: the maximal ideal annihilates it,
so `Deformation.kernelModule` applies. -/
@[instance_reducible]
noncomputable def smallExtensionKernelModule
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    Module k (RingHom.ker f₂.hom.toRingHom) :=
  kernelModule f₂ (smallExtension_kernel_annihilated f₂ hsmall)

/-- The kernel of a small extension is one-dimensional over `k`. -/
theorem smallExtension_kernel_finrank_eq_one
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    Module.finrank k (RingHom.ker f₂.hom.toRingHom) = 1 := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  let _ : Module k I := smallExtensionKernelModule f₂ hsmall
  let hT : Module.IsTorsionBySet A₂ I (maximalIdeal A₂) := fun i a =>
    Subtype.ext (smallExtension_kernel_annihilated f₂ hsmall a.1 a.2 i)
  let _ : Module (ResidueField A₂) I := hT.module
  let _ : IsScalarTower A₂ (ResidueField A₂) I := hT.isScalarTower
  have hsurj : Function.Surjective (algebraMap A₂ (ResidueField A₂)) := by
    intro x
    obtain ⟨a, ha⟩ := residue_surjective (R := A₂) x
    exact ⟨a, by simpa [IsLocalRing.residue_def] using ha⟩
  have hsimpR : IsSimpleModule A₂ I := by
    obtain ⟨-, -, -, -, -, hlen⟩ := hsmall
    exact Module.length_eq_one_iff.mp hlen
  have hsimpRes : IsSimpleModule (ResidueField A₂) I :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := ResidueField A₂) hsurj).mp hsimpR
  have hsimpK : IsSimpleModule k I := by
    let σ : k →+* ResidueField A₂ := A₂.residueEquiv.symm.toRingHom
    let l : I →ₛₗ[σ] I :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let _ : RingHomSurjective σ := ⟨A₂.residueEquiv.symm.surjective⟩
    exact (LinearMap.isSimpleModule_iff_of_bijective l Function.bijective_id).mpr hsimpRes
  exact isSimpleModule_iff_finrank_eq_one.mp hsimpK

/-- Scalar multiplication on the kernel of a small extension factors through the residue
field. -/
theorem smallExtension_kernel_scalar
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (a : A₂) (i : RingHom.ker f₂.hom.toRingHom) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    a • i = (A₂.residueEquiv (residue A₂ a)) • i := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  let hT : Module.IsTorsionBySet A₂ I (maximalIdeal A₂) := fun j x =>
    Subtype.ext (smallExtension_kernel_annihilated f₂ hsmall x.1 x.2 j)
  let _ : Module (ResidueField A₂) I := hT.module
  change a • i = A₂.residueEquiv.symm (A₂.residueEquiv (residue A₂ a)) • i
  rw [A₂.residueEquiv.symm_apply_apply]
  have hm := hT.mk_smul a i
  change residue A₂ a • i = a • i at hm
  exact hm.symm

/-- The kernel of a small extension is finite-dimensional over `k`. -/
theorem smallExtension_kernel_finiteDimensional
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    FiniteDimensional k (RingHom.ker f₂.hom.toRingHom) := by
  let _ : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
  exact FiniteDimensional.of_finrank_eq_succ (smallExtension_kernel_finrank_eq_one f₂ hsmall)

/-- A one-dimensional square-zero extension is the dual numbers. -/
noncomputable def trivSqZeroExtDualNumberEquiv
    {I : Type v} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [Module kᵐᵒᵖ I] [IsCentralScalar k I] (hfin : Module.finrank k I = 1) :
    TrivSqZeroExt k I ≃ₐ[k] DualNumber k := by
  classical
  let e : I ≃ₗ[k] k := LinearEquiv.ofFinrankEq I k (by simp [hfin])
  let f := TrivSqZeroExt.map e.toLinearMap
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply TrivSqZeroExt.ext
      · simpa [f] using congrArg TrivSqZeroExt.fst hxy
      · apply e.injective
        simpa [f] using congrArg TrivSqZeroExt.snd hxy
    · intro y
      refine ⟨(y.1, e.symm y.2), ?_⟩
      apply TrivSqZeroExt.ext
      · exact TrivSqZeroExt.fst_map e.toLinearMap (y.1, e.symm y.2)
      · exact (TrivSqZeroExt.snd_map e.toLinearMap (y.1, e.symm y.2)).trans
          (e.apply_symm_apply _)
  exact AlgEquiv.ofBijective f hf

/-- A presentation of `k[ker f₂]` as an object of `𝒞_Λ`: the object, a ring isomorphism with
the trivial square-zero extension, and additive coordinates compatible with the structure map
from `Λ` and with the residue map. -/
abbrev SmallExtensionSquareZeroTarget
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    [Module k (RingHom.ker f₂.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f₂.hom.toRingHom)] :=
  Σ target : ArtinianLocalAlgCat.{u, max v w, w} Λ k,
    (target.carrier ≃+* TrivSqZeroExt k (RingHom.ker f₂.hom.toRingHom)) ×
    { coordinate : target.carrier ≃+ (k × RingHom.ker f₂.hom.toRingHom) //
      (∀ r : Λ, coordinate (algebraMap Λ target.carrier r) = (algebraMap Λ k r, 0)) ∧
      (∀ a : target.carrier,
        (coordinate a).1 = target.residueEquiv (residue target a)) }

namespace SmallExtensionSquareZeroTarget

variable {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f₂ : A₂ ⟶ A}
  [Module k (RingHom.ker f₂.hom.toRingHom)]
  [Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom)]
  [IsCentralScalar k (RingHom.ker f₂.hom.toRingHom)]

/-- The underlying object of `𝒞_Λ`. -/
def target (S : SmallExtensionSquareZeroTarget f₂) :
    ArtinianLocalAlgCat.{u, max v w, w} Λ k := S.1

/-- The ring isomorphism with the trivial square-zero extension. -/
def coordinateRingEquiv (S : SmallExtensionSquareZeroTarget f₂) :
    S.target.carrier ≃+* TrivSqZeroExt k (RingHom.ker f₂.hom.toRingHom) := S.2.1

/-- The additive coordinates. -/
def coordinate (S : SmallExtensionSquareZeroTarget f₂) :
    S.target.carrier ≃+ (k × RingHom.ker f₂.hom.toRingHom) := S.2.2.1

/-- The coordinates of the image of the base ring. -/
theorem algebraMap_eq (S : SmallExtensionSquareZeroTarget f₂) (r : Λ) :
    S.coordinate (algebraMap Λ S.target.carrier r) = (algebraMap Λ k r, 0) :=
  S.2.2.2.1 r

/-- The first coordinate is the residue. -/
theorem residue_eq (S : SmallExtensionSquareZeroTarget f₂) (a : S.target.carrier) :
    (S.coordinate a).1 = S.target.residueEquiv (residue S.target a) :=
  S.2.2.2.2 a

end SmallExtensionSquareZeroTarget

/-- The canonical presentation of `k[ker f₂]` as an object of `𝒞_Λ`. -/
noncomputable def smallExtensionSquareZeroTarget
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom) := Module.compHom _ {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
    letI : IsCentralScalar k (RingHom.ker f₂.hom.toRingHom) := ⟨fun _ _ => rfl⟩
    SmallExtensionSquareZeroTarget f₂ := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f₂ hsmall
  letI : FiniteDimensional k I := smallExtension_kernel_finiteDimensional f₂ hsmall
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : IsScalarTower k k I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower k kᵐᵒᵖ I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let T := TrivSqZeroExt k I
  letI : Algebra k T := TrivSqZeroExt.algebra' k k I
  letI : Module.Finite k T :=
    ((Module.Basis.singleton Unit k).prod
      (Module.Basis.ofVectorSpace k I)).finiteDimensional_of_finite
  letI : IsArtinianRing T := IsArtinianRing.of_finite k T
  let s := squareZeroExtensionObject (Λ := Λ) (k := k) I
  let A' := s.1
  let e := Classical.choose s.2
  have he := Classical.choose_spec s.2
  letI : IsArtinianRing A' := e.symm.isArtinianRing
  let target : ArtinianLocalAlgCat.{u, max v w, w} Λ k := ⟨A', A'.residueEquiv⟩
  exact ⟨target, e, e.toAddEquiv, he.1, fun a => he.2 a⟩

/-- The canonical presentation is the dual numbers over `k`, since the kernel is
one-dimensional. -/
public noncomputable def smallExtensionSquareZeroDualNumberEquiv
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom) := Module.compHom _ {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y => by
        simp only [MulOpposite.unop_mul]
        exact mul_comm _ _
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    letI : IsCentralScalar k (RingHom.ker f₂.hom.toRingHom) := ⟨fun _ _ => rfl⟩
    (smallExtensionSquareZeroTarget f₂ hsmall).target.carrier ≃ₐ[Λ] DualNumber k := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f₂ hsmall
  letI : FiniteDimensional k I := smallExtension_kernel_finiteDimensional f₂ hsmall
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : IsScalarTower k k I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower k kᵐᵒᵖ I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let S := smallExtensionSquareZeroTarget f₂ hsmall
  let e := trivSqZeroExtDualNumberEquiv (smallExtension_kernel_finrank_eq_one f₂ hsmall)
  let er : S.target.carrier ≃+* DualNumber k := S.coordinateRingEquiv.trans e.toRingEquiv
  refine AlgEquiv.ofRingEquiv (f := er) ?_
  intro r
  have hcoord : S.coordinateRingEquiv (algebraMap Λ S.target.carrier r) =
      (algebraMap Λ k r, 0) := by
    change S.coordinate (algebraMap Λ S.target.carrier r) = _
    exact S.algebraMap_eq r
  change e (S.coordinateRingEquiv (algebraMap Λ S.target.carrier r)) =
    algebraMap Λ (DualNumber k) r
  rw [hcoord]
  change e (algebraMap k (TrivSqZeroExt k I) (algebraMap Λ k r)) = _
  rw [e.commutes]
  exact IsScalarTower.algebraMap_apply Λ k (DualNumber k) r

/-- The first coordinate is preserved by the identification of a one-dimensional square-zero
extension with the dual numbers. -/
theorem trivSqZeroExtDualNumberEquiv_fst
    {I : Type v} [AddCommGroup I] [Module k I]
    [Module kᵐᵒᵖ I] [IsCentralScalar k I] [Module.Finite k I]
    (hfin : Module.finrank k I = 1) (t : TrivSqZeroExt k I) :
    TrivSqZeroExt.fst (trivSqZeroExtDualNumberEquiv hfin t) = TrivSqZeroExt.fst t := by
  change TrivSqZeroExt.fst
    (TrivSqZeroExt.map
      (LinearEquiv.ofFinrankEq I k (by simp [hfin])).toLinearMap t) = _
  exact TrivSqZeroExt.fst_map _ _

/-- The first coordinate of the image of `t` under `smallExtensionSquareZeroDualNumberEquiv` is
the residue of `t` in `k`. -/
public theorem smallExtensionSquareZeroDualNumberEquiv_residue
    {A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom)) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom) := Module.compHom _ {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y => by simp only [MulOpposite.unop_mul]; exact mul_comm _ _
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    letI : IsCentralScalar k (RingHom.ker f₂.hom.toRingHom) := ⟨fun _ _ => rfl⟩
    ∀ t : (smallExtensionSquareZeroTarget f₂ hsmall).target.carrier,
      TrivSqZeroExt.fst (smallExtensionSquareZeroDualNumberEquiv f₂ hsmall t) =
        (smallExtensionSquareZeroTarget f₂ hsmall).target.residueEquiv
          (residue (smallExtensionSquareZeroTarget f₂ hsmall).target t) := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  let _ : Module k I := smallExtensionKernelModule f₂ hsmall
  let _ : FiniteDimensional k I := smallExtension_kernel_finiteDimensional f₂ hsmall
  let _ : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  let _ : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  refine fun (t : (smallExtensionSquareZeroTarget f₂ hsmall).target.carrier) => ?_
  change TrivSqZeroExt.fst
      (trivSqZeroExtDualNumberEquiv (smallExtension_kernel_finrank_eq_one f₂ hsmall)
        ((smallExtensionSquareZeroTarget f₂ hsmall).coordinateRingEquiv t)) = _
  rw [trivSqZeroExtDualNumberEquiv_fst]
  change ((smallExtensionSquareZeroTarget f₂ hsmall).coordinate t).1 = _
  exact (smallExtensionSquareZeroTarget f₂ hsmall).residue_eq t

/-- In a pullback along a surjection, a compatible pair comes from an element of the
fibre product. -/
private theorem exists_of_isPullback_of_surjective
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂}
    (hPB : IsPullback pr₂ pr₁ f₂ f₁) (hs : Function.Surjective f₂.hom)
    (v : A₂) (a : A₁) (hva : f₂.hom v = f₁.hom a) :
    ∃ y : Y, pr₂.hom y = v ∧ pr₁.hom y = a := by
  have hP := ArtinianLocalAlgCat.isPullback_of_surjective f₂ f₁ (Or.inl hs)
  let pair : AlgHom.pullback f₂.hom f₁.hom := ⟨(v, a), hva⟩
  refine ⟨(hPB.isoIsPullback A₂ A₁ hP).inv.hom pair, ?_, ?_⟩
  · have heq := congrArg (fun q => q.hom pair) (hPB.isoIsPullback_inv_fst A₂ A₁ hP)
    have hp : (ArtinianLocalAlgCat.pullbackFst_of_surjective f₂ f₁ (Or.inl hs)).hom pair = v := by
      rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
      rfl
    change pr₂.hom ((hPB.isoIsPullback A₂ A₁ hP).inv.hom pair) =
      (ArtinianLocalAlgCat.pullbackFst_of_surjective f₂ f₁ (Or.inl hs)).hom pair at heq
    rw [hp] at heq
    exact heq
  · have heq := congrArg (fun q => q.hom pair) (hPB.isoIsPullback_inv_snd A₂ A₁ hP)
    have hp : (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₂ f₁ (Or.inl hs)).hom pair = a := by
      rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
      rfl
    change pr₁.hom ((hPB.isoIsPullback A₂ A₁ hP).inv.hom pair) =
      (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₂ f₁ (Or.inl hs)).hom pair at heq
    rw [hp] at heq
    exact heq

/-- In a pullback along a surjection, elements with the same two projections are equal. -/
private theorem eq_of_isPullback_of_surjective
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂}
    (hPB : IsPullback pr₂ pr₁ f₂ f₁) (hs : Function.Surjective f₂.hom) {t s : Y}
    (h₂ : pr₂.hom t = pr₂.hom s) (h₁ : pr₁.hom t = pr₁.hom s) : t = s := by
  have hP := ArtinianLocalAlgCat.isPullback_of_surjective f₂ f₁ (Or.inl hs)
  let iPY := hPB.isoIsPullback A₂ A₁ hP
  have hfst (x : Y) : (iPY.hom.hom x).val.1 = pr₂.hom x := by
    have hh := congrArg (fun q => q.hom x) (hPB.isoIsPullback_hom_fst A₂ A₁ hP)
    change (ArtinianLocalAlgCat.pullbackFst_of_surjective f₂ f₁ (Or.inl hs)).hom
      (iPY.hom.hom x) = pr₂.hom x at hh
    rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom] at hh
    change ((AlgHom.pullback f₂.hom f₁.hom).val (iPY.hom.hom x)).1 = _
    exact hh
  have hsnd (x : Y) : (iPY.hom.hom x).val.2 = pr₁.hom x := by
    have hh := congrArg (fun q => q.hom x) (hPB.isoIsPullback_hom_snd A₂ A₁ hP)
    change (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₂ f₁ (Or.inl hs)).hom
      (iPY.hom.hom x) = pr₁.hom x at hh
    rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom] at hh
    change ((AlgHom.pullback f₂.hom f₁.hom).val (iPY.hom.hom x)).2 = _
    exact hh
  have hiPY : iPY.hom.hom t = iPY.hom.hom s :=
    Subtype.ext (Prod.ext ((hfst t).trans (h₂.trans (hfst s).symm))
      ((hsnd t).trans (h₁.trans (hsnd s).symm)))
  have hleft (x : Y) : iPY.inv.hom (iPY.hom.hom x) = x := by
    have hx := congrArg (fun q : Y ⟶ Y => q.hom x) iPY.hom_inv_id
    simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
      ArtinianLocalAlgCat.id_hom, AlgHom.id_apply] using hx
  exact (hleft t).symm.trans ((congrArg iPY.inv.hom hiPY).trans (hleft s))

/-- The coordinate map `Y → k[ker f₂]`, `(u, v) ↦ (ū, v - h(u))`. Multiplicativity uses that
the kernel is annihilated by the maximal ideal and has square zero. -/
noncomputable def infinitesimalCoordinateRingHom
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁) :
    letI : Module k (RingHom.ker f₂.hom.toRingHom) := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ (RingHom.ker f₂.hom.toRingHom) := Module.compHom _ {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
    letI : IsCentralScalar k (RingHom.ker f₂.hom.toRingHom) := ⟨fun _ _ => rfl⟩
    Y.carrier →+* TrivSqZeroExt k (RingHom.ker f₂.hom.toRingHom) := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f₂ hsmall
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : IsScalarTower k k I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower k kᵐᵒᵖ I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : CommRing (TrivSqZeroExt k I) := inferInstance
  let hI2 : I ^ 2 = ⊥ :=
    (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection
      (CommRingCat.ofHom f₂.hom.toRingHom) hsmall).2.2.2
  let d (t : Y) : I :=
    ⟨pr₂.hom t - h.hom (pr₁.hom t), infinitesimal_difference_mem f₁ f₂ h hh pr₁ pr₂ hPB t⟩
  let φ : Y → TrivSqZeroExt k I := fun t =>
    (A₁.residueEquiv (residue A₁ (pr₁.hom t)), d t)
  refine {
    toFun := φ
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · apply TrivSqZeroExt.ext
    · simp [φ]
    · apply Subtype.ext
      simp [φ, d]
  · intro t s
    apply TrivSqZeroExt.ext
    · change A₁.residueEquiv (residue A₁ (pr₁.hom (t * s))) =
        A₁.residueEquiv (residue A₁ (pr₁.hom t)) *
          A₁.residueEquiv (residue A₁ (pr₁.hom s))
      rw [map_mul]
      simp
    · apply Subtype.ext
      let u := pr₁.hom t
      let u' := pr₁.hom s
      let vv := pr₂.hom t
      let vv' := pr₂.hom s
      let dt := d t
      let ds := d s
      have hv : vv = h.hom u + (dt : A₂) := by
        dsimp [vv, dt, d]
        change pr₂.hom t = h.hom (pr₁.hom t) + (pr₂.hom t - h.hom (pr₁.hom t))
        calc
          pr₂.hom t = (pr₂.hom t - h.hom (pr₁.hom t)) + h.hom (pr₁.hom t) :=
            (sub_add_cancel _ _).symm
          _ = h.hom (pr₁.hom t) + (pr₂.hom t - h.hom (pr₁.hom t)) := by ac_rfl
      have hv' : vv' = h.hom u' + (ds : A₂) := by
        dsimp [vv', ds, d]
        change pr₂.hom s = h.hom (pr₁.hom s) + (pr₂.hom s - h.hom (pr₁.hom s))
        calc
          pr₂.hom s = (pr₂.hom s - h.hom (pr₁.hom s)) + h.hom (pr₁.hom s) :=
            (sub_add_cancel _ _).symm
          _ = h.hom (pr₁.hom s) + (pr₂.hom s - h.hom (pr₁.hom s)) := by ac_rfl
      have hdsq : (dt : A₂) * (ds : A₂) = 0 := by
        have hm : (dt : A₂) * (ds : A₂) ∈ I ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul dt.2 ds.2
        rw [hI2] at hm
        simpa using hm
      have hscalar : h.hom u • ds = (A₁.residueEquiv (residue A₁ u)) • ds := by
        rw [smallExtension_kernel_scalar f₂ hsmall (h.hom u) ds]
        exact congrArg (fun r : k => r • ds) (h.residue_comm u)
      have hscalar' : h.hom u' • dt = (A₁.residueEquiv (residue A₁ u')) • dt := by
        rw [smallExtension_kernel_scalar f₂ hsmall (h.hom u') dt]
        exact congrArg (fun r : k => r • dt) (h.residue_comm u')
      have hscalarVal :
          h.hom u * (ds : A₂) = ((A₁.residueEquiv (residue A₁ u)) • ds : I) := by
        have hh := congrArg (fun z : I => (z : A₂)) hscalar
        simpa [Submodule.coe_smul, smul_eq_mul] using hh
      have hscalarVal' :
          h.hom u' * (dt : A₂) = ((A₁.residueEquiv (residue A₁ u')) • dt : I) := by
        have hh := congrArg (fun z : I => (z : A₂)) hscalar'
        simpa [Submodule.coe_smul, smul_eq_mul] using hh
      change pr₂.hom (t * s) - h.hom (pr₁.hom (t * s)) =
        (((A₁.residueEquiv (residue A₁ u)) • ds : I) : A₂) +
          (((A₁.residueEquiv (residue A₁ u')) • dt : I) : A₂)
      rw [map_mul, map_mul]
      change vv * vv' - h.hom (u * u') = _
      rw [hv, hv', mul_add, add_mul, add_mul, hdsq, sub_eq_add_neg]
      simp only [add_zero]
      have hmul : h.hom (u * u') = h.hom u * h.hom u' := map_mul h.hom u u'
      rw [mul_comm (dt : A₂) (h.hom u'), hscalarVal', hscalarVal, hmul]
      ring
  · apply TrivSqZeroExt.ext
    · simp [φ]
    · apply Subtype.ext
      simp [φ, d]
  · intro t s
    apply TrivSqZeroExt.ext
    · change A₁.residueEquiv (residue A₁ (pr₁.hom (t + s))) =
        A₁.residueEquiv (residue A₁ (pr₁.hom t)) +
          A₁.residueEquiv (residue A₁ (pr₁.hom s))
      rw [map_add]
      simp
    · apply Subtype.ext
      change pr₂.hom (t + s) - h.hom (pr₁.hom (t + s)) = ((d t + d s : I) : A₂)
      simp [map_add, d]
      ring

/-- The canonical square-zero target and map for a split pullback of a small
extension. The additive coordinates are those of `k[ker f₂]`, not a chosen
identification of the kernel with the one-dimensional vector space `k`. -/
structure InfinitesimalMap
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f₂ : A₂ ⟶ A) (h : A₁ ⟶ A₂)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂) where
  /-- The object of `𝒞_Λ` presenting `k[ker f₂]`. -/
  target : ArtinianLocalAlgCat.{u, max v w, w} Λ k
  /-- Its additive coordinates. -/
  coordinate : target ≃+ (k × RingHom.ker f₂.hom.toRingHom)
  /-- The canonical surjection from the fibre product. -/
  g : Y ⟶ target
  /-- It is surjective. -/
  g_surjective : Function.Surjective g.hom
  /-- Its first coordinate is the residue of the first projection. -/
  first : ∀ t : Y,
    (coordinate (g.hom t)).1 = A₁.residueEquiv (residue A₁ (pr₁.hom t))
  /-- The difference `v - h(u)` lies in the kernel. -/
  difference_mem : ∀ t : Y,
    pr₂.hom t - h.hom (pr₁.hom t) ∈ RingHom.ker f₂.hom.toRingHom
  /-- Its second coordinate is that difference. -/
  second : ∀ t : Y,
    (coordinate (g.hom t)).2 = ⟨pr₂.hom t - h.hom (pr₁.hom t), difference_mem t⟩

/-- The intrinsic infinitesimal-coordinate map `(u,v) ↦ (ū,v-h(u))` into
`k[ker f₂]`, constructed without a basis of the kernel. -/
noncomputable def infinitesimalMap
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁) :
    InfinitesimalMap f₂ h pr₁ pr₂ := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f₂ hsmall
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : IsScalarTower k k I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower k kᵐᵒᵖ I := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let S := smallExtensionSquareZeroTarget f₂ hsmall
  let ρ := infinitesimalCoordinateRingHom f₁ f₂ hsmall h hh pr₁ pr₂ hPB
  let gr : Y.carrier →+* S.target.carrier := S.coordinateRingEquiv.symm.toRingHom.comp ρ
  have hρalg (r : Λ) : ρ (algebraMap Λ Y.carrier r) = (algebraMap Λ k r, 0) := by
    apply TrivSqZeroExt.ext
    · change A₁.residueEquiv (residue A₁ (pr₁.hom (algebraMap Λ Y.carrier r))) =
        algebraMap Λ k r
      rw [pr₁.hom.commutes]
      exact A₁.residueEquiv.commutes r
    · apply Subtype.ext
      change pr₂.hom (algebraMap Λ Y.carrier r) -
        h.hom (pr₁.hom (algebraMap Λ Y.carrier r)) = 0
      rw [pr₂.hom.commutes, pr₁.hom.commutes, h.hom.commutes]
      exact sub_self _
  let gAlg : Y.carrier →ₐ[Λ] S.target.carrier := {
    toRingHom := gr
    commutes' := by
      intro r
      apply S.coordinateRingEquiv.injective
      change S.coordinateRingEquiv (gr (algebraMap Λ Y.carrier r)) =
        S.coordinateRingEquiv (algebraMap Λ S.target.carrier r)
      change S.coordinateRingEquiv
          (S.coordinateRingEquiv.symm (ρ (algebraMap Λ Y.carrier r))) =
        S.coordinateRingEquiv (algebraMap Λ S.target.carrier r)
      rw [S.coordinateRingEquiv.apply_symm_apply]
      exact (hρalg r).trans (S.algebraMap_eq r).symm }
  have hsmallSurj : Function.Surjective f₂.hom := by
    rcases hsmall with ⟨-, -, -, -, hsurj, -⟩
    exact hsurj
  let pFst := ArtinianLocalAlgCat.pullbackFst_of_surjective f₂ f₁ (Or.inl hsmallSurj)
  let pSnd := ArtinianLocalAlgCat.pullbackSnd_of_surjective f₂ f₁ (Or.inl hsmallSurj)
  have hPpull : IsPullback pFst pSnd f₂ f₁ :=
    ArtinianLocalAlgCat.isPullback_of_surjective f₂ f₁ (Or.inl hsmallSurj)
  let iPY := hPB.isoIsPullback A₂ A₁ hPpull
  have hsurj : Function.Surjective gAlg := by
    intro b
    let coord := S.coordinateRingEquiv b
    let r : k := coord.1
    let j : I := coord.2
    have hb : b = S.coordinateRingEquiv.symm (r, j) := by
      dsimp [r, j, coord]
      exact (S.coordinateRingEquiv.symm_apply_apply b).symm
    obtain ⟨u, hu⟩ := residue_surjective (R := A₁) (A₁.residueEquiv.symm r)
    have hu' : A₁.residueEquiv (residue A₁ u) = r := by
      rw [hu]
      exact A₁.residueEquiv.apply_symm_apply r
    let pair : AlgHom.pullback f₂.hom f₁.hom :=
      ⟨(h.hom u + (j : A₂), u), by
        change f₂.hom (h.hom u + (j : A₂)) = f₁.hom u
        have hj : f₂.hom (j : A₂) = 0 := RingHom.mem_ker.mp j.2
        have hhu : f₂.hom (h.hom u) = f₁.hom u := by
          have hh' := congrArg (fun q : A₁ ⟶ A => q.hom u) hh
          simpa using hh'
        rw [map_add, hj, add_zero]
        exact hhu⟩
    let p : ArtinianLocalAlgCat.pullbackObj_of_surjective f₂ f₁ (Or.inl hsmallSurj) := by
      change AlgHom.pullback f₂.hom f₁.hom
      exact pair
    let y : Y := iPY.inv.hom p
    have hy₂ : pr₂.hom y = h.hom u + (j : A₂) := by
      have hc := CategoryTheory.IsPullback.isoIsPullback_inv_fst A₂ A₁ hPB hPpull
      have heq := congrArg (fun q : _ ⟶ A₂ => q.hom p) hc
      rw [ArtinianLocalAlgCat.comp_hom] at heq
      calc
        pr₂.hom y = pFst.hom p := by simpa [y] using heq
        _ = h.hom u + (j : A₂) := by
          rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
          rfl
    have hy₁ : pr₁.hom y = u := by
      have hc := CategoryTheory.IsPullback.isoIsPullback_inv_snd A₂ A₁ hPB hPpull
      have heq := congrArg (fun q : _ ⟶ A₁ => q.hom p) hc
      rw [ArtinianLocalAlgCat.comp_hom] at heq
      calc
        pr₁.hom y = pSnd.hom p := by simpa [y] using heq
        _ = u := by
          rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
          rfl
    refine ⟨y, ?_⟩
    rw [hb]
    dsimp [gAlg, gr]
    change S.coordinateRingEquiv.symm (ρ y) = S.coordinateRingEquiv.symm (r, j)
    have hρy : ρ y = (r, j) := by
      apply Prod.ext
      · change A₁.residueEquiv (residue A₁ (pr₁.hom y)) = r
        rw [hy₁, hu']
      · apply Subtype.ext
        change pr₂.hom y - h.hom (pr₁.hom y) = (j : A₂)
        rw [hy₂, hy₁]
        exact add_sub_cancel_left _ _
    exact congrArg (fun z : TrivSqZeroExt k I => S.coordinateRingEquiv.symm z) hρy
  have hcoord (t : Y) : S.coordinate (gAlg t) = ρ t := by
    change S.coordinateRingEquiv (S.coordinateRingEquiv.symm (ρ t)) = ρ t
    exact S.coordinateRingEquiv.apply_symm_apply _
  let g : Y ⟶ S.target := {
    hom := gAlg
    isLocal := IsLocalHom.of_surjective gr hsurj
    residue_comm := by
      intro t
      calc
        S.target.residueEquiv (residue S.target (gAlg t)) =
            (S.coordinate (gAlg t)).1 := (S.residue_eq (gAlg t)).symm
        _ = A₁.residueEquiv (residue A₁ (pr₁.hom t)) := by
          rw [hcoord t]
          rfl
        _ = Y.residueEquiv (residue Y t) := pr₁.residue_comm t }
  refine {
    target := S.target
    coordinate := S.coordinate
    g := g
    g_surjective := hsurj
    first := fun t => by rw [hcoord t]; rfl
    difference_mem := infinitesimal_difference_mem f₁ f₂ h hh pr₁ pr₂ hPB
    second := fun t => by rw [hcoord t]; rfl }

/-- Two morphisms of a predeformation category into an object over the residue field are
equal: their images agree, and the fibre over the residue field has only the identity. -/
theorem maps_to_special_fiber_eq
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    {x : F} (f g : x ⟶ x₀.1) : f = g := by
  classical
  have hfg : p.map f = p.map g := by
    have h := hom_residueFieldObject_ext
      ((p.map f) ≫ eqToHom x₀.2) ((p.map g) ≫ eqToHom x₀.2)
    calc
      p.map f = (p.map f ≫ eqToHom x₀.2) ≫ eqToHom x₀.2.symm := by simp
      _ = (p.map g ≫ eqToHom x₀.2) ≫ eqToHom x₀.2.symm :=
        congrArg (fun t => t ≫ eqToHom x₀.2.symm) h
      _ = p.map g := by simp
  obtain ⟨χ, hχ, -⟩ := existsUnique_factor_of_isHomLift hp.cofibered f g
    (𝟙 (p.obj x₀.1)) (by rw [hfg]; simp)
  let e : p.Fiber (residueFieldObject.{u, v, w} Λ k) ≌ Discrete PUnit.{u₁ + 1} :=
    Classical.choice hp.specialFiber
  let χF : x₀ ⟶ x₀ :=
    ⟨χ, IsHomLift.of_fac p (𝟙 (residueFieldObject.{u, v, w} Λ k)) χ x₀.2 x₀.2 (by
      simp [hχ.1])⟩
  have heq : χF = 𝟙 x₀ := e.fullyFaithfulFunctor.map_injective (Subsingleton.elim _ _)
  have hχeq : χ = 𝟙 x₀.1 := by
    have hh := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) heq
    change χ = 𝟙 x₀.1 at hh
    exact hh
  simpa [hχeq] using hχ.2

/-- Transporting along an equality of objects of `𝒞_Λ` and then applying an algebra
isomorphism of the target is evaluation after the induced `eqToHom`. -/
theorem artinianAlgEquivCast_apply
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {D : Type w}
    [CommSemiring D] [Algebra Λ D] (h : A = B) (e : B.carrier ≃ₐ[Λ] D) (a : A) :
    (AlgEquiv.cast (R := Λ) h).trans e a = e ((eqToHom h).hom a) := by
  cases h
  rfl

/-- The special case of `Deformation.artinianAlgEquivCast_apply` for the residue-field
object, whose carrier is `ULift k`. -/
theorem artinianAlgEquivCast_ulift_apply
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (h : A = residueFieldObject.{u, v, w} Λ k) (a : A) :
    ((AlgEquiv.cast (R := Λ) h).trans (ULift.algEquiv (R := Λ) (A := k))) a =
      ULift.down ((eqToHom h).hom a) := by
  cases h
  rfl

/-- A morphism to the object of the special fibre indexed by `x₀`. -/
noncomputable def mapToSpecialFiber
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (x : F) : x ⟶ x₀.1 := by
  classical
  let hlift := exists_pushforward_codomain hp.cofibered (rfl : p.obj x = p.obj x)
    (residueMorphism (p.obj x))
  let x' := Classical.choose hlift
  let f := Classical.choose (Classical.choose_spec hlift)
  let hx' := (Classical.choose_spec (Classical.choose_spec hlift)).1
  let x'F : p.Fiber (residueFieldObject.{u, v, w} Λ k) := ⟨x', hx'⟩
  let e : p.Fiber (residueFieldObject.{u, v, w} Λ k) ≌ Discrete PUnit.{u₁ + 1} :=
    Classical.choice hp.specialFiber
  let f' : e.functor.obj x'F ⟶ e.functor.obj x₀ := ⟨Subsingleton.elim _ _⟩
  let g : x'F ⟶ x₀ := e.fullyFaithfulFunctor.preimage f'
  exact f ≫ Functor.Fiber.fiberInclusion.map g

/-- An algebra isomorphism of the carriers of two objects of `𝒞_Λ` that is compatible
with the residue-field identifications is an isomorphism in `𝒞_Λ`. -/
noncomputable def artinianIsoOfAlgEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : A.carrier ≃ₐ[Λ] B.carrier)
    (hres : ∀ a : A,
      B.residueEquiv (IsLocalRing.residue B (e a)) =
        A.residueEquiv (IsLocalRing.residue A a)) : A ≅ B := by
  let f : A ⟶ B :=
    { hom := e.toAlgHom
      isLocal := IsLocalHom.of_surjective _ e.surjective
      residue_comm := hres }
  let g : B ⟶ A :=
    { hom := e.symm.toAlgHom
      isLocal := IsLocalHom.of_surjective _ e.symm.surjective
      residue_comm := fun b => by simpa using (hres (e.symm b)).symm }
  refine ⟨f, g, ?_, ?_⟩
  · apply ArtinianLocalAlgCat.hom_ext
    exact AlgHom.ext e.symm_apply_apply
  · apply ArtinianLocalAlgCat.hom_ext
    exact AlgHom.ext e.apply_symm_apply

/-- The projections of the induced map into a pullback, evaluated at an element. -/
private theorem lift_hom_apply
    {P X Y Z W : ArtinianLocalAlgCat.{u, v, w} Λ k} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hP : IsPullback fst snd f g) (a : W ⟶ X) (b : W ⟶ Y)
    (hab : a ≫ f = b ≫ g) (y : W) :
    fst.hom ((hP.lift a b hab).hom y) = a.hom y ∧
      snd.hom ((hP.lift a b hab).hom y) = b.hom y :=
  ⟨congrArg (fun q => q.hom y) (hP.lift_fst a b hab),
    congrArg (fun q => q.hom y) (hP.lift_snd a b hab)⟩

/-- The first coordinate of an element of the target of an infinitesimal-coordinate map is
its residue. -/
private theorem InfinitesimalMap.coordinate_fst
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₂ : A₂ ⟶ A} {h : A₁ ⟶ A₂} {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂}
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (b : S.target) :
    (S.coordinate b).1 = S.target.residueEquiv (IsLocalRing.residue S.target b) := by
  obtain ⟨t, rfl⟩ := S.g_surjective b
  rw [S.first]
  exact (pr₁.residue_comm t).trans (S.g.residue_comm t).symm

/-- The map from the fibre product `Y` to the pullback of the residue-field augmentations
induced by an infinitesimal-coordinate map is injective. -/
private theorem InfinitesimalMap.lift_injective
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {h : A₁ ⟶ A₂}
    {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂} (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (S : InfinitesimalMap f₂ h pr₁ pr₂)
    {P : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {fst : P ⟶ S.target} {snd : P ⟶ A₁}
    (hP : IsPullback fst snd (residueMorphism S.target) (residueMorphism A₁)) :
    Function.Injective (hP.lift S.g pr₁ (hom_residueFieldObject_ext _ _)).hom := by
  have hsurj₂ : Function.Surjective f₂.hom := hsmall.2.2.2.2.1
  have hfst := fun y => (lift_hom_apply hP S.g pr₁ (hom_residueFieldObject_ext _ _) y).1
  have hsnd := fun y => (lift_hom_apply hP S.g pr₁ (hom_residueFieldObject_ext _ _) y).2
  intro t s hts
  have hgt : S.g.hom t = S.g.hom s :=
    (hfst t).symm.trans ((congrArg fst.hom hts).trans (hfst s))
  have hpr₁ : pr₁.hom t = pr₁.hom s :=
    (hsnd t).symm.trans ((congrArg snd.hom hts).trans (hsnd s))
  have hdiff' :
      pr₂.hom t - h.hom (pr₁.hom t) =
        pr₂.hom s - h.hom (pr₁.hom s) := by
    simpa only [S.second] using
      congrArg Subtype.val (congrArg Prod.snd (congrArg S.coordinate hgt))
  rw [hpr₁] at hdiff'
  exact eq_of_isPullback_of_surjective hPB hsurj₂ (sub_left_inj.mp hdiff') hpr₁

/-- The map from the fibre product `Y` to the pullback of the residue-field augmentations
induced by an infinitesimal-coordinate map is surjective. -/
private theorem InfinitesimalMap.lift_surjective
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {h : A₁ ⟶ A₂} (hh : h ≫ f₂ = f₁)
    {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂} (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (S : InfinitesimalMap f₂ h pr₁ pr₂)
    {P : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {fst : P ⟶ S.target} {snd : P ⟶ A₁}
    (hP : IsPullback fst snd (residueMorphism S.target) (residueMorphism A₁))
    (hresS : Function.Surjective (residueMorphism S.target).hom) :
    Function.Surjective (hP.lift S.g pr₁ (hom_residueFieldObject_ext _ _)).hom := by
  have hsurj₂ : Function.Surjective f₂.hom := hsmall.2.2.2.2.1
  have hfst := fun y => (lift_hom_apply hP S.g pr₁ (hom_residueFieldObject_ext _ _) y).1
  have hsnd := fun y => (lift_hom_apply hP S.g pr₁ (hom_residueFieldObject_ext _ _) y).2
  intro n
  let u := fst.hom n
  let a := snd.hom n
  have hcompat : (residueMorphism S.target).hom u = (residueMorphism A₁).hom a :=
    congrArg (fun q => q.hom n) hP.w
  have hres : (S.coordinate u).1 = A₁.residueEquiv (IsLocalRing.residue A₁ a) := by
    calc
      (S.coordinate u).1 =
          S.target.residueEquiv (IsLocalRing.residue S.target u) := S.coordinate_fst u
      _ = (residueFieldObject Λ k).residueEquiv
          (IsLocalRing.residue _ ((residueMorphism S.target).hom u)) :=
            ((residueMorphism S.target).residue_comm u).symm
      _ = (residueFieldObject Λ k).residueEquiv
          (IsLocalRing.residue _ ((residueMorphism A₁).hom a)) :=
            congrArg (fun q : residueFieldObject Λ k =>
              (residueFieldObject Λ k).residueEquiv (IsLocalRing.residue _ q)) hcompat
      _ = A₁.residueEquiv (IsLocalRing.residue A₁ a) := (residueMorphism A₁).residue_comm a
  let i : RingHom.ker f₂.hom.toRingHom := (S.coordinate u).2
  have hpair : f₂.hom (h.hom a + (i : A₂)) = f₁.hom a := by
    rw [map_add, comp_eq_apply hh, show f₂.hom (i : A₂) = 0 from RingHom.mem_ker.mp i.2,
      add_zero]
  obtain ⟨y, hy₂, hy₁⟩ := exists_of_isPullback_of_surjective hPB hsurj₂ _ a hpair
  have hcoordY : S.coordinate (S.g.hom y) = S.coordinate u := by
    apply Prod.ext
    · rw [S.first, hy₁]
      exact hres.symm
    · apply Subtype.ext
      calc
        (S.coordinate (S.g.hom y)).2.1 = pr₂.hom y - h.hom (pr₁.hom y) :=
          congrArg Subtype.val (S.second y)
        _ = (i : A₂) := by rw [hy₂, hy₁]; simp
        _ = (S.coordinate u).2.1 := rfl
  have hgy : S.g.hom y = u := S.coordinate.injective hcoordY
  exact ⟨y, eq_of_isPullback_of_surjective hP hresS
    ((hfst y).trans hgy) ((hsnd y).trans hy₁)⟩

/-- The infinitesimal-coordinate map is a pullback of the residue-field augmentation of
`A₁` along that of its target: an element of the target and a compatible element of `A₁`
come from a unique element of the fibre product `Y`. -/
theorem infinitesimalMap_residue_pullback
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} (h : A₁ ⟶ A₂)
    (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (S : InfinitesimalMap f₂ h pr₁ pr₂) :
    IsPullback S.g pr₁ (residueMorphism S.target)
      (residueMorphism A₁) := by
  classical
  let resS := residueMorphism S.target
  let res₁ := residueMorphism A₁
  have hcomm : S.g ≫ resS = pr₁ ≫ res₁ := hom_residueFieldObject_ext _ _
  have hsurjRes : Function.Surjective resS.hom := by
    intro x
    let r : IsLocalRing.ResidueField S.target :=
      S.target.residueEquiv.symm (ULift.down x)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := S.target) r
    refine ⟨a, ?_⟩
    apply (ULift.algEquiv (R := Λ) (A := k)).injective
    change S.target.residueEquiv (IsLocalRing.residue S.target a) = ULift.down x
    simpa [r] using congrArg S.target.residueEquiv ha
  let newP := ArtinianLocalAlgCat.pullbackObj_of_surjective
    resS res₁ (Or.inl hsurjRes)
  let newFst := ArtinianLocalAlgCat.pullbackFst_of_surjective
    resS res₁ (Or.inl hsurjRes)
  let newSnd := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    resS res₁ (Or.inl hsurjRes)
  have hnewPB : IsPullback newFst newSnd resS res₁ :=
    ArtinianLocalAlgCat.isPullback_of_surjective
      resS res₁ (Or.inl hsurjRes)
  let φ : Y ⟶ newP := hnewPB.lift S.g pr₁ hcomm
  have hφfst : φ ≫ newFst = S.g := hnewPB.lift_fst _ _ _
  have hφsnd : φ ≫ newSnd = pr₁ := hnewPB.lift_snd _ _ _
  have hbij : Function.Bijective φ.hom :=
    ⟨S.lift_injective hPB hsmall hnewPB, S.lift_surjective hh hPB hsmall hnewPB hsurjRes⟩
  let eφ : Y.carrier ≃ₐ[Λ] newP.carrier := AlgEquiv.ofBijective φ.hom hbij
  have hresφ (x : Y) :
      newP.residueEquiv (IsLocalRing.residue newP (eφ x)) =
        Y.residueEquiv (IsLocalRing.residue Y x) := by
    have hfst : newFst.hom (φ.hom x) = S.g.hom x := congrArg (fun q => q.hom x) hφfst
    calc
      newP.residueEquiv (IsLocalRing.residue newP (eφ x)) =
          S.target.residueEquiv
            (IsLocalRing.residue S.target (newFst.hom (φ.hom x))) :=
              (newFst.residue_comm (φ.hom x)).symm
      _ = (S.coordinate (S.g.hom x)).1 := by rw [hfst, S.coordinate_fst]
      _ = Y.residueEquiv (IsLocalRing.residue Y x) := by
        rw [S.first]
        exact pr₁.residue_comm x
  let iφ : Y ≅ newP := artinianIsoOfAlgEquiv eφ hresφ
  have hiφMap : iφ.hom = φ := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  have hpull := hnewPB.of_iso' (P' := Y) (X' := S.target) (Y' := A₁)
    (Z' := residueFieldObject Λ k)
    (fst' := S.g) (snd' := pr₁) (f' := resS) (g' := res₁)
    iφ (Iso.refl S.target) (Iso.refl A₁)
    (Iso.refl (residueFieldObject Λ k))
    (by rw [hiφMap]; exact hφfst)
    (by rw [hiφMap]; exact hφsnd)
    (by simp)
    (by simp)
  simpa [iφ, eφ, resS, res₁] using hpull
/-- A map from `x₁` to the pushforward of `y` along the canonical
infinitesimal-coordinate map produces a lift `x₁ → x₂`. -/
@[stacks 06IT, sga "7 VI 1.5" "(2)"]
theorem exists_lift_of_pushforward_map
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (hS2 : SchlessingerConditionS2 p)
    {y x₁ x₂ x z : F}
    (a : y ⟶ x₁) (c : y ⟶ x₂) (a₁ : x₁ ⟶ x) (a₂ : x₂ ⟶ x)
    (hcomm : c ≫ a₂ = a ≫ a₁)
    (hPB : IsPullback (p.map c) (p.map a) (p.map a₂) (p.map a₁))
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (p.map a₂).hom.toRingHom))
    (h : p.obj x₁ ⟶ p.obj x₂)
    (hh : h ≫ p.map a₂ = p.map a₁)
    (target_eq : p.obj z =
      (infinitesimalMap (p.map a₁) (p.map a₂) hsmall h hh
        (p.map a) (p.map c) hPB).target)
    (q : y ⟶ z)
    (hqmap : p.map q =
      (infinitesimalMap (p.map a₁) (p.map a₂) hsmall h hh
        (p.map a) (p.map c) hPB).g ≫ eqToHom target_eq.symm)
    (_hq : p.IsCocartesian (p.map q) q)
    (lift : x₁ ⟶ z) :
    ∃ b : x₁ ⟶ x₂, b ≫ a₂ = a₁ := by
  classical
  let m := infinitesimalMap (p.map a₁) (p.map a₂) hsmall h hh (p.map a) (p.map c) hPB
  have htarget_m : p.obj z = m.target := by simpa [m] using target_eq
  let specialFiberEquiv := Classical.choice hp.specialFiber
  let x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k) :=
    specialFiberEquiv.inverse.obj ⟨PUnit.unit⟩
  let d : x₁ ⟶ x₀.1 := mapToSpecialFiber p hp x₀ x₁
  let e : z ⟶ x₀.1 := mapToSpecialFiber p hp x₀ z
  have hcomm' : q ≫ e = a ≫ d := maps_to_special_fiber_eq p hp x₀ (q ≫ e) (a ≫ d)
  have hlift' : lift ≫ e = d := maps_to_special_fiber_eq p hp x₀ (lift ≫ e) d
  have hdual : IsDualNumberProjection (p.map e) := by
    rw [isDualNumberProjection_iff]
    let I := RingHom.ker (p.map a₂).hom.toRingHom
    let _ : Module k I := smallExtensionKernelModule (p.map a₂) hsmall
    let _ : FiniteDimensional k I :=
      smallExtension_kernel_finiteDimensional (p.map a₂) hsmall
    let _ : Module kᵐᵒᵖ I := Module.compHom I {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
    let _ : Nonempty I := ⟨0⟩
    let _ : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    let S := smallExtensionSquareZeroTarget (p.map a₂) hsmall
    have hS : m.target = S.target := rfl
    let iε : (p.obj z).carrier ≃ₐ[Λ] DualNumber k :=
      (AlgEquiv.cast (R := Λ) (htarget_m.trans hS)).trans
        (smallExtensionSquareZeroDualNumberEquiv (p.map a₂) hsmall)
    let i₀ : (p.obj x₀.1).carrier ≃ₐ[Λ] k :=
      (AlgEquiv.cast (R := Λ) x₀.2).trans (ULift.algEquiv (R := Λ) (A := k))
    refine ⟨i₀, iε, ?_⟩
    ext t
    change i₀ ((p.map e).hom t) = TrivSqZeroExt.fst (iε t)
    have hmaps := hom_residueFieldObject_ext
      ((p.map e) ≫ eqToHom x₀.2) (residueMorphism (p.obj z))
    have heval := congrArg (fun f : p.obj z ⟶
        residueFieldObject.{u, v, w} Λ k => f.hom t) hmaps
    have hdown := congrArg ULift.down heval
    have hi₀ : i₀ ((p.map e).hom t) =
        ULift.down (((p.map e) ≫ eqToHom x₀.2).hom t) := by
      simpa [i₀, ArtinianLocalAlgCat.comp_hom] using
        artinianAlgEquivCast_ulift_apply x₀.2 ((p.map e).hom t)
    have hrid : ULift.down ((residueMorphism (p.obj z)).hom t) =
        (p.obj z).residueEquiv (residue (p.obj z) t) := by
      simp [residueMorphism, AlgHom.comp_apply]
    have htargetResidue :
        (p.obj z).residueEquiv (residue (p.obj z) t) =
          S.target.residueEquiv (residue S.target
            ((eqToHom (htarget_m.trans hS)).hom t)) :=
      ((eqToHom (htarget_m.trans hS)).residue_comm t).symm
    have hfst := smallExtensionSquareZeroDualNumberEquiv_residue
      (p.map a₂) hsmall ((eqToHom (htarget_m.trans hS)).hom t)
    calc
      i₀ ((p.map e).hom t) = ULift.down (((p.map e) ≫ eqToHom x₀.2).hom t) := hi₀
      _ = ULift.down ((residueMorphism (p.obj z)).hom t) := hdown
      _ = (p.obj z).residueEquiv (residue (p.obj z) t) := hrid
      _ = S.target.residueEquiv (residue S.target
          ((eqToHom (htarget_m.trans hS)).hom t)) := htargetResidue
      _ = TrivSqZeroExt.fst (iε t) := by
        rw [artinianAlgEquivCast_apply (htarget_m.trans hS)
          (smallExtensionSquareZeroDualNumberEquiv (p.map a₂) hsmall) t]
        exact hfst.symm
  have hres := infinitesimalMap_residue_pullback h hh (p.map a) (p.map c) hPB hsmall m
  have hE : eqToHom htarget_m ≫ residueMorphism m.target =
      p.map e ≫ eqToHom x₀.2 :=
    hom_residueFieldObject_ext _ _
  have hD : residueMorphism (p.obj x₁) = p.map d ≫ eqToHom x₀.2 :=
    hom_residueFieldObject_ext _ _
  have hpull : IsPullback (p.map q) (p.map a) (p.map e) (p.map d) := by
    apply hres.of_iso' (Iso.refl _) (eqToIso htarget_m) (Iso.refl _) (eqToIso x₀.2)
    · rw [hqmap]
      simp [m]
    · simp
    · exact hE
    · exact hD
  obtain ⟨s, hs⟩ :=
    (exists_section_iff_exists_dualNumberLift p hp.cofibered hS2
      q a e d hcomm' hdual hpull).mpr ⟨lift, hlift'⟩
  refine ⟨s ≫ c, ?_⟩
  calc
    (s ≫ c) ≫ a₂ = s ≫ (c ≫ a₂) := Category.assoc _ _ _
    _ = s ≫ (a ≫ a₁) := congrArg (fun f => s ≫ f) hcomm
    _ = (s ≫ a) ≫ a₁ := (Category.assoc _ _ _).symm
    _ = a₁ := by rw [hs]; simp

end

end Deformation

end
