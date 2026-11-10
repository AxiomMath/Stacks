module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.SimpleModule.Rank
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.SchlessingerConditions.SmallExtensionLift
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective
public import StacksFrontier.Deformation.TangentSpace.Predeformation
public import StacksFrontier.Deformation.Schlessinger.VersalImpliesS1
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# A criterion for versality of a formal object (Stacks 06IU)

A formal object of a predeformation category satisfying Schlessinger's conditions (S1) and
(S2) is versal precisely when its differential is surjective and every small-extension
diagram admits a filler on the underlying complete local algebras.

The proof is the one of the Stacks source. Versality is tested by the intrinsic lifting
criterion of Stacks 06HS, restricted to small extensions. Given a small extension `B → A`
and a diagram `ξ → x ← y` over it, the fibre product of the bases is formed (Stacks 06GH),
and the hypothesised lift of the map of underlying complete local algebras makes the
difference of the two coordinates land in the kernel; that produces the square-zero target
`k[ker]` and its surjection of Stacks 06IT, whose pushforward turns the lifting problem into
a problem about the tangent space. Surjectivity of the differential solves it. Conversely a
versal object has surjective differential, because a tangent vector is a diagram over the
dual numbers, which are a small extension of the residue field.

## Main results

* `Deformation.isVersal_iff_differential_surjective_and_base_lifts`: **Stacks 06IU**.

## Implementation notes

The morphism associated to the formal object is specified using a choice of pushforwards.
Its differential is independent of this choice up to the canonical identification. The
base-ring lifting condition asks only for a map of the bases; it does not assume a lift of
the formal-object morphism. The differential is the induced map on isomorphism classes
evaluated at `Deformation.artinianDualNumbers`. This presentation uses `ULift k` for its
rank-one module, allowing the Artinian carrier universe to vary independently of the
residue-field universe.

## References

* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
-/

-- This file proves Stacks 06IU. It uses throughout the square-zero-target apparatus that
-- Stacks 06IT (`Deformation/SchlessingerConditions/SmallExtensionLift.lean`) supplies
-- publicly. 06IT presents the target as a sigma type carrying its additive `coordinate` as an
-- independent field. On the canonical object the coordinates read through the ring
-- isomorphism agree definitionally with that field,
-- because `smallExtensionSquareZeroTarget` builds `coordinate` as the additive map underlying
-- `coordinateRingEquiv`, so reading the coordinates through the ring isomorphism needs no
-- bridging lemma -- only a `change`.

@[expose] public section

open CategoryTheory CategoryTheory.Limits
-- These transparency options are what
-- lets the proofs identify morphisms of based categories through the non-reducible
-- `abbrev`s of Stacks 06GX/06GW/06H3; they are search-strategy options and cannot affect
-- the axioms used by any declaration here.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Deformation

universe u v w uF vF uG vG

private lemma eqToHom_comp_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X X' Y Y' : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hX : X' = X) (hY : Y = Y')
    (f : X' ⟶ Y) (x : X') :
    (eqToHom hX.symm ≫ f ≫ eqToHom hY).hom ((eqToHom hX).hom x) =
      (eqToHom hY).hom (f.hom x) := by
  cases hX
  cases hY
  rfl

private lemma artinianUnderlying_map_eqToHom_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (h : A = A') (x : A) :
    (artinianUnderlying.map (eqToHom h)).hom x =
      (eqToHom h).hom x := by
  cases h
  rfl

private lemma artinianEqToHom_commAlg_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (h : A = A') (x : A) :
    (eqToHom h).hom x =
      (CommAlgCat.Hom.hom
        (eqToHom (congrArg
          (fun T : ArtinianLocalAlgCat.{u, max v w, w} Λ k => CommAlgCat.of Λ T) h))) x := by
  cases h
  rfl

private lemma completeEqToHom_commAlg_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R R' : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (h : R = R') (x : R) :
    (eqToHom h).hom x =
      (CommAlgCat.Hom.hom
        (eqToHom (congrArg
          (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k => CommAlgCat.of Λ T) h))) x := by
  cases h
  rfl

private lemma artinianEqToHom_hom_injective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A = A') :
    Function.Injective (eqToHom h).hom := by
  cases h
  intro x y hxy
  exact hxy

private lemma artinianEqToHom_symm_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A = A')
    (x : A') :
    (eqToHom h).hom ((eqToHom h.symm).hom x) = x := by
  cases h
  rfl

private lemma artinianEqToHom_symm_apply_left
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A = A')
    (x : A) :
    (eqToHom h.symm).hom ((eqToHom h).hom x) = x := by
  cases h
  rfl

/-- An isomorphism of Artinian local algebras is left inverse to its inverse, pointwise. -/
private lemma artinian_iso_hom_inv_id_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (e : X ≅ Y) (x : X) :
    e.inv.hom (e.hom.hom x) = x :=
  congrArg (fun q => q.hom x) e.hom_inv_id

/-- An isomorphism of Artinian local algebras is right inverse to its inverse, pointwise. -/
private lemma artinian_iso_inv_hom_id_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (e : X ≅ Y) (y : Y) :
    e.hom.hom (e.inv.hom y) = y :=
  congrArg (fun q => q.hom y) e.inv_hom_id

private lemma commAlgEqToHom_hom_injective
    {Λ : Type u} [CommRing Λ]
    {A A' : CommAlgCat.{v, u} Λ} (h : A = A') :
    Function.Injective (eqToHom h).hom := by
  cases h
  intro x y hxy
  exact hxy

private lemma completeEqToHom_hom_injective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R R' : CompleteLocalAlgCat.{u, max v w, w} Λ k} (h : R = R') :
    Function.Injective (eqToHom h).hom := by
  intro x y hxy
  have hcomm :
      (CommAlgCat.Hom.hom
        (eqToHom (congrArg (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k =>
          CommAlgCat.of Λ T) h))) x =
      (CommAlgCat.Hom.hom
        (eqToHom (congrArg (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k =>
          CommAlgCat.of Λ T) h))) y := by
    rw [← completeEqToHom_commAlg_apply h x,
      ← completeEqToHom_commAlg_apply h y]
    exact hxy
  exact commAlgEqToHom_hom_injective
    (congrArg (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k =>
      CommAlgCat.of Λ T) h) hcomm

private theorem smallExtension_kernel_ne_bot
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A' ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    RingHom.ker f.hom.toRingHom ≠ ⊥ := by
  intro h
  have hlen := hsmall.2.2.2.2.2
  change Module.length A' (RingHom.ker f.hom.toRingHom) = 1 at hlen
  rw [h] at hlen
  norm_num at hlen

@[instance_reducible]
private noncomputable def smallExtension_kernel_oppositeModule
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A' ⟶ A)
    [Module k (RingHom.ker f.hom.toRingHom)] :
    Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom) :=
  Module.compHom (RingHom.ker f.hom.toRingHom) {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

private def trivSqZeroExtAddEquiv
    {k : Type w} {I : Type v} [Semiring k] [AddCommGroup I] [Module k I] :
    TrivSqZeroExt k I ≃+ (k × I) where
  toFun x := (x.1, x.2)
  invFun x := (x.1, x.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl

private def infinitesimalDifference
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₂ : A₂ ⟶ A} (h : A₁ ⟶ A₂) (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (t : Y) :
    RingHom.ker f₂.hom.toRingHom :=
  ⟨pr₂.hom t - h.hom (pr₁.hom t), S.difference_mem t⟩

private theorem infinitesimalMap_coordinate_g
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₂ : A₂ ⟶ A} (h : A₁ ⟶ A₂) (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (t : Y) :
    S.coordinate (S.g.hom t) =
      (A₁.residueEquiv (IsLocalRing.residue A₁ (pr₁.hom t)),
       infinitesimalDifference h pr₁ pr₂ S t) := by
  apply Prod.ext
  · exact S.first t
  · exact S.second t

private theorem infinitesimalMap_coordinate_fst_residue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₂ : A₂ ⟶ A} (h : A₁ ⟶ A₂) (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (a : S.target) :
    (S.coordinate a).1 = S.target.residueEquiv (IsLocalRing.residue S.target a) := by
  obtain ⟨t, rfl⟩ := S.g_surjective a
  rw [infinitesimalMap_coordinate_g]
  exact (pr₁.residue_comm t).trans (S.g.residue_comm t).symm

private theorem infinitesimalMap_coordinate_algebraMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₂ : A₂ ⟶ A} (h : A₁ ⟶ A₂) (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (r : Λ) :
    S.coordinate (algebraMap Λ S.target.carrier r) = (algebraMap Λ k r, 0) := by
  have hg : S.g.hom (algebraMap Λ Y r) = algebraMap Λ S.target.carrier r := by
    simp
  rw [← hg, infinitesimalMap_coordinate_g h pr₁ pr₂ S]
  apply Prod.ext
  · have hp : pr₁.hom (algebraMap Λ Y r) = algebraMap Λ A₁ r := by simp
    rw [hp, ← IsLocalRing.ResidueField.algebraMap_eq]
    rw [← IsScalarTower.algebraMap_apply (R := Λ) (S := A₁)
      (A := IsLocalRing.ResidueField A₁)]
    exact A₁.residueEquiv.commutes r
  · apply Subtype.ext
    simp [infinitesimalDifference]

private theorem infinitesimalMap_coordinate_mul
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (_hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (_hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (t s : Y) :
    let I := RingHom.ker f₂.hom.toRingHom
    letI : Module k I := smallExtensionKernelModule f₂ hsmall
    S.coordinate (S.g.hom (t * s)) =
      ((S.coordinate (S.g.hom t)).1 * (S.coordinate (S.g.hom s)).1,
       (S.coordinate (S.g.hom t)).1 • (S.coordinate (S.g.hom s)).2 +
         (S.coordinate (S.g.hom s)).1 • (S.coordinate (S.g.hom t)).2) := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  let : Module k I := smallExtensionKernelModule f₂ hsmall
  let x := pr₁.hom t
  let y := pr₁.hom s
  let d := infinitesimalDifference h pr₁ pr₂ S t
  let e := infinitesimalDifference h pr₁ pr₂ S s
  have ht : pr₂.hom t = h.hom x + (d : A₂) := by
    dsimp [d, infinitesimalDifference, x]
    ring
  have hs : pr₂.hom s = h.hom y + (e : A₂) := by
    dsimp [e, infinitesimalDifference, y]
    ring
  have hdmax := kernel_mem_maximalIdeal f₂ d
  have hemax := kernel_mem_maximalIdeal f₂ e
  have hde : (d : A₂) * (e : A₂) = 0 :=
    smallExtension_kernel_annihilated f₂ hsmall (d : A₂) hdmax e
  have hdx : h.hom x * (e : A₂) =
      ((A₁.residueEquiv (IsLocalRing.residue A₁ x)) • e : I) := by
    have hscalar := smallExtension_kernel_scalar f₂ hsmall (h.hom x) e
    have hres := h.residue_comm x
    have hval := congrArg (fun z : I => (z : A₂)) hscalar
    simpa [Submodule.coe_smul, smul_eq_mul, hres] using hval
  have hdy : h.hom y * (d : A₂) =
      ((A₁.residueEquiv (IsLocalRing.residue A₁ y)) • d : I) := by
    have hscalar := smallExtension_kernel_scalar f₂ hsmall (h.hom y) d
    have hres := h.residue_comm y
    have hval := congrArg (fun z : I => (z : A₂)) hscalar
    simpa [Submodule.coe_smul, smul_eq_mul, hres] using hval
  have hsecond :
      (pr₂.hom (t * s) - h.hom (pr₁.hom (t * s)) : A₂) =
        ((A₁.residueEquiv (IsLocalRing.residue A₁ x)) • e : I) +
          ((A₁.residueEquiv (IsLocalRing.residue A₁ y)) • d : I) := by
    calc
      _ = pr₂.hom t * pr₂.hom s - h.hom (x * y) := by
        rw [map_mul (pr₂.hom), map_mul (pr₁.hom)]
      _ = h.hom x * (e : A₂) + h.hom y * (d : A₂) + (d : A₂) * (e : A₂) := by
        rw [ht, hs, map_mul]
        ring
      _ = _ := by
        rw [hdx, hdy]
        rw [hde]
        simp
  apply Prod.ext
  · rw [S.first (t * s), S.first t, S.first s]
    simp [map_mul]
  · apply Subtype.ext
    have hcoords := infinitesimalMap_coordinate_g h pr₁ pr₂ S
    rw [hcoords (t * s), hcoords t, hcoords s]
    change (pr₂.hom (t * s) - h.hom (pr₁.hom (t * s)) : A₂) = _
    simpa [x, y] using hsecond

private noncomputable def infinitesimalMapTargetRingEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) :
    let I := RingHom.ker f₂.hom.toRingHom
    letI : Module k I := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ I := Module.compHom I {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
    letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    S.target.carrier ≃+* TrivSqZeroExt k I := by
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
  let c : S.target.carrier ≃+ TrivSqZeroExt k I :=
    S.coordinate.trans trivSqZeroExtAddEquiv.symm
  let φ : S.target.carrier →+* TrivSqZeroExt k I := {
    toFun := fun a => trivSqZeroExtAddEquiv.symm (S.coordinate a)
    map_one' := by
      change trivSqZeroExtAddEquiv.symm (S.coordinate 1) = 1
      have hgo : S.g.hom (1 : Y) = 1 := map_one S.g.hom
      rw [← hgo]
      rw [infinitesimalMap_coordinate_g h pr₁ pr₂ S (1 : Y)]
      simp [infinitesimalDifference, trivSqZeroExtAddEquiv]
      rfl
    map_mul' := by
      intro a b
      obtain ⟨t, rfl⟩ := S.g_surjective a
      obtain ⟨s, rfl⟩ := S.g_surjective b
      have hgmul : S.g.hom (t * s) = S.g.hom t * S.g.hom s :=
        map_mul S.g.hom t s
      rw [← hgmul]
      have hm := infinitesimalMap_coordinate_mul hsmall h hh pr₁ pr₂ hPB S t s
      rw [hm]
      apply TrivSqZeroExt.ext
      · rfl
      · rfl
    map_zero' := c.map_zero
    map_add' := c.map_add }
  exact RingEquiv.ofBijective φ c.bijective

private theorem infinitesimalMapTargetRingEquiv_algebraMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) (r : Λ) :
    let I := RingHom.ker f₂.hom.toRingHom
    letI : Module k I := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ I := Module.compHom I {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
    letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    infinitesimalMapTargetRingEquiv hsmall h hh pr₁ pr₂ hPB S
        (algebraMap Λ S.target.carrier r) =
      trivSqZeroExtAddEquiv.symm (algebraMap Λ k r, 0) := by
  let I := RingHom.ker f₂.hom.toRingHom
  let : Module k I := smallExtensionKernelModule f₂ hsmall
  let : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  let : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  change trivSqZeroExtAddEquiv.symm
      (S.coordinate (algebraMap Λ S.target.carrier r)) = _
  rw [infinitesimalMap_coordinate_algebraMap]

private lemma completeEqToHom_quotient_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R R' : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (h : R = R') (I : Ideal R') (x : R) :
    (Ideal.Quotient.mk I) ((eqToHom h).hom x) =
      (Ideal.Quotient.mkₐ Λ I)
        ((CommAlgCat.Hom.hom
          (eqToHom (congrArg
            (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k => CommAlgCat.of Λ T) h))) x) := by
  rw [Ideal.Quotient.mkₐ_eq_mk (R₁ := Λ)]
  exact congrArg (Ideal.Quotient.mk I) (completeEqToHom_commAlg_apply h x)

private theorem completeLocalEqToHom_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (h : R = S) (x : R) :
    (eqToHom h).hom x =
      cast (congrArg (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k => T.carrier) h) x := by
  cases h
  rfl

/-- The quotient map by the zero ideal is injective. -/
private lemma quotient_mk_injective_of_eq_bot {R : Type*} [CommRing R] {I : Ideal R}
    (h : I = ⊥) : Function.Injective (Ideal.Quotient.mk I) :=
  (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, h])

private theorem truncatedArtinianIdeal_eq_bot
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (n : ℕ) :
    AdicTruncation.ideal
      (artinianToComplete.obj (AdicTruncation.obj R n)) n = ⊥ := by
  let I := AdicTruncation.ideal R n
  let q : R.carrier →+* (R.carrier ⧸ I) := Ideal.Quotient.mk I
  let : Nontrivial (R.carrier ⧸ I) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  let : IsLocalRing (R.carrier ⧸ I) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hI : I < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top
  have hmax : IsLocalRing.maximalIdeal (R.carrier ⧸ I) =
      (IsLocalRing.maximalIdeal R.carrier).map q := by
    ext z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [q, sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hI.ne)]
  change IsLocalRing.maximalIdeal (R.carrier ⧸ I) ^ (n + 1) = ⊥
  rw [hmax, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
  change IsLocalRing.maximalIdeal R.carrier ^ (n + 1) ≤ RingHom.ker q
  rw [Ideal.mk_ker]

private theorem formalObject_component_isStronglyCocartesian
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (i : ξ ⟶ η) (n : ℕ) :
    p.IsStronglyCocartesian
      ((AdicTruncation.functor n).map i.base) (i.app n) := by
  let : p.IsHomLift ((AdicTruncation.functor n).map i.base) (i.app n) :=
    i.app_lift n
  exact all_cocartesian hp _ _

private theorem stronglyCocartesian_factor
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : C ⥤ D) {x y z : C}
    (f : p.obj x ⟶ p.obj y) (i : x ⟶ y)
    (hi : p.IsStronglyCocartesian f i)
    (g : p.obj y ⟶ p.obj z) (a : x ⟶ z)
    (h : p.map a = f ≫ g) :
    ∃ b : y ⟶ z, p.IsHomLift g b ∧ i ≫ b = a := by
  let := hi
  let : p.IsHomLift (f ≫ g) a := by
    exact h ▸ IsHomLift.map p a
  obtain ⟨b, ⟨hb, hfac⟩, _⟩ :=
    Functor.IsStronglyCocartesian.universal_property p f i g (f ≫ g) rfl a
  exact ⟨b, hb, hfac⟩

private theorem formalObject_exists_pushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) {S : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (f : ξ.base ⟶ S) :
    ∃ η : FormalObject p, ∃ i : ξ ⟶ η,
      (FormalObject.projection (p := p)).IsHomLift f i := by
  let q := FormalObject.projection (p := p)
  let hq := formalObjectProjection_isCofiberedInGroupoids p
    hp.cofibered
  obtain ⟨ηop, iop, hi⟩ := hq.exists_lift f.op (Opposite.op ξ) rfl
  refine ⟨Opposite.unop ηop, Opposite.unop iop, ?_⟩
  exact CategoryTheory.isHomLift_unop q f.op (Opposite.unop iop).op (inst := hi)

private theorem factor_formal_morphism_through_pushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {ξ y x : FormalObject p} (a : ξ ⟶ x) (g : y ⟶ x)
    (b : ξ.base ⟶ y.base) (hb : b ≫ g.base = a.base) :
    ∃ η : FormalObject p, ∃ hη : η.base = y.base,
      ∃ i : ξ ⟶ η, ∃ j : η ⟶ x,
        (FormalObject.projection (p := p)).IsHomLift b i ∧
        i ≫ j = a ∧ j.base = eqToHom hη ≫ g.base := by
  let q := FormalObject.projection (p := p)
  obtain ⟨η, i, hi⟩ := formalObject_exists_pushforward hp ξ b
  have hη : η.base = y.base := IsHomLift.codomain_eq q b i
  have hmap : q.map i = b ≫ eqToHom hη.symm := by
    let := hi
    simpa using IsHomLift.fac' q b i
  let f : η.base ⟶ x.base := eqToHom hη ≫ g.base
  have hcomp : q.map i ≫ f = q.map a := by
    rw [hmap]
    change (b ≫ eqToHom hη.symm) ≫ (eqToHom hη ≫ g.base) = a.base
    calc
      (b ≫ eqToHom hη.symm) ≫ (eqToHom hη ≫ g.base) = b ≫ g.base := by
        simp [Category.assoc]
      _ = a.base := hb
  obtain ⟨j, hj, hfac⟩ := cofibered_factor q
    (formalObjectProjection_isCofiberedInGroupoids p hp.cofibered)
    i a f hcomp
  refine ⟨η, hη, i, j, hi, hfac, ?_⟩
  simpa [q, f] using hj

private theorem formalObjectHom_comp_app
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {ξ η ζ : FormalObject p} (f : ξ ⟶ η) (g : η ⟶ ζ) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

private theorem classOf_eq_of_iso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (hp : IsCofiberedInGroupoids 𝓕.p)
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x y : 𝓕.p.Fiber A) (h : Nonempty (x ≅ y)) :
    classOf 𝓕 hp x = classOf 𝓕 hp y := by
  apply (Equiv.cast (isomorphismClasses_obj 𝓕 hp A)).injective
  have hx := classOf_eq 𝓕 hp x
  have hy := classOf_eq 𝓕 hp y
  change cast (isomorphismClasses_obj 𝓕 hp A)
      (classOf 𝓕 hp x) =
    cast (isomorphismClasses_obj 𝓕 hp A)
      (classOf 𝓕 hp y)
  rw [hx, hy]
  exact Quotient.sound h

private theorem associated_pointInclusion_isHomLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (assoc : AssociatedMorphism
      (p := p) ξ pushforwards)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    p.IsHomLift (assoc.factor α) (assoc.pointInclusion α) := by
  let n := assoc.level α
  let P := pushforwards (assoc.factor α)
  let src : p.Fiber (AdicTruncation.obj ξ.base n) :=
    ⟨ξ.level n, ξ.level_eq n⟩
  have hinc : p.IsHomLift (assoc.factor α) (P.inclusion src) :=
    (P.cocartesian src).toIsHomLift
  have hP : p.obj (P.obj src).1 = α.1 :=
    IsHomLift.codomain_eq p (assoc.factor α) (P.inclusion src)
  have hψ : p.obj (assoc.toBasedFunctor.obj α) = α.1 :=
    assoc.toBasedFunctor.w_obj α
  have hcast : p.IsHomLift (𝟙 α.1) (eqToHom (assoc.obj_eq α).symm) := by
    apply IsHomLift.of_fac p _ _ hP hψ
    simp only [eqToHom_map, eqToHom_trans]
    have hpath : (hP.symm.trans
        (congrArg p.obj (assoc.obj_eq α).symm)).trans hψ = rfl :=
      Subsingleton.elim _ _
    rw [hpath]
    simp
  have hpoint : assoc.pointInclusion α =
      P.inclusion src ≫ eqToHom (assoc.obj_eq α).symm := by
    rw [← assoc.pointInclusion_eq α]
    simp
  rw [hpoint]
  let := hinc
  let := hcast
  simpa using IsHomLift.comp_lift_id_right' p (assoc.factor α)
    (P.inclusion src) α.1 (eqToHom (assoc.obj_eq α).symm)

private theorem descend_through_chosen_pushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (pushforwards : ChosenPushforwards p)
    {A B C : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A ⟶ B) (g : B ⟶ C) (fg : A ⟶ C) (hfg : fg = f ≫ g)
    (x : p.Fiber A) (z : p.Fiber C) (φ : x.1 ⟶ z.1)
    (hφ : p.IsHomLift fg φ) :
    ∃ ψ : ((pushforwards f).obj x).1 ⟶ z.1,
      p.IsHomLift g ψ ∧ (pushforwards f).inclusion x ≫ ψ = φ := by
  let P := pushforwards f
  let i := P.inclusion x
  have hi : p.IsStronglyCocartesian f i := P.cocartesian x
  let := hi
  let : p.IsHomLift (f ≫ g) φ := hfg ▸ hφ
  obtain ⟨ψ, ⟨hψ, hfac⟩, _⟩ :=
    Functor.IsStronglyCocartesian.universal_property p f i g (f ≫ g) rfl φ
  exact ⟨ψ, hψ, hfac⟩

private theorem exists_fiber_iso_of_mapIsomorphismClasses_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (z : 𝓖.p.Fiber A)
    (hsurj : Function.Surjective
      (mapIsomorphismClasses h𝓕 h𝓖 φ A)) :
    ∃ x : 𝓕.p.Fiber A,
      Nonempty ((fiberFunctor φ A).obj x ≅ z) := by
  obtain ⟨c, hc⟩ := hsurj (classOf 𝓖 h𝓖 z)
  obtain ⟨x, hx⟩ := classOf_surjective 𝓕 h𝓕 A c
  have hclass :
      classOf 𝓖 h𝓖 ((fiberFunctor φ A).obj x) =
        classOf 𝓖 h𝓖 z := by
    calc
      _ = mapIsomorphismClasses h𝓕 h𝓖 φ A
          (classOf 𝓕 h𝓕 x) := by
            rw [mapIsomorphismClasses_classOf]
      _ = mapIsomorphismClasses h𝓕 h𝓖 φ A c := by rw [hx]
      _ = classOf 𝓖 h𝓖 z := hc
  have hq :
      cast (isomorphismClasses_obj 𝓖 h𝓖 A)
          (classOf 𝓖 h𝓖 ((fiberFunctor φ A).obj x)) =
        cast (isomorphismClasses_obj 𝓖 h𝓖 A)
          (classOf 𝓖 h𝓖 z) :=
    congrArg (cast (isomorphismClasses_obj 𝓖 h𝓖 A)) hclass
  rw [classOf_eq, classOf_eq] at hq
  obtain ⟨i⟩ := Quotient.exact hq
  exact ⟨x, ⟨i⟩⟩

private theorem mapIsomorphismClasses_surjective_of_iso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (e : A ≅ B)
    (hsurj : Function.Surjective
      (mapIsomorphismClasses h𝓕 h𝓖 φ A)) :
    Function.Surjective (mapIsomorphismClasses h𝓕 h𝓖 φ B) := by
  intro b
  let c := (isomorphismClasses 𝓖 h𝓖).map e.inv b
  obtain ⟨a, ha⟩ := hsurj c
  refine ⟨(isomorphismClasses 𝓕 h𝓕).map e.hom a, ?_⟩
  rw [mapIsomorphismClasses_naturality h𝓕 h𝓖 φ e.hom a, ha]
  change (isomorphismClasses 𝓖 h𝓖).map e.hom
    ((isomorphismClasses 𝓖 h𝓖).map e.inv b) = b
  rw [← Functor.map_comp_apply]
  simp

private noncomputable def smallExtensionDualNumberIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A' ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    let I := RingHom.ker f.hom.toRingHom
    letI : Module k I := smallExtensionKernelModule f hsmall
    letI : Module kᵐᵒᵖ I := Module.compHom I {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y => by
        change MulOpposite.unop y * MulOpposite.unop x =
          MulOpposite.unop x * MulOpposite.unop y
        exact mul_comm _ _
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    artinianDualNumbers Λ k ≅
      (smallExtensionSquareZeroTarget f hsmall).target := by
  classical
  let I := RingHom.ker f.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f hsmall
  have hdim : Module.finrank k I = 1 := smallExtension_kernel_finrank_eq_one f hsmall
  letI : FiniteDimensional k I := FiniteDimensional.of_finrank_eq_succ hdim
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  let S := smallExtensionSquareZeroTarget f hsmall
  let eI : ULift.{v} k ≃ₗ[k] I :=
    LinearEquiv.ofFinrankEq (ULift.{v} k) I (by simp [hdim])
  let V0 := FGModuleCat.of k (ULift.{v} k)
  let V := FGModuleCat.of k I
  let eV : V0 ≅ V := {
    hom := FGModuleCat.ofHom eI.toLinearMap
    inv := FGModuleCat.ofHom eI.symm.toLinearMap
    hom_inv_id := by ext x; exact congrArg ULift.down (eI.symm_apply_apply x)
    inv_hom_id := by ext x; exact congrArg Subtype.val (eI.apply_symm_apply x) }
  let T := (squareZeroExtensionArtinian Λ k).obj V
  letI : Algebra Λ (TrivSqZeroExt k I) := T.algebra
  let eAlg : T.carrier ≃ₐ[Λ] S.target.carrier :=
    AlgEquiv.ofRingEquiv (f := S.coordinateRingEquiv.symm) (by
      intro r
      have hc : S.coordinateRingEquiv
          (algebraMap Λ S.target.carrier r) = (algebraMap Λ k r, (0 : I)) :=
        S.algebraMap_eq r
      change S.coordinateRingEquiv.symm (algebraMap Λ T.carrier r) =
        algebraMap Λ S.target.carrier r
      apply S.coordinateRingEquiv.injective
      rw [S.coordinateRingEquiv.apply_symm_apply, hc]
      apply TrivSqZeroExt.ext
      · change TrivSqZeroExt.fst (algebraMap Λ (TrivSqZeroExt k I) r) =
          TrivSqZeroExt.fst (TrivSqZeroExt.inl (algebraMap Λ k r))
        rfl
      · change TrivSqZeroExt.snd (algebraMap Λ (TrivSqZeroExt k I) r) =
          TrivSqZeroExt.snd (TrivSqZeroExt.inl (algebraMap Λ k r))
        rfl)
  have hres : ∀ t : T,
      S.target.residueEquiv (IsLocalRing.residue S.target (eAlg t)) =
        T.residueEquiv (IsLocalRing.residue T t) := by
    intro t
    rw [squareZeroExtensionArtinian_residue Λ k V t]
    calc
      S.target.residueEquiv (IsLocalRing.residue S.target (eAlg t)) =
          (S.coordinate (eAlg t)).1 := (S.residue_eq (eAlg t)).symm
      _ = t.1 := by
        change TrivSqZeroExt.fst
          (S.coordinateRingEquiv (S.coordinateRingEquiv.symm t)) = t.1
        exact congrArg Prod.fst (S.coordinateRingEquiv.apply_symm_apply t)
  let eTS : T ≅ S.target := artinianIsoOfAlgEquiv eAlg hres
  exact (squareZeroExtensionArtinian Λ k).mapIso eV ≪≫ eTS

private noncomputable def smallExtensionInfinitesimalTargetIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f₂.hom.toRingHom))
    (h : A₁ ⟶ A₂) (hh : h ≫ f₂ = f₁)
    (pr₁ : Y ⟶ A₁) (pr₂ : Y ⟶ A₂)
    (hPB : IsPullback pr₂ pr₁ f₂ f₁)
    (S : InfinitesimalMap f₂ h pr₁ pr₂) :
    let I := RingHom.ker f₂.hom.toRingHom
    letI : Module k I := smallExtensionKernelModule f₂ hsmall
    letI : Module kᵐᵒᵖ I := smallExtension_kernel_oppositeModule f₂
    letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    (smallExtensionSquareZeroTarget f₂ hsmall).target ≅ S.target := by
  classical
  let I := RingHom.ker f₂.hom.toRingHom
  letI : Module k I := smallExtensionKernelModule f₂ hsmall
  letI : Module kᵐᵒᵖ I := smallExtension_kernel_oppositeModule f₂
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  have hdim : Module.finrank k I = 1 := smallExtension_kernel_finrank_eq_one f₂ hsmall
  letI : FiniteDimensional k I := FiniteDimensional.of_finrank_eq_succ hdim
  let S₀ := smallExtensionSquareZeroTarget f₂ hsmall
  let e₀ := S₀.coordinateRingEquiv
  let e₁ := infinitesimalMapTargetRingEquiv hsmall h hh pr₁ pr₂ hPB S
  let eAlg : S₀.target.carrier ≃ₐ[Λ] S.target.carrier :=
    AlgEquiv.ofRingEquiv (f := e₀.trans e₁.symm) (by
      intro r
      apply e₁.injective
      change e₁ (e₁.symm (e₀ (algebraMap Λ S₀.target.carrier r))) =
        e₁ (algebraMap Λ S.target.carrier r)
      rw [e₁.apply_symm_apply,
        infinitesimalMapTargetRingEquiv_algebraMap hsmall h hh pr₁ pr₂ hPB S r]
      -- `e₀` is `S₀.coordinateRingEquiv`, and on the canonical presentation the additive
      -- `coordinate` field is the additive map underlying it, so `algebraMap_eq` applies up
      -- to definitional unfolding -- `exact` absorbs that where `rw` cannot match it.
      exact S₀.algebraMap_eq r)
  have hres : ∀ a : S₀.target.carrier,
      S.target.residueEquiv (IsLocalRing.residue S.target (eAlg a)) =
        S₀.target.residueEquiv (IsLocalRing.residue S₀.target a) := by
    intro a
    have hcoord : S.coordinate (eAlg a) = trivSqZeroExtAddEquiv (e₀ a) := by
      have hh := congrArg trivSqZeroExtAddEquiv (e₁.apply_symm_apply (e₀ a))
      change S.coordinate (e₁.symm (e₀ a)) = trivSqZeroExtAddEquiv (e₀ a) at hh
      exact hh
    calc
      _ = (S.coordinate (eAlg a)).1 :=
        (infinitesimalMap_coordinate_fst_residue h pr₁ pr₂ S (eAlg a)).symm
      _ = (e₀ a).1 := by rw [hcoord]; rfl
      _ = S₀.target.residueEquiv (IsLocalRing.residue S₀.target a) := S₀.residue_eq a
  exact artinianIsoOfAlgEquiv eAlg hres

private theorem smallExtension_conj
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A B' A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : B ⟶ A) (eS : B' ≅ B) (eT : A ≅ A')
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (eS.hom ≫ f ≫ eT.hom).hom.toRingHom) := by
  classical
  rcases hsmall with ⟨_, _, _, _, hsurj, hlen⟩
  let g := eS.hom ≫ f ≫ eT.hom
  let : Algebra B' B := eS.hom.hom.toRingHom.toAlgebra
  let : Module B' (RingHom.ker f.hom.toRingHom) :=
    Module.compHom _ eS.hom.hom.toRingHom
  have hTleft : Function.LeftInverse eT.inv.hom eT.hom.hom := artinian_iso_hom_inv_id_apply eT
  have hTright : Function.LeftInverse eT.hom.hom eT.inv.hom := artinian_iso_inv_hom_id_apply eT
  have hSleft : Function.LeftInverse eS.inv.hom eS.hom.hom := artinian_iso_hom_inv_id_apply eS
  have hSright : Function.LeftInverse eS.hom.hom eS.inv.hom := artinian_iso_inv_hom_id_apply eS
  let ek : RingHom.ker g.hom.toRingHom ≃ₗ[B']
      RingHom.ker f.hom.toRingHom :=
    { toFun := fun x => ⟨eS.hom.hom x.1, by
        have hg := RingHom.mem_ker.mp x.2
        change eT.hom.hom (f.hom (eS.hom.hom x.1)) = 0 at hg
        apply RingHom.mem_ker.mpr
        apply hTleft.injective
        simpa using hg⟩
      invFun := fun x => ⟨eS.inv.hom x.1, by
        have he : eS.hom.hom (eS.inv.hom x.1) = x.1 := hSright x.1
        apply RingHom.mem_ker.mpr
        change eT.hom.hom (f.hom (eS.hom.hom (eS.inv.hom x.1))) = 0
        rw [he]
        have hx := RingHom.mem_ker.mp x.2
        change f.hom x.1 = 0 at hx
        simpa using congrArg eT.hom.hom hx⟩
      left_inv x := Subtype.ext (hSleft x.1)
      right_inv x := Subtype.ext (hSright x.1)
      map_add' := by intro x y; ext; exact map_add eS.hom.hom _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        change eS.hom.hom (r * x.1) = eS.hom.hom r * eS.hom.hom x.1
        exact map_mul eS.hom.hom r x.1 }
  let : RingHomSurjective eS.hom.hom.toRingHom := ⟨hSright.surjective⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    hTright.surjective.comp (hsurj.comp hSright.surjective), ?_⟩
  change Module.length B' (RingHom.ker g.hom.toRingHom) = 1
  calc
    Module.length B' (RingHom.ker g.hom.toRingHom) =
        Module.length B' (RingHom.ker f.hom.toRingHom) := ek.length_eq
    _ = Module.length B (RingHom.ker f.hom.toRingHom) :=
      Module.length_eq_of_surjective (M := RingHom.ker f.hom.toRingHom) hSright.surjective
    _ = 1 := hlen

private theorem exists_level_map_to_target_of_class_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (hS : IsCofiberedInGroupoids
      (Functor.Elements.π (restrictedCoyoneda ξ.base)))
    (hT : IsCofiberedInGroupoids p)
    (assoc : AssociatedMorphism
      (p := p) ξ pushforwards)
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (z : p.Fiber A)
    (hsurj : Function.Surjective
      (mapIsomorphismClasses hS hT assoc.toBasedFunctor A)) :
    ∃ s : (BasedCategory.ofFunctor
        (Functor.Elements.π (restrictedCoyoneda ξ.base))).p.Fiber A,
      ∃ e : (fiberFunctor assoc.toBasedFunctor A).obj s ≅ z,
      ∃ j : ξ.level (assoc.level s.1) ⟶ z.1,
        j = assoc.pointInclusion s.1 ≫ e.hom.1 ∧
        p.IsHomLift (assoc.factor s.1 ≫ eqToHom s.2) j := by
  obtain ⟨s, hiso⟩ := exists_fiber_iso_of_mapIsomorphismClasses_surjective
    hS hT assoc.toBasedFunctor A z hsurj
  let e : (fiberFunctor assoc.toBasedFunctor A).obj s ≅ z :=
    Classical.choice hiso
  let α : (restrictedCoyoneda ξ.base).Elements := s.1
  have hpoint := associated_pointInclusion_isHomLift ξ pushforwards assoc α
  have hcod : p.obj (assoc.toBasedFunctor.obj α) = A :=
    (assoc.toBasedFunctor.w_obj α).trans s.2
  have hpoint' : p.IsHomLift
      (assoc.factor α ≫ eqToHom s.2) (assoc.pointInclusion α) := by
    apply IsHomLift.of_fac' p _ _ (ξ.level_eq (assoc.level α)) hcod
    let := hpoint
    have hf := IsHomLift.fac' p (assoc.factor α) (assoc.pointInclusion α)
    simpa [Category.assoc] using hf
  let := hpoint'
  have he : p.IsHomLift (𝟙 A) e.hom.1 := e.hom.2
  let := he
  have hj : p.IsHomLift (assoc.factor α ≫ eqToHom s.2)
      (assoc.pointInclusion α ≫ e.hom.1) :=
    IsHomLift.comp_lift_id_right' p (assoc.factor α ≫ eqToHom s.2)
      (assoc.pointInclusion α) A e.hom.1
  exact ⟨s, e, assoc.pointInclusion α ≫ e.hom.1, rfl, hj⟩


private noncomputable def adicTruncationPoint
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (n : ℕ) :
    R ⟶ artinianToComplete.obj (AdicTruncation.obj R n) := by
  letI : Nontrivial (R.carrier ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  letI : IsLocalRing (R.carrier ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  let f : R.carrier →ₐ[Λ] AdicTruncation.obj R n :=
    Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)
  have hf : IsLocalHom f.toRingHom :=
    IsLocalHom.of_surjective f.toRingHom Ideal.Quotient.mk_surjective
  refine { hom := f, isLocal := hf, residue_comm := ?_ }
  intro x
  exact AdicTruncation.residueEquiv_residue_mk R n x

private lemma exists_factor_through_adicTruncation
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (α : (restrictedCoyoneda R).obj A)
    {n : ℕ} (hn : IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ a : AdicTruncation.obj R n ⟶ A,
      a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom := by
  have : IsLocalHom α.hom.toRingHom := α.isLocal
  let : Nontrivial (R.carrier ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  let : IsLocalRing (R.carrier ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  have hker : AdicTruncation.ideal R n ≤ RingHom.ker α.hom.toRingHom := by
    change AdicTruncation.ideal R n ≤
      (⊥ : Ideal (artinianToComplete.obj A)).comap α.hom.toRingHom
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact (Ideal.pow_right_mono
      (IsLocalRing.map_maximalIdeal_le α.hom.toRingHom) _).trans_eq hn
  let f := Ideal.Quotient.liftₐ (AdicTruncation.ideal R n) α.hom hker
  have hf : IsLocalHom f.toRingHom := by
    constructor
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.mk (AdicTruncation.ideal R n)).isUnit_map
      (α.isLocal.map_nonunit r hx)
  refine ⟨{ hom := f, isLocal := hf, residue_comm := ?_ }, ?_⟩
  · intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.residueEquiv (IsLocalRing.residue A (α.hom r)) =
      AdicTruncation.residueEquiv R n
        (IsLocalRing.residue _ (Ideal.Quotient.mk (AdicTruncation.ideal R n) r))
    rw [AdicTruncation.residueEquiv_residue_mk]
    exact α.residue_comm r
  · ext r
    rfl

private lemma exists_adic_factorization
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (α : (restrictedCoyoneda R).obj A) :
    ∃ n : ℕ, ∃ a : AdicTruncation.obj R n ⟶ A,
      a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom := by
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have hnil : IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥ := by
    simp [pow_succ, hn]
  obtain ⟨a, ha⟩ := exists_factor_through_adicTruncation α hnil
  exact ⟨n, a, ha⟩

private noncomputable def adicTruncationMapLE
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    {n m : ℕ} (hn : n ≤ m) : AdicTruncation.obj R m ⟶ AdicTruncation.obj R n := by
  let Im := AdicTruncation.ideal R m
  let In := AdicTruncation.ideal R n
  have hIm : Im ≤ In :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right hn 1)
  let f : AdicTruncation.obj R m →ₐ[Λ] AdicTruncation.obj R n :=
    Ideal.Quotient.factorₐ Λ hIm
  letI : Nontrivial (R.carrier ⧸ Im) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R m))
  letI : IsLocalRing (R.carrier ⧸ Im) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R m))
  letI : Nontrivial (R.carrier ⧸ In) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  letI : IsLocalRing (R.carrier ⧸ In) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  refine { hom := f, isLocal := ?_, residue_comm := ?_ }
  · exact IsLocalHom.of_surjective f.toRingHom (Ideal.Quotient.factor_surjective hIm)
  · intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change AdicTruncation.residueEquiv R n
        (IsLocalRing.residue _ (Ideal.Quotient.factorₐ Λ hIm
          (Ideal.Quotient.mk Im r))) =
      AdicTruncation.residueEquiv R m
        (IsLocalRing.residue _ (Ideal.Quotient.mk Im r))
    rw [Ideal.Quotient.factorₐ_apply_mk]
    dsimp only [Im, In]
    rw [AdicTruncation.residueEquiv_residue_mk,
      AdicTruncation.residueEquiv_residue_mk]

/-- Precomposing a factorization through level `n` with the transition from level `m ≥ n`
gives a factorization through level `m`. -/
private lemma adicTruncationMapLE_comp_factorization
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n m : ℕ} (hn : n ≤ m)
    (a : AdicTruncation.obj R n ⟶ A) (φ : R.carrier →ₐ[Λ] A)
    (ha : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = φ) :
    (adicTruncationMapLE R hn ≫ a).hom.comp
      (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R m)) = φ := by
  rw [← ha]
  rfl

/-- Two maps out of a truncation that agree after the quotient map from `R` are equal. -/
private lemma comp_eq_of_comp_mk
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n m : ℕ}
    (t : AdicTruncation.obj R n ⟶ AdicTruncation.obj R m) (c : AdicTruncation.obj R m ⟶ A)
    (d : AdicTruncation.obj R n ⟶ A)
    (ht : t.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) =
      Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R m))
    (hd : d.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) =
      c.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R m))) :
    t ≫ c = d := by
  apply ArtinianLocalAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  rw [hd, ← ht]
  rfl

private lemma exists_common_adic_factorization_above
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (α : (restrictedCoyoneda R).obj A)
    (β : (restrictedCoyoneda R).obj B)
    (m : ℕ) (a₀ : AdicTruncation.obj R m ⟶ A)
    (ha₀ : a₀.hom.comp
      (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R m)) = α.hom) :
    ∃ n : ℕ, m ≤ n ∧ ∃ a : AdicTruncation.obj R n ⟶ A,
      ∃ b : AdicTruncation.obj R n ⟶ B,
        a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom ∧
        b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = β.hom := by
  obtain ⟨nβ, bβ, hbβ⟩ := exists_adic_factorization β
  exact ⟨max m nβ, le_max_left _ _, _, _,
    adicTruncationMapLE_comp_factorization R (le_max_left _ _) a₀ _ ha₀,
    adicTruncationMapLE_comp_factorization R (le_max_right _ _) bβ _ hbβ⟩

private lemma transitionTo_self_local
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) :
    transitionTo ξ (le_refl n) = 𝟙 _ := by
  unfold transitionTo
  generalize_proofs h
  revert h
  rw [Nat.sub_self]
  intro h
  simp [transitionIter]

private lemma transitionTo_succ_local
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    transitionTo ξ
        (h.trans (Nat.le_succ m)) =
      ξ.transition m ≫
        transitionTo ξ h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold transitionTo
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [Nat.succ_sub h, Nat.add_sub_cancel_left]
  intro h₁ h₂
  simp [transitionIter]

private lemma transitionTo_isHomLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    ∃ t : AdicTruncation.obj ξ.base m ⟶ AdicTruncation.obj ξ.base n,
      t.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base m)) =
        Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n) ∧
      p.IsHomLift t (transitionTo ξ h) := by
  induction m, h using Nat.le_induction with
  | base =>
    refine ⟨𝟙 _, ?_, ?_⟩
    · rfl
    · rw [transitionTo_self_local]
      exact IsHomLift.id (ξ.level_eq n)
  | @succ m hm ih =>
    obtain ⟨t, ht, htl⟩ := ih
    refine ⟨AdicTruncation.transition ξ.base m ≫ t, ?_, ?_⟩
    · apply AlgHom.ext
      intro r
      exact DFunLike.congr_fun ht r
    · rw [transitionTo_succ_local ξ hm]
      have htr : p.IsHomLift (AdicTruncation.transition ξ.base m)
          (ξ.transition m) := ξ.transition_lift m
      exact IsHomLift.comp p _ _ _ _

private lemma tangent_point_after_common_truncation
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (hS : IsCofiberedInGroupoids
      (Functor.Elements.π (restrictedCoyoneda ξ.base)))
    (hT : IsCofiberedInGroupoids p)
    (assoc : AssociatedMorphism
      (p := p) ξ pushforwards)
    (D : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (z : p.Fiber D)
    (β : (restrictedCoyoneda ξ.base).Elements)
    (hsurj : Function.Surjective
      (mapIsomorphismClasses hS hT assoc.toBasedFunctor D)) :
    ∃ n : ℕ, ∃ b : AdicTruncation.obj ξ.base n ⟶ β.1,
      ∃ d : AdicTruncation.obj ξ.base n ⟶ D,
      ∃ j : ξ.level n ⟶ z.1,
        b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) = β.2.hom ∧
        p.IsHomLift d j := by
  obtain ⟨s, e, j₀, hj₀eq, hj₀⟩ :=
    exists_level_map_to_target_of_class_surjective ξ pushforwards hS hT assoc D z hsurj
  let α : (restrictedCoyoneda ξ.base).Elements := s.1
  let m := assoc.level α
  have hαD : α.1 = D := by
    change (Functor.Elements.π
      (restrictedCoyoneda ξ.base)).obj α = D
    exact s.2
  have hα := (assoc.factor_spec α).2.2
  obtain ⟨n, hmn, a, b, ha, hb⟩ :=
    exists_common_adic_factorization_above α.2 β.2 m (assoc.factor α) hα
  obtain ⟨t, ht, htl⟩ := transitionTo_isHomLift ξ hmn
  change ξ.level m ⟶ z.1 at j₀
  have hta : t ≫ assoc.factor α = a :=
    comp_eq_of_comp_mk t _ a ht (ha.trans hα.symm)
  let j := transitionTo ξ hmn ≫ j₀
  let d := a ≫ eqToHom hαD
  have hj : p.IsHomLift d j := by
    let tau := transitionTo ξ hmn
    let gam := assoc.factor α ≫ eqToHom s.2
    let : p.IsHomLift t tau := htl
    let : p.IsHomLift gam j₀ := hj₀
    have hcomp : p.IsHomLift (t ≫ gam) (tau ≫ j₀) :=
      IsHomLift.comp p t gam tau j₀
    have hbase :
        t ≫ gam = d := by
      dsimp [gam, d]
      rw [← Category.assoc, hta]
    rw [← hbase]
    simpa [j, tau] using hcomp
  exact ⟨n, b, d, j, hb, hj⟩

/-- A section supplied by (S2), retaining the base map of its second leg.
The latter is the part needed when this section is used to compare a chosen
infinitesimal lift with a prescribed map of algebras. -/
private theorem exists_section_with_second_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    {y xε x x₀ : F} (a : y ⟶ x) (b : y ⟶ xε)
    (e : xε ⟶ x₀) (d : x ⟶ x₀)
    (hcomm : b ≫ e = a ≫ d)
    (hdual : IsDualNumberProjection (p.map e))
    (hPB : IsPullback (p.map b) (p.map a) (p.map e) (p.map d))
    (sε : x ⟶ xε) (hsε : sε ≫ e = d) :
    ∃ s : x ⟶ y, s ≫ a = 𝟙 x ∧ p.map (s ≫ b) = p.map sε := by
  classical
  let σ : p.obj x ⟶ p.obj y :=
    hPB.lift (p.map sε) (𝟙 (p.obj x)) (by
      calc
        p.map sε ≫ p.map e = p.map (sε ≫ e) := (Functor.map_comp p _ _).symm
        _ = p.map d := congrArg (fun q => p.map q) hsε
        _ = (𝟙 (p.obj x)) ≫ p.map d := by simp)
  have hσb : σ ≫ p.map b = p.map sε := hPB.lift_fst _ _ _
  have hσa : σ ≫ p.map a = 𝟙 (p.obj x) := hPB.lift_snd _ _ _
  obtain ⟨z, φ, hz, hφ⟩ := cofibered_lift hp rfl σ
  have hφmap : p.map φ = σ ≫ eqToHom hz.symm := by
    let := hφ
    simpa using IsHomLift.fac' p σ φ
  let ub : p.obj z ⟶ p.obj xε := eqToHom hz ≫ p.map b
  let rb : p.obj z ⟶ p.obj x := eqToHom hz ≫ p.map a
  have hfactorU : p.map φ ≫ ub = p.map sε := by
    rw [hφmap]
    dsimp [ub]
    simp [Category.assoc, hσb]
  have hfactorR : p.map φ ≫ rb = p.map (𝟙 x) := by
    rw [hφmap]
    dsimp [rb]
    simp [Category.assoc, hσa]
  obtain ⟨u, huMap, huFac⟩ := cofibered_factor p hp φ sε ub hfactorU
  obtain ⟨r, hrMap, hrFac⟩ := cofibered_factor p hp φ (𝟙 x) rb hfactorR
  have hbaseLeg : ub ≫ p.map e = rb ≫ p.map d := by
    change (eqToHom hz ≫ p.map b) ≫ p.map e =
      (eqToHom hz ≫ p.map a) ≫ p.map d
    calc
      (eqToHom hz ≫ p.map b) ≫ p.map e =
          eqToHom hz ≫ (p.map b ≫ p.map e) := by simp [Category.assoc]
      _ = eqToHom hz ≫ (p.map a ≫ p.map d) :=
        congrArg (fun q => eqToHom hz ≫ q) hPB.w
      _ = (eqToHom hz ≫ p.map a) ≫ p.map d := by simp [Category.assoc]
  have htotal : φ ≫ (u ≫ e) = φ ≫ (r ≫ d) := by
    rw [← Category.assoc, huFac, hsε, ← Category.assoc, hrFac, Category.id_comp]
  have huE : p.map (u ≫ e) = ub ≫ p.map e := by
    simp only [Functor.map_comp, huMap]
  have hrD : p.map (r ≫ d) = ub ≫ p.map e := by
    rw [Functor.map_comp, hrMap, hbaseLeg]
  let : p.IsStronglyCocartesian (p.map φ) φ := all_cocartesian hp _ _
  let : p.IsHomLift (ub ≫ p.map e) (u ≫ e) := huE ▸ IsHomLift.map p (u ≫ e)
  let : p.IsHomLift (ub ≫ p.map e) (r ≫ d) := hrD ▸ IsHomLift.map p (r ≫ d)
  have hcomm' : u ≫ e = r ≫ d :=
    CategoryTheory.Functor.IsStronglyCocartesian.ext (p := p)
      (f := p.map φ) φ (ub ≫ p.map e) htotal
  let P : PullbackCompletion p d e (p.map a) (p.map b) :=
    ⟨z, hz, r, u, hcomm', hrMap, huMap⟩
  let Q : PullbackCompletion p d e (p.map a) (p.map b) :=
    ⟨y, rfl, a, b, hcomm, rfl, rfl⟩
  obtain ⟨v, hvFirst, hvMap⟩ := hS2.comparison d e hdual
    (p.map a) (p.map b) hPB P Q
  have hfirst : r = v ≫ a := by simpa [P, Q] using hvFirst
  let s := φ ≫ v
  refine ⟨s, ?_, ?_⟩
  · dsimp [s]
    rw [Category.assoc, ← hfirst, hrFac]
  · dsimp [s]
    calc
      p.map ((φ ≫ v) ≫ b) = p.map φ ≫ p.map v ≫ p.map b := by
        simp [Functor.map_comp, Category.assoc]
      _ = (σ ≫ eqToHom hz.symm) ≫
          (eqToHom hz ≫ eqToHom rfl.symm) ≫ p.map b := by rw [hφmap, hvMap]
      _ = σ ≫ p.map b := by simp [Category.assoc]
      _ = p.map sε := hσb

set_option maxHeartbeats 4000000 in
-- Resource bound, not a logical one: the forward direction threads the chosen pushforwards
-- through every level of the formal object, and the composite `whnf` cost of the
-- quotient-level coherences exceeds the default budget.
/-- Surjectivity on tangent spaces together with lifting the map of underlying
complete local algebras across every small-extension triangle characterizes
versality for a predeformation category satisfying (S1) and (S2). -/
@[stacks 06IU]
public theorem isVersal_iff_differential_surjective_and_base_lifts
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory 𝓕.p)
    (hS1 : SchlessingerConditionS1 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (ξ : FormalObject 𝓕.p)
    (pushforwards : ChosenPushforwards 𝓕.p) :
    IsVersal hpre.cofibered ξ ↔
      (Function.Surjective
        (mapIsomorphismClasses
          (categoryOfElements_projection_isCofibered
            (restrictedCoyoneda ξ.base))
          hpre.cofibered
          (associatedMorphism
            hpre.cofibered ξ pushforwards).toBasedFunctor
          (artinianDualNumbers Λ k)) ∧
       ∀ ⦃B A : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄ (f : B ⟶ A),
         InfinitesimalLifting.IsSmallExtension
           (CommRingCat.ofHom f.hom.toRingHom) →
         ∀ ⦃y x : FormalObject 𝓕.p⦄ (g : y ⟶ x),
           (FormalObject.projection (p := 𝓕.p)).IsHomLift
             (artinianToComplete.map f) g →
         ∀ (a : ξ ⟶ x), ∃ b : ξ.base ⟶ y.base,
             b ≫ g.base = a.base) := by
  constructor
  · intro hversal
    constructor
    · intro z
      classical
      let S := BasedCategory.ofFunctor
        (Functor.Elements.π (restrictedCoyoneda ξ.base))
      let T := BasedCategory.ofFunctor 𝓕.p
      let hS : IsCofiberedInGroupoids S.p :=
        categoryOfElements_projection_isCofibered
          (restrictedCoyoneda ξ.base)
      let ψ := (associatedMorphism
        hpre.cofibered ξ pushforwards).toBasedFunctor
      let Aε := artinianDualNumbers Λ k
      let A₀ := residueFieldObject Λ k
      let f := residueMorphism Aε
      obtain ⟨y, rfl⟩ := classOf_surjective
        T hpre.cofibered Aε z
      let yraw : T.obj := y.1
      have hy : T.p.obj yraw = Aε := y.2
      obtain ⟨y₀op, pushop, hpushop⟩ := hpre.cofibered.exists_lift f.op
        (Opposite.op yraw) (congrArg Opposite.op hy)
      let y₀ : T.obj := Opposite.unop y₀op
      have hy₀ : T.p.obj y₀ = A₀ := by
        have hpushop' : T.p.op.IsHomLift f.op pushop := hpushop
        let := hpushop'
        exact congrArg Opposite.unop (IsHomLift.domain_eq (p := T.p.op) f.op pushop)
      let push : yraw ⟶ y₀ := Opposite.unop pushop
      have hpush : T.p.IsHomLift f push := by
        cases y₀op
        exact CategoryTheory.isHomLift_unop T.p f.op push.op (inst := hpushop)
      let α₀ := residuePoint ξ.base
      let α₀E : (restrictedCoyoneda ξ.base).Elements :=
        (restrictedCoyoneda ξ.base).elementsMk A₀ α₀
      let s₀ : S.obj := α₀E
      let x₀raw := ψ.obj s₀
      have hx₀ : T.p.obj x₀raw = A₀ := by
        change T.p.obj (ψ.obj s₀) = A₀
        rw [ψ.w_obj]
        rfl
      let y₀F : T.p.Fiber A₀ := ⟨y₀, hy₀⟩
      let x₀F : T.p.Fiber A₀ := ⟨x₀raw, hx₀⟩
      let i₀ := Classical.choice (specialFiberObjects_isomorphic T.p hpre y₀F x₀F)
      let q : yraw ⟶ x₀raw := push ≫ i₀.hom.1
      have hq : T.p.IsHomLift f q := by
        have hi : T.p.IsHomLift (𝟙 A₀) i₀.hom.1 := i₀.hom.2
        exact IsHomLift.comp_lift_id_right' T.p f push A₀ i₀.hom.1
      have hfsurj : Function.Surjective f.hom := by
        change Function.Surjective
          (fun a : Aε => (ULift.algEquiv (R := Λ) (A := k)).symm
            (Aε.residueEquiv (IsLocalRing.residue Aε a)))
        exact (ULift.algEquiv (R := Λ) (A := k)).symm.surjective.comp
          (Aε.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := Aε)))
      obtain ⟨sε, sh, a, hsε, ha, hcomm⟩ := (hversal pushforwards) f hfsurj
        yraw s₀ q hq
      have := hsε
      let sεF : S.p.Fiber Aε :=
        ⟨sε, IsHomLift.domain_eq (p := S.p) f sh⟩
      let xεF : T.p.Fiber Aε := (fiberFunctor ψ Aε).obj sεF
      have hclass :
          classOf T hpre.cofibered xεF =
            classOf T hpre.cofibered y := by
        have ha' : T.p.IsHomLift (𝟙 Aε) a := ha
        simpa using @map_classOf _ _ T hpre.cofibered Aε Aε
          (𝟙 Aε) xεF y a ha'
      refine ⟨classOf S hS sεF, ?_⟩
      rw [mapIsomorphismClasses_classOf hS hpre.cofibered ψ sεF]
      exact hclass
    · intro B A f hf y x g hg a
      obtain ⟨b, hb⟩ := ((isVersal_iff_lifts_smallExtensions
        hpre.cofibered ξ).mp hversal) f hf g hg a
      exact ⟨b.base, congrArg FormalObject.Hom.base hb⟩
  · intro hconditions
    rcases hconditions with ⟨htangent, hbase⟩
    apply (isVersal_iff_lifts_smallExtensions
      hpre.cofibered ξ).2
    intro B A f hf y x g hg a
    obtain ⟨b, hb⟩ := hbase f hf g hg a
    obtain ⟨η, hη, i, j, hi, hij, hjbase⟩ :=
      factor_formal_morphism_through_pushforward
      hpre a g b hb
    let q := FormalObject.projection (p := 𝓕.p)
    have hybase : y.base = artinianToComplete.obj B :=
      IsHomLift.domain_eq q (artinianToComplete.map f) g
    have hxbase : x.base = artinianToComplete.obj A :=
      IsHomLift.codomain_eq q (artinianToComplete.map f) g
    let hηbase : η.base = artinianToComplete.obj B := hη.trans hybase
    let e := restrictionCompletionEquivalence 𝓕.p hpre.cofibered
    let P := CategoricalPullback e.inclusion q
    let Eη : P := ⟨B, η,
      e.inclusionIso.app B ≪≫ eqToIso hηbase.symm⟩
    let Ey : P := ⟨B, y,
      e.inclusionIso.app B ≪≫ eqToIso hybase.symm⟩
    let Ex : P := ⟨A, x,
      e.inclusionIso.app A ≪≫ eqToIso hxbase.symm⟩
    have hgb : g.base = eqToHom hybase ≫ artinianToComplete.map f ≫
        eqToHom hxbase.symm := by
      let := hg
      have hh := IsHomLift.fac' q (artinianToComplete.map f) g
      simpa [q, artinianToComplete] using hh
    have hsquare : ∀ (z : FormalObject 𝓕.p) (hz : z.base = artinianToComplete.obj B)
        (h : z ⟶ x), h.base = eqToHom hz ≫ artinianToComplete.map f ≫ eqToHom hxbase.symm →
        e.inclusion.map f ≫ (e.inclusionIso.app A).hom ≫ eqToHom hxbase.symm =
          (e.inclusionIso.app B).hom ≫ eqToHom hz.symm ≫ h.base := by
      intro z hz h hh
      have hnat := e.inclusionIso.hom.naturality f
      have hnat' : e.inclusion.map f ≫ (e.inclusionIso.app A).hom =
          (e.inclusionIso.app B).hom ≫
            artinianToComplete.map f := by
        convert hnat <;> rfl
      rw [← Category.assoc, hnat', hh]
      simp
    let gj : Eη ⟶ Ex := ⟨f, j, hsquare η hηbase j (by rw [hjbase, hgb]; simp)⟩
    let gy : Ey ⟶ Ex := ⟨f, g, hsquare y hybase g hgb⟩
    let cη := e.can.map gj
    let cy := e.can.map gy
    let cxη : 𝓕.p.obj (e.can.obj Eη) ≅ B :=
      e.canOver.app Eη ≪≫ eqToIso (by rfl)
    let cxy : 𝓕.p.obj (e.can.obj Ey) ≅ B :=
      e.canOver.app Ey ≪≫ eqToIso (by rfl)
    let cxx : 𝓕.p.obj (e.can.obj Ex) ≅ A :=
      e.canOver.app Ex ≪≫ eqToIso (by rfl)
    have hcη : 𝓕.p.map cη ≫ cxx.hom = cxη.hom ≫ f := by
      have hh := e.canOver.hom.naturality gj
      simpa [cη, cxη, cxx, P, q, CategoricalPullback.π₁] using hh
    have hcy : 𝓕.p.map cy ≫ cxx.hom = cxy.hom ≫ f := by
      have hh := e.canOver.hom.naturality gy
      simpa [cy, cxy, cxx, P, q, CategoricalPullback.π₁] using hh
    have hsurj : Function.Surjective f.hom := by
      rcases hf with ⟨_, _, _, _, hsurj, _⟩
      exact hsurj
    have hcySurj : Function.Surjective (𝓕.p.map cy).hom := by
      intro z0
      obtain ⟨z1, hz1⟩ := hsurj (cxx.hom.hom z0)
      refine ⟨cxy.inv.hom z1, ?_⟩
      have hcy' := congrArg (fun m => m.hom) hcy
      have hmap := DFunLike.congr_fun hcy' (cxy.inv.hom z1)
      change cxx.hom.hom ((𝓕.p.map cy).hom (cxy.inv.hom z1)) =
        f.hom (cxy.hom.hom (cxy.inv.hom z1)) at hmap
      rw [artinian_iso_inv_hom_id_apply cxy, hz1] at hmap
      exact Function.LeftInverse.injective (artinian_iso_hom_inv_id_apply cxx) hmap
    let pbData := ArtinianLocalAlgCat.hasPullback_of_surjective
      f f (Or.inl hsurj)
    let PB := ArtinianLocalAlgCat.pullbackObj_of_surjective
      f f (Or.inl hsurj)
    let prFst := ArtinianLocalAlgCat.pullbackFst_of_surjective
      f f (Or.inl hsurj)
    let prSnd := ArtinianLocalAlgCat.pullbackSnd_of_surjective
      f f (Or.inl hsurj)
    have hPB0 : IsPullback prFst prSnd f f :=
      ArtinianLocalAlgCat.isPullback_of_surjective
        f f (Or.inl hsurj)
    let g1 : PB ⟶ 𝓕.p.obj (e.can.obj Eη) := prSnd ≫ cxη.inv
    let g2 : PB ⟶ 𝓕.p.obj (e.can.obj Ey) := prFst ≫ cxy.inv
    have hPB : IsPullback g2 g1 (𝓕.p.map cy) (𝓕.p.map cη) := by
      apply hPB0.of_iso' (Iso.refl PB) cxy cxη cxx
      · simp [g2]
      · simp [g1]
      · simpa [g2, cxy, cxx] using hcy.symm
      · simpa [g1, cxη, cxx] using hcη.symm
    let cpl := Classical.choice (hS1.completion cη cy hcySurj g1 g2 hPB)
    have hcySmall : InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom (𝓕.p.map cy).hom.toRingHom) := by
      have hmap : 𝓕.p.map cy = cxy.hom ≫ f ≫ cxx.inv :=
        (cancel_mono cxx.hom).1 (by simp [hcy])
      rw [hmap]
      exact smallExtension_conj f cxy cxx.symm hf
    let hbase := cxη.hom ≫ cxy.inv
    have hbase_lift : hbase ≫ 𝓕.p.map cy = 𝓕.p.map cη :=
      (cancel_mono cxx.hom).1 (by simp [hbase, hcy, hcη])
    let inf0 := infinitesimalMap (𝓕.p.map cη) (𝓕.p.map cy)
      hcySmall hbase hbase_lift g1 g2 hPB
    let diag : B ⟶ PB := hPB0.lift (𝟙 B) (𝟙 B) (by simp)
    have hdiagFst : diag ≫ prFst = 𝟙 B := hPB0.lift_fst _ _ _
    have hdiagSnd : diag ≫ prSnd = 𝟙 B := hPB0.lift_snd _ _ _
    let bB : ξ.base ⟶ artinianToComplete.obj B := b ≫ eqToHom hybase
    let betaMap : ξ.base ⟶ artinianToComplete.obj inf0.target :=
      bB ≫ artinianToComplete.map (diag ≫ inf0.g)
    let beta : (restrictedCoyoneda ξ.base).Elements :=
      (restrictedCoyoneda ξ.base).elementsMk inf0.target betaMap
    let assoc := associatedMorphism
      hpre.cofibered ξ pushforwards
    let htanInf : Function.Surjective
        (mapIsomorphismClasses
          (categoryOfElements_projection_isCofibered
            (restrictedCoyoneda ξ.base))
          hpre.cofibered assoc.toBasedFunctor inf0.target) := by
      let f₂ := 𝓕.p.map cy
      let I := RingHom.ker f₂.hom.toRingHom
      let : Module k I := smallExtensionKernelModule f₂ hcySmall
      let : Module kᵐᵒᵖ I := smallExtension_kernel_oppositeModule f₂
      let : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
      let eε₀ := smallExtensionDualNumberIso f₂ hcySmall
      let eε₁ := smallExtensionInfinitesimalTargetIso hcySmall hbase
        hbase_lift g1 g2 hPB inf0
      let eε := eε₀ ≪≫ eε₁
      exact mapIsomorphismClasses_surjective_of_iso
        (categoryOfElements_projection_isCofibered
          (restrictedCoyoneda ξ.base)) hpre.cofibered assoc.toBasedFunctor
        eε htangent
    let z0F : 𝓕.p.Fiber PB := ⟨cpl.apex, cpl.apex_eq⟩
    let z0Push := (pushforwards inf0.g).obj z0F
    let z0T : 𝓕.p.Fiber inf0.target := z0Push
    obtain ⟨nTan, bTan, dTan, jTan, hbTan, hjTan⟩ :=
      tangent_point_after_common_truncation ξ pushforwards
        (categoryOfElements_projection_isCofibered
          (restrictedCoyoneda ξ.base)) hpre.cofibered assoc
        inf0.target z0T beta htanInf
    let αB : (restrictedCoyoneda ξ.base).obj B := bB
    obtain ⟨nB, aB, haB⟩ := exists_adic_factorization αB
    let betaTanMap := adicTruncationPoint ξ.base nTan ≫
      artinianToComplete.map dTan
    let betaTan : (restrictedCoyoneda ξ.base).obj inf0.target := betaTanMap
    obtain ⟨nArt, hnArt⟩ :=
      (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
    have hkillB : IsLocalRing.maximalIdeal B ^ (nArt + 1) = ⊥ := by
      simp [pow_succ, hnArt]
    let m₀ := max nTan nB
    let m := max m₀ nArt
    have hnTan : nTan ≤ m := (le_max_left _ _).trans (le_max_left _ _)
    have hnB : nB ≤ m := (le_max_right _ _).trans (le_max_left _ _)
    have hnArt : nArt ≤ m := le_max_right _ _
    let tmB := adicTruncationMapLE ξ.base hnB
    let a0 := tmB ≫ aB
    have ha0 : a0.hom.comp
        (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base m)) = bB.hom :=
      adicTruncationMapLE_comp_factorization ξ.base hnB aB _ haB
    obtain ⟨N, hmN, bN, dN, hbN, hdN⟩ :=
      exists_common_adic_factorization_above αB betaTan m a0 ha0
    have hNtan : nTan ≤ N := hnTan.trans hmN
    obtain ⟨tNtan, htNtan, hτN⟩ := transitionTo_isHomLift ξ hNtan
    have hdN_eq : dN = tNtan ≫ dTan := (comp_eq_of_comp_mk tNtan dTan dN htNtan hdN).symm
    let τN := transitionTo ξ hNtan
    let jN := τN ≫ jTan
    have hjN : 𝓕.p.IsHomLift dN jN := by
      rw [hdN_eq]
      let := hτN
      let := hjTan
      exact IsHomLift.comp 𝓕.p tNtan dTan τN jTan
    have hkillBN : IsLocalRing.maximalIdeal B ^ (N + 1) = ⊥ :=
      le_bot_iff.mp ((Ideal.pow_le_pow_right
        (Nat.add_le_add_right (hnArt.trans hmN) 1)).trans hkillB.le)
    have hkillEη : IsLocalRing.maximalIdeal Eη.fst ^ (N + 1) = ⊥ := hkillBN
    let ηNiso := e.objIsoLevel Eη N hkillEη
    let ξNToEη : ξ.level N ⟶ e.can.obj Eη :=
      i.app N ≫ ηNiso.inv
    have hprSnd : Function.Surjective prSnd.hom := by
      intro b
      obtain ⟨a, ha⟩ := hsurj (f.hom b)
      refine ⟨⟨(a, b), ha⟩, ?_⟩
      change (ArtinianLocalAlgCat.pullbackSnd_of_surjective
        f f (Or.inl hsurj)).hom ⟨(a, b), ha⟩ = b
      rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
      rfl
    have hsurjCplToFirst : Function.Surjective
        (𝓕.p.map cpl.toFirst).hom := by
      have hcx : Function.Surjective cxη.inv.hom := fun y =>
        ⟨cxη.hom.hom y, artinian_iso_hom_inv_id_apply cxη y⟩
      have hg1 : Function.Surjective g1.hom := hcx.comp hprSnd
      have heq : Function.Surjective (eqToHom cpl.apex_eq).hom := by
        intro y
        refine ⟨(eqToHom cpl.apex_eq.symm).hom y, ?_⟩
        have hh : eqToHom cpl.apex_eq.symm ≫ eqToHom cpl.apex_eq = 𝟙 PB := by
          simp
        have hh' := congrArg (fun q : PB ⟶ PB => q.hom y) hh
        change (eqToHom cpl.apex_eq).hom
          ((eqToHom cpl.apex_eq.symm).hom y) = y
        exact hh'
      rw [cpl.map_toFirst]
      exact hg1.comp heq
    let pb1Data := ArtinianLocalAlgCat.hasPullback_of_surjective
      (𝓕.p.map ξNToEη) (𝓕.p.map cpl.toFirst) (Or.inr hsurjCplToFirst)
    let PB1 := ArtinianLocalAlgCat.pullbackObj_of_surjective
      (𝓕.p.map ξNToEη) (𝓕.p.map cpl.toFirst) (Or.inr hsurjCplToFirst)
    let prN := ArtinianLocalAlgCat.pullbackFst_of_surjective
      (𝓕.p.map ξNToEη) (𝓕.p.map cpl.toFirst) (Or.inr hsurjCplToFirst)
    let prZ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
      (𝓕.p.map ξNToEη) (𝓕.p.map cpl.toFirst) (Or.inr hsurjCplToFirst)
    have hPB1 := ArtinianLocalAlgCat.isPullback_of_surjective
      (𝓕.p.map ξNToEη) (𝓕.p.map cpl.toFirst) (Or.inr hsurjCplToFirst)
    let cpl1 := Classical.choice (hS1.completion ξNToEη cpl.toFirst
      hsurjCplToFirst prN prZ hPB1.flip)
    have hPBfirst : IsPullback (𝓕.p.map cpl.toSecond)
        (𝓕.p.map cpl.toFirst) (𝓕.p.map cy) (𝓕.p.map cη) := by
      apply hPB.of_iso' (eqToIso cpl.apex_eq)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · simp [cpl.map_toSecond]
      · simp [cpl.map_toFirst]
      · simp
      · simp
    have hPBsecond : IsPullback (𝓕.p.map cpl1.toSecond)
        (𝓕.p.map cpl1.toFirst) (𝓕.p.map cpl.toFirst)
        (𝓕.p.map ξNToEη) := by
      apply hPB1.flip.of_iso' (eqToIso cpl1.apex_eq)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · simp [cpl1.map_toSecond, prZ]
      · simp [cpl1.map_toFirst, prN]
      · simp
      · simp
    have hPBouter0 : IsPullback
        (𝓕.p.map cpl1.toSecond ≫ 𝓕.p.map cpl.toSecond)
        (𝓕.p.map cpl1.toFirst) (𝓕.p.map cy)
        (𝓕.p.map ξNToEη ≫ 𝓕.p.map cη) :=
      hPBsecond.paste_horiz hPBfirst
    have hPBouter : IsPullback
        (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond))
        (𝓕.p.map cpl1.toFirst) (𝓕.p.map cy)
        (𝓕.p.map (ξNToEη ≫ cη)) := by
      simpa only [Functor.map_comp] using hPBouter0
    let houter := 𝓕.p.map ξNToEη ≫ hbase
    have houter_lift0 : houter ≫ 𝓕.p.map cy =
        𝓕.p.map ξNToEη ≫ 𝓕.p.map cη := by
      dsimp [houter]
      calc
        (𝓕.p.map ξNToEη ≫ hbase) ≫ 𝓕.p.map cy =
            𝓕.p.map ξNToEη ≫ (hbase ≫ 𝓕.p.map cy) := by
              simp [Category.assoc]
        _ = 𝓕.p.map ξNToEη ≫ 𝓕.p.map cη := by rw [hbase_lift]
    have houter_lift : houter ≫ 𝓕.p.map cy =
        𝓕.p.map (ξNToEη ≫ cη) := by
      simpa only [Functor.map_comp] using houter_lift0
    let inf1 := infinitesimalMap
      (𝓕.p.map (ξNToEη ≫ cη)) (𝓕.p.map cy) hcySmall houter
      houter_lift (𝓕.p.map cpl1.toFirst)
      (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond)) hPBouter
    let I := RingHom.ker (𝓕.p.map cy).hom.toRingHom
    let : Module k I := smallExtensionKernelModule (𝓕.p.map cy) hcySmall
    let : Module kᵐᵒᵖ I := smallExtension_kernel_oppositeModule (𝓕.p.map cy)
    let : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
    let eOld := smallExtensionInfinitesimalTargetIso hcySmall hbase hbase_lift
      g1 g2 hPB inf0
    let eNew := smallExtensionInfinitesimalTargetIso hcySmall houter houter_lift
      (𝓕.p.map cpl1.toFirst)
      (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond)) hPBouter inf1
    let infTargetIso := eOld.symm ≪≫ eNew
    let mPB := 𝓕.p.map cpl1.toSecond ≫ eqToHom cpl.apex_eq
    have hmPBfirst : mPB ≫ g1 =
        𝓕.p.map cpl1.toFirst ≫ 𝓕.p.map ξNToEη := by
      calc
        mPB ≫ g1 = 𝓕.p.map cpl1.toSecond ≫ 𝓕.p.map cpl.toFirst := by
          simp [mPB, cpl.map_toFirst, Category.assoc]
        _ = 𝓕.p.map (cpl1.toSecond ≫ cpl.toFirst) := by
          rw [← Functor.map_comp]
        _ = 𝓕.p.map (cpl1.toFirst ≫ ξNToEη) := by rw [cpl1.comm]
        _ = 𝓕.p.map cpl1.toFirst ≫ 𝓕.p.map ξNToEη := by
          rw [← Functor.map_comp]
    have hmPBsecond : mPB ≫ g2 =
        𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond) := by
      calc
        mPB ≫ g2 =
            𝓕.p.map cpl1.toSecond ≫ 𝓕.p.map cpl.toSecond := by
              simp [mPB, cpl.map_toSecond, Category.assoc]
        _ = 𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond) := by
              rw [← Functor.map_comp]
    have hcoordinate (x : 𝓕.p.obj cpl1.apex) :
        inf1.coordinate (inf1.g.hom x) =
          inf0.coordinate (inf0.g.hom (mPB.hom x)) := by
      rw [infinitesimalMap_coordinate_g houter
        (𝓕.p.map cpl1.toFirst)
        (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond)) inf1 x]
      rw [infinitesimalMap_coordinate_g hbase g1 g2 inf0 (mPB.hom x)]
      apply Prod.ext
      · have h := congrArg (fun q => q.hom x) hmPBfirst
        calc
          _ = (𝓕.p.obj (e.can.obj Eη)).residueEquiv
              (IsLocalRing.residue (𝓕.p.obj (e.can.obj Eη))
                ((𝓕.p.map ξNToEη).hom ((𝓕.p.map cpl1.toFirst).hom x))) :=
                ((𝓕.p.map ξNToEη).residue_comm
                  ((𝓕.p.map cpl1.toFirst).hom x)).symm
          _ = (𝓕.p.obj (e.can.obj Eη)).residueEquiv
              (IsLocalRing.residue (𝓕.p.obj (e.can.obj Eη))
                (g1.hom (mPB.hom x))) := by
                  have h' : g1.hom (mPB.hom x) =
                      (𝓕.p.map ξNToEη).hom ((𝓕.p.map cpl1.toFirst).hom x) := by
                    simpa using h
                  exact congrArg
                    (fun a => (𝓕.p.obj (e.can.obj Eη)).residueEquiv
                      (IsLocalRing.residue (𝓕.p.obj (e.can.obj Eη)) a)) h'.symm
      · apply Subtype.ext
        have h₁ := congrArg (fun q => q.hom x) hmPBfirst
        have h₂ := congrArg (fun q => q.hom x) hmPBsecond
        dsimp [infinitesimalDifference, houter] at *
        rw [← h₂, ← h₁]
    let rOld := infinitesimalMapTargetRingEquiv hcySmall hbase hbase_lift g1 g2 hPB inf0
    let rNew := infinitesimalMapTargetRingEquiv hcySmall houter houter_lift
      (𝓕.p.map cpl1.toFirst)
      (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond)) hPBouter inf1
    have hRingMap (x : 𝓕.p.obj cpl1.apex) :
        rNew (inf1.g.hom x) =
          rOld (inf0.g.hom (mPB.hom x)) := by
      change trivSqZeroExtAddEquiv.symm (inf1.coordinate (inf1.g.hom x)) =
        trivSqZeroExtAddEquiv.symm
          (inf0.coordinate (inf0.g.hom (mPB.hom x)))
      exact congrArg trivSqZeroExtAddEquiv.symm (hcoordinate x)
    let S0 := smallExtensionSquareZeroTarget (𝓕.p.map cy) hcySmall
    let e0 := S0.coordinateRingEquiv
    have hOldCoord (a : S0.target.carrier) :
        rOld (eOld.hom.hom a) = e0 a := by
      change rOld (e0.trans rOld.symm a) = e0 a
      exact rOld.apply_symm_apply (e0 a)
    have hNewCoord (a : S0.target.carrier) :
        rNew (eNew.hom.hom a) = e0 a := by
      change rNew (e0.trans rNew.symm a) = e0 a
      exact rNew.apply_symm_apply (e0 a)
    have hIsoApply (a : inf0.target.carrier) :
        rNew (infTargetIso.hom.hom a) = rOld a := by
      change rNew (eNew.hom.hom (eOld.inv.hom a)) = rOld a
      calc
        rNew (eNew.hom.hom (eOld.inv.hom a)) =
            e0 (eOld.inv.hom a) := hNewCoord _
        _ = rOld (eOld.hom.hom (eOld.inv.hom a)) := (hOldCoord _).symm
        _ = rOld a := congrArg rOld (artinian_iso_inv_hom_id_apply eOld a)
    let zTarget1 := (pushforwards infTargetIso.hom).obj z0Push
    let q1 := cpl1.toSecond ≫ (pushforwards inf0.g).inclusion z0F ≫
      (pushforwards infTargetIso.hom).inclusion z0Push
    let tangentToZ1 := jN ≫
      (pushforwards infTargetIso.hom).inclusion z0Push
    have hpointMap (x : 𝓕.p.obj cpl1.apex) :
        infTargetIso.hom.hom
          (inf0.g.hom (mPB.hom x)) = inf1.g.hom x := by
      apply rNew.injective
      calc
        rNew (infTargetIso.hom.hom (inf0.g.hom (mPB.hom x))) =
            rOld (inf0.g.hom (mPB.hom x)) := hIsoApply _
        _ = rNew (inf1.g.hom x) := (hRingMap x).symm
    have hmPBMap : mPB ≫ inf0.g ≫ infTargetIso.hom = inf1.g :=
      ArtinianLocalAlgCat.hom_ext (AlgHom.ext hpointMap)
    have hinc0 : 𝓕.p.map ((pushforwards inf0.g).inclusion z0F) =
        eqToHom cpl.apex_eq ≫ inf0.g ≫ eqToHom z0Push.2.symm := by
      have h := (pushforwards inf0.g).cocartesian z0F
      let := h.toIsHomLift
      simpa using IsHomLift.fac' 𝓕.p inf0.g
        ((pushforwards inf0.g).inclusion z0F)
    have hincIso : 𝓕.p.map ((pushforwards infTargetIso.hom).inclusion z0Push) =
        eqToHom z0Push.2 ≫ infTargetIso.hom ≫ eqToHom zTarget1.2.symm := by
      have h := (pushforwards infTargetIso.hom).cocartesian z0Push
      let := h.toIsHomLift
      simpa using IsHomLift.fac' 𝓕.p infTargetIso.hom
        ((pushforwards infTargetIso.hom).inclusion z0Push)
    have hq1map : 𝓕.p.map q1 =
        inf1.g ≫ eqToHom zTarget1.2.symm := by
      calc
        𝓕.p.map q1 = 𝓕.p.map cpl1.toSecond ≫
            𝓕.p.map ((pushforwards inf0.g).inclusion z0F) ≫
            𝓕.p.map ((pushforwards infTargetIso.hom).inclusion z0Push) := by
              simp [q1]
        _ = mPB ≫ inf0.g ≫ infTargetIso.hom ≫
            eqToHom zTarget1.2.symm := by
              rw [hinc0, hincIso]
              simp [mPB, Category.assoc]
        _ = inf1.g ≫ eqToHom zTarget1.2.symm :=
              congrArg (fun q => q ≫ eqToHom zTarget1.2.symm) hmPBMap
    let : 𝓕.p.IsHomLift (𝓕.p.map q1) q1 := IsHomLift.map 𝓕.p q1
    have hq1strong := all_cocartesian hpre.cofibered (𝓕.p.map q1) q1
    have hq1 : 𝓕.p.IsCocartesian (𝓕.p.map q1) q1 := by
      let := hq1strong
      infer_instance
    have hcomm : (cpl1.toSecond ≫ cpl.toSecond) ≫ cy =
        cpl1.toFirst ≫ (ξNToEη ≫ cη) := by
      calc
        (cpl1.toSecond ≫ cpl.toSecond) ≫ cy =
            cpl1.toSecond ≫ (cpl.toSecond ≫ cy) := by
              simp [Category.assoc]
        _ = cpl1.toSecond ≫ (cpl.toFirst ≫ cη) := by rw [cpl.comm]
        _ = (cpl1.toSecond ≫ cpl.toFirst) ≫ cη := by
              simp [Category.assoc]
        _ = (cpl1.toFirst ≫ ξNToEη) ≫ cη := by rw [cpl1.comm]
        _ = cpl1.toFirst ≫ (ξNToEη ≫ cη) := by
              simp [Category.assoc]
    have htarget_eq : 𝓕.p.obj zTarget1.1 = inf1.target := zTarget1.2
    let specialFiberEquiv := Classical.choice hpre.specialFiber
    let x₀ : 𝓕.p.Fiber (residueFieldObject Λ k) :=
      specialFiberEquiv.inverse.obj ⟨PUnit.unit⟩
    let d : ξ.level N ⟶ x₀.1 := mapToSpecialFiber 𝓕.p hpre x₀ (ξ.level N)
    let eSpecialMap : zTarget1.1 ⟶ x₀.1 :=
      mapToSpecialFiber 𝓕.p hpre x₀ zTarget1.1
    have hcommSpecial : q1 ≫ eSpecialMap = cpl1.toFirst ≫ d :=
      maps_to_special_fiber_eq 𝓕.p hpre x₀ _ _
    have hliftSpecial : tangentToZ1 ≫ eSpecialMap = d :=
      maps_to_special_fiber_eq 𝓕.p hpre x₀ _ _
    have hbijInv : Function.Bijective eNew.inv.hom :=
      ⟨Function.LeftInverse.injective (artinian_iso_inv_hom_id_apply eNew), fun x =>
        ⟨eNew.hom.hom x, artinian_iso_hom_inv_id_apply eNew x⟩⟩
    let eNewInvAlg : inf1.target.carrier ≃ₐ[Λ] S0.target.carrier :=
      AlgEquiv.ofBijective eNew.inv.hom hbijInv
    let i₀ : (𝓕.p.obj x₀.1).carrier ≃ₐ[Λ] k :=
      (AlgEquiv.cast (R := Λ) x₀.2).trans
        (ULift.algEquiv (R := Λ) (A := k))
    let iε : (𝓕.p.obj zTarget1.1).carrier ≃ₐ[Λ] DualNumber k :=
      (AlgEquiv.cast (R := Λ) htarget_eq).trans
        (eNewInvAlg.trans
          (smallExtensionSquareZeroDualNumberEquiv (𝓕.p.map cy) hcySmall))
    have hdual : IsDualNumberProjection (𝓕.p.map eSpecialMap) := by
      rw [isDualNumberProjection_iff]
      refine ⟨i₀, iε, ?_⟩
      ext t
      change i₀ ((𝓕.p.map eSpecialMap).hom t) = TrivSqZeroExt.fst (iε t)
      have hmaps := hom_residueFieldObject_ext
        ((𝓕.p.map eSpecialMap) ≫ eqToHom x₀.2)
        (residueMorphism (𝓕.p.obj zTarget1.1))
      have heval := congrArg (fun f : 𝓕.p.obj zTarget1.1 ⟶
          residueFieldObject Λ k => f.hom t) hmaps
      have hdown := congrArg ULift.down heval
      have hi₀ : i₀ ((𝓕.p.map eSpecialMap).hom t) =
          ULift.down (((𝓕.p.map eSpecialMap) ≫ eqToHom x₀.2).hom t) := by
        simpa [i₀, ArtinianLocalAlgCat.comp_hom] using
          artinianAlgEquivCast_ulift_apply x₀.2 ((𝓕.p.map eSpecialMap).hom t)
      have hrid :
          ULift.down ((residueMorphism (𝓕.p.obj zTarget1.1)).hom t) =
            (𝓕.p.obj zTarget1.1).residueEquiv
              (IsLocalRing.residue (𝓕.p.obj zTarget1.1) t) := by
        change ULift.down.{v, w} (ULift.up.{v, w}
          ((𝓕.p.obj zTarget1.1).residueEquiv
            (IsLocalRing.residue (𝓕.p.obj zTarget1.1) t))) = _
        rfl
      have hεfst : TrivSqZeroExt.fst (iε t) =
          (𝓕.p.obj zTarget1.1).residueEquiv
            (IsLocalRing.residue (𝓕.p.obj zTarget1.1) t) := by
        rw [artinianAlgEquivCast_apply]
        change TrivSqZeroExt.fst
          ((eNewInvAlg.trans
            (smallExtensionSquareZeroDualNumberEquiv (𝓕.p.map cy) hcySmall))
              ((eqToHom htarget_eq).hom t)) = _
        rw [AlgEquiv.trans_apply]
        change TrivSqZeroExt.fst
          (smallExtensionSquareZeroDualNumberEquiv (𝓕.p.map cy) hcySmall
            (eNew.inv.hom ((eqToHom htarget_eq).hom t))) = _
        calc
          _ = S0.target.residueEquiv
              (IsLocalRing.residue S0.target
                (eNew.inv.hom ((eqToHom htarget_eq).hom t))) :=
                smallExtensionSquareZeroDualNumberEquiv_residue
                  (𝓕.p.map cy) hcySmall _
          _ = inf1.target.residueEquiv
              (IsLocalRing.residue inf1.target ((eqToHom htarget_eq).hom t)) :=
                eNew.inv.residue_comm _
          _ = (𝓕.p.obj zTarget1.1).residueEquiv
              (IsLocalRing.residue (𝓕.p.obj zTarget1.1) t) :=
                (eqToHom htarget_eq).residue_comm t
      calc
        i₀ ((𝓕.p.map eSpecialMap).hom t) =
            ULift.down (((𝓕.p.map eSpecialMap) ≫ eqToHom x₀.2).hom t) := hi₀
        _ = ULift.down
            ((residueMorphism (𝓕.p.obj zTarget1.1)).hom t) := hdown
        _ = (𝓕.p.obj zTarget1.1).residueEquiv
            (IsLocalRing.residue (𝓕.p.obj zTarget1.1) t) := hrid
        _ = TrivSqZeroExt.fst (iε t) := hεfst.symm
    have hE : eqToHom htarget_eq ≫
        residueMorphism inf1.target =
          𝓕.p.map eSpecialMap ≫ eqToHom x₀.2 :=
      hom_residueFieldObject_ext _ _
    have hD : residueMorphism (𝓕.p.obj (ξ.level N)) =
        𝓕.p.map d ≫ eqToHom x₀.2 :=
      hom_residueFieldObject_ext _ _
    have hPBres := infinitesimalMap_residue_pullback houter houter_lift
      (𝓕.p.map cpl1.toFirst) (𝓕.p.map (cpl1.toSecond ≫ cpl.toSecond))
      hPBouter hcySmall inf1
    have hPBspecial : IsPullback (𝓕.p.map q1) (𝓕.p.map cpl1.toFirst)
        (𝓕.p.map eSpecialMap) (𝓕.p.map d) := by
      apply hPBres.of_iso' (Iso.refl _) (eqToIso htarget_eq)
        (Iso.refl _) (eqToIso x₀.2)
      · rw [hq1map]
        simp
      · simp
      · exact hE
      · exact hD
    obtain ⟨s, hsfirst, hsq⟩ := exists_section_with_second_map
      𝓕.p hpre.cofibered hS2 cpl1.toFirst q1 eSpecialMap d hcommSpecial hdual
      hPBspecial tangentToZ1 hliftSpecial
    let bridge0 := s ≫ cpl1.toSecond ≫ cpl.toSecond
    have hbridge0fac : bridge0 ≫ cy = ξNToEη ≫ cη := by
      dsimp [bridge0]
      calc
        (s ≫ cpl1.toSecond ≫ cpl.toSecond) ≫ cy =
            s ≫ ((cpl1.toSecond ≫ cpl.toSecond) ≫ cy) := by
              simp [Category.assoc]
        _ = s ≫ (cpl1.toFirst ≫ (ξNToEη ≫ cη)) := by rw [hcomm]
        _ = ξNToEη ≫ cη := by rw [← Category.assoc, hsfirst]; simp
    have hkillA : IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥ := by
      let : IsLocalHom f.hom.toRingHom := f.isLocal
      rw [← IsLocalRing.map_maximalIdeal_of_surjective f.hom.toRingHom hsurj,
        ← Ideal.map_pow, hkillBN]
      simp
    have hOldApp : (ξNToEη ≫ cη) ≫ (e.objIsoLevel Ex N hkillA).hom =
        a.app N := by
      dsimp [ξNToEη, cη]
      rw [Category.assoc, e.objIsoLevel_naturality gj N hkillEη hkillA]
      have hh := congrArg (fun m : ξ ⟶ x => m.app N) hij
      rw [formalObjectHom_comp_app i j N] at hh
      simpa [gj, ηNiso, Ex] using hh
    have haAppBase : (AdicTruncation.functor N).map a.base =
        eqToHom (ξ.level_eq N).symm ≫ 𝓕.p.map (a.app N) ≫
          eqToHom (x.level_eq N) := by
      let := a.app_lift N
      convert IsHomLift.fac 𝓕.p ((AdicTruncation.functor N).map a.base)
        (a.app N)
    let bN' : AdicTruncation.obj ξ.base N ⟶ B :=
      eqToHom (ξ.level_eq N).symm ≫ 𝓕.p.map bridge0 ≫ cxy.hom
    let bComplete : ξ.base ⟶ artinianToComplete.obj B :=
      adicTruncationPoint ξ.base N ≫
        artinianToComplete.map bN'
    let bNew : ξ.base ⟶ y.base := bComplete ≫ eqToHom hybase.symm
    have hbNew : bNew ≫ g.base = a.base := by
      cases y
      cases hybase
      have hIx : AdicTruncation.ideal x.base N = ⊥ := by
        rw [hxbase]
        change IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥
        exact hkillA
      dsimp [bNew, bComplete, bN']
      rw [hgb]
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro r
      dsimp [adicTruncationPoint, artinianToComplete,
        CompleteLocalAlgCat.comp_hom, ArtinianLocalAlgCat.comp_hom]
      refine quotient_mk_injective_of_eq_bot hIx ?_
      have hOverAEval := congrArg
        (fun φ => φ.hom
          ((𝓕.p.map (ξNToEη ≫ cη)).hom
            ((eqToHom (ξ.level_eq N).symm).hom
              (Ideal.Quotient.mk
                (AdicTruncation.ideal ξ.base N) r))))
        (e.objIsoLevel_over Ex N hkillA)
      have haAppEval := congrArg
        (fun φ => φ.hom
          (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r)) haAppBase
      have haAppEval' := haAppEval
      dsimp [AdicTruncation.functor, AdicTruncation.map] at haAppEval'
      have hOldAppEval := congrArg
        (fun m => (𝓕.p.map m).hom
          ((eqToHom (ξ.level_eq N).symm).hom
            (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r))) hOldApp
      have hOldAppEval' := congrArg
        (fun z => (eqToHom (x.level_eq N)).hom z) hOldAppEval
      have hcy' := hcy.symm
      have hcyEval := congrArg
        (fun m => (Ideal.Quotient.mk (AdicTruncation.ideal x.base N))
          ((eqToHom hxbase.symm).hom
            (m.hom
              ((𝓕.p.map bridge0).hom
                ((eqToHom (ξ.level_eq N).symm).hom
                  (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r)))))) hcy'
      have hbridgeEval :
          (𝓕.p.map cy).hom
              ((𝓕.p.map bridge0).hom
                ((eqToHom (ξ.level_eq N).symm).hom
                  (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r))) =
            (𝓕.p.map (ξNToEη ≫ cη)).hom
              ((eqToHom (ξ.level_eq N).symm).hom
                (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r)) := by
        have hh := congrArg
          (fun m => m.hom
            ((eqToHom (ξ.level_eq N).symm).hom
              (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r)))
          (congrArg (fun m => 𝓕.p.map m) hbridge0fac)
        simpa [Functor.map_comp, ArtinianLocalAlgCat.comp_hom,
          AlgHom.comp_apply] using hh
      calc
        _ = (eqToHom (x.level_eq N)).hom
            ((𝓕.p.map (a.app N)).hom
              ((eqToHom (ξ.level_eq N).symm).hom
                (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r))) := by
          have hcyToOver := by
            simpa [← Functor.map_comp, Category.assoc, Ex, P, q,
              artinianToComplete, hbridge0fac] using hcyEval
          have hcyToOver' := by
            simpa [adicTruncationPoint, artinianToComplete,
              CompleteLocalAlgCat.comp_hom, ArtinianLocalAlgCat.comp_hom,
              hηbase, hxbase, Ideal.Quotient.mkₐ_eq_mk] using hcyToOver
          have hOverAEval' := by
            simpa [Ex, cxx, P, q, Category.assoc,
              artinianToComplete] using hOverAEval
          have hOverAEval'' :
              (eqToHom (x.level_eq N)).hom
                ((𝓕.p.map (e.objIsoLevel Ex N hkillA).hom).hom
                  ((𝓕.p.map cη).hom
                    ((𝓕.p.map ξNToEη).hom
                      ((eqToHom (ξ.level_eq N).symm).hom
                        (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r))))) =
              (Ideal.Quotient.mk (AdicTruncation.ideal x.base N))
                ((eqToHom hxbase.symm).hom
                  (cxx.hom.hom
                    ((𝓕.p.map cη).hom
                      ((𝓕.p.map ξNToEη).hom
                        ((eqToHom (ξ.level_eq N).symm).hom
                          (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r)))))) := by
            simpa [artinianUnderlying,
              completeUnderlying, artinianToComplete,
              AdicTruncation.obj, AdicTruncation.functor,
              Ex, cxx, P, q, Category.assoc] using hOverAEval'
          have hOldAppEvalComp := by
            simpa [Functor.map_comp, ArtinianLocalAlgCat.comp_hom,
              AlgHom.comp_apply] using hOldAppEval'
          convert hcyToOver' using 1
          · rw [hxbase]
            rfl
          · rfl
          · rw [hbridgeEval]
            simpa [artinianUnderlying,
              completeUnderlying, artinianToComplete,
              AdicTruncation.obj, AdicTruncation.functor,
              Functor.map_comp, ArtinianLocalAlgCat.comp_hom,
              AlgHom.comp_apply] using
                hOldAppEvalComp.symm.trans hOverAEval''
        _ = (Ideal.Quotient.mk (AdicTruncation.ideal x.base N)) (a.base.hom r) := by
          convert haAppEval'.symm using 1 <;> rfl
    obtain ⟨ηNew, hηNew, iNew, jNew, hiNew, hijNew, hjNewBase⟩ :=
      factor_formal_morphism_through_pushforward hpre a g bNew hbNew
    let hηbaseNew : ηNew.base = artinianToComplete.obj B :=
      hηNew.trans hybase
    let EηNew : P := ⟨B, ηNew,
      e.inclusionIso.app B ≪≫ eqToIso hηbaseNew.symm⟩
    let ηNewNiso := e.objIsoLevel EηNew N hkillBN
    let ξNToEηNew : ξ.level N ⟶ e.can.obj EηNew :=
      iNew.app N ≫ ηNewNiso.inv
    let cNew : 𝓕.p.obj (e.can.obj EηNew) ≅ B :=
      e.canOver.app EηNew ≪≫ eqToIso (by rfl)
    have hEηNewIsoBase :
        e.inclusionIso.inv.app B ≫ EηNew.iso.hom = eqToHom hηbaseNew.symm := by
      simp [EηNew]
    let gjNew : EηNew ⟶ Ex := ⟨f, jNew, hsquare ηNew hηbaseNew jNew (by rw [hjNewBase, hgb]; simp)⟩
    let cηNew := e.can.map gjNew
    have hNewBase : iNew.base = bNew ≫ eqToHom hηNew.symm := by
      let := hiNew
      simpa [q] using IsHomLift.fac' q bNew iNew
    have hNewAppBase : (AdicTruncation.functor N).map iNew.base =
        eqToHom (ξ.level_eq N).symm ≫ 𝓕.p.map (iNew.app N) ≫
          eqToHom (ηNew.level_eq N) := by
      let := iNew.app_lift N
      convert IsHomLift.fac 𝓕.p ((AdicTruncation.functor N).map iNew.base)
        (iNew.app N)
    have hIB : AdicTruncation.ideal
        (artinianToComplete.obj B) N = ⊥ := by
      change IsLocalRing.maximalIdeal B ^ (N + 1) = ⊥
      exact hkillBN
    have hIηNew : AdicTruncation.ideal ηNew.base N = ⊥ := by
      rw [hηbaseNew]
      change IsLocalRing.maximalIdeal B ^ (N + 1) = ⊥
      exact hkillBN
    have hnewMap : 𝓕.p.map ξNToEηNew ≫ cNew.hom =
        𝓕.p.map bridge0 ≫ cxy.hom := by
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      refine quotient_mk_injective_of_eq_bot hIB ?_
      have hNewAppEval := congrArg
        (fun φ => φ.hom ((eqToHom (ξ.level_eq N)).hom x)) hNewAppBase
      have hNewBaseTrunc := congrArg
        (fun m => (AdicTruncation.functor N).map m) hNewBase
      have hNewBaseTruncEval := congrArg
        (fun m => m.hom ((eqToHom (ξ.level_eq N)).hom x)) hNewBaseTrunc
      have hOverEval := congrArg
        (fun φ => φ.hom
          ((𝓕.p.map (e.objIsoLevel EηNew N hkillBN).inv).hom
            ((𝓕.p.map (iNew.app N)).hom x)))
        (e.objIsoLevel_over EηNew N hkillBN)
      have hOverEval' := by
        simpa [EηNew, cNew, ηNewNiso, hηbaseNew,
          hEηNewIsoBase, hIB, hIηNew,
          artinianToComplete, Category.assoc] using hOverEval.symm
      have hηNewIsoCancel :
          𝓕.p.map ηNewNiso.inv ≫ 𝓕.p.map ηNewNiso.hom = 𝟙 _ := by
        rw [← 𝓕.p.map_comp, ηNewNiso.inv_hom_id]
        simp
      have hηNewIsoCancelEval := congrArg
        (fun m => m.hom ((𝓕.p.map (iNew.app N)).hom x)) hηNewIsoCancel
      have hηNewIsoCancelValue :
          (𝓕.p.map ηNewNiso.hom).hom
              ((𝓕.p.map ηNewNiso.inv).hom ((𝓕.p.map (iNew.app N)).hom x)) =
            (𝓕.p.map (iNew.app N)).hom x := by
        change (𝓕.p.map ηNewNiso.hom).hom
            ((𝓕.p.map ηNewNiso.inv).hom ((𝓕.p.map (iNew.app N)).hom x)) =
          (𝓕.p.map (iNew.app N)).hom x at hηNewIsoCancelEval
        exact hηNewIsoCancelEval
      have hOverEvalBridge :
          (Ideal.Quotient.mk (AdicTruncation.ideal ηNew.base N))
              ((eqToHom hηbaseNew.symm).hom
                (cNew.hom.hom ((𝓕.p.map ξNToEηNew).hom x))) =
          ((AdicTruncation.functor N).map iNew.base).hom
              ((eqToHom (ξ.level_eq N)).hom x) := by
          have hOverEvalBridgeApp :
              Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ηNew.base N)
                ((CommAlgCat.Hom.hom (eqToHom
                  (congrArg
                    (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k =>
                      CommAlgCat.of Λ T) hηbaseNew.symm)))
                  (cNew.hom.hom ((𝓕.p.map ξNToEηNew).hom x))) =
              (CommAlgCat.Hom.hom (artinianUnderlying.map
                (eqToHom (ηNew.level_eq N)))) ((𝓕.p.map (iNew.app N)).hom x) := by
            simpa [EηNew, cNew, ηNewNiso, ξNToEηNew,
              artinianUnderlying, completeUnderlying,
              artinianToComplete, Category.assoc, Functor.map_comp,
              ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
              eqToHom_trans, eqToHom_refl, eqToHom_map,
              hηbaseNew, hEηNewIsoBase, hηNewIsoCancelValue,
              completeEqToHom_commAlg_apply, artinianEqToHom_commAlg_apply,
              Ideal.Quotient.mkₐ_eq_mk,
              AdicTruncation.functor, AdicTruncation.obj] using hOverEval'
          have hAppTransport :
              (CommAlgCat.Hom.hom (artinianUnderlying.map
                (eqToHom (ηNew.level_eq N)))) ((𝓕.p.map (iNew.app N)).hom x) =
              ((AdicTruncation.functor N).map iNew.base).hom
                ((eqToHom (ξ.level_eq N)).hom x) := by
            calc
              _ = (eqToHom (ηNew.level_eq N)).hom
                  ((𝓕.p.map (iNew.app N)).hom x) :=
                    by simp [artinianUnderlying]
              _ = (eqToHom (ξ.level_eq N).symm ≫ 𝓕.p.map (iNew.app N) ≫
                  eqToHom (ηNew.level_eq N)).hom
                    ((eqToHom (ξ.level_eq N)).hom x) :=
                      (eqToHom_comp_apply (ξ.level_eq N) (ηNew.level_eq N)
                        (𝓕.p.map (iNew.app N)) x).symm
              _ = ((AdicTruncation.functor N).map iNew.base).hom
                  ((eqToHom (ξ.level_eq N)).hom x) := hNewAppEval.symm
          calc
            _ = Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ηNew.base N)
                  ((CommAlgCat.Hom.hom (eqToHom
                    (congrArg
                      (fun T : CompleteLocalAlgCat.{u, max v w, w} Λ k =>
                        CommAlgCat.of Λ T) hηbaseNew.symm)))
                    (cNew.hom.hom ((𝓕.p.map ξNToEηNew).hom x))) := by
                    rw [Ideal.Quotient.mkₐ_eq_mk]
                    exact congrArg (Ideal.Quotient.mk
                      (AdicTruncation.ideal ηNew.base N))
                      (completeEqToHom_commAlg_apply hηbaseNew.symm _)
            _ = (CommAlgCat.Hom.hom (artinianUnderlying.map
                (eqToHom (ηNew.level_eq N)))) ((𝓕.p.map (iNew.app N)).hom x) :=
                  hOverEvalBridgeApp
            _ = ((AdicTruncation.functor N).map iNew.base).hom
                  ((eqToHom (ξ.level_eq N)).hom x) := hAppTransport
      have htruncate :
          (Ideal.Quotient.mk (AdicTruncation.ideal ηNew.base N))
              ((eqToHom hηbaseNew.symm).hom
                (cNew.hom.hom ((𝓕.p.map ξNToEηNew).hom x))) =
          (Ideal.Quotient.mk (AdicTruncation.ideal ηNew.base N))
              ((eqToHom hηbaseNew.symm).hom
                (cxy.hom.hom ((𝓕.p.map bridge0).hom x))) := by
        calc
          _ = ((AdicTruncation.functor N).map iNew.base).hom
                ((eqToHom (ξ.level_eq N)).hom x) := by
                  simpa [ξNToEηNew, EηNew, cNew, ηNewNiso,
                    artinianToComplete, artinianUnderlying,
                    hηbaseNew, hIB, hIηNew, eqToHom_map,
                    ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using
                    hOverEvalBridge
          _ = ((AdicTruncation.functor N).map
                (bNew ≫ eqToHom hηNew.symm)).hom
                ((eqToHom (ξ.level_eq N)).hom x) := hNewBaseTruncEval
          _ = (Ideal.Quotient.mk (AdicTruncation.ideal ηNew.base N))
                ((eqToHom hηbaseNew.symm).hom
                  (cxy.hom.hom ((𝓕.p.map bridge0).hom x))) := by
                  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
                    ((eqToHom (ξ.level_eq N)).hom x)
                  have hx : x = (eqToHom (ξ.level_eq N).symm).hom
                      (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) r) := by
                    have hx' := congrArg
                      (fun z => (eqToHom (ξ.level_eq N).symm).hom z) hr.symm
                    rw [artinianEqToHom_symm_apply_left (ξ.level_eq N) x] at hx'
                    exact hx'
                  have hlevel := truncatedArtinianIdeal_eq_bot ξ.base N
                  rw [hx]
                  rw [artinianEqToHom_symm_apply]
                  dsimp only [AdicTruncation.functor, AdicTruncation.map,
                    AdicTruncation.obj]
                  simp only [Ideal.quotient_map_mkₐ,
                    Ideal.Quotient.mkₐ_eq_mk]
                  simp [bNew, bComplete, bN', adicTruncationPoint, artinianToComplete, cxy,
                    eqToHom_trans, Functor.map_comp, ArtinianLocalAlgCat.comp_hom,
                    CompleteLocalAlgCat.comp_hom, AlgHom.comp_apply]
                  all_goals rfl
      have hcast := quotient_mk_injective_of_eq_bot hIηNew htruncate
      have hinj : Function.Injective (eqToHom hηbaseNew.symm).hom :=
        completeEqToHom_hom_injective hηbaseNew.symm
      have hvalues : cNew.hom.hom ((𝓕.p.map ξNToEηNew).hom x) =
          cxy.hom.hom ((𝓕.p.map bridge0).hom x) := hinj hcast
      exact congrArg (Ideal.Quotient.mk
        (AdicTruncation.ideal (artinianToComplete.obj B) N)) hvalues
    let bridgeBase := cNew.hom ≫ cxy.inv
    have hbridgeBase : 𝓕.p.map ξNToEηNew ≫ bridgeBase =
        𝓕.p.map bridge0 := by
      change 𝓕.p.map ξNToEηNew ≫ (cNew.hom ≫ cxy.inv) = _
      calc
        𝓕.p.map ξNToEηNew ≫ (cNew.hom ≫ cxy.inv) =
            (𝓕.p.map ξNToEηNew ≫ cNew.hom) ≫ cxy.inv := by
              simp [Category.assoc]
        _ = (𝓕.p.map bridge0 ≫ cxy.hom) ≫ cxy.inv := by rw [hnewMap]
        _ = 𝓕.p.map bridge0 := by simp [Category.assoc]
    obtain ⟨bridge, hbridge, hbridgeFac⟩ := cofibered_factor
      𝓕.p hpre.cofibered ξNToEηNew bridge0 bridgeBase hbridgeBase
    have hNewApp : (ξNToEηNew ≫ cηNew) ≫
        (e.objIsoLevel Ex N hkillA).hom = a.app N := by
      dsimp [ξNToEηNew, cηNew]
      rw [Category.assoc, e.objIsoLevel_naturality gjNew N hkillBN hkillA]
      have hh := congrArg (fun m : ξ ⟶ x => m.app N) hijNew
      rw [formalObjectHom_comp_app iNew jNew N] at hh
      simpa [gjNew, ηNewNiso, Ex] using hh
    have hsectionNew : ξNToEηNew ≫ cηNew = ξNToEη ≫ cη := by
      apply (cancel_mono (e.objIsoLevel Ex N hkillA).hom).1
      calc
        (ξNToEηNew ≫ cηNew) ≫ (e.objIsoLevel Ex N hkillA).hom = a.app N := hNewApp
        _ = (ξNToEη ≫ cη) ≫ (e.objIsoLevel Ex N hkillA).hom := hOldApp.symm
    have hcηNew : 𝓕.p.map cηNew ≫ cxx.hom = cNew.hom ≫ f := by
      have hh := e.canOver.hom.naturality gjNew
      simpa [cηNew, cNew, cxx, EηNew, Ex, P, q,
        CategoricalPullback.π₁] using hh
    have hbridgeTriangle : bridge ≫ cy = cηNew := by
      have hbaseNewCy : bridgeBase ≫ 𝓕.p.map cy = 𝓕.p.map cηNew := by
        apply (cancel_mono cxx.hom).1
        simp [bridgeBase, Category.assoc, hcy, hcηNew]
      let : 𝓕.p.IsStronglyCocartesian
          (𝓕.p.map ξNToEηNew) ξNToEηNew :=
        all_cocartesian hpre.cofibered (𝓕.p.map ξNToEηNew) ξNToEηNew
      let : 𝓕.p.IsHomLift (bridgeBase ≫ 𝓕.p.map cy) (bridge ≫ cy) := by
        have hmap : 𝓕.p.map (bridge ≫ cy) = bridgeBase ≫ 𝓕.p.map cy := by
          rw [Functor.map_comp, hbridge]
        exact hmap.symm ▸ IsHomLift.map 𝓕.p (bridge ≫ cy)
      let : 𝓕.p.IsHomLift (bridgeBase ≫ 𝓕.p.map cy) cηNew :=
        hbaseNewCy ▸ IsHomLift.map 𝓕.p cηNew
      apply CategoryTheory.Functor.IsStronglyCocartesian.ext (p := 𝓕.p)
        (f := 𝓕.p.map ξNToEηNew) ξNToEηNew (bridgeBase ≫ 𝓕.p.map cy)
      change ξNToEηNew ≫ (bridge ≫ cy) = ξNToEηNew ≫ cηNew
      calc
        ξNToEηNew ≫ (bridge ≫ cy) = bridge0 ≫ cy := by
          rw [← Category.assoc, hbridgeFac]
        _ = ξNToEη ≫ cη := hbridge0fac
        _ = ξNToEηNew ≫ cηNew := hsectionNew.symm
    let : e.can.Faithful := e.isEquivalence.faithful
    let : e.can.Full := e.isEquivalence.full
    let m : EηNew ⟶ Ey := e.can.preimage bridge
    have hm : e.can.map m = bridge := e.can.map_preimage bridge
    have hmgy : m ≫ gy = gjNew := by
      apply e.can.map_injective
      calc
        e.can.map (m ≫ gy) = bridge ≫ cy := by rw [Functor.map_comp, hm]
        _ = cηNew := hbridgeTriangle
        _ = e.can.map gjNew := rfl
    have hmgy' : m.snd ≫ g = jNew := by
      have hh := congrArg CategoricalPullback.Hom.snd hmgy
      change m.snd ≫ g = jNew at hh
      exact hh
    refine ⟨iNew ≫ m.snd, ?_⟩
    calc
      (iNew ≫ m.snd) ≫ g = iNew ≫ (m.snd ≫ g) := Category.assoc _ _ _
      _ = iNew ≫ jNew := by rw [hmgy']
      _ = a := hijNew

end Deformation

end
