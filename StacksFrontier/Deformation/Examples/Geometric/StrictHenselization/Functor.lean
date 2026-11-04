module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksCore.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Localization
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Flatness
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.Deformation.Examples.Geometric.StrictHenselization.Objects
import all StacksFrontier.Deformation.Examples.Geometric.StrictHenselization.Objects

/-!
# The strict henselization functor on deformation categories

The strict henselization of a morphism of deformations of a local `k`-algebra `P`, and the
resulting functor over `𝒞_Λ` from the deformation category of `P` to that of a strict
henselization `Pˢʰ`. On morphisms the comparison is the unique local lift out of an ind-étale
algebra into a henselian one inducing a prescribed map of residue fields, and cartesianness
follows from Nakayama: the two flat algebras agree after the nilpotent base change to `k`.

## Main definitions

* `Deformation.Examples.strictDeformationFunctor`: the functor of deformation categories itself.

## Main results

* `Deformation.Examples.strictHenselizationFunctor`: strict henselization of the flat algebra of
  each deformation is such a functor.

## References

* [Stacks Project, Tag 0DYU](https://stacks.math.columbia.edu/tag/0DYU)
-/

@[expose] public section

open CategoryTheory
open IsLocalRing

universe u v w

namespace Deformation.Examples

variable {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  [CommRing P] [Algebra k P] [IsLocalRing P]
variable {κsep : Type v} [Field κsep]
  [Algebra (maximalIdeal P).ResidueField κsep]
  [IsSepClosure (maximalIdeal P).ResidueField κsep]
variable (Psh : Type w) [CommRing Psh] [IsLocalRing Psh]
  [Algebra P Psh] [Algebra k Psh] [IsScalarTower k P Psh]

/-! ### The strict henselization of a morphism of deformations -/

/-- Nakayama: a map of modules over a ring with a nilpotent ideal which is surjective modulo that
ideal and whose kernel lies in it is bijective, when the target is flat. -/
@[sga "3 III 3.3" "more general",
  sga "3 VIB 6.2.2" "more general",
  sga "3 VIIB 0.3.7" "partial, special case"]
private theorem bijective_of_isNilpotent_of_ker_le_smul_top
    {R : Type*} [CommRing R] {I : Ideal R} {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] [Module.Flat R N]
    (hI : IsNilpotent I) (f : M →ₗ[R] N)
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R N)).mkQ.comp f))
    (hker : LinearMap.ker f ≤ I • (⊤ : Submodule R M)) : Function.Bijective f := by
  have hf := LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent I f hI hsurj
  refine ⟨LinearMap.ker_eq_bot.1
    (Submodule.eq_bot_of_le_smul_of_isNilpotent I _ hI ?_), hf⟩
  rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I f hf]
  exact le_inf le_rfl hker

/-- Two base changes of a nilpotent thickening agree: a map of algebras over `B` compatible with
the maps to a common base change along a surjection `B → K` with nilpotent kernel is bijective. -/
private theorem bijective_of_nilpotent_pushout_fibers
    {B K C D E : Type*} [CommRing B] [CommRing K] [CommRing C]
    [CommRing D] [CommRing E]
    [Algebra B K] [Algebra B C] [Algebra B D] [Algebra B E]
    [Algebra K E] [Algebra C E] [Algebra D E]
    [IsScalarTower B K E] [IsScalarTower B C E] [IsScalarTower B D E]
    [Module.Flat B D]
    (hK : Function.Surjective (algebraMap B K))
    (hI : IsNilpotent (RingHom.ker (algebraMap B K)))
    (hC : Algebra.IsPushout B K C E) (hD : Algebra.IsPushout B K D E)
    (f : C →ₐ[B] D)
    (hf : (algebraMap D E).comp f.toRingHom = algebraMap C E) :
    Function.Bijective f := by
  let I := RingHom.ker (algebraMap B K)
  let : Algebra.IsPushout B K C E := hC
  obtain ⟨hCs, hCk⟩ :=
    Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
      (R := B) (S := K) (R' := C) (S' := E) hK
  let : Algebra.IsPushout B K D E := hD
  obtain ⟨_, hDk⟩ :=
    Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
      (R := B) (S := K) (R' := D) (S' := E) hK
  let F : C →ₗ[B] D := f.toLinearMap
  have hker : LinearMap.ker F ≤ I • (⊤ : Submodule B C) := by
    intro c hc
    have hc' : f c = 0 := (LinearMap.mem_ker).mp hc
    have hcE : algebraMap C E c = 0 := by
      simpa [hc'] using (RingHom.congr_fun hf c).symm
    rw [Ideal.smul_top_eq_map, ← hCk]
    exact hcE
  have hsurj : Function.Surjective
      ((I • (⊤ : Submodule B D)).mkQ.comp F) := by
    intro d
    obtain ⟨d₀, rfl⟩ := Submodule.mkQ_surjective _ d
    obtain ⟨c, hc⟩ := hCs (algebraMap D E d₀)
    refine ⟨c, ?_⟩
    change (Submodule.mkQ (I • (⊤ : Submodule B D))) (f c) =
      (Submodule.mkQ (I • (⊤ : Submodule B D))) d₀
    apply (Submodule.Quotient.eq _).mpr
    rw [Ideal.smul_top_eq_map, ← hDk]
    apply (RingHom.mem_ker).mpr
    have h := RingHom.congr_fun hf c
    change algebraMap D E (f c) = algebraMap C E c at h
    change algebraMap D E (f c - d₀) = 0
    rw [map_sub, h, hc, sub_self]
  exact bijective_of_isNilpotent_of_ker_le_smul_top hI F hsurj hker

/-- Cancelling a nilpotent specialization out of a pushout square. If the outer squares over
`A → K` and `B → K` are pushouts and `B → K` is surjective with nilpotent kernel, then the inner
square over `A → B` is a pushout. -/
private theorem isPushout_of_nilpotent_specialization
    {A B K C D E : Type*} [CommRing A] [CommRing B] [CommRing K]
    [CommRing C] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A K] [Algebra A C] [Algebra A D] [Algebra A E]
    [Algebra B K] [Algebra B D] [Algebra B E]
    [Algebra C D] [Algebra C E] [Algebra D E] [Algebra K E]
    [IsScalarTower A B K] [IsScalarTower A B D] [IsScalarTower A C D]
    [IsScalarTower A B E] [IsScalarTower A C E] [IsScalarTower A K E]
    [IsScalarTower B D E] [IsScalarTower B K E] [IsScalarTower C D E]
    [Module.Flat B D]
    (hC : Algebra.IsPushout A K C E)
    (hD : Algebra.IsPushout B K D E)
    (hs : Function.Surjective (algebraMap B K))
    (hnil : IsNilpotent (RingHom.ker (algebraMap B K))) :
    Algebra.IsPushout A B C D := by
  let T := TensorProduct A B C
  let gD : T →ₐ[B] D := Algebra.TensorProduct.lift
    (Algebra.ofId B D) (IsScalarTower.toAlgHom A C D)
    (fun _ _ => Commute.all _ _)
  let gE : T →ₐ[B] E := Algebra.TensorProduct.lift
    (Algebra.ofId B E) (IsScalarTower.toAlgHom A C E)
    (fun _ _ => Commute.all _ _)
  let : Algebra T D := gD.toRingHom.toAlgebra
  let : Algebra T E := gE.toRingHom.toAlgebra
  let : IsScalarTower B T E := IsScalarTower.of_algebraMap_eq' (by
    ext b
    change algebraMap B E b = gE (TensorProduct.tmul A b (1 : C))
    change algebraMap B E b =
      (Algebra.TensorProduct.lift (Algebra.ofId B E)
        (IsScalarTower.toAlgHom A C E) (fun _ _ => Commute.all _ _))
        (TensorProduct.tmul A b (1 : C))
    rw [Algebra.TensorProduct.lift_tmul]
    simp)
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A C T := Algebra.TensorProduct.right_isScalarTower
  let : IsScalarTower A T E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    calc
      algebraMap A E a = algebraMap B E (algebraMap A B a) :=
        IsScalarTower.algebraMap_apply A B E a
      _ = algebraMap T E (algebraMap B T (algebraMap A B a)) :=
        IsScalarTower.algebraMap_apply B T E _
      _ = algebraMap T E (algebraMap A T a) := by
        rw [← IsScalarTower.algebraMap_apply A B T])
  let : IsScalarTower C T E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap C E c = gE (TensorProduct.tmul A (1 : B) c)
    change algebraMap C E c =
      (Algebra.TensorProduct.lift (Algebra.ofId B E)
        (IsScalarTower.toAlgHom A C E) (fun _ _ => Commute.all _ _))
        (TensorProduct.tmul A (1 : B) c)
    rw [Algebra.TensorProduct.lift_tmul]
    simp)
  have hT : Algebra.IsPushout A B C T := TensorProduct.isPushout
  have hTE : Algebra.IsPushout B K T E :=
    (Algebra.IsPushout.comp_iff A B C T).mp hC
  have hcomp : (algebraMap D E).comp gD.toRingHom = algebraMap T E := by
    apply RingHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
        change algebraMap D E (gD (TensorProduct.tmul A b c)) =
          gE (TensorProduct.tmul A b c)
        dsimp [gD, gE]
        rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul]
        simp only [Algebra.ofId_apply, IsScalarTower.toAlgHom_apply]
        rw [IsScalarTower.algebraMap_apply B D E,
          IsScalarTower.algebraMap_apply C D E]
    | add x y hx hy =>
        change algebraMap D E (gD x) = algebraMap T E x at hx
        change algebraMap D E (gD y) = algebraMap T E y at hy
        change algebraMap D E (gD (x + y)) = algebraMap T E (x + y)
        simp only [map_add]
        rw [hx, hy]
  have hbij : Function.Bijective gD :=
    bijective_of_nilpotent_pushout_fibers hs hnil hTE hD gD hcomp
  apply Algebra.IsPushout.of_equiv (AlgEquiv.ofBijective gD hbij)
  ext c
  change gD (TensorProduct.tmul A (1 : B) c) = algebraMap C D c
  change (Algebra.TensorProduct.lift (Algebra.ofId B D)
    (IsScalarTower.toAlgHom A C D) (fun _ _ => Commute.all _ _))
      (TensorProduct.tmul A (1 : B) c) = algebraMap C D c
  rw [Algebra.TensorProduct.lift_tmul]
  simp

omit [Algebra k Psh] [IsScalarTower k P Psh] in
/-- The map of chosen strict henselizations induced by a morphism of deformations: the unique
local lift inducing the composite identification of residue fields. -/
private theorem fiberStrictMap_exists
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    ∃ g : DX.carrier →ₐ[X.left.fiber] DY.carrier,
      (residue DY.carrier).comp g.toRingHom =
        ((fiberSpecializationResidueEquiv Psh X hsh).trans
          (fiberSpecializationResidueEquiv Psh Y hsh).symm).toRingHom.comp
          (residue DX.carrier) := by
  let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  let : CommRing DX.carrier := DX.commRing
  let : CommRing DY.carrier := DY.commRing
  let : IsLocalRing DX.carrier := DX.isLocalRing
  let : IsLocalRing DY.carrier := DY.isLocalRing
  let : Algebra X.left.fiber DX.carrier := DX.algebra
  let : Algebra Y.left.fiber DY.carrier := DY.algebra
  let : Algebra X.left.fiber DY.carrier :=
    ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
  let : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := DX.residueAlgebra
  let : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := DX.sepClosure
  let : Algebra (maximalIdeal Y.left.fiber).ResidueField κsep := DY.residueAlgebra
  let : IsSepClosure (maximalIdeal Y.left.fiber).ResidueField κsep := DY.sepClosure
  let : HenselianLocalRing DY.carrier := DY.strict.henselian
  have hloc : IsLocalHom (f.left.map.hom : X.left.fiber →+* Y.left.fiber) := by
    let : Nontrivial (residueFieldAlgebra (Λ := Λ) (k := k) P).fiber := by
      change Nontrivial P
      infer_instance
    let : IsLocalHom (X.hom.map.hom : X.left.fiber →+* P) :=
      IsLocalHom.of_surjective _ (deformationSpecialFiberMap_surjective X)
    refine ⟨fun q hq => ?_⟩
    have huP : IsUnit (Y.hom.map.hom (f.left.map.hom q)) :=
      hq.map (Y.hom.map.hom : Y.left.fiber →+* P)
    rw [deformationMorphism_map_comm f q] at huP
    exact IsLocalHom.map_nonunit q huP
  let eX := fiberSpecializationResidueEquiv Psh X hsh
  let eY := fiberSpecializationResidueEquiv Psh Y hsh
  let φ : ResidueField DX.carrier ≃+* ResidueField DY.carrier := eX.trans eY.symm
  have hφ : φ.toRingHom.comp
      ((residue DX.carrier).comp (algebraMap X.left.fiber DX.carrier)) =
      (residue DY.carrier).comp (algebraMap X.left.fiber DY.carrier) := by
    apply RingHom.ext
    intro q
    apply eY.injective
    simp only [RingHom.comp_apply]
    change eY (φ (residue DX.carrier (algebraMap X.left.fiber DX.carrier q))) =
      eY (residue DY.carrier (algebraMap X.left.fiber DY.carrier q))
    have key (Z : ringDeformationCategory (Λ := Λ) (k := k) P) [IsLocalRing Z.left.fiber]
        (z : Z.left.fiber) :
        let D := fiberStrictData Z κsep
        letI : CommRing D.carrier := D.commRing
        letI : IsLocalRing D.carrier := D.isLocalRing
        letI : Algebra Z.left.fiber D.carrier := D.algebra
        fiberSpecializationResidueEquiv Psh Z hsh
            (residue D.carrier (algebraMap Z.left.fiber D.carrier z)) =
          residue Psh (algebraMap P Psh (Z.hom.map.hom z)) := by
      let D := fiberStrictData Z κsep
      let : CommRing D.carrier := D.commRing
      let : IsLocalRing D.carrier := D.isLocalRing
      let : Algebra Z.left.fiber D.carrier := D.algebra
      let : Algebra Z.left.fiber Psh := ((algebraMap P Psh).comp Z.hom.map.hom).toAlgebra
      exact (RingHom.congr_fun (fiberSpecializationMap_residue Psh Z hsh) _).symm.trans
        (congrArg (residue Psh) (fiberSpecializationMap_comp Psh Z hsh z))
    have hx := key X q
    have hy : eY (residue DY.carrier
        (algebraMap X.left.fiber DY.carrier q)) =
        residue Psh (algebraMap P Psh (Y.hom.map.hom (f.left.map.hom q))) :=
      key Y (f.left.map.hom q)
    calc
      eY (φ (residue DX.carrier (algebraMap X.left.fiber DX.carrier q))) =
          eX (residue DX.carrier (algebraMap X.left.fiber DX.carrier q)) := by
        simp [φ]
      _ = residue Psh (algebraMap P Psh (X.hom.map.hom q)) := hx
      _ = residue Psh
          (algebraMap P Psh (Y.hom.map.hom (f.left.map.hom q))) := by
        rw [deformationMorphism_map_comm f q]
      _ = eY (residue DY.carrier
          (algebraMap X.left.fiber DY.carrier q)) := hy.symm
  let hExist := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
    DX.strict.isFilteredColimitEtale φ.toRingHom hφ
  exact ⟨Classical.choose hExist, (Classical.choose_spec hExist).1.2⟩

/-- The map of chosen strict henselizations induced by a morphism of deformations. -/
private noncomputable def fiberStrictMap
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    DX.carrier →ₐ[X.left.fiber] DY.carrier :=
  Classical.choose (fiberStrictMap_exists Psh f hsh)

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberStrictMap_residue
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    (residue DY.carrier).comp (fiberStrictMap Psh f hsh).toRingHom =
      ((fiberSpecializationResidueEquiv Psh X hsh).trans
        (fiberSpecializationResidueEquiv Psh Y hsh).symm).toRingHom.comp
        (residue DX.carrier) :=
  Classical.choose_spec (fiberStrictMap_exists Psh f hsh)

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberStrictMap_base
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh)
    (q : X.left.fiber) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    (fiberStrictMap Psh f hsh) (algebraMap X.left.fiber DX.carrier q) =
      algebraMap Y.left.fiber DY.carrier (f.left.map.hom q) := by
  let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  let : CommRing DX.carrier := DX.commRing
  let : CommRing DY.carrier := DY.commRing
  let : IsLocalRing DX.carrier := DX.isLocalRing
  let : IsLocalRing DY.carrier := DY.isLocalRing
  let : Algebra X.left.fiber DX.carrier := DX.algebra
  let : Algebra Y.left.fiber DY.carrier := DY.algebra
  let : Algebra X.left.fiber DY.carrier :=
    ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
  exact (fiberStrictMap Psh f hsh).commutes q

/-- A local algebra map out of an ind-étale algebra into a henselian local ring is determined by
the map of residue fields it induces. -/
private theorem strictMap_unique_of_residue
    {Q R T : Type w} [CommRing Q] [CommRing R] [CommRing T]
    [IsLocalRing R] [HenselianLocalRing T]
    [Algebra Q R] [Algebra Q T]
    (hind : StacksDraft.IndEtale Q R)
    (φ : ResidueField R →+* ResidueField T)
    (f g : R →ₐ[Q] T)
    (hf : (residue T).comp f.toRingHom = φ.comp (residue R))
    (hg : (residue T).comp g.toRingHom = φ.comp (residue R)) : f = g := by
  have hφ : φ.comp ((residue R).comp (algebraMap Q R)) =
      (residue T).comp (algebraMap Q T) := by
    ext q
    have h := RingHom.congr_fun hf (algebraMap Q R q)
    change residue T (f (algebraMap Q R q)) =
      φ (residue R (algebraMap Q R q)) at h
    rw [f.commutes] at h
    exact h.symm
  obtain ⟨_, _, huniq⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale hind φ hφ
  have hlocF : IsLocalHom f := ⟨fun x hx =>
    (isLocalHom_of_residue_eq f.toRingHom φ (RingHom.congr_fun hf)).map_nonunit x hx⟩
  have hlocG : IsLocalHom g := ⟨fun x hx =>
    (isLocalHom_of_residue_eq g.toRingHom φ (RingHom.congr_fun hg)).map_nonunit x hx⟩
  exact (huniq f ⟨hlocF, hf⟩).trans (huniq g ⟨hlocG, hg⟩).symm

omit [Algebra k Psh] [IsScalarTower k P Psh] in
/-- The maps of chosen strict henselizations are compatible with the specialization maps to
`Pˢʰ`: both composites are the unique local lift inducing the same map of residue fields. -/
private theorem fiberStrictMap_specialization
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    letI : Algebra Y.left.fiber Psh :=
      ((algebraMap P Psh).comp Y.hom.map.hom).toAlgebra
    (fiberSpecializationMap Psh Y hsh).toRingHom.comp
      (fiberStrictMap Psh f hsh).toRingHom =
      (fiberSpecializationMap Psh X hsh).toRingHom := by
  let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  let : CommRing DX.carrier := DX.commRing
  let : CommRing DY.carrier := DY.commRing
  let : IsLocalRing DX.carrier := DX.isLocalRing
  let : IsLocalRing DY.carrier := DY.isLocalRing
  let : Algebra X.left.fiber DX.carrier := DX.algebra
  let : Algebra Y.left.fiber DY.carrier := DY.algebra
  let : Algebra X.left.fiber DY.carrier :=
    ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
  let : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  let : Algebra Y.left.fiber Psh :=
    ((algebraMap P Psh).comp Y.hom.map.hom).toAlgebra
  let : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := DX.residueAlgebra
  let : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := DX.sepClosure
  let : Algebra (maximalIdeal Y.left.fiber).ResidueField κsep := DY.residueAlgebra
  let : IsSepClosure (maximalIdeal Y.left.fiber).ResidueField κsep := DY.sepClosure
  let : HenselianLocalRing Psh := hsh.henselian
  let eX := fiberSpecializationResidueEquiv Psh X hsh
  let eY := fiberSpecializationResidueEquiv Psh Y hsh
  let φ := eX.trans eY.symm
  let gX := fiberSpecializationMap Psh X hsh
  let gY := fiberSpecializationMap Psh Y hsh
  let g := fiberStrictMap Psh f hsh
  let h : DX.carrier →ₐ[X.left.fiber] Psh :=
    { toRingHom := gY.toRingHom.comp g.toRingHom
      commutes' := fun q => by
        change gY (g (algebraMap X.left.fiber DX.carrier q)) =
          algebraMap P Psh (X.hom.map.hom q)
        rw [fiberStrictMap_base Psh f hsh q,
          fiberSpecializationMap_comp Psh Y hsh,
          deformationMorphism_map_comm f q] }
  have hg : (residue Psh).comp h.toRingHom =
      eX.toRingHom.comp (residue DX.carrier) := by
    calc
      (residue Psh).comp h.toRingHom =
          ((residue Psh).comp gY.toRingHom).comp g.toRingHom := rfl
      _ = (eY.toRingHom.comp (residue DY.carrier)).comp g.toRingHom := by
        rw [fiberSpecializationMap_residue Psh Y hsh]
      _ = eY.toRingHom.comp ((residue DY.carrier).comp g.toRingHom) := rfl
      _ = eY.toRingHom.comp (φ.toRingHom.comp (residue DX.carrier)) := by
        rw [fiberStrictMap_residue Psh f hsh]
      _ = eX.toRingHom.comp (residue DX.carrier) := by
        ext q
        simp [φ, eX, eY]
  exact congrArg AlgHom.toRingHom
    (strictMap_unique_of_residue DX.strict.isFilteredColimitEtale eX.toRingHom h gX hg
      (fiberSpecializationMap_residue Psh X hsh))

/-- The strict henselization of a morphism of deformations is cartesian: both flat algebras
become the same after the nilpotent base change to `k`. -/
private theorem fiberStrictMap_isPushout
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
    let DX := fiberStrictData X κsep
    let DY := fiberStrictData Y κsep
    letI : CommRing DX.carrier := DX.commRing
    letI : CommRing DY.carrier := DY.commRing
    letI : IsLocalRing DX.carrier := DX.isLocalRing
    letI : IsLocalRing DY.carrier := DY.isLocalRing
    letI : Algebra X.left.fiber DX.carrier := DX.algebra
    letI : Algebra Y.left.fiber DY.carrier := DY.algebra
    letI : Algebra X.left.fiber DY.carrier :=
      ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
    IsPushout
      (FlatAlgebraCategory.structureMap (fiberStrictFlatObject (κsep := κsep) X))
      (FlatAlgebraCategory.baseMap f.left.base)
      (CommRingCat.ofHom (fiberStrictMap Psh f hsh).toRingHom)
      (FlatAlgebraCategory.structureMap (fiberStrictFlatObject (κsep := κsep) Y)) := by
  let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  let : CommRing DX.carrier := DX.commRing
  let : CommRing DY.carrier := DY.commRing
  let : IsLocalRing DX.carrier := DX.isLocalRing
  let : IsLocalRing DY.carrier := DY.isLocalRing
  let : Algebra X.left.fiber DX.carrier := DX.algebra
  let : Algebra Y.left.fiber DY.carrier := DY.algebra
  let : Algebra X.left.fiber DY.carrier :=
    ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
  let A := X.left.base
  let B := Y.left.base
  let C := DX.carrier
  let D := DY.carrier
  let : Algebra A B := f.left.base.hom.toRingHom.toAlgebra
  let : Algebra A k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra B k := Y.hom.base.hom.toRingHom.toAlgebra
  let : Algebra A C := ((algebraMap X.left.fiber C).comp
    (algebraMap A X.left.fiber)).toAlgebra
  let : Algebra B D := ((algebraMap Y.left.fiber D).comp
    (algebraMap B Y.left.fiber)).toAlgebra
  let : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  let : Algebra A Psh := ((algebraMap k Psh).comp (algebraMap A k)).toAlgebra
  let : Algebra B Psh := ((algebraMap k Psh).comp (algebraMap B k)).toAlgebra
  let : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  let : Algebra Y.left.fiber Psh :=
    ((algebraMap P Psh).comp Y.hom.map.hom).toAlgebra
  let : Algebra C D := (fiberStrictMap Psh f hsh).toRingHom.toAlgebra
  let : Algebra C Psh := (fiberSpecializationMap Psh X hsh).toRingHom.toAlgebra
  let : Algebra D Psh := (fiberSpecializationMap Psh Y hsh).toRingHom.toAlgebra
  let : Module.Flat B D := (fiberStrictFlatObject (κsep := κsep) Y).flat
  have hABk : (algebraMap B k).comp (algebraMap A B) = algebraMap A k :=
    congrArg (fun g : X.left ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P =>
      g.base.hom.toRingHom) (Over.w f)
  let : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq' hABk.symm
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B Psh := IsScalarTower.of_algebraMap_eq' (by
    change (algebraMap k Psh).comp (algebraMap A k) =
      ((algebraMap k Psh).comp (algebraMap B k)).comp (algebraMap A B)
    rw [RingHom.comp_assoc, hABk])
  let : IsScalarTower A k Psh := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B k Psh := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap B D (algebraMap A B a) =
      (fiberStrictMap Psh f hsh)
        (algebraMap X.left.fiber C (algebraMap A X.left.fiber a))
    symm
    rw [fiberStrictMap_base Psh f hsh]
    exact congrArg (algebraMap Y.left.fiber D)
      (congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of Y.left.fiber => g.hom a)
        f.left.cartesian.w))
  let : IsScalarTower A C Psh := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k Psh (algebraMap A k a) =
      (fiberSpecializationMap Psh X hsh)
        (algebraMap X.left.fiber C (algebraMap A X.left.fiber a))
    symm
    rw [fiberSpecializationMap_comp Psh X hsh]
    have h := congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of P => g.hom a)
      X.hom.cartesian.w
    change X.hom.map.hom (algebraMap A X.left.fiber a) =
      algebraMap k P (X.hom.base.hom a) at h
    rw [h]
    exact (IsScalarTower.algebraMap_apply k P Psh (X.hom.base.hom a)).symm)
  let : IsScalarTower B D Psh := IsScalarTower.of_algebraMap_eq' (by
    ext b
    change algebraMap k Psh (algebraMap B k b) =
      (fiberSpecializationMap Psh Y hsh)
        (algebraMap Y.left.fiber D (algebraMap B Y.left.fiber b))
    symm
    rw [fiberSpecializationMap_comp Psh Y hsh]
    have h := congrArg (fun g : CommRingCat.of B ⟶ CommRingCat.of P => g.hom b)
      Y.hom.cartesian.w
    change Y.hom.map.hom (algebraMap B Y.left.fiber b) =
      algebraMap k P (Y.hom.base.hom b) at h
    rw [h]
    exact (IsScalarTower.algebraMap_apply k P Psh (Y.hom.base.hom b)).symm)
  let : IsScalarTower C D Psh := IsScalarTower.of_algebraMap_eq'
    (fiberStrictMap_specialization Psh f hsh).symm
  have hC : Algebra.IsPushout A k C Psh := by
    apply (CommRingCat.isPushout_iff_isPushout (R := A) (R' := k)
      (S := C) (S' := Psh)).mp
    convert (fiberStrictSpecializationHom Psh X hsh).cartesian.flip using 1
    all_goals rfl
  have hD : Algebra.IsPushout B k D Psh := by
    apply (CommRingCat.isPushout_iff_isPushout (R := B) (R' := k)
      (S := D) (S' := Psh)).mp
    convert (fiberStrictSpecializationHom Psh Y hsh).cartesian.flip using 1
    all_goals rfl
  let : IsLocalHom (algebraMap B k) :=
    IsLocalHom.of_surjective _ (deformationBaseMap_surjective Y)
  have hker : RingHom.ker (algebraMap B k) = maximalIdeal B := by
    rw [RingHom.ker_eq_comap_bot,
      ← IsLocalRing.maximalIdeal_comap (algebraMap B k)]
    simp [IsLocalRing.maximalIdeal_eq_bot (R := k)]
  have hnil : IsNilpotent (RingHom.ker (algebraMap B k)) := by
    rw [hker]
    exact isNilpotent_maximalIdeal_of_isArtinianRing B
  have hpo : Algebra.IsPushout A B C D :=
    isPushout_of_nilpotent_specialization hC hD (deformationBaseMap_surjective Y) hnil
  convert ((CommRingCat.isPushout_iff_isPushout (R := A) (R' := B)
    (S := C) (S' := D)).mpr hpo).flip using 1
  all_goals rfl

/-- The value of the strict henselization functor on a morphism of deformations. -/
private noncomputable def fiberStrictHom
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    fiberStrictOver Psh X hsh ⟶ fiberStrictOver Psh Y hsh := by
  letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  letI : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  letI : CommRing DX.carrier := DX.commRing
  letI : CommRing DY.carrier := DY.commRing
  letI : IsLocalRing DX.carrier := DX.isLocalRing
  letI : IsLocalRing DY.carrier := DY.isLocalRing
  letI : Algebra X.left.fiber DX.carrier := DX.algebra
  letI : Algebra Y.left.fiber DY.carrier := DY.algebra
  letI : Algebra X.left.fiber DY.carrier :=
    ((algebraMap Y.left.fiber DY.carrier).comp f.left.map.hom).toAlgebra
  let m : (fiberStrictOver Psh X hsh).left ⟶
      (fiberStrictOver Psh Y hsh).left :=
    { base := f.left.base
      map := CommRingCat.ofHom (fiberStrictMap Psh f hsh).toRingHom
      cartesian := fiberStrictMap_isPushout Psh f hsh }
  refine Over.homMk m ?_
  apply FlatAlgebraCategory.Hom.ext
  · change f.left.base ≫ Y.hom.base = X.hom.base
    exact congrArg FlatAlgebraCategory.Hom.base (Over.w f)
  · apply CommRingCat.hom_ext
    ext q
    change (fiberSpecializationMap Psh Y hsh)
      ((fiberStrictMap Psh f hsh) q) =
        (fiberSpecializationMap Psh X hsh) q
    exact RingHom.congr_fun (fiberStrictMap_specialization Psh f hsh) q

/-! ### Functoriality -/

/-- The strict henselization map out of the flat algebra of a deformation. -/
private noncomputable def strictFiberMap
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    X.left.fiber →+* (fiberStrictOver Psh X hsh).left.fiber := by
  letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : Algebra X.left.fiber D.carrier := D.algebra
  exact algebraMap X.left.fiber D.carrier

/-- Two morphisms between values of the strict henselization construction with the same base and
the same restriction along the strict henselization maps are equal. -/
private theorem fiberStrictOver_hom_ext
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh)
    (g h : fiberStrictOver Psh X hsh ⟶ fiberStrictOver Psh Y hsh)
    (hb : g.left.base = h.left.base)
    (hc : ∀ q, g.left.map.hom (strictFiberMap Psh X hsh q) =
      h.left.map.hom (strictFiberMap Psh X hsh q)) : g = h := by
  let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  let : IsLocalRing Y.left.fiber := deformationFiber_isLocalRing Y
  let DX := fiberStrictData X κsep
  let DY := fiberStrictData Y κsep
  let : CommRing DX.carrier := DX.commRing
  let : CommRing DY.carrier := DY.commRing
  let : IsLocalRing DX.carrier := DX.isLocalRing
  let : IsLocalRing DY.carrier := DY.isLocalRing
  let : Algebra X.left.fiber DX.carrier := DX.algebra
  let : Algebra Y.left.fiber DY.carrier := DY.algebra
  let : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := DX.residueAlgebra
  let : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := DX.sepClosure
  let : Algebra (maximalIdeal Y.left.fiber).ResidueField κsep := DY.residueAlgebra
  let : IsSepClosure (maximalIdeal Y.left.fiber).ResidueField κsep := DY.sepClosure
  let : HenselianLocalRing DY.carrier := DY.strict.henselian
  let : Algebra X.left.fiber DY.carrier :=
    (g.left.map.hom.comp (algebraMap X.left.fiber DX.carrier)).toAlgebra
  let ga : DX.carrier →ₐ[X.left.fiber] DY.carrier :=
    { toRingHom := g.left.map.hom
      commutes' := fun _ => rfl }
  let ha : DX.carrier →ₐ[X.left.fiber] DY.carrier :=
    { toRingHom := h.left.map.hom
      commutes' := fun q => (hc q).symm }
  let eX := fiberSpecializationResidueEquiv Psh X hsh
  let eY := fiberSpecializationResidueEquiv Psh Y hsh
  let φ := (eX.trans eY.symm).toRingHom
  have hres (t : fiberStrictOver Psh X hsh ⟶ fiberStrictOver Psh Y hsh) :
      (residue DY.carrier).comp t.left.map.hom = φ.comp (residue DX.carrier) := by
    ext q
    apply eY.injective
    change eY (residue DY.carrier (t.left.map.hom q)) =
      eY (eY.symm (eX (residue DX.carrier q)))
    rw [eY.apply_symm_apply]
    have heX := RingHom.congr_fun (fiberSpecializationMap_residue Psh X hsh) q
    have heY := RingHom.congr_fun (fiberSpecializationMap_residue Psh Y hsh)
      (t.left.map.hom q)
    have ht := congrArg (fun m => m.map.hom q) (Over.w t)
    change (fiberSpecializationMap Psh Y hsh) (t.left.map.hom q) =
      (fiberSpecializationMap Psh X hsh) q at ht
    exact heY.symm.trans ((congrArg (residue Psh) ht).trans heX)
  exact Over.OverMorphism.ext (FlatAlgebraCategory.Hom.ext hb (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (strictMap_unique_of_residue
      DX.strict.isFilteredColimitEtale φ ga ha (hres g) (hres h)))))

private theorem fiberStrictHom_inclusion
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y) (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh)
    (q : X.left.fiber) :
    (fiberStrictHom Psh f hsh).left.map.hom (strictFiberMap Psh X hsh q) =
      strictFiberMap Psh Y hsh (f.left.map.hom q) :=
  fiberStrictMap_base Psh f hsh q

private theorem fiberStrictHom_id
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    fiberStrictHom Psh (𝟙 X) hsh = 𝟙 (fiberStrictOver Psh X hsh) :=
  fiberStrictOver_hom_ext Psh hsh _ _ rfl (fiberStrictHom_inclusion Psh (𝟙 X) hsh)

private theorem fiberStrictHom_comp
    {X Y Z : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    fiberStrictHom Psh (f ≫ g) hsh =
      fiberStrictHom Psh f hsh ≫ fiberStrictHom Psh g hsh := by
  apply fiberStrictOver_hom_ext Psh hsh
  · rfl
  · intro q
    change (fiberStrictHom Psh (f ≫ g) hsh).left.map.hom
      (strictFiberMap Psh X hsh q) =
      (fiberStrictHom Psh g hsh).left.map.hom
        ((fiberStrictHom Psh f hsh).left.map.hom (strictFiberMap Psh X hsh q))
    rw [fiberStrictHom_inclusion, fiberStrictHom_inclusion,
      fiberStrictHom_inclusion]
    rfl

/-- **The strict henselization functor on deformation categories.** Its value on a deformation
`(A, Q) → (k, P)` is `(A, Qˢʰ) → (k, Pˢʰ)` for a chosen strict henselization `Qˢʰ` of `Q`, and
its value on a morphism is the unique local map of the chosen strict henselizations compatible
with the identifications of their residue fields with that of `Pˢʰ`. -/
@[no_expose]
noncomputable def strictDeformationFunctor
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    ringDeformationCategory (Λ := Λ) (k := k) P ⥤
      ringDeformationCategory (Λ := Λ) (k := k) Psh where
  obj X := fiberStrictOver Psh X hsh
  map f := fiberStrictHom Psh f hsh
  map_id X := fiberStrictHom_id Psh X hsh
  map_comp f g := fiberStrictHom_comp Psh f g hsh

/-- **Stacks 0DYU.** Let `P` be a local `k`-algebra and let `Pˢʰ` be a strict henselization of
`P` with respect to a separable algebraic closure of its residue field. There is a natural
functor from the deformation category of `P` to that of `Pˢʰ`, over the category `𝒞_Λ` of
Artinian local bases: strict henselize the flat algebra of each deformation. -/
@[no_expose, stacks 0DYU]
noncomputable def strictHenselizationFunctor
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    StrictHenselizationFunctorData (Λ := Λ) (k := k) (P := P) Psh where
  functor :=
    { toFunctor := strictDeformationFunctor Psh hsh
      w := rfl }
  fiberLocal := deformationFiber_isLocalRing
  strictFiberLocal X :=
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    (fiberStrictData X κsep).isLocalRing
  fiberMap X := strictFiberMap Psh X hsh
  fiberStrict X := by
    letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    change @Stacks.StrictHenselization.IsStrictHenselization X.left.fiber _ _
      (SeparableClosure (maximalIdeal X.left.fiber).ResidueField) _ _ _
      D.carrier _ _ (algebraMap X.left.fiber D.carrier).toAlgebra
    rw [toAlgebra_algebraMap]
    exact fiberStrictCanonical (κsep := κsep) X
  base_comm _ _ := rfl
  special_comm X q := by
    let : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
    exact fiberSpecializationMap_comp Psh X hsh q
  naturality f q := fiberStrictHom_inclusion Psh f hsh q

end Deformation.Examples

end
