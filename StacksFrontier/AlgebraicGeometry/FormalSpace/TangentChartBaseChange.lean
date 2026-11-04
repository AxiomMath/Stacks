module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FieldPointLift
public import StacksFrontier.Deformation.TangentSpace.RingValueFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Base change of a first-order test point to a finite extension of the residue field

Fix a field `k` with a factorization `Spec k ⟶ Spec Λ ⟶ S`, an object `T₀` of the big fppf site
over `S` lying over `Spec k`, and a finite extension `l/k`. A *test datum* over a finite
dimensional `k`-vector space `V` is an object `T` of the site lying over
`Spec k[V] ⟶ Spec Λ ⟶ S`, together with a morphism `T₀ ⟶ T` lying over the closed point
`Spec k ⟶ Spec k[V]`; these are what the deformations of a point over the square-zero extensions
`k[V] = k ⊕ V` provide.

This file constructs the base change `T_l = Spec (k[V] ⊗_k l)` of a test datum, the morphism
`T_l ⟶ T`, which is an fppf covering, and the closed point `Spec l ⟶ T_l`, which is a
square-zero closed immersion through which `Spec l ⟶ T₀ ⟶ T` factors.

## Main definitions

* `AlgebraicGeometry.FormalSpace.TangentChart.TestDatum`: a test datum.
* `AlgebraicGeometry.FormalSpace.TangentChart.TestDatum.baseChange`: the object
  `Spec (k[V] ⊗_k l)`.
* `AlgebraicGeometry.FormalSpace.TangentChart.TestDatum.baseChangeMap`: its morphism to `T`.
* `AlgebraicGeometry.FormalSpace.TangentChart.closedPointMap`: the closed point
  `Spec l ⟶ Spec (k[V] ⊗_k l)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u w

namespace AlgebraicGeometry.FormalSpace.TangentChart

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The right `k`-module structure on `V` given by the left action through `MulOpposite.unop`. -/
local instance (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

/-- The left and right actions of `k` on `V` agree. -/
local instance (V : FGModuleCat.{u} k) : IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

/-! ### The ring `k[V] ⊗_k l` -/

section Ring

variable (l : Type u) [Field l] [Algebra k l] (V : FGModuleCat.{u} k)

/-- The residue map `k[V] ⊗_k l ⟶ l`. -/
def residueHom : TrivSqZeroExt k V ⊗[k] l →ₐ[k] l :=
  (Algebra.TensorProduct.lid k l).toAlgHom.comp
    (Algebra.TensorProduct.map (TrivSqZeroExt.fstHom k k V) (AlgHom.id k l))

/-- The residue map sends `a ⊗ x` to `a.fst • x`. -/
theorem residueHom_tmul (a : TrivSqZeroExt k V) (x : l) :
    residueHom l V (a ⊗ₜ x) = a.fst • x := rfl

/-- The residue map is surjective. -/
theorem residueHom_surjective : Function.Surjective (residueHom l V) := fun x =>
  ⟨1 ⊗ₜ x, by rw [residueHom_tmul, TrivSqZeroExt.fst_one, one_smul]⟩

/-- The first projection of `k[V] ⊗_k l` is `w ↦ 1 ⊗ residueHom l V w`. -/
theorem tensorFst_eq (w : TrivSqZeroExt k V ⊗[k] l) :
    Deformation.tensorFst l V w = 1 ⊗ₜ residueHom l V w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, TensorProduct.tmul_add]
  | tmul a x =>
    rw [residueHom_tmul, LinearMap.rTensor_tmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

/-- An element lies in the kernel of the residue map if and only if its first projection vanishes.
-/
theorem residueHom_eq_zero_iff (w : TrivSqZeroExt k V ⊗[k] l) :
    residueHom l V w = 0 ↔ Deformation.tensorFst l V w = 0 := by
  rw [tensorFst_eq]
  constructor
  · intro h; rw [h, TensorProduct.tmul_zero]
  · intro h
    have := congrArg (Algebra.TensorProduct.lid k l) h
    simpa using this

/-- The kernel of the residue map has vanishing products. -/
theorem mul_eq_zero_of_residueHom {a b : TrivSqZeroExt k V ⊗[k] l} (ha : residueHom l V a = 0)
    (hb : residueHom l V b = 0) : a * b = 0 := by
  obtain ⟨a', rfl⟩ := Deformation.mem_range_tensorInr l V ((residueHom_eq_zero_iff l V a).1 ha)
  obtain ⟨b', rfl⟩ := Deformation.mem_range_tensorInr l V ((residueHom_eq_zero_iff l V b).1 hb)
  exact Deformation.tensorInr_mul_tensorInr l V a' b'

/-- The kernel of the residue map has square zero. -/
theorem ker_residueHom_sq : RingHom.ker (residueHom l V).toRingHom ^ 2 = ⊥ := by
  rw [sq, eq_bot_iff]
  refine Ideal.mul_le.mpr fun a ha b hb => ?_
  rw [Ideal.mem_bot]
  exact mul_eq_zero_of_residueHom l V ha hb

/-- Nilpotent elements of `k[V] ⊗_k l` multiply to zero. -/
theorem mul_eq_zero_of_isNilpotent {a b : TrivSqZeroExt k V ⊗[k] l} (ha : IsNilpotent a)
    (hb : IsNilpotent b) : a * b = 0 :=
  mul_eq_zero_of_residueHom l V ((ha.map (residueHom l V)).eq_zero)
    ((hb.map (residueHom l V)).eq_zero)

end Ring

/-! ### Test data -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (iΛ : Spec (.of Λ) ⟶ S)
  (T₀ : BigFppfOver B S hS) (e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k))

/-- A *test datum* over a finite dimensional `k`-vector space `V`: an object of the site lying
over `Spec k[V] ⟶ Spec Λ ⟶ S` and a morphism from `T₀` lying over the closed point. -/
structure TestDatum (V : FGModuleCat.{u} k) where
  /-- The object of the site. -/
  T : BigFppfOver B S hS
  /-- Its underlying scheme is `Spec k[V]`. -/
  eS : (BigFppfOver.toScheme B S hS).obj T = Spec (.of (TrivSqZeroExt k V))
  /-- It lies over `Spec k[V] ⟶ Spec Λ ⟶ S`. -/
  hom_eq : B.inclusion.map T.hom = eqToHom eS ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Λ ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ
  /-- The closed point. -/
  j : T₀ ⟶ T
  /-- The closed point lies over `Spec k ⟶ Spec k[V]`. -/
  j_eq : B.inclusion.map j.left = eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom
      (Deformation.Artin.residueMap ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫
    eqToHom eS.symm

/-! ### The base change and its two morphisms -/

section BaseChange

variable (l : Type u) [Field l] [Algebra k l]

/-- The residue map of `k[V]` is the first projection. -/
theorem residueMap_squareZero (V : FGModuleCat.{u} k) (a : TrivSqZeroExt k V) :
    Deformation.Artin.residueMap ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj V) a =
      a.fst := rfl

/-- The structure map `Λ → k[V] ⊗_k l`. -/
abbrev structureHom (V : FGModuleCat.{u} k) : Λ →+* TrivSqZeroExt k V ⊗[k] l :=
  (algebraMap k (TrivSqZeroExt k V ⊗[k] l)).comp (algebraMap Λ k)

/-- The base change `Spec (k[V] ⊗_k l)`, as an object of the site over `S`. -/
abbrev baseChange (V : FGModuleCat.{u} k)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) : BigFppfOver B S hS :=
  siteObject B S hS hC (Spec.map (CommRingCat.ofHom (structureHom l V)) ≫ iΛ)

variable {iΛ T₀ e₀}

/-- The underlying scheme of a test datum is contained in the site. -/
theorem TestDatum.contains {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V) :
    B.Contains (Spec (.of (TrivSqZeroExt k V))) :=
  d.eS ▸ d.T.left.2

/-- The inclusion `k[V] ⟶ k[V] ⊗_k l`. -/
abbrev includeHom (V : FGModuleCat.{u} k) :
    CommRingCat.of (TrivSqZeroExt k V) ⟶ CommRingCat.of (TrivSqZeroExt k V ⊗[k] l) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := k)).toRingHom

/-- The morphism `Spec (k[V] ⊗_k l) ⟶ T` of the site. -/
def TestDatum.baseChangeMap {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) :
    baseChange iΛ l V hC ⟶ d.T :=
  Over.homMk (B.inclusion.preimage (X := (baseChange iΛ l V hC).left) (Y := d.T.left)
    (Spec.map (includeHom l V) ≫ eqToHom d.eS.symm)) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, Category.assoc, d.hom_eq,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Category.assoc, ← Spec.map_comp]
      rfl)

/-- The underlying morphism of schemes of `TestDatum.baseChangeMap` is induced by the inclusion
`k[V] ⟶ k[V] ⊗_k l`. -/
theorem TestDatum.toScheme_baseChangeMap {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) :
    B.inclusion.map (d.baseChangeMap l hC).left = Spec.map (includeHom l V) ≫ eqToHom d.eS.symm :=
  Functor.map_preimage _ _

variable (iΛ T₀ e₀) in
/-- The closed point `Spec l ⟶ Spec (k[V] ⊗_k l)` of the site. -/
def closedPointMap
    (h₀ : B.inclusion.map T₀.hom = eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    (V : FGModuleCat.{u} k)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) (hl : B.Contains (Spec (.of l))) :
    fieldExtensionObject T₀ e₀ l hl ⟶ baseChange iΛ l V hC :=
  Over.homMk (B.inclusion.preimage (X := B.obj hl) (Y := (baseChange iΛ l V hC).left)
    (Spec.map (CommRingCat.ofHom (residueHom l V).toRingHom))) (by
      apply B.inclusion.map_injective
      change B.inclusion.map (_ ≫ _) = B.inclusion.map (_ ≫ T₀.hom)
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_comp, Functor.map_preimage]
      change _ ≫ Spec.map _ ≫ iΛ = (_ ≫ _) ≫ B.inclusion.map T₀.hom
      rw [Category.assoc, h₀, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r
      change residueHom l V (algebraMap k _ (algebraMap Λ k r)) = _
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, Algebra.smul_def, mul_one]
      rfl)

variable (h₀ : B.inclusion.map T₀.hom =
  eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)

/-- The underlying morphism of schemes of `closedPointMap` is induced by the residue map. -/
theorem toScheme_closedPointMap (V : FGModuleCat.{u} k)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) (hl : B.Contains (Spec (.of l))) :
    B.inclusion.map (closedPointMap iΛ T₀ e₀ l h₀ V hC hl).left =
      Spec.map (CommRingCat.ofHom (residueHom l V).toRingHom) :=
  Functor.map_preimage _ _

/-- The closed point is a square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_closedPointMap (V : FGModuleCat.{u} k)
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) (hl : B.Contains (Spec (.of l))) :
    Space.IsSquareZeroClosedImmersion B S hS (closedPointMap iΛ T₀ e₀ l h₀ V hC hl) := by
  change Stacks.Thickenings.IsFirstOrderThickening
    (B.inclusion.map (closedPointMap iΛ T₀ e₀ l h₀ V hC hl).left)
  rw [toScheme_closedPointMap]
  exact Stacks.Smooth.isFirstOrderThickening_specMap _ (residueHom_surjective l V)
    (ker_residueHom_sq l V)

/-- Morphisms of the site with the same underlying morphism of schemes are equal. -/
private theorem hom_ext_of_inclusion_map {X Y : BigFppfOver B S hS} {f g : X ⟶ Y}
    (h : B.inclusion.map f.left = B.inclusion.map g.left) : f = g :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- The closed point of the base change lies over the closed point of the test datum. -/
theorem TestDatum.closedPointMap_baseChangeMap {V : FGModuleCat.{u} k}
    (d : TestDatum iΛ T₀ e₀ V) (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))))
    (hl : B.Contains (Spec (.of l))) :
    closedPointMap iΛ T₀ e₀ l h₀ V hC hl ≫ d.baseChangeMap l hC =
      fieldExtensionMap T₀ e₀ l hl ≫ d.j := by
  apply hom_ext_of_inclusion_map
  rw [Over.comp_left, Over.comp_left]
  have hf : B.inclusion.map (fieldExtensionMap T₀ e₀ l hl).left =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ eqToHom e₀.symm :=
    toScheme_map_fieldExtensionMap T₀ e₀ l hl
  rw [Functor.map_comp, Functor.map_comp, toScheme_closedPointMap, d.toScheme_baseChangeMap l hC,
    d.j_eq, hf]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change residueHom l V (a ⊗ₜ 1) = algebraMap k l a.fst
  rw [residueHom_tmul, Algebra.algebraMap_eq_smul_one]

end BaseChange

/-! ### Naturality in `V` -/

section Naturality

variable {iΛ T₀ e₀}
  (h₀ : B.inclusion.map T₀.hom = eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
  (l : Type u) [Field l] [Algebra k l]

/-- The morphism `Spec (k[V'] ⊗_k l) ⟶ Spec (k[V] ⊗_k l)` induced by `f : V ⟶ V'`. -/
def baseChangeMorph {V V' : FGModuleCat.{u} k} (f : V ⟶ V')
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))))
    (hC' : B.Contains (Spec (.of (TrivSqZeroExt k V' ⊗[k] l)))) :
    baseChange (hS := hS) iΛ l V' hC' ⟶ baseChange (hS := hS) iΛ l V hC :=
  Over.homMk (B.inclusion.preimage (X := (baseChange (hS := hS) iΛ l V' hC').left)
    (Y := (baseChange (hS := hS) iΛ l V hC).left) (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (TrivSqZeroExt.map f.hom.hom) (AlgHom.id k l)).toRingHom))) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      change _ ≫ Spec.map _ ≫ iΛ = Spec.map _ ≫ iΛ
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext r
      change (Algebra.TensorProduct.map (TrivSqZeroExt.map f.hom.hom) (AlgHom.id k l))
        (algebraMap k _ (algebraMap Λ k r)) = algebraMap k _ (algebraMap Λ k r)
      exact AlgHom.commutes _ _)

/-- The underlying morphism of schemes of `baseChangeMorph` is induced by `k[f] ⊗_k l`. -/
theorem toScheme_baseChangeMorph {V V' : FGModuleCat.{u} k} (f : V ⟶ V')
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))))
    (hC' : B.Contains (Spec (.of (TrivSqZeroExt k V' ⊗[k] l)))) :
    B.inclusion.map (baseChangeMorph (hS := hS) (iΛ := iΛ) l f hC hC').left =
      Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (TrivSqZeroExt.map f.hom.hom) (AlgHom.id k l)).toRingHom) :=
  Functor.map_preimage _ _

/-- The morphism `baseChangeMorph` is compatible with the closed points. -/
theorem closedPointMap_baseChangeMorph {V V' : FGModuleCat.{u} k} (f : V ⟶ V')
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))))
    (hC' : B.Contains (Spec (.of (TrivSqZeroExt k V' ⊗[k] l)))) (hl : B.Contains (Spec (.of l))) :
    closedPointMap iΛ T₀ e₀ l h₀ V' hC' hl ≫ baseChangeMorph l f hC hC' =
      closedPointMap iΛ T₀ e₀ l h₀ V hC hl := by
  apply hom_ext_of_inclusion_map
  rw [Over.comp_left, Functor.map_comp, toScheme_closedPointMap, toScheme_baseChangeMorph,
    toScheme_closedPointMap, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x =>
    change residueHom l V' (TrivSqZeroExt.map f.hom.hom a ⊗ₜ x) = residueHom l V (a ⊗ₜ x)
    rw [residueHom_tmul, residueHom_tmul, TrivSqZeroExt.fst_map]

/-- A morphism of test data over `f : V ⟶ V'`: a morphism of the site lying over
`Spec k[V'] ⟶ Spec k[V]`, compatible with the closed points. -/
structure TestDatum.Hom {V V' : FGModuleCat.{u} k} (f : V ⟶ V') (d : TestDatum iΛ T₀ e₀ V)
    (d' : TestDatum iΛ T₀ e₀ V') where
  /-- The morphism of the site. -/
  m : d'.T ⟶ d.T
  /-- It lies over `Spec k[V'] ⟶ Spec k[V]`. -/
  m_eq : B.inclusion.map m.left = eqToHom d'.eS ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) ≫ eqToHom d.eS.symm
  /-- It is compatible with the closed points. -/
  j_m : d'.j ≫ m = d.j

/-- The base change maps commute with a morphism of test data and `baseChangeMorph`. -/
theorem TestDatum.Hom.baseChangeMap_comp {V V' : FGModuleCat.{u} k} {f : V ⟶ V'}
    {d : TestDatum iΛ T₀ e₀ V} {d' : TestDatum iΛ T₀ e₀ V'} (φ : TestDatum.Hom f d d')
    (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))))
    (hC' : B.Contains (Spec (.of (TrivSqZeroExt k V' ⊗[k] l)))) :
    d'.baseChangeMap l hC' ≫ φ.m = baseChangeMorph l f hC hC' ≫ d.baseChangeMap l hC := by
  apply hom_ext_of_inclusion_map
  rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp,
    d'.toScheme_baseChangeMap l hC', φ.m_eq, toScheme_baseChangeMorph,
    d.toScheme_baseChangeMap l hC]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

end Naturality

/-! ### The base change is an fppf covering -/

section Covering

variable (l : Type u) [Field l] [Algebra k l] [Module.Finite k l]

/-- `k[V]` has a single prime ideal. -/
theorem subsingleton_spec_squareZero (V : FGModuleCat.{u} k) :
    Subsingleton (Spec (.of (TrivSqZeroExt k V))) := by
  have key : ∀ p : PrimeSpectrum (TrivSqZeroExt k V),
      p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom := by
    intro p
    have hmax : (RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ TrivSqZeroExt.fst_surjective
    refine (hmax.eq_of_le p.2.ne_top fun x hx => ?_).symm
    have hx0 : x = TrivSqZeroExt.inr x.snd := by
      ext
      · exact hx
      · rfl
    have hsq : x * x = 0 := by rw [hx0, TrivSqZeroExt.inr_mul_inr]
    exact (p.2.mem_or_mem (hsq ▸ p.asIdeal.zero_mem)).elim id id
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

variable {iΛ T₀ e₀}

/-- A section of an fppf sheaf over a test datum is determined by its restriction along
`TestDatum.baseChangeMap`, which is an fppf covering. -/
theorem TestDatum.injective_map_baseChangeMap
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) {V : FGModuleCat.{u} k}
    (d : TestDatum iΛ T₀ e₀ V) (hC : B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))) :
    Function.Injective (P.map (d.baseChangeMap l hC).op) := by
  have hP' : Presieve.IsSheaf (BigFppfOver.topology B S hS) P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hP
  have hflat : RingHom.Flat (includeHom l V).hom :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Algebra.FinitePresentation k l :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  have hfp : RingHom.FinitePresentation (includeHom l V).hom :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hmem : Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{1} => baseChange iΛ l V hC)
      (fun _ => d.baseChangeMap l hC)) ∈ BigFppfOver.topology B S hS d.T := by
    refine BigFppfOver.sieve_generate_ofArrows_mem_topology _ _ ?_
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    have hmap : (BigFppfOver.toScheme B S hS).map (d.baseChangeMap l hC) =
        Spec.map (includeHom l V) ≫ eqToHom d.eS.symm := d.toScheme_baseChangeMap l hC
    refine ⟨fun y => ?_, fun _ => ?_⟩
    · have : Subsingleton ((BigFppfOver.toScheme B S hS).obj d.T) := by
        rw [d.eS]; exact subsingleton_spec_squareZero V
      obtain ⟨x⟩ : Nonempty (Spec (.of (TrivSqZeroExt k V ⊗[k] l))) :=
        inferInstanceAs (Nonempty (PrimeSpectrum _))
      exact ⟨PUnit.unit, x, Subsingleton.elim _ _⟩
    · rw [hmap]
      refine ⟨?_, ?_⟩
      · have : Flat (Spec.map (includeHom l V)) :=
          (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflat
        infer_instance
      · have : LocallyOfFinitePresentation (Spec.map (includeHom l V)) :=
          (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hfp
        infer_instance
  intro x y hxy
  refine (hP' _ hmem).isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨Z, h, _, ⟨⟩, rfl⟩ := hg
  rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply, hxy]

end Covering

end AlgebraicGeometry.FormalSpace.TangentChart

end
