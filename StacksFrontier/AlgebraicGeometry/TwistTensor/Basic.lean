module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict

/-!
# The multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` is an isomorphism on `D₊(pq)`

Let `S` be a graded ring, `X = Proj(S)`, and let `p ∈ S_{e+d}`, `q ∈ S_e` be homogeneous. On the
standard open `D₊(pq)` the ratio `p/q` is a unit of degree `d` of every local ring, and `(p/q)^n`
trivializes `𝒪_X(nd)` there. The canonical multiplication map

`𝒪_X(dn) ⊗_{𝒪_X} 𝒪_X(dm) ⟶ 𝒪_X(dn + dm)`

of `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` becomes an isomorphism
after restriction to `D₊(pq)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_over_basicOpen_mul`: the
  multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` restricted to `D₊(pq)` is an isomorphism whenever
  `a = n d` and `b = m d`.
* `Stacks.AlgebraicGeometry.TwistTensor.isGoodOpen_basicOpen_mul`: `D₊(pq)` is a good open for `d`
  whenever `deg p = deg q + d`.
* `Stacks.AlgebraicGeometry.TwistTensor.ratioLocus_le_whereInvertible`: the union of the standard
  opens `D₊(fg)` with `deg f = deg g + d` is contained in `W_d`.
* `Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top`: if
  `ratioLocus 𝒮 k` is all of `Proj S`, then `twistMultiplicationMap 𝒮 (kn) (km)` is an
  isomorphism of sheaves of modules on `Proj S`.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistTensor

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Rank-one freeness recognizes isomorphisms out of a tensor product -/

section Abstract

variable {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- A map out of `A ⊗ B` which respects scalars in the left factor is bijective as soon as `A`,
`B` and `C` are free of rank one and it carries the tensor of the two generators to the
generator. -/
lemma bijective_of_tmul_generators (eA : R ≃ₗ[R] A) (eB : R ≃ₗ[R] B) (eC : R ≃ₗ[R] C)
    (h : A ⊗[R] B → C)
    (hsmul : ∀ (r : R) (x : A) (y : B), h ((r • x) ⊗ₜ[R] y) = r • h (x ⊗ₜ[R] y))
    (hgen : h (eA 1 ⊗ₜ[R] eB 1) = eC 1) : Function.Bijective h := by
  set ψ : R ≃ₗ[R] A ⊗[R] B := (TensorProduct.lid R R).symm.trans (TensorProduct.congr eA eB)
    with hψ
  have hψ_apply : ∀ r : R, ψ r = (r • eA 1) ⊗ₜ[R] eB 1 := by
    intro r
    have h1 : ψ r = eA 1 ⊗ₜ[R] eB r := by
      rw [hψ]
      simp [TensorProduct.congr_tmul]
    rw [h1, show eB r = r • eB 1 by rw [← eB.map_smul, smul_eq_mul, mul_one],
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have key : ∀ r : R, h (ψ r) = eC r := by
    intro r
    rw [hψ_apply, hsmul, hgen, ← eC.map_smul, smul_eq_mul, mul_one]
  have hcomp : (h : A ⊗[R] B → C) = (eC : R → C) ∘ (ψ.symm : A ⊗[R] B → R) := by
    funext z
    have := key (ψ.symm z)
    rwa [LinearEquiv.apply_symm_apply] at this
  rw [hcomp]
  exact eC.bijective.comp ψ.symm.bijective

end Abstract

/-! ### The pointwise formula for the multiplication map -/

/-- The localization of `TensorProduct.lid`, read through the identification of the localization
of a tensor product with the tensor product of the localizations, is multiplication of the two
local values. -/
lemma map_lid_tensorLocalization (P : Submonoid S) (u v : LocalizedModule P S) :
    LocalizedModule.map P (TensorProduct.lid S S).toLinearMap
      (tensorLocalizationEquivOverLocalization (S := S) (M := S) (N := S) P (u ⊗ₜ[S] v))
      = u * v := by
  induction u using LocalizedModule.induction_on with
  | h x s =>
    induction v using LocalizedModule.induction_on with
    | h y t =>
      rw [tensorLocalizationEquivOverLocalization_mk, LocalizedModule.map_mk,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul]
      exact (Localization.mk_mul _ _ _ _).symm

variable {p q : S} {e d : ℕ}

/-- `(p/q)^n · (p/q)^m = (p/q)^{n+m}` in every local ring of `D₊(pq)`. -/
lemma ratioFun_mul (n m : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W) :
    ratioFun 𝒮 n hW x * ratioFun 𝒮 m hW x = ratioFun 𝒮 (n + m) hW x := by
  rw [ratioFun, ratioFun, ratioFun, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [Submonoid.coe_mul]
  calc q ^ (n + m).toNat * p ^ (-(n + m)).toNat
        * (p ^ n.toNat * q ^ (-n).toNat * (p ^ m.toNat * q ^ (-m).toNat))
      = p ^ (n.toNat + m.toNat + (-(n + m)).toNat)
        * q ^ ((-n).toNat + (-m).toNat + (n + m).toNat) := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ = p ^ ((n + m).toNat + (-n).toNat + (-m).toNat)
        * q ^ ((-(n + m)).toNat + n.toNat + m.toNat) := by congr 2 <;> omega
    _ = q ^ n.toNat * p ^ (-n).toNat * (q ^ m.toNat * p ^ (-m).toNat)
        * (p ^ (n + m).toNat * q ^ (-(n + m)).toNat) := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring

/-- The multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` sends the image of a pure tensor of honest
sections to the section whose value at each point is the product of the two local values. -/
lemma twistMultiplicationMap_tmul (a b : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒮))
    (ς : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W)
    (τ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W) (x : W) :
    ((((twistMultiplicationMap 𝒮 a b).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) (op W) (ς ⊗ₜ[_] τ))).1 x)
      = ς.1 x * τ.1 x := by
  let _ := tensorGrading_decomposition (S := S) 𝒮 (twistGrading (S := S) 𝒮 a)
    (twistGrading (S := S) 𝒮 b)
  let _ := tensorGrading_gradedSMul (S := S) 𝒮 (twistGrading (S := S) 𝒮 a)
    (twistGrading (S := S) 𝒮 b)
  have hcomp : ((twistMultiplicationMap 𝒮 a b).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) (op W) (ς ⊗ₜ[_] τ))
      = ((associatedModuleSheafMap 𝒮
          (Stacks.GradedModule.tensorGrading (S := S) (twistGrading (S := S) 𝒮 a)
            (twistGrading (S := S) 𝒮 b))
          (twistGrading (S := S) 𝒮 (a + b)) (TensorProduct.lid S S).toLinearMap
          (twistMultiplication_preserves_grading 𝒮 a b)).val.app (op W)).hom
        (((associatedModuleSheafTensorMap 𝒮 (twistGrading (S := S) 𝒮 a)
            (twistGrading (S := S) 𝒮 b)).val.app (op W)).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
            𝒮).toRingedSpace
            (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) (op W) (ς ⊗ₜ[_] τ))) := rfl
  have hstep : ((twistMultiplicationMap 𝒮 a b).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) (op W) (ς ⊗ₜ[_] τ))
      = ((associatedModuleSheafMap 𝒮
          (Stacks.GradedModule.tensorGrading (S := S) (twistGrading (S := S) 𝒮 a)
            (twistGrading (S := S) 𝒮 b))
          (twistGrading (S := S) 𝒮 (a + b)) (TensorProduct.lid S S).toLinearMap
          (twistMultiplication_preserves_grading 𝒮 a b)).val.app (op W)).hom
        (tensorModuleSectionsAddHom 𝒮 (twistGrading (S := S) 𝒮 a)
          (twistGrading (S := S) 𝒮 b) W (ς ⊗ₜ[_] τ)) :=
    hcomp.trans (congrArg _ (associatedModuleSheafTensorMap_app_toTensorSheafSection 𝒮
      (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b) (op W) _))
  rw [hstep, tensorModuleSectionsAddHom_tmul]
  exact map_lid_tensorLocalization _ _ _

/-! ### Bijectivity on the sections of the presheaf tensor product -/

/-- The trivialization of `𝒪(nd)` on an open of `D₊(pq)` carries `1` to the trivializing
section. -/
lemma ratioEquiv_one (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    ratioEquiv 𝒮 hp hq hc hW 1 = ratioSection 𝒮 hp hq hc hW := by
  show ratioHom 𝒮 hp hq hc hW 1 = _
  rw [ratioHom, LinearMap.toSpanSingleton_apply, one_smul]

/-- On every open `W ⊆ D₊(pq)`, the sheafification unit followed by the multiplication map is a
bijection `𝒪(a)(W) ⊗_{𝒪(W)} 𝒪(b)(W) → 𝒪(a+b)(W)`. -/
lemma bijective_twistMultiplicationMap_toTensorSheafSection
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n m a b : ℤ}
    (ha : (n : ℤ) * d = a) (hb : (m : ℤ) * d = b)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective (fun z => ((twistMultiplicationMap 𝒮 a b).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) (op W) z)) := by
  have hab : (n + m : ℤ) * d = a + b := by rw [← ha, ← hb]; ring
  refine bijective_of_tmul_generators (ratioEquiv 𝒮 hp hq ha hW) (ratioEquiv 𝒮 hp hq hb hW)
    (ratioEquiv 𝒮 hp hq hab hW) _ (fun r x y => ?_) ?_
  · refine Subtype.ext (funext fun z => ?_)
    calc _ = (r • x).1 z * y.1 z := twistMultiplicationMap_tmul 𝒮 a b W (r • x) y z
      _ = HomogeneousLocalization.val (r.1 z) * (x.1 z * y.1 z) := mul_assoc _ _ _
      _ = _ := congrArg (fun t => HomogeneousLocalization.val (r.1 z) * t)
        (twistMultiplicationMap_tmul 𝒮 a b W x y z).symm
  · rw [ratioEquiv_one, ratioEquiv_one, ratioEquiv_one]
    refine Subtype.ext (funext fun x => ?_)
    exact (twistMultiplicationMap_tmul 𝒮 a b W _ _ x).trans (ratioFun_mul 𝒮 n m hW x)

/-! ### From sections over the opens of `D₊(pq)` to the stalks -/

/-- The image in `X` of an open of an open subspace `U` is contained in `U`. -/
lemma imF_obj_le {Y : TopCat} (U : Opens Y)
    (V : Opens ((Opens.toTopCat Y).obj U)) : (TopCat.Presheaf.imF U).obj V ≤ U := by
  rintro y ⟨v, -, rfl⟩
  exact v.2


/-- The sheafification unit of the presheaf tensor product of two twists, read on the underlying
presheaves of abelian groups. -/
noncomputable def twistUnitAb (a b : ℤ) :=
  (PresheafOfModules.toPresheaf.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit (AlgebraicGeometry.Proj
      𝒮).toRingedSpace ((PresheafOfModules.tensorObj
        (O := (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf)
        (twistingSheaf 𝒮 a).val (twistingSheaf 𝒮 b).val)))

/-- The multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)`, read on the underlying presheaves of abelian
groups. -/
noncomputable def twistMultAb (a b : ℤ) :=
  (PresheafOfModules.toPresheaf.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
    (twistMultiplicationMap 𝒮 a b).val

/-- At every point of `D₊(pq)` the multiplication map is an isomorphism on stalks. -/
lemma isIso_stalkFunctor_map_twistMultiplication
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n m a b : ℤ}
    (ha : (n : ℤ) * d = a) (hb : (m : ℤ) * d = b)
    {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (twistMultAb 𝒮 a b)) := by
  set U : Opens ↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace :=
    ProjectiveSpectrum.basicOpen 𝒮 (p * q) with hU
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (twistUnitAb 𝒮 a b ≫ twistMultAb 𝒮 a b)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_twistMultiplicationMap_toTensorSheafSection 𝒮 hp hq ha hb
      (W := (TopCat.Presheaf.imF U).obj V.unop) (imF_obj_le U V.unop)
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : ↥U)).map (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (twistUnitAb 𝒮 a b ≫ twistMultAb 𝒮 a b))) := inferInstance
  have h3 := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    (twistUnitAb 𝒮 a b ≫ twistMultAb 𝒮 a b) ⟨x, hx⟩).mp h2
  have h4 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
      (twistUnitAb 𝒮 a b ≫ twistMultAb 𝒮 a b)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (twistUnitAb 𝒮 a b) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (twistMultAb 𝒮 a b) := Functor.map_comp _ _ _
  rw [h4] at h3
  have hηiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (U.inclusion' ⟨x, hx⟩)).map (twistUnitAb 𝒮 a b)) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap_sheafifyUnit_isIso (AlgebraicGeometry.Proj
      𝒮).toRingedSpace _ _
  exact (@isIso_comp_left_iff _ _ _ _ _ _ _ hηiso).mp h3

/-- The multiplication map is bijective on the sections over every open contained in
`D₊(pq)`. -/
lemma bijective_twistMultiplicationMap_app
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n m a b : ℤ}
    (ha : (n : ℤ) * d = a) (hb : (m : ℤ) * d = b)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective (ConcreteCategory.hom ((twistMultAb 𝒮 a b).app (op W))) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf.{u} (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map (twistMultiplicationMap 𝒮 a b)) W
    (fun x hx => ?_)
  have h := isIso_stalkFunctor_map_twistMultiplication 𝒮 hp hq ha hb (x := x) (hW hx)
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-! ### The local form, and Tag 01MU's inclusion -/

/-- A morphism of sheaves of modules is an isomorphism once it is one on the underlying sheaves of
abelian groups. -/
private lemma isIso_of_isIso_toSheaf_map {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) (h : IsIso ((SheafOfModules.toSheaf.{u} R).map f)) : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f (SheafOfModules.toSheaf.{u} R) h
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1

/-- For `p` homogeneous of degree `e + d` and `q` homogeneous of degree `e`,
the multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` between two `d`-divisible twists becomes an
isomorphism on the restricted site of the standard open `D₊(pq)`. -/
theorem isIso_twistMultiplicationMap_over_basicOpen_mul
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n m a b : ℤ}
    (ha : (n : ℤ) * d = a) (hb : (m : ℤ) * d = b) :
    IsIso ((twistMultiplicationMap 𝒮 a b).over
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q))) := by
  have hmap : IsIso ((SheafOfModules.forget.{u}
      ((structureSheafRing (AlgebraicGeometry.Proj
        𝒮).toRingedSpace).over
        (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q))) ⋙
      PresheafOfModules.toPresheaf.{u} _).map ((twistMultiplicationMap 𝒮 a b).over
        (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_twistMultiplicationMap_app 𝒮 hp hq ha hb (W := V.unop.left)
      (leOfHom V.unop.hom)
  have hsheaf : IsIso ((SheafOfModules.toSheaf.{u}
      ((structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace).over
        (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)))).map
      ((twistMultiplicationMap 𝒮 a b).over
        (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)))) :=
    @isIso_of_reflects_iso _ _ _ _ _ _ _ (sheafToPresheaf _ _) hmap inferInstance
  exact isIso_of_isIso_toSheaf_map _ hsheaf

/-- `D₊(pq)` is a good open for `d` whenever `deg p = deg q + d`: the twists are invertible there
and the multiplication maps between them are isomorphisms there. -/
theorem isGoodOpen_basicOpen_mul (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) :
    IsGoodOpen 𝒮 d (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)) :=
  isGoodOpen_basicOpen_mul_of_isIso_mul 𝒮 hp hq fun n m =>
    isIso_twistMultiplicationMap_over_basicOpen_mul 𝒮 hp hq (mul_comm (n : ℤ) (d : ℤ))
      (mul_comm (m : ℤ) (d : ℤ))

/-- The union of the standard opens `D₊(fg)` with `deg f = deg g + k` is contained in `W_k`. -/
theorem ratioLocus_le_whereInvertible (k : ℕ) :
    Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒮 k ≤ whereInvertible 𝒮 k :=
  ratioLocus_le_whereInvertible_of_isIso_mul 𝒮 k fun _ f g n m =>
    isIso_twistMultiplicationMap_over_basicOpen_mul 𝒮 f.2 g.2 (mul_comm (n : ℤ) (k : ℤ))
      (mul_comm (m : ℤ) (k : ℤ))

/-! ### A conditional global form -/

/-- If the union of the standard opens `D₊(fg)` with
`deg f = deg g + k` is all of `Proj S` — for `k = 1` this is the usual hypothesis that `S` is
generated in degree one — then the multiplication map
`𝒪(kn) ⊗ 𝒪(km) ⟶ 𝒪(kn + km)` is an isomorphism of sheaves of modules on `Proj S`. -/
theorem isIso_twistMultiplicationMap_of_ratioLocus_eq_top {k : ℕ}
    (hk : Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒮 k = ⊤) (n m : ℤ) :
    IsIso (twistMultiplicationMap 𝒮 ((k : ℤ) * n) ((k : ℤ) * m)) := by
  have hstalk : ∀ x : ↑↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf.{u} (structureSheafRing
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
          (twistMultiplicationMap 𝒮 ((k : ℤ) * n) ((k : ℤ) * m))).hom) := by
    intro x
    have hx : x ∈ (⨆ (j : ℕ) (f : 𝒮 (j + k)) (g : 𝒮 j),
        AlgebraicGeometry.Proj.basicOpen 𝒮 ((f : S) * (g : S))) := by
      rw [iSup_basicOpen_mul_eq_ratioLocus, hk]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    obtain ⟨f, hf⟩ := Opens.mem_iSup.mp hj
    obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hf
    exact isIso_stalkFunctor_map_twistMultiplication 𝒮 f.2 g.2 (mul_comm (n : ℤ) (k : ℤ))
      (mul_comm (m : ℤ) (k : ℤ)) hg
  have h := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf.{u} (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
      (twistMultiplicationMap 𝒮 ((k : ℤ) * n) ((k : ℤ) * m)))
  exact isIso_of_isIso_toSheaf_map _ h

end Stacks.AlgebraicGeometry.TwistTensor

end
