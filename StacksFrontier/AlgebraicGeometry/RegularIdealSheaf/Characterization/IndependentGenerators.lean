module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalSheaves
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.FiniteTypeAndWords
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.LocalKernel
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalLocallyFree
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.LocalInjectivity

/-!
# Quasi-regular ideal sheaves: generators with independent conormal classes

Inverting the free comparison of the conormal sheaf, local generators of `J` whose conormal
classes are independent, and the characterization `isQuasiRegularIdealSheaf_iff` (Tag 063H).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingTheory.QuasiRegular
open scoped BigOperators
universe u v

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.toSheaf PresheafOfModules.presheaf
open Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal in
attribute [local implicit_reducible] quotientPresheaf quotientSheaf gradedPresheaf
attribute [local implicit_reducible] PresheafOfModules.freeObj ModuleCat.free
  CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

/-- **The comparison carries the conormal class of the lifted section to the chosen
generating section itself.** This is the identity the `hfree` half is read through: the
step-(c) equation lands in the restriction of the value on `U₀`, and the compatibility of
`σ.s i` as a section identifies that restriction with the value on `V`. -/
private lemma conormalUnit_conormalClass_eq_section (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) (i : σ.I)
    {V : Opens X} (hVU₀ : V ≤ U₀) (z : J.obj (op V))
    (hz : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) z) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s i).val (op (Over.mk (𝟙 U₀))))) :
    (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) z) =
      (σ.s i).val (op (Over.mk (homOfLE hVU₀))) := by
  rw [hz]
  exact (σ.s i).property (Over.homMk (homOfLE hVU₀) :
    (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op

/-- **The join.** On every open below the witness, the unit carries an `O_X/J`-linear
combination of the conormal classes of the lifted sections to the value of the
presheaf-level free map on the corresponding coordinate vector. -/
private lemma conormalUnit_freeMk (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) (i : σ.I)
    {V : Opens X} (hVU₀ : V ≤ U₀) (z : J.obj (op V))
    (hz : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) z) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s i).val (op (Over.mk (𝟙 U₀))))) :
    (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) z) =
      (freePresheafMap
        (Functor.whiskerLeft (Over.forget U₀).op
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)))
        ((conormalSheaf X J).over U₀) σ.s).app
        (op (Over.mk (homOfLE hVU₀))) (ModuleCat.freeMk i) := by
  rw [conormalUnit_conormalClass_eq_section X J U₀ σ i hVU₀ z hz]
  exact (freePresheafMap_freeMk _ ((conormalSheaf X J).over U₀) σ.s
    (op (Over.mk (homOfLE hVU₀))) i).symm

/-- Linear independence of the conormal classes of the germs of `f` at `y`, transported
to the stalk of the restricted space, where the quasi-regularity map lives. -/
private lemma conormal_independent_germSequence (X : RingedSpace.{u}) (U : Opens X)
    (y : X) (hy : y ∈ U) {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hind : ∀ a : Fin r → X.presheaf.stalk y,
      (∑ k, a k * X.presheaf.germ U y hy (f k)) ∈
        Jid (fun k => X.presheaf.germ U y hy (f k)) ^ 2 →
      ∀ k, a k ∈ Jid (fun k => X.presheaf.germ U y hy (f k))) :
    ∀ a : Fin r → (X.restrict U.isOpenEmbedding).presheaf.stalk ⟨y, hy⟩,
      (∑ k, a k * QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun i => sectionOnRestriction X U (f i)) ⟨y, hy⟩ k) ∈
        Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
          (fun i => sectionOnRestriction X U (f i)) ⟨y, hy⟩) ^ 2 →
      ∀ k, a k ∈ Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun i => sectionOnRestriction X U (f i)) ⟨y, hy⟩) :=
  conormal_independent_of_ringHom
    (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hy⟩).inv.hom
    (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hy⟩).hom.hom
    (fun z => (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding
      ⟨y, hy⟩).inv_hom_id_apply z)
    (fun z => (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding
      ⟨y, hy⟩).hom_inv_id_apply z)
    (fun k => X.presheaf.germ U y hy (f k))
    (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
      (fun i => sectionOnRestriction X U (f i)) ⟨y, hy⟩)
    (fun k => germInRestriction_self X U y hy (f k)) hind

/-- Finitely many germs at a point are simultaneously represented by sections on one small
open, for an arbitrary finite index type. -/
private lemma exists_sections_of_finite_germs_index (X : RingedSpace.{u}) (x : X)
    (U : Opens X) (hx : x ∈ U) {ι : Type*} [Finite ι] (a : ι → X.presheaf.stalk x) :
    ∃ (V : Opens X) (_ : V ≤ U) (hxV : x ∈ V) (b : ι → X.presheaf.obj (op V)),
      ∀ i, X.presheaf.germ V x hxV (b i) = a i := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    exists_sections_of_finite_germs X x U hx (fun k => a (e.symm k))
  refine ⟨V, hVU, hxV, fun i => b (e i), fun i => ?_⟩
  rw [hb (e i), Equiv.symm_apply_apply]

/-- The basis sections of a free module are independent: a vanishing combination over an
injectively indexed family has vanishing coefficients. -/
private lemma free_coeff_eq_zero_of_sum_eq_zero {Λ : Type u} [Ring Λ] {ι : Type u} {r : ℕ}
    (ι₀ : Fin r → ι) (hinj : Function.Injective ι₀) (c : Fin r → Λ)
    (h : (∑ k, c k • (ModuleCat.freeMk (R := Λ) (ι₀ k))) = 0) (j : Fin r) : c j = 0 := by
  classical
  let π : (ModuleCat.free Λ).obj ι ⟶ ModuleCat.of Λ Λ :=
    ModuleCat.freeDesc (↾fun i => if i = ι₀ j then (1 : Λ) else 0)
  have hπ : ∀ i : ι, (ConcreteCategory.hom π) (ModuleCat.freeMk i) =
      if i = ι₀ j then (1 : Λ) else 0 := fun i => ModuleCat.freeDesc_apply _ _
  have hz : (ConcreteCategory.hom π)
      (∑ k, c k • (ModuleCat.freeMk (R := Λ) (ι₀ k))) = 0 := by
    rw [h, map_zero]
  have h2 : ∑ k, (ConcreteCategory.hom π) (c k • (ModuleCat.freeMk (R := Λ) (ι₀ k))) = 0 :=
    (map_sum (ConcreteCategory.hom π) _ Finset.univ).symm.trans hz
  have h3 : ∀ k : Fin r, (ConcreteCategory.hom π) (c k • (ModuleCat.freeMk (R := Λ) (ι₀ k))) =
      if ι₀ k = ι₀ j then c k else 0 := by
    intro k
    refine (map_smul (ConcreteCategory.hom π) (c k) _).trans ?_
    rw [hπ, smul_ite_zero, smul_eq_mul, mul_one]
  have h4 : ∑ k, (if ι₀ k = ι₀ j then c k else 0) = 0 :=
    (Finset.sum_congr rfl (fun k _ => (h3 k).symm)).trans h2
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)] at h4
  · simpa using h4
  · intro k _ hk
    exact ite_eq_right_iff.mpr (fun he => absurd (hinj he) hk)

/-- Over a finite index type, every section of a free presheaf of modules on a constant
family is a combination of the basis sections. -/
private lemma exists_free_coeff {C : Type v} [Category.{v} C] {R₀ : Cᵒᵖ ⥤ RingCat.{u}}
    {ι : Type u} {Y : Cᵒᵖ} {r : ℕ} (e : Fin r ≃ ι)
    (t : (PresheafOfModules.freeObj (R := R₀) ((Functor.const Cᵒᵖ).obj ι)).obj Y) :
    ∃ c : Fin r → R₀.obj Y, (∑ k, c k • ModuleCat.freeMk (e k)) = t := by
  classical
  let _ : Fintype ι := Fintype.ofEquiv (Fin r) e
  obtain ⟨tf, htf⟩ : ∃ tf : ι →₀ R₀.obj Y, t = tf := ⟨t, rfl⟩
  refine ⟨fun k => tf (e k), ?_⟩
  have h1 : tf = ∑ i : ι, Finsupp.single i (tf i) :=
    ((Finsupp.sum_fintype tf (fun i c => Finsupp.single i c)
      (fun i => Finsupp.single_zero i)).symm.trans (Finsupp.sum_single tf)).symm
  have h2 : (∑ i : ι, Finsupp.single i (tf i)) = ∑ k : Fin r, Finsupp.single (e k) (tf (e k)) :=
    (Equiv.sum_comp e (fun i => Finsupp.single i (tf i))).symm
  refine Eq.trans ?_ (htf.trans (h1.trans h2)).symm
  exact Finset.sum_congr rfl (fun k _ => Finsupp.smul_single_one (e k) (tf (e k)))

/-- Restriction in a free presheaf of modules on a constant family moves only the
coefficients of a combination of the basis sections. -/
private lemma freeObj_const_map_sum {C : Type v} [Category.{v} C] {R₀ : Cᵒᵖ ⥤ RingCat.{u}}
    {ι : Type u} {Y Z : Cᵒᵖ} (g : Y ⟶ Z) {r : ℕ} (ι₀ : Fin r → ι) (c : Fin r → R₀.obj Y)
    (t : (PresheafOfModules.freeObj (R := R₀) ((Functor.const Cᵒᵖ).obj ι)).obj Y)
    (ht : (∑ k, c k • ModuleCat.freeMk (ι₀ k)) = t) :
    (∑ k, R₀.map g (c k) • ModuleCat.freeMk (ι₀ k)) =
      (PresheafOfModules.freeObj (R := R₀) ((Functor.const Cᵒᵖ).obj ι)).map g t := by
  have hgen : ∀ i : ι, (PresheafOfModules.freeObj (R := R₀)
      ((Functor.const Cᵒᵖ).obj ι)).map g (ModuleCat.freeMk i) = ModuleCat.freeMk i :=
    fun i => ModuleCat.freeDesc_apply _ _
  subst ht
  refine Eq.trans ?_ (map_sum (ConcreteCategory.hom ((PresheafOfModules.freeObj (R := R₀)
    ((Functor.const Cᵒᵖ).obj ι)).map g)) (fun k => c k • ModuleCat.freeMk (ι₀ k))
      Finset.univ).symm
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Eq.trans ?_ ((PresheafOfModules.freeObj (R := R₀)
    ((Functor.const Cᵒᵖ).obj ι)).map_smul g (c k) (ModuleCat.freeMk (ι₀ k))).symm
  exact congrArg (fun z => R₀.map g (c k) • z) (hgen (ι₀ k)).symm

/-- A combination of the basis sections of a free presheaf of modules on a constant family
that dies after restriction has coefficients that die after restriction. -/
private lemma freeObj_const_coeff_eq_zero {C : Type v} [Category.{v} C]
    {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {ι : Type u} {Y Z : Cᵒᵖ} (g : Y ⟶ Z) {r : ℕ} (ι₀ : Fin r → ι)
    (hinj : Function.Injective ι₀) (c : Fin r → R₀.obj Y)
    (t : (PresheafOfModules.freeObj (R := R₀) ((Functor.const Cᵒᵖ).obj ι)).obj Y)
    (ht : (∑ k, c k • ModuleCat.freeMk (ι₀ k)) = t)
    (h : (PresheafOfModules.freeObj (R := R₀) ((Functor.const Cᵒᵖ).obj ι)).map g t = 0)
    (k : Fin r) : R₀.map g (c k) = 0 :=
  free_coeff_eq_zero_of_sum_eq_zero ι₀ hinj _
    ((freeObj_const_map_sum g ι₀ c t ht).trans h) k

/-- **The conormal class of a combination.** Reducing the coefficients modulo the ideal of
sections turns a combination of sections of `J` into the matching combination of conormal
classes. -/
private lemma conormalClass_combination (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {W : Opens X} {r : ℕ}
    (b : Fin r → X.presheaf.obj (op W)) (c : Fin r → sectionIdeal X J (op W))
    (z : sectionIdeal X J (op W))
    (hzval : z.val = ∑ k, b k * (c k).val) :
    ∑ k, Ideal.Quotient.mk (sectionIdeal X J (op W)) (b k) •
        conormalClass (sectionIdeal X J (op W)) (c k) =
      conormalClass (sectionIdeal X J (op W)) z := by
  have hsum : (∑ k, b k • c k) = z := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hzval.symm
  rw [← hsum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

/-- The free presheaf of modules on the index type of a family of generating sections of the
conormal sheaf over `U₀`, named so that every statement about it is written one way. -/
private noncomputable abbrev conormalFreeSource (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X) (I : Type u) :
    PresheafOfModules.{u} ((Over.forget U₀).op ⋙ quotientPresheaf X J) :=
  PresheafOfModules.freeObj ((Functor.const (Over U₀)ᵒᵖ).obj I)

/-- The presheaf-level free map attached to a family of generating sections of the conormal
sheaf over `U₀`, named so that every statement about it is written in one spelling. -/
private noncomputable abbrev conormalFreeMap (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) :=
  freePresheafMap
    (Functor.whiskerLeft (Over.forget U₀).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)))
    ((conormalSheaf X J).over U₀) σ.s

/-- **The combination identity.** The free presheaf map carries a coordinate vector to the
image under the comparison of the conormal class of the matching combination of the lifted
sections. Both halves of the free-sheaf inversion are read through this identity. -/
private lemma conormalFreeMap_app_eq (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) {r : ℕ} (e : Fin r → σ.I)
    {V W : Opens X} (hVU₀ : V ≤ U₀) (hWV : W ≤ V) (hWU₀ : W ≤ U₀) (f : Fin r → J.obj (op V))
    (hz : ∀ k, (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) (f k)) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s (e k)).val (op (Over.mk (𝟙 U₀)))))
    (b : Fin r → X.presheaf.obj (op W))
    (q : Fin r → ((Over.forget U₀).op ⋙ quotientPresheaf X J).obj
      (op (Over.mk (homOfLE hWU₀) : Over U₀)))
    (hq : ∀ k, q k = Ideal.Quotient.mk (sectionIdeal X J (op W)) (b k))
    (z : sectionIdeal X J (op W))
    (hzval : z.val = ∑ k, b k * X.presheaf.map (homOfLE hWV).op (f k).val)
    (t : (conormalFreeSource X J U₀ σ.I).obj (op (Over.mk (homOfLE hWU₀) : Over U₀)))
    (ht : (∑ k, q k • ModuleCat.freeMk (e k)) = t) :
    (conormalFreeMap X J U₀ σ).app (op (Over.mk (homOfLE hWU₀))) t =
      (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
        (conormalClass (sectionIdeal X J (op W)) z) := by
  have hbg : ∀ k, (conormalFreeMap X J U₀ σ).app (op (Over.mk (homOfLE hWU₀)))
        (ModuleCat.freeMk (e k)) =
      (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
        (conormalClass (sectionIdeal X J (op W))
          ⟨X.presheaf.map (homOfLE hWV).op (f k).val,
            J.toSubmodule.map_mem (homOfLE hWV).op (f k).property⟩) :=
    fun k => (freePresheafMap_freeMk _ _ σ.s _ (e k)).trans
      (conormalUnit_conormalClass_eq_section X J U₀ σ (e k) hWU₀ _
        (conormal_lift_restrict X J U₀ σ (e k) hVU₀ hWV hWU₀ (f k) (hz k))).symm
  refine (congrArg (fun w => (conormalFreeMap X J U₀ σ).app (op (Over.mk (homOfLE hWU₀))) w)
    ht.symm).trans ?_
  refine (map_sum (ConcreteCategory.hom ((conormalFreeMap X J U₀ σ).app
    (op (Over.mk (homOfLE hWU₀))))) _ Finset.univ).trans ?_
  refine Eq.trans (Finset.sum_congr rfl (fun k _ =>
    (map_smul (ConcreteCategory.hom ((conormalFreeMap X J U₀ σ).app
      (op (Over.mk (homOfLE hWU₀))))) (q k) (ModuleCat.freeMk (e k))).trans
      (congrArg (fun w => q k • w) (hbg k)))) ?_
  refine Eq.trans (Finset.sum_congr rfl (fun k _ =>
    (map_smul (ConcreteCategory.hom ((conormalSheafificationUnitOver X J U₀).app
      (op (Over.mk (homOfLE hWU₀))))) (q k) _).symm)) ?_
  refine (map_sum (ConcreteCategory.hom ((conormalSheafificationUnitOver X J U₀).app
    (op (Over.mk (homOfLE hWU₀))))) _ Finset.univ).symm.trans ?_
  refine congrArg (fun w => (conormalSheafificationUnitOver X J U₀).app
    (op (Over.mk (homOfLE hWU₀))) w) ?_
  simp only [hq]
  exact conormalClass_combination X J b (fun k => ⟨X.presheaf.map (homOfLE hWV).op (f k).val,
    J.toSubmodule.map_mem (homOfLE hWV).op (f k).property⟩) z hzval

/-- Restriction along a composite of inclusions, read on sections. -/
private lemma map_map_apply (X : RingedSpace.{u}) {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : X.presheaf.obj (op U)) :
    X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op s) =
      X.presheaf.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- A coefficient whose class in the quotient presheaf dies after restriction is a section of
`J` after restriction. -/
private lemma mem_of_quotientPresheaf_map_mk_eq_zero (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : X.presheaf.obj U)
    (h : (quotientPresheaf X J).map i
        (Submodule.Quotient.mk s : X.presheaf.obj U ⧸ sectionIdeal X J U) = 0) :
    X.presheaf.map i s ∈ J.obj V := by
  have h' : (Submodule.Quotient.mk (p := J.obj V) (X.presheaf.map i s)) = 0 := h
  exact (Submodule.Quotient.mk_eq_zero (J.obj V)).mp h'

/-- Two sections of `J` with the same conormal class differ by an element of the square of the
ideal of sections. -/
private lemma sub_mem_sq_of_conormalClass_eq (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {W : Opens X}
    (a b : X.presheaf.obj (op W)) (ha : a ∈ sectionIdeal X J (op W))
    (hb : b ∈ sectionIdeal X J (op W))
    (h : conormalClass (sectionIdeal X J (op W)) ⟨a, ha⟩ =
      conormalClass (sectionIdeal X J (op W)) ⟨b, hb⟩) :
    a - b ∈ sectionIdeal X J (op W) ^ 2 := by
  have h0 : conormalClass (sectionIdeal X J (op W))
      ((⟨a, ha⟩ : sectionIdeal X J (op W)) - ⟨b, hb⟩) = 0 := by
    rw [map_sub, h, sub_self]
  exact (conormalClass_eq_zero_iff _ _).mp h0

/-- A combination of restrictions of sections of `J` is a section of `J` on the smaller open. -/
private lemma sum_mul_map_mem_sectionIdeal (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {V W : Opens X} (hWV : W ≤ V)
    {r : ℕ} (b : Fin r → X.presheaf.obj (op W)) (f : Fin r → X.presheaf.obj (op V))
    (hf : ∀ k, f k ∈ J.obj (op V)) :
    (∑ k, b k * X.presheaf.map (homOfLE hWV).op (f k)) ∈ sectionIdeal X J (op W) :=
  Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ (J.toSubmodule.map_mem _ (hf k)))

/-- The quotient-ring comparison is locally injective on the over-site of `U₀`. -/
private lemma conormalOverRing_locallyInjective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X) :
    Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U₀)
      (Functor.whiskerLeft (Over.forget U₀).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J))) := by
  have := (quotientSheaf_unit_locallyBijective X J).1
  exact Presheaf.isLocallyInjective_whisker ((Opens.grothendieckTopology X).over U₀)
    (Opens.grothendieckTopology X) (Over.forget U₀) _

/-- The quotient-ring comparison is locally surjective on the over-site of `U₀`. -/
private lemma conormalOverRing_locallySurjective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U₀)
      (Functor.whiskerLeft (Over.forget U₀).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J))) := by
  have := (quotientSheaf_unit_locallyBijective X J).2
  exact Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X).over U₀)
    (Opens.grothendieckTopology X) (Over.forget U₀) _

/-- **Local bijectivity of the free presheaf map of a conormal basis.** This is
`freePresheafMap_locallyBijective_of_isIso` read at the over-site of `U₀`. -/
private lemma conormalFreeMap_locallyBijective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections)
    (hiso : IsIso (((conormalSheaf X J).over U₀).freeHomEquiv.symm σ.s)) :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U₀)
        (conormalFreeMap X J U₀ σ) ∧
      PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U₀)
        (conormalFreeMap X J U₀ σ) :=
  freePresheafMap_locallyBijective_of_isIso _
    (conormalOverRing_locallyInjective X J U₀) (conormalOverRing_locallySurjective X J U₀)
    _ σ.s hiso

/-- **Reading independence off local injectivity of the free presheaf map.** If a
combination of the lifted sections lies in the square of the ideal of sections, then its
coefficients lie in that ideal after restriction to a neighbourhood of any point. -/
private lemma exists_local_coeffs_mem (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) {r : ℕ} (e : Fin r ≃ σ.I)
    (hβ : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U₀)
      (conormalFreeMap X J U₀ σ))
    {V W : Opens X} (hVU₀ : V ≤ U₀) (hWV : W ≤ V) (hWU₀ : W ≤ U₀) (f : Fin r → J.obj (op V))
    (hz : ∀ k, (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) (f k)) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s (e k)).val (op (Over.mk (𝟙 U₀)))))
    (b : Fin r → X.presheaf.obj (op W))
    (hb : (∑ k, b k * X.presheaf.map (homOfLE hWV).op (f k).val) ∈
      sectionIdeal X J (op W) ^ 2)
    (y : X) (hy : y ∈ W) :
    ∃ (W' : Opens X) (_ : y ∈ W') (hW'W : W' ≤ W),
      ∀ k, X.presheaf.map (homOfLE hW'W).op (b k) ∈ J.obj (op W') := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : Fin r → ((Over.forget U₀).op ⋙ quotientPresheaf X J).obj
      (op (Over.mk (homOfLE hWU₀) : Over U₀)),
      ∀ k, q k = Ideal.Quotient.mk (sectionIdeal X J (op W)) (b k) :=
    ⟨fun k => Ideal.Quotient.mk (sectionIdeal X J (op W)) (b k), fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : (conormalFreeSource X J U₀ σ.I).obj
      (op (Over.mk (homOfLE hWU₀) : Over U₀)), (∑ k, q k • ModuleCat.freeMk (e k)) = t :=
    ⟨_, rfl⟩
  have hmem : (∑ k, b k * X.presheaf.map (homOfLE hWV).op (f k).val) ∈
      sectionIdeal X J (op W) :=
    sum_mul_map_mem_sectionIdeal X J hWV b (fun k => (f k).val) (fun k => (f k).property)
  have hkey := conormalFreeMap_app_eq X J U₀ σ (fun k => e k) hVU₀ hWV hWU₀ f hz b q hq
    ⟨_, hmem⟩ rfl t ht
  have hzero : conormalClass (sectionIdeal X J (op W))
      (⟨_, hmem⟩ : sectionIdeal X J (op W)) = 0 :=
    (conormalClass_eq_zero_iff (sectionIdeal X J (op W)) ⟨_, hmem⟩).mpr hb
  have heq : (conormalFreeMap X J U₀ σ).app (op (Over.mk (homOfLE hWU₀))) t =
      (conormalFreeMap X J U₀ σ).app (op (Over.mk (homOfLE hWU₀))) 0 :=
    hkey.trans ((congrArg (fun w => (conormalSheafificationUnitOver X J U₀).app
        (op (Over.mk (homOfLE hWU₀))) w) hzero).trans
      ((map_zero (ConcreteCategory.hom ((conormalSheafificationUnitOver X J U₀).app
            (op (Over.mk (homOfLE hWU₀)))))).trans
        (map_zero (ConcreteCategory.hom ((conormalFreeMap X J U₀ σ).app
          (op (Over.mk (homOfLE hWU₀)))))).symm))
  obtain ⟨W', hyW', i, hi⟩ := exists_local_eq_of_locallyInjective_over U₀
    (conormalFreeMap X J U₀ σ) hβ (Over.mk (homOfLE hWU₀)) t 0 heq y hy
  refine ⟨W', hyW', leOfHom i, fun k => ?_⟩
  have hc := freeObj_const_coeff_eq_zero _ (fun k => e k) e.injective q t ht
    (hi.trans (map_zero _)) k
  rw [hq k] at hc
  exact mem_of_quotientPresheaf_map_mk_eq_zero X J (homOfLE (leOfHom i)).op (b k) hc

/-- **Reading local generation off local surjectivity of the free presheaf map.** Near any
point of the witness open, a section of `J` agrees, modulo the square of the ideal of
sections, with a combination of the lifted sections. -/
private lemma exists_local_conormal_combination (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) {r : ℕ} (e : Fin r ≃ σ.I)
    (hβ : PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U₀)
      (conormalFreeMap X J U₀ σ))
    (hγ : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U₀)
      (conormalSheafificationUnitOver X J U₀))
    {V W : Opens X} (hVU₀ : V ≤ U₀) (hWV : W ≤ V) (hWU₀ : W ≤ U₀) (f : Fin r → J.obj (op V))
    (hz : ∀ k, (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) (f k)) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s (e k)).val (op (Over.mk (𝟙 U₀)))))
    (s : sectionIdeal X J (op W)) (y : X) (hy : y ∈ W) :
    ∃ (W' : Opens X) (_ : y ∈ W') (hW'W : W' ≤ W) (b : Fin r → X.presheaf.obj (op W')),
      X.presheaf.map (homOfLE hW'W).op s.val -
          ∑ k, b k * X.presheaf.map (homOfLE (hW'W.trans hWV)).op (f k).val ∈
        sectionIdeal X J (op W') ^ 2 := by
  classical
  obtain ⟨W₁, hyW₁, i, t, ht⟩ := exists_local_preimage_over U₀ (conormalFreeMap X J U₀ σ) hβ
    (Over.mk (homOfLE hWU₀))
    ((conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
      (conormalClass (sectionIdeal X J (op W)) s)) y hy
  have hW₁W : W₁ ≤ W := leOfHom i
  have hW₁U₀ : W₁ ≤ U₀ := hW₁W.trans hWU₀
  have hW₁V : W₁ ≤ V := hW₁W.trans hWV
  obtain ⟨q, hqt⟩ := exists_free_coeff e t
  obtain ⟨b, hq⟩ : ∃ b : Fin r → X.presheaf.obj (op W₁),
      ∀ k, q k = Ideal.Quotient.mk (sectionIdeal X J (op W₁)) (b k) := by
    choose b hb using fun k => Ideal.Quotient.mk_surjective (q k)
    exact ⟨b, fun k => (hb k).symm⟩
  have hmem : (∑ k, b k * X.presheaf.map (homOfLE hW₁V).op (f k).val) ∈
      sectionIdeal X J (op W₁) :=
    sum_mul_map_mem_sectionIdeal X J hW₁V b (fun k => (f k).val) (fun k => (f k).property)
  have hkey := conormalFreeMap_app_eq X J U₀ σ (fun k => e k) hVU₀ hW₁V hW₁U₀ f hz b q hq
    ⟨_, hmem⟩ rfl t hqt
  have hnat : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hW₁U₀)))
        (((PresheafOfModules.pushforward₀ (Over.forget U₀) (quotientPresheaf X J)).obj
            (gradedPresheaf X J 1)).map
          (Over.homMk (homOfLE hW₁W) :
            (Over.mk (homOfLE hW₁U₀) : Over U₀) ⟶ Over.mk (homOfLE hWU₀)).op
          (conormalClass (sectionIdeal X J (op W)) s)) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hW₁W) :
          (Over.mk (homOfLE hW₁U₀) : Over U₀) ⟶ Over.mk (homOfLE hWU₀)).op
        ((conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
          (conormalClass (sectionIdeal X J (op W)) s)) :=
    PresheafOfModules.naturality_apply _ _ _
  have hfin : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hW₁U₀)))
        (conormalClass (sectionIdeal X J (op W₁)) ⟨_, hmem⟩) =
      (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hW₁U₀)))
        (conormalClass (sectionIdeal X J (op W₁))
          ⟨X.presheaf.map (homOfLE hW₁W).op s.val,
            J.toSubmodule.map_mem (homOfLE hW₁W).op s.property⟩) :=
    hkey.symm.trans (ht.trans hnat.symm)
  obtain ⟨W₂, hyW₂, i₂, hi₂⟩ := exists_local_eq_of_locallyInjective_over U₀
    (conormalSheafificationUnitOver X J U₀) hγ (Over.mk (homOfLE hW₁U₀)) _ _ hfin y hyW₁
  have hW₂W₁ : W₂ ≤ W₁ := leOfHom i₂
  have hcc : conormalClass (sectionIdeal X J (op W₂))
        ⟨X.presheaf.map (homOfLE hW₂W₁).op
            (∑ k, b k * X.presheaf.map (homOfLE hW₁V).op (f k).val),
          J.toSubmodule.map_mem (homOfLE hW₂W₁).op hmem⟩ =
      conormalClass (sectionIdeal X J (op W₂))
        ⟨X.presheaf.map (homOfLE hW₂W₁).op (X.presheaf.map (homOfLE hW₁W).op s.val),
          J.toSubmodule.map_mem (homOfLE hW₂W₁).op
            (J.toSubmodule.map_mem (homOfLE hW₁W).op s.property)⟩ := hi₂
  refine ⟨W₂, hyW₂, hW₂W₁.trans hW₁W, fun k => X.presheaf.map (homOfLE hW₂W₁).op (b k), ?_⟩
  have h1 := sub_mem_sq_of_conormalClass_eq X J
    (X.presheaf.map (homOfLE hW₂W₁).op (X.presheaf.map (homOfLE hW₁W).op s.val))
    (X.presheaf.map (homOfLE hW₂W₁).op
      (∑ k, b k * X.presheaf.map (homOfLE hW₁V).op (f k).val))
    (J.toSubmodule.map_mem (homOfLE hW₂W₁).op
      (J.toSubmodule.map_mem (homOfLE hW₁W).op s.property))
    (J.toSubmodule.map_mem (homOfLE hW₂W₁).op hmem) hcc.symm
  simpa only [map_sum, map_mul, map_map_apply X hW₁W hW₂W₁,
    map_map_apply X hW₁V hW₂W₁ (f _).val] using h1

/-- **From a germ-level congruence to a section-level one.** If a combination of the germs of
sections of `J` lies in the square of the stalk ideal they generate, then the matching
combination of sections lies in the square of the ideal of sections on a neighbourhood. -/
private lemma exists_local_sum_mem_sq (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (hf : ∀ k, f k ∈ J.obj (op U))
    (y : X) (hy : y ∈ U) (a : Fin r → X.presheaf.stalk y)
    (ha : (∑ k, a k * X.presheaf.germ U y hy (f k)) ∈
      Jid (fun k => X.presheaf.germ U y hy (f k)) ^ 2) :
    ∃ (W : Opens X) (hyW : y ∈ W) (hWU : W ≤ U) (b : Fin r → X.presheaf.obj (op W)),
      (∀ k, X.presheaf.germ W y hyW (b k) = a k) ∧
      (∑ k, b k * X.presheaf.map (homOfLE hWU).op (f k)) ∈ sectionIdeal X J (op W) ^ 2 := by
  classical
  obtain ⟨W₁, hW₁U, hyW₁, bb, hbb⟩ := exists_sections_of_finite_germs X y U hy a
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (pow_jid_le_span_monomials (fun k => X.presheaf.germ U y hy (f k)) 2 ha)
  obtain ⟨W₂, hW₂W₁, hyW₂, dd, hdd⟩ := exists_sections_of_finite_germs_index X y W₁ hyW₁ c
  have hW₂U : W₂ ≤ U := hW₂W₁.trans hW₁U
  have hL : X.presheaf.germ W₂ y hyW₂
        (∑ k, X.presheaf.map (homOfLE hW₂W₁).op (bb k) *
          X.presheaf.map (homOfLE hW₂U).op (f k)) =
      ∑ k, a k * X.presheaf.germ U y hy (f k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hbb k]
  have hR : X.presheaf.germ W₂ y hyW₂
        (∑ t : Fin 2 → Fin r, dd t * ∏ j, X.presheaf.map (homOfLE hW₂U).op (f (t j))) =
      ∑ t : Fin 2 → Fin r, c t * ∏ j, X.presheaf.germ U y hy (f (t j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_mul, map_prod, hdd t]
    refine congrArg _ (Finset.prod_congr rfl (fun j _ => ?_))
    rw [TopCat.Presheaf.germ_res_apply]
  obtain ⟨W₃, hyW₃, j₁, j₂, hj⟩ := X.presheaf.germ_eq y hyW₂ hyW₂ _ _
    (hL.trans (hc.symm.trans hR.symm))
  have hW₃W₂ : W₃ ≤ W₂ := leOfHom j₁
  rw [Subsingleton.elim j₂ j₁] at hj
  refine ⟨W₃, hyW₃, hW₃W₂.trans hW₂U,
    fun k => X.presheaf.map (homOfLE (hW₃W₂.trans hW₂W₁)).op (bb k), fun k => ?_, ?_⟩
  · rw [TopCat.Presheaf.germ_res_apply]
    exact hbb k
  · have hsum : (∑ k, X.presheaf.map (homOfLE (hW₃W₂.trans hW₂W₁)).op (bb k) *
        X.presheaf.map (homOfLE (hW₃W₂.trans hW₂U)).op (f k)) =
        X.presheaf.map (homOfLE hW₃W₂).op
          (∑ k, X.presheaf.map (homOfLE hW₂W₁).op (bb k) *
            X.presheaf.map (homOfLE hW₂U).op (f k)) := by
      simp only [map_sum, map_mul, map_map_apply X hW₂W₁ hW₃W₂ (bb _),
        map_map_apply X hW₂U hW₃W₂ (f _)]
    have hsq : X.presheaf.map (homOfLE hW₃W₂).op
        (∑ t : Fin 2 → Fin r, dd t * ∏ j, X.presheaf.map (homOfLE hW₂U).op (f (t j))) ∈
        sectionIdeal X J (op W₃) ^ 2 := by
      rw [map_sum]
      refine Ideal.sum_mem _ (fun t _ => ?_)
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [map_prod, Fin.prod_univ_two, pow_two]
      have hmem : ∀ k, X.presheaf.map (homOfLE hW₃W₂).op (X.presheaf.map (homOfLE hW₂U).op (f k)) ∈
          sectionIdeal X J (op W₃) := fun k => by
        rw [map_map_apply X hW₂U hW₃W₂]
        exact J.toSubmodule.map_mem _ (hf k)
      exact Ideal.mul_mem_mul (hmem _) (hmem _)
    rw [hsum]
    exact hj ▸ hsq

/-- **The last input for Tag 063H.** From finiteness of type and finite local freeness of the
conormal sheaf, local generators of `J` at `x` whose conormal classes are independent at
every point of the witness open.

Finiteness of type supplies some local generators `g`; local freeness of the conormal sheaf
supplies, on an open `U₀` around `x`, a basis of the conormal sheaf, which
`freePresheafMap_locallyBijective_of_isIso` turns into a locally bijective map of presheaves
of modules on `(Opens X).over U₀`. Local surjectivity of `conormalSheafificationUnitOver`
replaces that basis by the conormal classes of honest sections `f` of `J`
(`exists_local_conormal_lift`), and the two halves of local bijectivity then say exactly that
the conormal classes of the `f` generate (`exists_local_conormal_combination`) and are
independent (`exists_local_coeffs_mem`). Nakayama in the form
`span_range_val_eq_of_cotangent_span` upgrades generation of the conormal module at `x` to
generation of the stalk ideal, and `exists_isGeneratedByOn_of_germ_span` spreads that out to
a neighbourhood. -/
@[sga "6 VII 1.4" "1.4.3"]
private lemma exists_local_generators_with_independent_conormal (X : LocallyRingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X.toRingedSpace).Submodule)
    (hfinite : J.toSheafOfModules.IsFiniteType)
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (conormalSheaf X.toRingedSpace J))
    (x : X) (_hx : x ∈ idealQuotientSupport X.toRingedSpace J) :
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
      IsGeneratedByOn X.toRingedSpace J U f ∧
      ∀ (y : X) (hy : y ∈ U) (a : Fin r → X.presheaf.stalk y),
        (∑ k, a k * X.presheaf.germ U y hy (f k)) ∈
          Jid (fun k => X.presheaf.germ U y hy (f k)) ^ 2 →
        ∀ k, a k ∈ Jid (fun k => X.presheaf.germ U y hy (f k)) := by
  classical
  obtain ⟨U₁, hxU₁, m, g, hgen₁⟩ := exists_isGeneratedByOn_of_isFiniteType J hfinite x
  by_cases hone : (1 : X.presheaf.stalk x) ∈ Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j))
  · -- `J` is the unit ideal near `x`: one generator, and independence is vacuous
    obtain ⟨W, hxW, i, hW⟩ := exists_local_mem_of_germ_mem_span X.toRingedSpace J U₁ U₁ g
      (mem_of_isGeneratedByOn X.toRingedSpace J U₁ g hgen₁) (1 : X.presheaf.obj (op U₁))
      x hxU₁ hxU₁ (by simpa only [map_one] using hone)
    rw [map_one] at hW
    refine ⟨W, hxW, 1, fun _ => (1 : X.presheaf.obj (op W)),
      isGeneratedByOn_one X.toRingedSpace J W hW, ?_⟩
    intro y hy a _ k
    have htop : Jid (fun _ : Fin 1 =>
        X.presheaf.germ W y hy (1 : X.presheaf.obj (op W))) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have h1 : X.presheaf.germ W y hy (1 : X.presheaf.obj (op W)) = 1 := map_one _
      exact h1 ▸ Ideal.subset_span (Set.mem_range_self (0 : Fin 1))
    rw [htop]
    exact Submodule.mem_top
  · -- the main case: a conormal basis near `x`, lifted to sections of `J`
    obtain ⟨qd, hqfree, hqfin⟩ := hfree.exists_isFiniteLocallyFreeData
    have hcov : (⨆ i, qd.X i) = (⊤ : Opens X) := (Opens.coversTop_iff X qd.X).1 qd.coversTop
    obtain ⟨i₀, hxU₀⟩ := (Opens.mem_iSup).mp (hcov ▸ (by trivial : x ∈ (⊤ : Opens X)))
    have hfinI : Finite (qd.generators i₀).I := (hqfin.isFiniteType i₀).finite
    obtain ⟨r, ⟨e₀⟩⟩ := Finite.exists_equiv_fin (qd.generators i₀).I
    -- local bijectivity of the free presheaf map attached to the conormal basis
    have hβ := conormalFreeMap_locallyBijective X.toRingedSpace J (qd.X i₀) (qd.generators i₀)
      (hqfree.isIso i₀)
    have hγ := conormalSheafificationUnitOver_locallyBijective X.toRingedSpace J (qd.X i₀)
    -- the conormal basis, lifted to sections of `J` on a common open with `U₁`
    obtain ⟨V₀, hxV₀, hV₀U₀, f₀, hz₀⟩ := exists_local_conormal_lift X.toRingedSpace J (qd.X i₀)
      (qd.generators i₀) e₀.symm x hxU₀
    obtain ⟨V, hxV, hVU₀, hVU₁, f, hz⟩ :
        ∃ (V : Opens X) (_ : x ∈ V) (hVU₀ : V ≤ qd.X i₀) (_ : V ≤ U₁)
          (f : Fin r → J.obj (op V)),
          ∀ k, (conormalSheafificationUnitOver X.toRingedSpace J (qd.X i₀)).app
                (op (Over.mk (homOfLE hVU₀)))
              (conormalClass (sectionIdeal X.toRingedSpace J (op V)) (f k)) =
            (conormalOverTarget X.toRingedSpace J (qd.X i₀)).map
              (Over.homMk (homOfLE hVU₀) :
                (Over.mk (homOfLE hVU₀) : Over (qd.X i₀)) ⟶ Over.mk (𝟙 (qd.X i₀))).op
              (((qd.generators i₀).s (e₀.symm k)).val (op (Over.mk (𝟙 (qd.X i₀))))) := by
      refine ⟨V₀ ⊓ U₁, ⟨hxV₀, hxU₁⟩, (inf_le_left : V₀ ⊓ U₁ ≤ V₀).trans hV₀U₀, inf_le_right,
        fun k => ⟨X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ U₁ ≤ V₀)).op (f₀ k).val,
          J.toSubmodule.map_mem _ (f₀ k).property⟩, fun k => ?_⟩
      exact conormal_lift_restrict X.toRingedSpace J (qd.X i₀) (qd.generators i₀) (e₀.symm k) hV₀U₀
        inf_le_left ((inf_le_left : V₀ ⊓ U₁ ≤ V₀).trans hV₀U₀) (f₀ k) (hz₀ k)
    -- modulo the square, every germ of `J` at `x` is a combination of the lifted sections
    have hstalk : Stacks.RingedSpace.stalkIdeal J x =
        Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j)) :=
      stalkIdeal_eq_jid_of_isGeneratedByOn J g hgen₁ x hxU₁
    have hmod : ∀ w : Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j)),
        ∃ c : Fin r → X.presheaf.stalk x,
          (w : X.presheaf.stalk x) - ∑ k, c k * X.presheaf.germ V x hxV (f k).val ∈
            Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j)) ^ 2 := by
      intro w
      -- write `w` as the germ of a section of `J`, then use local surjectivity
      obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.mp w.property
      obtain ⟨W₀, hW₀V, hxW₀, bb, hbb⟩ := exists_sections_of_finite_germs X.toRingedSpace x V hxV d
      have hW₀U₁ : W₀ ≤ U₁ := hW₀V.trans hVU₁
      have hs₀ : (∑ j, bb j * X.presheaf.map (homOfLE hW₀U₁).op (g j)) ∈
          sectionIdeal X.toRingedSpace J (op W₀) :=
        sum_mul_map_mem_sectionIdeal X.toRingedSpace J hW₀U₁ bb g
          (mem_of_isGeneratedByOn X.toRingedSpace J U₁ g hgen₁)
      have hgerms₀ : X.presheaf.germ W₀ x hxW₀
          (∑ j, bb j * X.presheaf.map (homOfLE hW₀U₁).op (g j)) = (w : X.presheaf.stalk x) := by
        rw [map_sum]
        refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) hd
        rw [map_mul, TopCat.Presheaf.germ_res_apply, hbb j]
      obtain ⟨W', hxW', hW'W₀, bc, hbc⟩ := exists_local_conormal_combination X.toRingedSpace J
        (qd.X i₀) (qd.generators i₀) e₀.symm hβ.2 hγ.1 hVU₀ hW₀V (hW₀V.trans hVU₀) f hz
        ⟨_, hs₀⟩ x hxW₀
      refine ⟨fun k => X.presheaf.germ W' x hxW' (bc k), ?_⟩
      have hIle : sectionIdeal X.toRingedSpace J (op W') ≤
          (Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j))).comap
            (X.presheaf.germ W' x hxW').hom := by
        intro uu huu
        exact germ_mem_span_of_isGeneratedByOn X.toRingedSpace J U₁ W' g hgen₁ (hW'W₀.trans hW₀U₁)
          uu huu x hxW'
      have hpow := Construction.map_pow_mem (sectionIdeal X.toRingedSpace J (op W'))
        (Jid (fun j => X.presheaf.germ U₁ x hxU₁ (g j)))
        (X.presheaf.germ W' x hxW').hom hIle hbc
      have hgerm : X.presheaf.germ W' x hxW'
          (X.presheaf.map (homOfLE hW'W₀).op
              (∑ j, bb j * X.presheaf.map (homOfLE hW₀U₁).op (g j)) -
            ∑ k, bc k * X.presheaf.map (homOfLE ((hW'W₀.trans hW₀V))).op (f k).val) =
          (w : X.presheaf.stalk x) -
            ∑ k, X.presheaf.germ W' x hxW' (bc k) * X.presheaf.germ V x hxV (f k).val := by
        rw [map_sub, TopCat.Presheaf.germ_res_apply, hgerms₀, map_sum]
        refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_))
        refine (map_mul _ _ _).trans ?_
        exact congrArg (fun z => X.presheaf.germ W' x hxW' (bc k) * z)
          (X.presheaf.germ_res_apply (homOfLE (hW'W₀.trans hW₀V)) x hxW' (f k).val)
      exact hgerm ▸ hpow
    -- Nakayama and shrinking, from the finite type of `J`
    have hne : Stacks.RingedSpace.stalkIdeal J x ≠ ⊤ := fun htop =>
      hone (by rw [← hstalk, htop]; exact Submodule.mem_top)
    have hle : Stacks.RingedSpace.stalkIdeal J x ≤
        Jid (germFamily X.toRingedSpace V (fun k => (f k).val) x hxV) ⊔
          Stacks.RingedSpace.stalkIdeal J x ^ 2 := by
      intro w hw
      obtain ⟨c, hc⟩ := hmod ⟨w, hstalk ▸ hw⟩
      have hsum : (∑ k, c k * X.presheaf.germ V x hxV (f k).val) ∈
          Jid (germFamily X.toRingedSpace V (fun k => (f k).val) x hxV) :=
        Ideal.sum_mem _ fun k _ =>
          Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k))
      have hsq : (w - ∑ k, c k * X.presheaf.germ V x hxV (f k).val) ∈
          Stacks.RingedSpace.stalkIdeal J x ^ 2 := by rwa [hstalk]
      have hadd := Submodule.add_mem (Jid (germFamily X.toRingedSpace V
        (fun k => (f k).val) x hxV) ⊔ Stacks.RingedSpace.stalkIdeal J x ^ 2)
        (Submodule.mem_sup_left hsum) (Submodule.mem_sup_right hsq)
      rwa [add_sub_cancel] at hadd
    obtain ⟨U, hxU, hUV, hgenU⟩ :=
      exists_isGeneratedByOn_of_isFiniteType_of_le_sup_sq J hfinite hne hxV
        (fun k => (f k).val) (fun k => (f k).property) hle
    refine ⟨U, hxU, r, fun k => X.presheaf.map (homOfLE hUV).op (f k).val, hgenU, ?_⟩
    -- independence at every point of the witness open
    intro y hy a ha k
    obtain ⟨W₃, hyW₃, hW₃U, bb, hbbg, hbbsq⟩ := exists_local_sum_mem_sq X.toRingedSpace J U
      (fun k => X.presheaf.map (homOfLE hUV).op (f k).val)
      (fun k => J.toSubmodule.map_mem (homOfLE hUV).op (f k).property) y hy a ha
    have hsq : (∑ k, bb k * X.presheaf.map (homOfLE (hW₃U.trans hUV)).op (f k).val) ∈
        sectionIdeal X.toRingedSpace J (op W₃) ^ 2 := by
      refine Eq.mp ?_ hbbsq
      refine congrArg (fun z => z ∈ sectionIdeal X.toRingedSpace J (op W₃) ^ 2)
        (Finset.sum_congr rfl (fun k _ => ?_))
      exact congrArg (fun z => bb k * z) (map_map_apply X.toRingedSpace hUV hW₃U (f k).val)
    obtain ⟨W₄, hyW₄, hW₄W₃, hmem₄⟩ := exists_local_coeffs_mem X.toRingedSpace J (qd.X i₀)
      (qd.generators i₀) e₀.symm hβ.1 hVU₀ (hW₃U.trans hUV) (hW₃U.trans (hUV.trans hVU₀))
      f hz bb hsq y hyW₃
    have hgermk : X.presheaf.germ W₄ y hyW₄ (X.presheaf.map (homOfLE hW₄W₃).op (bb k)) =
        a k := by
      rw [TopCat.Presheaf.germ_res_apply]
      exact hbbg k
    rw [← hgermk]
    exact germ_mem_span_of_isGeneratedByOn X.toRingedSpace J U W₄
      (fun k => X.presheaf.map (homOfLE hUV).op (f k).val) hgenU (hW₄W₃.trans hW₃U)
      _ (hmem₄ k) y hyW₄

/-- **Stacks Project, Tag 063H.** A sheaf of ideals is quasi-regular if and only
if it is of finite type, has finite locally free conormal sheaf, and has
isomorphic canonical symmetric-power-to-associated-graded maps in every degree. -/
@[stacks 063H "both directions of the characterization: quasi-regular iff of finite type,
with finite locally free conormal sheaf and isomorphic symmetric-power-to-graded maps",
  ega "IV 16.9.4",
  ega "IV 17.12.1" "more general"]
public theorem isQuasiRegularIdealSheaf_iff (X : LocallyRingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X.toRingedSpace).Submodule) :
    IsQuasiRegularIdealSheaf X.toRingedSpace J ↔
      (J.toSheafOfModules.IsFiniteType ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (conormalSheaf X.toRingedSpace J) ∧
        ∀ n : ℕ, IsIso (conormalSymmetricToGradedMap X.toRingedSpace J n)) := by
  classical
  constructor
  · intro h
    refine ⟨isFiniteType_of_isQuasiRegularIdealSheaf X.toRingedSpace J h,
      conormalSheaf_isFiniteLocallyFree X.toRingedSpace J h, fun n => ?_⟩
    apply conormalSymmetricToGradedMap_isIso_of_local_kernel_on_support
    intro U z hz x hxU hxS
    obtain ⟨W, hxW, r, f, hqr, hgen⟩ := h x hxS
    exact canonicalMap_local_kernel_of_quasiRegular_generators
      X.toRingedSpace J W f hgen hqr U n z hz x hxU hxW
  · rintro ⟨hfinite, hfree, hmaps⟩
    have hkernel := fun n =>
      (conormalSymmetricToGradedMap_isIso_iff_local_kernel X.toRingedSpace J n).mp (hmaps n)
    intro x hx
    obtain ⟨U, hxU, r, f, hgen, hind⟩ :=
      exists_local_generators_with_independent_conormal X J hfinite hfree x hx
    refine ⟨U, hxU, r, f, ?_, hgen⟩
    apply (quasiRegularMap_isIso_iff _ _).mpr
    intro y
    obtain ⟨L, hsq, hL⟩ := exists_coords_of_conormal_independent _
      (conormal_independent_germSequence X.toRingedSpace U y.1 y.2 f (hind y.1 y.2))
    exact polynomialQuasiRegularCanonicalMap_bijective_of_coords _ L hsq hL
      (fun n => canonicalMap_injective_of_local_kernel X.toRingedSpace J hkernel U f hgen
        n y.1 y.2)

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
