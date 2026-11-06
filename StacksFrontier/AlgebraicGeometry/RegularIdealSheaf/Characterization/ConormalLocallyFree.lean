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

/-!
# Quasi-regular ideal sheaves: the conormal sheaf is finite locally free

Conormal classes, the free presentation of the conormal sheaf by quasi-regular generators,
finite local freeness of `J/J²`, and bijectivity of the polynomial comparison from coordinates.
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

noncomputable def conormalClass {R : Type u} [CommRing R] (I : Ideal R) :
    I →ₗ[R] Construction.GradedPiece I 1 :=
  (Submodule.mkQ _).comp (Submodule.inclusion (show I ≤ I ^ 1 by simp))

lemma conormalClass_eq_zero_iff {R : Type u} [CommRing R]
    (I : Ideal R) (s : I) : conormalClass I s = 0 ↔ (s : R) ∈ I ^ 2 :=
  Submodule.Quotient.mk_eq_zero _

private lemma gradedMap_conormalClass {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (K : Ideal S) (φ : R →+* S) (h : I ≤ K.comap φ) (s : I) :
    Construction.gradedMap I K φ h 1 (conormalClass I s) =
      conormalClass K (Construction.idealMap I K φ h s) := rfl

private lemma coefficients_mem_of_local_quasiRegular_generators (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (hgen : IsGeneratedByOn X J U f)
    (hqr : IsIso (QuasiRegular.quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun k => sectionOnRestriction X U (f k))).hom)
    (V : Opens X) (i : V ⟶ U) (a : Fin r → X.presheaf.obj (op V))
    (ha : ∑ k, a k * X.presheaf.map i.op (f k) ∈ sectionIdeal X J (op V) ^ 2) :
    ∀ k, a k ∈ J.obj (op V) := by
  intro k
  apply J.isSheaf (a k)
  intro x hx
  let g := QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
    (fun k => sectionOnRestriction X U (f k)) ⟨x, leOfHom i hx⟩
  let φ := germInRestriction X U x (leOfHom i hx) V hx
  have hI : sectionIdeal X J (op V) ≤ (Jid g).comap φ := by
    intro s hs
    apply (germInRestriction_mem_span_iff X U x (leOfHom i hx) f V hx s).mpr
    exact germ_mem_span_of_isGeneratedByOn X J U V f hgen (leOfHom i) s hs x hx
  have hφ (j : Fin r) : φ (X.presheaf.map i.op (f j)) = g j := by
    show germInRestriction X U x _ V hx (X.presheaf.map i.op (f j)) = _
    rw [germInRestriction_res X U x (leOfHom i hx) V U hx (leOfHom i hx) i,
      germInRestriction_self]
    rfl
  have hsum : ∑ j, φ (a j) * g j ∈ Jid g ^ 2 := by
    have h := Construction.map_pow_mem _ _ φ hI ha
    simpa only [map_sum, map_mul, hφ] using h
  have hk := coefficients_mem_of_sum_mem_square g
    ((quasiRegularMap_isIso_iff _ _).mp hqr ⟨x, leOfHom i hx⟩).1 _ hsum k
  obtain ⟨W, hxW, j, hj⟩ := exists_local_mem_of_germ_mem_span X J U V f
    (mem_of_isGeneratedByOn X J U f hgen) (a k) x (leOfHom i hx) hx
    ((germInRestriction_mem_span_iff X U x (leOfHom i hx) f V hx _).mp hk)
  exact ⟨W, j, hj, hxW⟩

lemma conormalClass_linearIndependent {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → I)
    (h : ∀ a : Fin r → R, (∑ k, a k * (f k : R)) ∈ I ^ 2 → ∀ k, a k ∈ I) :
    LinearIndependent (R ⧸ I) (fun k => conormalClass I (f k)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc k
  choose a ha using fun j => Ideal.Quotient.mk_surjective (c j)
  have hc' : conormalClass I (∑ j, a j • f j) = 0 := by
    rw [map_sum]
    simpa only [map_smul, ← ha, ← Ideal.Quotient.algebraMap_eq,
      algebraMap_smul] using hc
  have hmem := (conormalClass_eq_zero_iff I _).mp hc'
  have hcoeff := h a (by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hmem)
  rw [← ha k]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff k)

private noncomputable def presheafSectionOver {C : Type v} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R) (U : C) (s : M.obj (op U)) :
    ((PresheafOfModules.pushforward₀ (Over.forget U) R).obj M).sections :=
  PresheafOfModules.sectionsMk (fun V => M.map V.unop.hom.op s) (by
    intro V W i
    change M.map i.unop.left.op (M.map V.unop.hom.op s) = _
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

private noncomputable def conormalPresentation (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U)) :
    PresheafOfModules.freeObj ((Functor.const (Over U)ᵒᵖ).obj (ULift.{u} (Fin r))) ⟶
      (PresheafOfModules.pushforward₀ (Over.forget U) (quotientPresheaf X J)).obj
        (gradedPresheaf X J 1) :=
  (constantFreeHomEquiv _ _).symm (fun k =>
    presheafSectionOver (gradedPresheaf X J 1) U
      (conormalClass (sectionIdeal X J (op U)) (f k.down)))

private lemma conormalPresentation_freeMk (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U)) (V : (Over U)ᵒᵖ) (k : ULift.{u} (Fin r)) :
    (conormalPresentation X J U f).app V (ModuleCat.freeMk k) =
      conormalClass (sectionIdeal X J (op V.unop.left))
        ⟨X.presheaf.map V.unop.hom.op (f k.down).val, J.toSubmodule.map_mem V.unop.hom.op
          (f k.down).property⟩ := by
  have h := congrArg (fun s => (s k).val V)
    ((constantFreeHomEquiv _ _).apply_symm_apply (fun k : ULift.{u} (Fin r) =>
      presheafSectionOver (gradedPresheaf X J 1) U
        (conormalClass (sectionIdeal X J (op U)) (f k.down))))
  exact h

private lemma conormalPresentation_mono (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U))
    (hgen : IsGeneratedByOn X J U (fun k => (f k).val))
    (hqr : IsIso (QuasiRegular.quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun k => sectionOnRestriction X U (f k).val)).hom) :
    Mono (conormalPresentation X J U f) := by
  apply PresheafOfModules.mono_of_injective
  intro V
  have hli := conormalClass_linearIndependent (sectionIdeal X J (op V.unop.left))
    (fun k => ⟨X.presheaf.map V.unop.hom.op (f k).val, J.toSubmodule.map_mem V.unop.hom.op
      (f k).property⟩)
    (coefficients_mem_of_local_quasiRegular_generators X J U (fun k => (f k).val)
      hgen hqr V.unop.left V.unop.hom)
  have hli' := hli.comp (fun k : ULift.{u} (Fin r) => k.down) ULift.down_injective
  have he : (conormalPresentation X J U f).app V = ModuleCat.ofHom
      (Finsupp.linearCombination (X.presheaf.obj (op V.unop.left) ⧸
        sectionIdeal X J (op V.unop.left)) (fun k : ULift.{u} (Fin r) =>
        conormalClass (sectionIdeal X J (op V.unop.left))
          ⟨X.presheaf.map V.unop.hom.op (f k.down).val,
            J.toSubmodule.map_mem V.unop.hom.op (f k.down).property⟩)) := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro k a
    simp only
    rw [← Finsupp.smul_single_one k a, map_smul]
    rw [map_smul]
    have hh := Finsupp.linearCombination_single
      (X.presheaf.obj (op V.unop.left) ⧸ sectionIdeal X J (op V.unop.left))
      (v := fun k : ULift.{u} (Fin r) =>
        conormalClass (sectionIdeal X J (op V.unop.left))
          ⟨X.presheaf.map V.unop.hom.op (f k.down).val,
            J.toSubmodule.map_mem V.unop.hom.op (f k.down).property⟩) 1 k
    rw [one_smul] at hh
    exact (congrArg (a • ·) (conormalPresentation_freeMk X J U f V k)).trans
      (congrArg (a • ·) hh.symm)
  rw [he]
  exact hli'

private lemma conormalPresentation_apply (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U)) (V : (Over U)ᵒᵖ)
    (c : ULift.{u} (Fin r) →₀ (X.presheaf.obj (op V.unop.left) ⧸
      sectionIdeal X J (op V.unop.left))) :
    (conormalPresentation X J U f).app V c =
      ∑ k : ULift.{u} (Fin r), c k •
        conormalClass (sectionIdeal X J (op V.unop.left))
          ⟨X.presheaf.map V.unop.hom.op (f k.down).val, J.toSubmodule.map_mem V.unop.hom.op
            (f k.down).property⟩ := by
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [map_finsuppSum]
  have hsingle (k : ULift.{u} (Fin r))
      (a : X.presheaf.obj (op V.unop.left) ⧸ sectionIdeal X J (op V.unop.left)) :
      Finsupp.single k a = a • ModuleCat.freeMk k :=
    (Finsupp.smul_single_one k a).symm
  simp only [hsingle, map_smul]
  show c.sum (fun k a => a • (conormalPresentation X J U f).app V (ModuleCat.freeMk k)) = _
  simp only [conormalPresentation_freeMk]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)

private lemma conormalPresentation_locallySurjective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U))
    (hgen : IsGeneratedByOn X J U (fun k => (f k).val)) :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (conormalPresentation X J U f) := by
  classical
  constructor
  intro V s
  rw [GrothendieckTopology.mem_over_iff]
  intro x hx
  change Construction.GradedPiece (sectionIdeal X J (op V.left)) 1 at s
  induction s using Submodule.Quotient.induction_on with | _ s =>
  obtain ⟨W, hxW, iU, iV, a, ha⟩ := exists_local_linearCombination_of_isGeneratedByOn
    X J U V.left (fun k => (f k).val) hgen (leOfHom V.hom) s
    ((pow_one (sectionIdeal X J (op V.left))).le s.property) x hx
  refine ⟨W, iV, ?_, hxW⟩
  rw [Sieve.overEquiv_iff]
  let Z : Over U := Over.mk (iV ≫ V.hom)
  let c : ULift.{u} (Fin r) →₀ (X.presheaf.obj (op W) ⧸ sectionIdeal X J (op W)) :=
    Finsupp.equivFunOnFinite.symm (fun k => Ideal.Quotient.mk _ (a k.down))
  refine ⟨c, ?_⟩
  show (conormalPresentation X J U f).app (op Z) c =
    Construction.gradedMap _ _ (X.presheaf.map iV.op).hom
      (sectionIdeal_map X J iV.op) 1 (Submodule.Quotient.mk s)
  rw [conormalPresentation_apply]
  show (∑ k : ULift.{u} (Fin r),
    (Ideal.Quotient.mk (sectionIdeal X J (op W)) (a k.down)) •
    conormalClass (sectionIdeal X J (op W))
      ⟨X.presheaf.map iU.op (f k.down).val, _⟩) = _
  simp only [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, ← map_smul, ← map_sum]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  dsimp only [Submodule.coe_inclusion, Construction.powerMap, LinearMap.restrict_apply,
    RingHom.coe_toSemilinearMap]
  simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
  exact (Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
      (fun k => a k * X.presheaf.map iU.op (f k).val)).trans ha

lemma quotientSheaf_unit_locallyBijective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)) ∧
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)) := by
  let T := Opens.grothendieckTopology X
  let : Limits.HasColimitsOfSize.{u, u} RingCat.{u} :=
    Limits.hasColimitsOfSizeShrink RingCat.{u}
  let : ∀ U : Opens X, Limits.HasColimitsOfShape (T.Cover U)ᵒᵖ RingCat.{u} := fun U =>
    Limits.HasColimitsOfShape.of_small (C := RingCat.{u}) ((T.Cover U)ᵒᵖ)
  let : Limits.PreservesFilteredColimitsOfSize.{u, u} (forget RingCat.{u}) :=
    Limits.preservesFilteredColimitsOfSize_shrink _
  let : T.PreservesSheafification (forget RingCat.{u}) :=
    GrothendieckTopology.instPreservesSheafification T (forget RingCat.{u})
  let : ConcreteCategory.{u} RingCat
      (fun A B : RingCat.{u} => A →+* B) := inferInstance
  let : T.WEqualsLocallyBijective RingCat.{u} := inferInstance
  exact ⟨inferInstance, inferInstance⟩

noncomputable def gradedSheafificationUnit (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ) :
    gradedPresheaf X J n ⟶
      (PresheafOfModules.restrictScalars
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J))).obj
          (associatedGradedPiece X J n).val := by
  have := (quotientSheaf_unit_locallyBijective X J).1
  have := (quotientSheaf_unit_locallyBijective X J).2
  exact (PresheafOfModules.sheafificationAdjunction
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J))).unit.app _

noncomputable def conormalSheafificationUnitOver (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) :
    (PresheafOfModules.pushforward₀ (Over.forget U) (quotientPresheaf X J)).obj
      (gradedPresheaf X J 1) ⟶
    (PresheafOfModules.restrictScalars
      (Functor.whiskerLeft (Over.forget U).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)))).obj
      ((conormalSheaf X J).over U).val :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (quotientPresheaf X J)).map
    (gradedSheafificationUnit X J 1)

lemma conormalSheafificationUnitOver_locallyBijective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
        (conormalSheafificationUnitOver X J U) ∧
      PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
        (conormalSheafificationUnitOver X J U) := by
  constructor
  · exact Presheaf.isLocallyInjective_whisker ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) (Over.forget U)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (gradedPresheaf X J 1).presheaf)
  · exact Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) (Over.forget U)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (gradedPresheaf X J 1).presheaf)

private noncomputable def conormalGeneratingSections (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U)) : ULift.{u} (Fin r) → ((conormalSheaf X J).over U).sections :=
  fun k => by
    let t := PresheafOfModules.sectionsMap (conormalSheafificationUnitOver X J U)
      (presheafSectionOver (gradedPresheaf X J 1) U
        (conormalClass (sectionIdeal X J (op U)) (f k.down)))
    exact t

private lemma freePresheafMap_conormalGeneratingSections (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U)) :
    freePresheafMap
      (Functor.whiskerLeft (Over.forget U).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)))
      ((conormalSheaf X J).over U) (conormalGeneratingSections X J U f) =
      conormalPresentation X J U f ≫ conormalSheafificationUnitOver X J U := by
  apply (constantFreeHomEquiv _ _).injective
  funext k
  apply PresheafOfModules.sections_ext
  intro V
  rw [constantFreeHomEquiv_apply, freePresheafMap_freeMk, constantFreeHomEquiv_apply]
  show (conormalSheafificationUnitOver X J U).app V
      ((gradedPresheaf X J 1).map V.unop.hom.op
        (conormalClass (sectionIdeal X J (op U)) (f k.down))) =
    (conormalSheafificationUnitOver X J U).app V
      ((conormalPresentation X J U f).app V (ModuleCat.freeMk k))
  rw [conormalPresentation_freeMk]
  rfl

private lemma conormalGeneratingSections_isIso (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → J.obj (op U))
    (hgen : IsGeneratedByOn X J U (fun k => (f k).val))
    (hqr : IsIso (QuasiRegular.quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun k => sectionOnRestriction X U (f k).val)).hom) :
    IsIso (((conormalSheaf X J).over U).freeHomEquiv.symm
      (conormalGeneratingSections X J U f)) := by
  let α := Functor.whiskerLeft (Over.forget U).op
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J))
  have := (quotientSheaf_unit_locallyBijective X J).2
  have : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U) α :=
    Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) (Over.forget U) _
  have := conormalPresentation_mono X J U f hgen hqr
  have hmono : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (conormalPresentation X J U f) := by
    apply Presheaf.isLocallyInjective_of_injective
    exact PresheafOfModules.injective_of_mono (conormalPresentation X J U f)
  have := conormalPresentation_locallySurjective X J U f hgen
  have := (conormalSheafificationUnitOver_locallyBijective X J U).1
  have := (conormalSheafificationUnitOver_locallyBijective X J U).2
  have hβ : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
        (freePresheafMap α ((conormalSheaf X J).over U) (conormalGeneratingSections X J U f)) ∧
      PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
        (freePresheafMap α ((conormalSheaf X J).over U) (conormalGeneratingSections X J U f)) := by
    rw [freePresheafMap_conormalGeneratingSections]
    dsimp only [PresheafOfModules.IsLocallyInjective, PresheafOfModules.IsLocallySurjective]
    rw [Functor.map_comp]
    exact ⟨inferInstance, inferInstance⟩
  have := hβ.1
  have := hβ.2
  exact isIso_freeHomEquiv_of_locallyBijective α _ _

private lemma quasiRegularMap_isIso_one (X : RingedSpace.{u}) (U : Opens X) :
    IsIso (QuasiRegular.quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun _ : Fin 1 => sectionOnRestriction X U 1)).hom := by
  apply (quasiRegularMap_isIso_iff _ _).mpr
  intro x
  let g := QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
    (fun _ : Fin 1 => sectionOnRestriction X U 1) x
  have hg : g 0 = 1 := by
    apply (ConcreteCategory.bijective_of_isIso
      (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding x).hom).1
    show (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding x).hom
      ((X.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial
        (sectionOnRestriction X U 1)) = _
    exact (restrictStalkIso_germ_onRestriction X U x 1).trans ((map_one _).trans (map_one _).symm)
  have hI : Jid g = ⊤ := (Ideal.eq_top_iff_one _).mpr (hg ▸
    Ideal.subset_span (Set.mem_range_self (f := g) 0))
  have : Subsingleton (qrRbar g) := by
    show Subsingleton (_ ⧸ Jid g)
    rw [hI]
    infer_instance
  have : Subsingleton (Target ((X.restrict U.isOpenEmbedding).presheaf.stalk x) g) :=
    Module.subsingleton (qrRbar g) _
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private lemma exists_quasiRegular_generators_at (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (h : IsQuasiRegularIdealSheaf X J) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → J.obj (op U)),
      IsGeneratedByOn X J U (fun k => (f k).val) ∧
        IsIso (QuasiRegular.quasiRegularMap (X.restrict U.isOpenEmbedding)
          (fun k => sectionOnRestriction X U (f k).val)).hom := by
  classical
  by_cases hx : x ∈ idealQuotientSupport X J
  · obtain ⟨U, hxU, r, f, hqr, hgen⟩ := h x hx
    exact ⟨U, hxU, r,
      fun k => ⟨f k, mem_of_isGeneratedByOn X J U f hgen k⟩, hgen, hqr⟩
  · obtain ⟨U, hxU, hU⟩ := exists_one_mem_of_notMem_support X J x hx
    exact ⟨U, hxU, 1, fun _ => ⟨(1 : X.presheaf.obj (op U)), hU⟩,
      isGeneratedByOn_one X J U hU, quasiRegularMap_isIso_one X U⟩

lemma conormalSheaf_isFiniteLocallyFree (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (h : IsQuasiRegularIdealSheaf X J) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalSheaf X J) := by
  classical
  choose U hx r f hgen hqr using exists_quasiRegular_generators_at X J h
  have hi := fun x => conormalGeneratingSections_isIso X J (U x) (f x) (hgen x) (hqr x)
  let q : (conormalSheaf X J).LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff X U).2 (by
        show iSup U = ⊤
        apply top_unique
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
      generators x :=
        { I := ULift.{u} (Fin (r x))
          s := conormalGeneratingSections X J (U x) (f x)
          epi := by infer_instance } }
  apply AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
  refine ⟨q, ?_, ?_⟩
  · exact SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := q) (fun x => hi x)
  · constructor
    intro x
    exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (r x))))⟩

/-- A product of variables is the monomial on the corresponding exponent sum. -/
private lemma prod_X_eq_monomial_sum {K : Type*} [CommRing K] {r : ℕ} {ι : Type*}
    (s : Finset ι) (t : ι → Fin r) :
    ∏ j ∈ s, (MvPolynomial.X (t j) : MvPolynomial (Fin r) K) =
      MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (t j) 1) 1 := by
  classical
  have hX : ∀ i : Fin r, (MvPolynomial.X i : MvPolynomial (Fin r) K) =
      MvPolynomial.monomial (Finsupp.single i 1) 1 := by
    intro i
    rw [← MvPolynomial.C_mul_X_eq_monomial, map_one, one_mul]
  refine Finset.induction_on s ?_ ?_
  · simp [MvPolynomial.monomial_zero']
  · intro a s' ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, hX,
      MvPolynomial.monomial_mul_monomial, one_mul]

private lemma prod_X_tupleExponent {K : Type*} [CommRing K] {r n : ℕ} (t : Fin n → Fin r) :
    ∏ j, (MvPolynomial.X (t j) : MvPolynomial (Fin r) K) =
      MvPolynomial.monomial (tupleExponent t) 1 :=
  prod_X_eq_monomial_sum Finset.univ t

/-- Every exponent vector of total degree `n` is the exponent of some `n`-tuple. -/
private lemma exists_tupleExponent_of_sum {r : ℕ} :
    ∀ (n : ℕ) (e : Fin r →₀ ℕ), ∑ i, e i = n → ∃ t : Fin n → Fin r, tupleExponent t = e := by
  intro n
  induction n with
  | zero =>
    intro e he
    refine ⟨Fin.elim0, ?_⟩
    have : e = 0 := by
      ext i
      have := Finset.sum_eq_zero_iff.mp he i (Finset.mem_univ i)
      simpa using this
    simp [tupleExponent, this]
  | succ m ih =>
    intro e he
    have hne : ∃ i, e i ≠ 0 := by
      by_contra hc
      have hall : ∀ i, e i = 0 := fun i => by
        by_contra h
        exact hc ⟨i, h⟩
      rw [Finset.sum_congr rfl (fun i _ => hall i)] at he
      simp at he
    obtain ⟨i₀, hi₀⟩ := hne
    have hle : Finsupp.single i₀ 1 ≤ e :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi₀)
    set e' := e - Finsupp.single i₀ 1 with he'
    have hcancel : Finsupp.single i₀ 1 + e' = e := add_tsub_cancel_of_le hle
    have hsum : ∑ i, e' i = m := by
      have h1 : ∑ i, (Finsupp.single i₀ (1 : ℕ) + e') i = ∑ i, e i := by
        rw [hcancel]
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1
      have h2 : ∑ i, (Finsupp.single i₀ (1 : ℕ)) i = 1 := by
        simp [Finsupp.single_apply]
      rw [h2, he] at h1
      omega
    obtain ⟨t', ht'⟩ := ih e' hsum
    refine ⟨Fin.cons i₀ t', ?_⟩
    rw [tupleExponent, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [show (∑ j : Fin m, Finsupp.single (t' j) (1 : ℕ)) = e' from ht']
    exact hcancel

private lemma gradedPieceToTarget_injective {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) : Function.Injective (gradedPieceToTarget f n) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro z hz
  induction z using Submodule.Quotient.induction_on with | _ a =>
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  show (a : R) ∈ Jid f ^ (n + 1)
  have hz' : (DirectSum.lof R ℕ (fun k => Tcomp R f k) n)
      (Submodule.Quotient.mk (⟨(a : R), by simp [JpowM]⟩ : JpowM R f n)) = 0 := hz
  have h := congrArg (DirectSum.component R ℕ (fun k => Tcomp R f k) n) hz'
  rw [DirectSum.component.lof_self, map_zero] at h
  have h' := (Submodule.Quotient.mk_eq_zero _).mp h
  change (a : R) ∈ JpowM R f (n + 1) at h'
  simpa [JpowM] using h'

open scoped TensorProduct in
private lemma polynomialQuasiRegularCanonicalMap_surjective
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    Function.Surjective (associatedGradedMap f) := by
  let q0 : qrRbar f ≃ₗ[R] qrMbar R f :=
    Submodule.quotEquivOfEq (Jid f : Submodule R R)
      (Jid f • (⊤ : Submodule R R)) (by simp)
  let q : qrRbar f ≃ₗ[qrRbar f] qrMbar R f :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective q0
  let e : MvPolynomial (Fin r) (qrRbar f) ≃ₗ[qrRbar f] Source R f :=
    (TensorProduct.rid _ _).symm.trans (TensorProduct.congr (.refl _ _) q)
  have he : e.toLinearMap = (TensorProduct.mk (qrRbar f) _ _).flip (q0 1) := by
    apply LinearMap.ext
    intro p
    simp [e, q]
  show Function.Surjective ((quasiRegularCanonicalMap (M := R) f).comp
    ((TensorProduct.mk (qrRbar f) _ _).flip (q0 1)))
  rw [← he]
  exact (quasiRegularCanonicalMap_surjective f).comp e.surjective
namespace Construction
section Coordinates

variable {R : Type u} [CommRing R] (I : Ideal R) {r : ℕ}

/-- The multilinear product of the linear forms attached to a coordinate system `L`
on the conormal module `I/I²`. -/
private noncomputable def coordProduct
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I)) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => I) (MvPolynomial (Fin r) (R ⧸ I)) :=
  (MultilinearMap.mkPiAlgebra R (Fin n) (MvPolynomial (Fin r) (R ⧸ I))).compLinearMap
    fun _ => L

private lemma coordProduct_apply
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I)) {n : ℕ} (a : Fin n → I) :
    coordProduct I L n a = ∏ j, L (a j) := rfl

private noncomputable def coordWordsMap
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I)) (n : ℕ) :
    Words I n →ₗ[R] MvPolynomial (Fin r) (R ⧸ I) :=
  Finsupp.linearCombination R (coordProduct I L n)

@[simp] private lemma coordWordsMap_word
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I)) {n : ℕ} (a : Fin n → I) :
    coordWordsMap I L n (word I a) = coordProduct I L n a := by
  simp [coordWordsMap, word]

/-- A coordinate system on `I/I²` kills every defining relation of the symmetric
power presentation, so it descends to the symmetric power. -/
private lemma relations_le_ker_coordWordsMap
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I))
    (hsq : ∀ x : I, (x : R) ∈ I ^ 2 → L x = 0) (n : ℕ) :
    relations I n ≤ (coordWordsMap I L n).ker := by
  rw [relations, Submodule.span_le]
  intro z hz
  show coordWordsMap I L n z = 0
  cases hz with
  | add a i x y => simp [MultilinearMap.map_update_add]
  | smul a i c x => simp [MultilinearMap.map_update_smul]
  | perm a σ =>
    simp only [map_sub, coordWordsMap_word, sub_eq_zero, coordProduct_apply]
    exact Equiv.prod_comp σ (fun j => L (a j))
  | coeff a c hc =>
    simp only [map_smul, coordWordsMap_word, coordProduct_apply]
    have hc0 : (Ideal.Quotient.mk I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    have h1 : c • (∏ j, L (a j)) =
        ((Ideal.Quotient.mk I) c) • (∏ j, L (a j)) :=
      (algebraMap_smul (R ⧸ I) c (∏ j, L (a j))).symm
    rw [h1, hc0, zero_smul]
  | square a i hi =>
    simp only [coordWordsMap_word, coordProduct_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hsq (a i) hi)

/-- The coordinate system, descended to `Symⁿ(I/I²)`. It is a left inverse of the
presentation of `Symⁿ` by degree-`n` polynomials in the coordinates. -/
private noncomputable def coordSymmetricMap
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I))
    (hsq : ∀ x : I, (x : R) ∈ I ^ 2 → L x = 0) (n : ℕ) :
    SymmetricPower I n →ₗ[R] MvPolynomial (Fin r) (R ⧸ I) :=
  (relations I n).liftQ (coordWordsMap I L n) (relations_le_ker_coordWordsMap I L hsq n)

@[simp] private lemma coordSymmetricMap_wordClass
    (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I))
    (hsq : ∀ x : I, (x : R) ∈ I ^ 2 → L x = 0) {n : ℕ} (a : Fin n → I) :
    coordSymmetricMap I L hsq n (wordClass I n a) = ∏ j, L (a j) := by
  show coordWordsMap I L n (word I a) = _
  rw [coordWordsMap_word, coordProduct_apply]

end Coordinates
end Construction

/-- The coordinate system on `Symⁿ`, regarded as `R/I`-linear. -/
private noncomputable def coordSymmetricMapBar {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (L : I →ₗ[R] MvPolynomial (Fin r) (R ⧸ I))
    (hsq : ∀ x : I, (x : R) ∈ I ^ 2 → L x = 0) (n : ℕ) :
    Construction.SymmetricPower I n →ₗ[R ⧸ I] MvPolynomial (Fin r) (R ⧸ I) :=
  (Construction.coordSymmetricMap I L hsq n).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- On the tuple presentation, the coordinate system recovers the polynomial. -/
private lemma coordSymmetricMapBar_tupleWordMap {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (L : Jid f →ₗ[R] MvPolynomial (Fin r) (qrRbar f))
    (hsq : ∀ x : Jid f, (x : R) ∈ Jid f ^ 2 → L x = 0)
    (hL : ∀ i, L (idealGenerator f i) = MvPolynomial.X i)
    (n : ℕ) (w : (Fin n → Fin r) →₀ qrRbar f) :
    coordSymmetricMapBar (Jid f) L hsq n (tupleWordMap f n w) =
      tuplePolynomialMap f n w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | single t c =>
    simp only [tupleWordMap, tuplePolynomialMap, Finsupp.linearCombination_single, map_smul]
    congr 1
    show Construction.coordSymmetricMap (Jid f) L hsq n
      (Construction.wordClass (Jid f) n (idealGenerator f ∘ t)) = _
    rw [Construction.coordSymmetricMap_wordClass]
    simp only [Function.comp_apply, hL]
    exact prod_X_tupleExponent t
private noncomputable def gradedPieceToTcomp {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    Construction.GradedPiece (Jid f) n →ₗ[R] Tcomp R f n :=
  Submodule.mapQ _ _ (Submodule.inclusion (show Jid f ^ n ≤ JpowM R f n by simp [JpowM])) (by
    intro a ha
    change (a : R) ∈ JpowM R f (n + 1)
    simpa [JpowM] using ha)

private lemma gradedPieceToTarget_eq {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (z : Construction.GradedPiece (Jid f) n) :
    gradedPieceToTarget f n z =
      (DirectSum.lof R ℕ (fun k => Tcomp R f k) n) (gradedPieceToTcomp f n z) := rfl

/-- The degree summands of the target are independent, so a finite sum of graded
pieces vanishes only when each piece does. -/
private lemma gradedPieceToTarget_sum_eq_zero {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (s : Finset ℕ) (z : ∀ n, Construction.GradedPiece (Jid f) n)
    (h : ∑ n ∈ s, gradedPieceToTarget f n (z n) = 0) :
    ∀ n ∈ s, z n = 0 := by
  classical
  intro m hm
  have h' := congrArg (DirectSum.component R ℕ (fun k => Tcomp R f k) m) h
  rw [map_zero, map_sum] at h'
  have hvanish : ∀ n ∈ s, n ≠ m →
      DirectSum.component R ℕ (fun k => Tcomp R f k) m
        (gradedPieceToTarget f n (z n)) = 0 := by
    intro n _ hnm
    rw [gradedPieceToTarget_eq, DirectSum.component.of]
    simp [hnm]
  rw [Finset.sum_eq_single_of_mem m hm hvanish, gradedPieceToTarget_eq,
    DirectSum.component.lof_self] at h'
  apply gradedPieceToTarget_injective f m
  rw [gradedPieceToTarget_eq, h', map_zero, map_zero]

/-- Every homogeneous polynomial of degree `n` comes from the tuple presentation. -/
private lemma exists_tuplePolynomialMap_of_isHomogeneous {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (p : MvPolynomial (Fin r) (qrRbar f))
    (hp : p.IsHomogeneous n) :
    ∃ w : (Fin n → Fin r) →₀ qrRbar f, tuplePolynomialMap f n w = p := by
  classical
  have hdeg : ∀ e ∈ p.support, ∑ i, e i = n := by
    intro e he
    have hc : p.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have hwe : (Finsupp.weight (1 : Fin r → ℕ)) e = n := hp hc
    have hsupp : ∑ i, e i = ∑ i ∈ e.support, e i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simpa using Finsupp.notMem_support_iff.mp hi
    rw [hsupp, ← hwe]
    simp [Finsupp.weight_apply, Finsupp.sum]
  choose t ht using fun (e : {e : Fin r →₀ ℕ // e ∈ p.support}) =>
    exists_tupleExponent_of_sum n (e : Fin r →₀ ℕ) (hdeg e.1 e.2)
  refine ⟨∑ e ∈ p.support.attach, Finsupp.single (t e) (p.coeff e.1), ?_⟩
  rw [map_sum]
  conv_rhs => rw [p.as_sum, ← Finset.sum_attach p.support
    (fun e => MvPolynomial.monomial e (p.coeff e))]
  apply Finset.sum_congr rfl
  intro e _
  simp only [tuplePolynomialMap, Finsupp.linearCombination_single, ht e,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- **The ring-level heart of the converse.** If the conormal module `I/I²` of the
ideal generated by `f` admits a coordinate system dual to `f`, and the canonical map
from each symmetric power to the associated graded piece is injective, then the
polynomial quasi-regularity map of `f` is bijective. -/
@[ega "IV 16.9.3" "(i), special case", sga "1 II 4.14" "(a), special case, (i)"]
lemma polynomialQuasiRegularCanonicalMap_bijective_of_coords
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (L : Jid f →ₗ[R] MvPolynomial (Fin r) (qrRbar f))
    (hsq : ∀ x : Jid f, (x : R) ∈ Jid f ^ 2 → L x = 0)
    (hL : ∀ i, L (idealGenerator f i) = MvPolynomial.X i)
    (hinj : ∀ n, Function.Injective (Construction.canonicalMap (Jid f) n)) :
    Function.Bijective (associatedGradedMap f) := by
  classical
  refine ⟨?_, polynomialQuasiRegularCanonicalMap_surjective f⟩
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro p hp
  choose w hw using fun n => exists_tuplePolynomialMap_of_isHomogeneous f n
    (MvPolynomial.homogeneousComponent n p)
    (MvPolynomial.homogeneousComponent_isHomogeneous n p)
  set s := Finset.range (p.totalDegree + 1) with hs
  set z : ∀ n, Construction.GradedPiece (Jid f) n := fun n =>
    canonicalMapOverQuotient (Jid f) n (tupleWordMap f n (w n)) with hzdef
  have hpsum : ∑ n ∈ s, MvPolynomial.homogeneousComponent n p = p :=
    MvPolynomial.sum_homogeneousComponent p
  have hsum : ∑ n ∈ s, gradedPieceToTarget f n (z n) = 0 := by
    have heq : ∑ n ∈ s, gradedPieceToTarget f n (z n) =
        associatedGradedMap f p := by
      rw [← hpsum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro n _
      rw [← hw n, polynomialCanonicalMap_tuplePolynomialMap]
    rw [heq, hp]
  have hz0 := gradedPieceToTarget_sum_eq_zero f s z hsum
  rw [← hpsum]
  refine Finset.sum_eq_zero ?_
  intro n hn
  have h1 : Construction.canonicalMap (Jid f) n (tupleWordMap f n (w n)) = 0 := hz0 n hn
  have h2 : tupleWordMap f n (w n) = 0 := hinj n (h1.trans (map_zero _).symm)
  rw [← hw n, ← coordSymmetricMapBar_tupleWordMap f L hsq hL n (w n), h2, map_zero]

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
