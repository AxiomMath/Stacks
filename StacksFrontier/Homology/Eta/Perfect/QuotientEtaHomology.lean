module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Eta.Cohomology
public import StacksFrontier.Homology.Eta.Complex

/-!
# Cohomology of a complex reduced modulo a nonzerodivisor

Let `A` be a ring, `f ∈ A`, and `P^•` a complex of `A`-modules on whose terms `f` acts
injectively.  If `f` also acts injectively on `H^{n+1}(P^•)`, then
`H^n(P^• ⊗_A A/fA) ≅ A/fA ⊗_A H^n(P^•)`.

If `f` acts injectively on the terms of `M^•` and on `H^n(M^•)`, then
`H^n(η_f M^•) ≅ H^n(M^•)`.

## Main results

* `Stacks.Eta.QuotientHomology.nonempty_homology_extendScalars_quotient_equiv`: the
  isomorphism `H^n(P^• ⊗_A A/fA) ≅ A/fA ⊗_A H^n(P^•)`.
* `Stacks.Eta.QuotientHomology.nonempty_homology_etaObject_equiv`: the isomorphism
  `H^n(η_f M^•) ≅ H^n(M^•)`.

## References

* [Stacks Project, Tag 0F7P](https://stacks.math.columbia.edu/tag/0F7P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Eta.QuotientHomology

variable {A : Type u} [CommRing A] (f : A)

/-- The quotient map `A → A ⧸ fA`. -/
abbrev quotMap : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk _

/-- Reduction modulo `f` of an `A`-module, read again as an `A`-module. -/
abbrev reduce (f : A) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  ModuleCat.extendScalars.{u, u, u} (quotMap f) ⋙ ModuleCat.restrictScalars.{u} (quotMap f)

/-- The map `M → A/fA ⊗_A M`, `x ↦ 1 ⊗ x`. -/
abbrev reduceUnit (M : ModuleCat.{u} A) : M ⟶ (reduce f).obj M :=
  (ModuleCat.extendRestrictScalarsAdj (quotMap f)).unit.app M

/-- The `A`-linear identification of `A/fA ⊗_A M`, as built by extension of scalars, with
`M ⧸ fM`. -/
def reduceEquiv (M : ModuleCat.{u} A) :
    (reduce f).obj M ≃ₗ[A] M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)) :=
  let e : (ModuleCat.restrictScalars (quotMap f)).obj (ModuleCat.of _ (A ⧸ Ideal.span {f})) ≃ₗ[A]
      A ⧸ Ideal.span {f} :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => by
        rw [ModuleCat.restrictScalars.smul_def]
        simp only [RingHom.id_apply]
        rfl }
  ((TensorProduct.congr e (LinearEquiv.refl A M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {f})) : _)

/-- The identification `reduceEquiv` sends `1 ⊗ x` to the class of `x` in `M ⧸ fM`. -/
theorem reduceEquiv_reduceUnit (M : ModuleCat.{u} A) (x : M) :
    reduceEquiv f M (reduceUnit f M x) = Submodule.Quotient.mk x :=
  TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x

/-- Reduction modulo `f` kills the multiples of `f`. -/
theorem reduceUnit_smul (M : ModuleCat.{u} A) (x : M) : reduceUnit f M (f • x) = 0 := by
  apply (reduceEquiv f M).injective
  rw [reduceEquiv_reduceUnit, map_zero, Submodule.Quotient.mk_eq_zero,
    Submodule.ideal_span_singleton_smul]
  exact Submodule.smul_mem_pointwise_smul x f ⊤ trivial

/-- Multiplication by `f` followed by reduction modulo `f` is zero. -/
theorem smul_id_comp_reduceUnit (M : ModuleCat.{u} A) : (f • 𝟙 M) ≫ reduceUnit f M = 0 := by
  ext x
  exact reduceUnit_smul f M x

/-- Multiplication by `f` followed by reduction modulo `f`, on a module on which `f` acts
injectively, is a short exact sequence `0 → M → M → A/fA ⊗_A M → 0`. -/
theorem shortExact_reduce (M : ModuleCat.{u} A) (hM : IsSMulRegular M f) :
    (ShortComplex.mk (f • 𝟙 M) (reduceUnit f M) (smul_id_comp_reduceUnit f M)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : (Submodule.Quotient.mk x : M ⧸ (Ideal.span {f} • (⊤ : Submodule A M))) = 0 := by
      rw [← reduceEquiv_reduceUnit]
      show reduceEquiv f M (reduceUnit f M x) = 0
      rw [show reduceUnit f M x = 0 from hx, map_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact ⟨y, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).2 hM
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((reduceEquiv f M) z)
    exact ⟨x, (reduceEquiv f M).injective (by rw [reduceEquiv_reduceUnit, hx])⟩

/-- The reduction map `P^• → A/fA ⊗_A P^•` of a complex. -/
def reduceComplexUnit (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    P ⟶ ((reduce f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P where
  f i := reduceUnit f (P.X i)
  comm' i j _ := ((ModuleCat.extendRestrictScalarsAdj (quotMap f)).unit.naturality
    (P.d i j)).symm

/-- The short exact sequence of complexes `0 → P^• → P^• → A/fA ⊗_A P^• → 0`. -/
def reduceShortComplex (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (f • 𝟙 P) (reduceComplexUnit f P) (by
    ext i : 1
    exact smul_id_comp_reduceUnit f (P.X i))

/-- The sequence `0 → P^• → P^• → A/fA ⊗_A P^• → 0` is short exact when `f` acts injectively
on every term of `P^•`. -/
theorem shortExact_reduceShortComplex (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ i, IsSMulRegular (P.X i) f) : (reduceShortComplex f P).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => shortExact_reduce f _ (hP i)

/-- Multiplication by a scalar acts on cohomology by that scalar. -/
theorem homologyMap_smul_id (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    HomologicalComplex.homologyMap (f • 𝟙 P) n = f • 𝟙 (P.homology n) := by
  rw [HomologicalComplex.homologyMap]
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat A) (.up ℤ) n).map (f • 𝟙 P) =
      f • 𝟙 ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (.up ℤ) n).obj P) := by
    ext <;> simp <;> rfl
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

variable {f} in
/-- The map `H^n(P^•) → H^n(P^• ⊗_A A/fA)` is surjective with kernel `f H^n(P^•)` as soon as `f`
acts injectively on the terms of `P^•` and on `H^{n+1}(P^•)`. -/
theorem surjective_and_ker_homologyMap_reduceComplexUnit
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : ∀ i, IsSMulRegular (P.X i) f) (n : ℤ)
    (hH : IsSMulRegular (P.homology (n + 1)) f) :
    Function.Surjective (HomologicalComplex.homologyMap (reduceComplexUnit f P) n) ∧
      LinearMap.ker (HomologicalComplex.homologyMap (reduceComplexUnit f P) n).hom =
        Ideal.span {f} • (⊤ : Submodule A (P.homology n)) := by
  have hS := shortExact_reduceShortComplex f P hP
  have hδ : hS.δ n (n + 1) rfl = 0 := by
    have h1 := hS.homology_exact₁ n (n + 1) rfl
    have hmono : Mono (HomologicalComplex.homologyMap (reduceShortComplex f P).f (n + 1)) := by
      show Mono (HomologicalComplex.homologyMap (f • 𝟙 P) (n + 1))
      rw [homologyMap_smul_id, ModuleCat.mono_iff_injective]
      exact hH
    exact (ShortComplex.Exact.mono_g_iff h1).mp hmono
  have h2 := hS.homology_exact₂ n
  have h3 := hS.homology_exact₃ n (n + 1) rfl
  refine ⟨fun y => ?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff] at h3
    exact h3 y (by
      show (hS.δ n (n + 1) rfl) y = 0
      rw [hδ]
      rfl)
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h2
    change _ = LinearMap.ker (HomologicalComplex.homologyMap (reduceShortComplex f P).g n).hom
      at h2
    show LinearMap.ker (HomologicalComplex.homologyMap (reduceShortComplex f P).g n).hom = _
    rw [← h2, Submodule.ideal_span_singleton_smul]
    show LinearMap.range (HomologicalComplex.homologyMap (f • 𝟙 P) n).hom = _
    rw [homologyMap_smul_id]
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩

variable {f} in
/-- `H^n(P^• ⊗_A A/fA) ≅ H^n(P^•) ⧸ f H^n(P^•)` as `A`-modules, when `f` acts injectively on the
terms of `P^•` and on `H^{n+1}(P^•)`. -/
def homologyReduceEquiv (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ i, IsSMulRegular (P.X i) f) (n : ℤ) (hH : IsSMulRegular (P.homology (n + 1)) f) :
    (P.homology n ⧸ (Ideal.span {f} • (⊤ : Submodule A (P.homology n)))) ≃ₗ[A]
      (((reduce f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology n :=
  let h := surjective_and_ker_homologyMap_reduceComplexUnit P hP n hH
  (Submodule.quotEquivOfEq _ _ h.2.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ h.1)

variable {f} in
/-- **`H^n(P^• ⊗_A A/fA) ≅ A/fA ⊗_A H^n(P^•)`**, when `f` acts injectively on the terms of `P^•`
and on `H^{n+1}(P^•)`. -/
theorem nonempty_homology_extendScalars_quotient_equiv (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ i, IsSMulRegular (P.X i) f) (n : ℤ) (hH : IsSMulRegular (P.homology (n + 1)) f) :
    Nonempty ((((ModuleCat.extendScalars.{u, u, u} (quotMap f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology n ≃ₗ[A ⧸ Ideal.span {f}]
      (A ⧸ Ideal.span {f}) ⊗[A] P.homology n) := by
  let E := ModuleCat.extendScalars.{u, u, u} (quotMap f)
  let R := ModuleCat.restrictScalars.{u} (quotMap f)
  let H := ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology n
  let e₁ : (((reduce f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology n ≅ R.obj H :=
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso R
        (ComplexShape.up ℤ) n).app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  let e : (A ⧸ Ideal.span {f}) ⊗[A] P.homology n ≃ₗ[A] R.obj H :=
    (TensorProduct.quotTensorEquivQuotSMul _ _).trans
      ((homologyReduceEquiv P hP n hH).trans e₁.toLinearEquiv)
  let : Module A H := Module.compHom _ (quotMap f)
  have : IsScalarTower A (A ⧸ Ideal.span {f}) H := .of_algebraMap_smul fun _ _ => rfl
  let ι : R.obj H ≃ₗ[A] H :=
    { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact ⟨(LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective (e.trans ι)).symm⟩

/-! ### The cohomology of the décalage of a complex with `f`-torsion-free cohomology -/

section Decalage

open Stacks.Decalage.Cohomology

variable {f}

/-- A complex of `f`-torsion-free modules, as the datum of Tag 0F7P. -/
def toFTFComplex (N : CochainComplex (ModuleCat.{u} A) ℤ) (htf : ∀ i, IsSMulRegular (N.X i) f) :
    FTFComplex A f where
  M i := N.X i
  d i := (N.d i (i + 1)).hom
  d_comp_d i := by
    rw [← ModuleCat.hom_comp, N.d_comp_d]
    rfl
  tf := htf

/-- The cohomology of a complex in degree `j + 1` is the quotient `Z^{j+1} ⧸ B^{j+1}` of
Tag 0F7P. -/
def homologyEquivHcohom (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (htf : ∀ i, IsSMulRegular (N.X i) f) (j : ℤ) :
    N.homology (j + 1) ≃ₗ[A] Hcohom (toFTFComplex N htf) j :=
  ((N.homologyIsoSc' j (j + 1) (j + 1 + 1) (by simp) (by simp)) ≪≫
      (N.sc' j (j + 1) (j + 1 + 1)).moduleCatHomologyIso).toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (by
      ext ⟨x, hx⟩
      simp only [Submodule.submoduleOf, LinearMap.mem_range]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩))

/-- The cohomology of the décalage of a complex in degree `j + 1` is the quotient
`Z^{j+1}(η_f M^•) ⧸ B^{j+1}(η_f M^•)` of Tag 0F7P. -/
def homologyEtaEquivHeta (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (htf : ∀ i, IsSMulRegular (N.X i) f) (j : ℤ) :
    (EtaComplex.etaObject.{u, u} f N).homology (j + 1) ≃ₗ[A] Heta (toFTFComplex N htf) j := by
  let E := EtaComplex.etaObject.{u, u} f N
  let S := E.sc' j (j + 1) (j + 1 + 1)
  have hg : ∀ y : EtaComplex.term f N (j + 1),
      S.g.hom y = EtaComplex.etaDifferential f N (j + 1) y := fun y => by
    change ((EtaComplex.etaObject f N).d (j + 1) (j + 1 + 1)).hom y = _
    rw [EtaComplex.etaObject_d]
    rfl
  have hf : ∀ y : EtaComplex.term f N j,
      S.f.hom y = EtaComplex.etaDifferential f N j y := fun y => by
    change ((EtaComplex.etaObject f N).d j (j + 1)).hom y = _
    rw [EtaComplex.etaObject_d]
    rfl
  let e : LinearMap.ker S.g.hom ≃ₗ[A] Zeta (toFTFComplex N htf) j :=
    { toFun z := ⟨z.1.1, z.1.2, LinearMap.mem_ker.mpr
        ((EtaComplex.etaDifferential_val f N (j + 1) z.1).symm.trans
          (congrArg Subtype.val ((hg z.1).symm.trans (LinearMap.mem_ker.mp z.2))))⟩
      invFun w := ⟨⟨w.1, w.2.1⟩, LinearMap.mem_ker.mpr ((hg ⟨w.1, w.2.1⟩).trans
        (Subtype.ext ((EtaComplex.etaDifferential_val f N (j + 1) ⟨w.1, w.2.1⟩).trans
          (LinearMap.mem_ker.mp w.2.2))))⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine ((E.homologyIsoSc' j (j + 1) (j + 1 + 1) (by simp) (by simp)) ≪≫
      S.moduleCatHomologyIso).toLinearEquiv.trans (Submodule.Quotient.equiv _ _ e ?_)
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.submoduleOf,
    Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y.1, y.2, (EtaComplex.etaDifferential_val f N j y).symm.trans
      (congrArg Subtype.val (hf y).symm)⟩
  · rintro ⟨y, hy, hyw⟩
    refine ⟨e.symm w, ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext ?_)⟩, e.apply_symm_apply w⟩
    exact (congrArg Subtype.val (hf ⟨y, hy⟩)).trans
      ((EtaComplex.etaDifferential_val f N j ⟨y, hy⟩).trans hyw)

/-- **The cohomology of the décalage of a complex with `f`-torsion-free cohomology** (Tag 0F7P):
if `f` acts injectively on the terms of `M^•` and on `H^n(M^•)`, then
`H^n(η_f M^•) ≅ H^n(M^•)`. -/
theorem nonempty_homology_etaObject_equiv (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (htf : ∀ i, IsSMulRegular (N.X i) f) (n : ℤ) (hH : IsSMulRegular (N.homology n) f) :
    Nonempty ((EtaComplex.etaObject.{u, u} f N).homology n ≃ₗ[A] N.homology n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by lia⟩
  obtain ⟨Φ, e, hker, -⟩ := tag_0F7P_iso (toFTFComplex N htf) j
  have hbot : LinearMap.ker Φ = ⊥ := by
    refine eq_bot_iff.2 fun ξ hξ => (Submodule.mem_bot A).2 <|
      (homologyEquivHcohom N htf j).symm.injective ?_
    rw [map_zero]
    apply hH
    show f • (homologyEquivHcohom N htf j).symm ξ = f • 0
    rw [smul_zero, ← map_smul, (hker ξ).mp hξ, map_zero]
  exact ⟨(homologyEtaEquivHeta N htf j).trans (e.symm.trans
    ((Submodule.quotEquivOfEqBot _ hbot).trans (homologyEquivHcohom N htf j).symm))⟩

end Decalage

end Stacks.Eta.QuotientHomology
