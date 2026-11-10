module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Category
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Module.ReduceModIdealExact
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.AdicComparison

/-!
# Ext over adic quotients: flat base change on inverse limits (Tag 0EH0)

Ext groups as homology of `Hom` out of a projective resolution, reduction of `Hom` modulo an
ideal, flat resolutions over a flat base, and the tag 0EH0 isomorphism on inverse limits
between the adic quotients of `Ext_B(M, N)` and the Ext groups over `B ⧸ I ^ n B`.
-/

@[expose] public section

/-! ## Tag 0EH0 -/

section

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped TensorProduct ModuleCat.Algebra

namespace Stacks.AdicSystem.ExtFlatBaseChange

section Ext

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Abelian C]
  [Linear R C] [HasExt C] {X : C} (P : ProjectiveResolution X) (Y : C)

private lemma smul_extMk (n : ℕ) (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) (r : R) :
    P.extMk (r • f) (n + 1) rfl (by simp [hf]) =
      r • P.extMk f (n + 1) rfl hf := by
  rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
  simp

private lemma extMk_zero_eq_zero_iff (f : P.complex.X 0 ⟶ Y)
    (hf : P.complex.d 1 0 ≫ f = 0) :
    P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  open CochainComplex HomComplex in
    simp only [← P.extEquivCohomologyClass.apply_eq_iff_eq,
      P.extEquivCohomologyClass_extMk, P.extEquivCohomologyClass_zero,
      CohomologyClass.mk_eq_zero_iff]
    rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by simp)]
    have hz := CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1
    constructor
    · rintro ⟨g, hg⟩
      rw [hz.eq_of_src g 0, comp_zero] at hg
      exact (cancel_epi (P.cochainComplexXIso 0 0).hom).mp (by simpa using hg.symm)
    · rintro rfl
      exact ⟨0, by simp⟩

private abbrev homDifferential (n : ℕ) :
    (P.complex.X n ⟶ Y) →ₗ[R] (P.complex.X (n + 1) ⟶ Y) :=
  Linear.leftComp R Y (P.complex.d (n + 1) n)

private def cyclesToExt (n : ℕ) :
    (homDifferential (R := R) P Y n).ker →ₗ[R] Ext X Y n where
  toFun f := P.extMk f.1 (n + 1) rfl f.2
  map_add' f g := (P.add_extMk f.1 g.1 (n + 1) rfl f.2 g.2).symm
  map_smul' r f := smul_extMk P Y n f.1 f.2 r

private lemma cyclesToExt_surjective (n : ℕ) :
    Function.Surjective (cyclesToExt (R := R) P Y n) := by
  intro x
  obtain ⟨f, hf, h⟩ := P.extMk_surjective x (n + 1) rfl
  exact ⟨⟨f, hf⟩, h⟩

private lemma ker_cyclesToExt_succ (n : ℕ) :
    (cyclesToExt (R := R) P Y (n + 1)).ker =
      (homDifferential (R := R) P Y n).range.comap
        (homDifferential (R := R) P Y (n + 1)).ker.subtype := by
  ext f
  exact P.extMk_eq_zero_iff f.1 (n + 1 + 1) rfl f.2 n rfl

private def homologyEquivExtSucc (n : ℕ) :
    ((homDifferential (R := R) P Y (n + 1)).ker ⧸
      (homDifferential (R := R) P Y n).range.comap
        (homDifferential (R := R) P Y (n + 1)).ker.subtype) ≃ₗ[R]
      Ext X Y (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (ker_cyclesToExt_succ P Y n).symm).trans
    ((cyclesToExt P Y (n + 1)).quotKerEquivOfSurjective
      (cyclesToExt_surjective P Y (n + 1)))

private abbrev homIncoming (n : ℕ) :
    (P.complex.X (n - 1) ⟶ Y) →ₗ[R] (P.complex.X n ⟶ Y) :=
  if n = 0 then 0 else Linear.leftComp R Y (P.complex.d n (n - 1))

omit [HasExt C] in
private lemma homDifferential_comp_homIncoming (n : ℕ) :
    (homDifferential (R := R) P Y n).comp (homIncoming P Y n) = 0 := by
  cases n with
  | zero => simp [homIncoming]
  | succ n =>
    ext f
    simp [homIncoming, homDifferential, Linear.leftComp_apply, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma ker_cyclesToExt (n : ℕ) :
    (cyclesToExt (R := R) P Y n).ker =
      (homIncoming (R := R) P Y n).range.comap
        (homDifferential (R := R) P Y n).ker.subtype := by
  cases n with
  | zero =>
    ext f
    change P.extMk f.1 1 rfl f.2 = 0 ↔ _
    rw [extMk_zero_eq_zero_iff]
    simp [homIncoming]
  | succ n => simpa [homIncoming, homDifferential] using ker_cyclesToExt_succ P Y n

private def homologyEquivExt (n : ℕ) :
    ((homDifferential (R := R) P Y n).ker ⧸
      (homIncoming (R := R) P Y n).range.comap
        (homDifferential (R := R) P Y n).ker.subtype) ≃ₗ[R] Ext X Y n :=
  (Submodule.quotEquivOfEq _ _ (ker_cyclesToExt P Y n).symm).trans
    ((cyclesToExt P Y n).quotKerEquivOfSurjective (cyclesToExt_surjective P Y n))

/-- Transport of Ext classes along isomorphisms of source and target. -/
private def extCongrHom {Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Ext X Y n →ₗ[R] Ext X' Y' n :=
  ((Ext.mk₀ eY.hom).postcompOfLinear R X' (add_zero n)).comp
    ((Ext.mk₀ eX.inv).precompOfLinear R Y (zero_add n))

/-- Transporting along an iso and then its inverse is the identity. -/
private lemma extCongrHom_comp_symm {Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    (extCongrHom (R := R) eX eY n).comp (extCongrHom (R := R) eX.symm eY.symm n) =
      LinearMap.id := by
  ext x
  change ((Ext.mk₀ eX.inv).comp
    (((Ext.mk₀ eX.hom).comp x (zero_add n)).comp (Ext.mk₀ eY.inv) (add_zero n))
    (zero_add n)).comp (Ext.mk₀ eY.hom) (add_zero n) = x
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id]

private def extCongr {Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ₗ[R] Ext X' Y' n :=
  LinearEquiv.ofLinearMap (extCongrHom eX eY n) (extCongrHom eX.symm eY.symm n)
    (extCongrHom_comp_symm eX eY n) (extCongrHom_comp_symm eX.symm eY.symm n)

end Ext

section Modules

private lemma flat_ker_of_surjective
    {R P M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup M]
    [Module R P] [Module R M] [Module.Flat R P] [Module.Flat R M]
    (f : P →ₗ[R] M) (hf : Function.Surjective f) : Module.Flat R f.ker := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro V W _ _ _ _ g hg
  suffices h : Function.Injective
      ((f.ker.subtype.lTensor W).comp (g.rTensor f.ker)) from
    fun x y hxy => h (congrArg (f.ker.subtype.lTensor W) hxy)
  have hcomm : (f.ker.subtype.lTensor W).comp (g.rTensor f.ker) =
      (g.rTensor P).comp (f.ker.subtype.lTensor V) := by
    ext
    rfl
  rw [hcomm]
  exact (Module.Flat.rTensor_preserves_injective_linearMap (M := P) g hg).comp
    (LinearMap.lTensor_injective_of_exact_of_flat f hf f.ker.subtype
      f.ker.subtype_injective f.exact_subtype_ker_map V)

private lemma mem_smul_hom_of_forall_mem_of_free
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Free R P] [Module.Finite R P]
    (I : Ideal R) (f : P →ₗ[R] N)
    (hf : ∀ x, f x ∈ I • (⊤ : Submodule R N)) :
    f ∈ I • (⊤ : Submodule R (P →ₗ[R] N)) := by
  classical
  let b := Module.Free.chooseBasis R P
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex R P)
  let e := b.constr (M' := N) R
  let g := e.symm f
  have hg : g ∈ I • (⊤ : Submodule R (Module.Free.ChooseBasisIndex R P → N)) := by
    rw [← Finset.univ_sum_single g]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_top_le_comap_smul_top I (LinearMap.single R _ i)
    exact hf (b i)
  simpa [g] using Submodule.smul_top_le_comap_smul_top I e.toLinearMap hg

private lemma mem_smul_hom_of_forall_mem
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Finite R P]
    (I : Ideal R) (f : P →ₗ[R] N)
    (hf : ∀ x, f x ∈ I • (⊤ : Submodule R N)) :
    f ∈ I • (⊤ : Submodule R (P →ₗ[R] N)) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  have h := mem_smul_hom_of_forall_mem_of_free I (f.comp g) (fun x => hf (g x))
  have h' := Submodule.smul_top_le_comap_smul_top I (LinearMap.lcomp R N s) h
  change (f.comp g).comp s ∈ I • (⊤ : Submodule R (P →ₗ[R] N)) at h'
  simpa [LinearMap.comp_assoc, hs] using h'

private lemma ker_reduceModIdeal
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Finite R P]
    (I : Ideal R) :
    (LinearMap.reduceModIdeal I (M := P) (N := N)).ker =
      I • (⊤ : Submodule R (P →ₗ[R] N)) := by
  apply le_antisymm
  · intro f hf
    apply mem_smul_hom_of_forall_mem I f
    intro x
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact DFunLike.congr_fun (LinearMap.mem_ker.mp hf) (Submodule.Quotient.mk x)
  · intro f hf
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.smul_top_le_comap_smul_top I (LinearMap.applyₗ x) hf

private lemma reduceModIdeal_surjective
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P]
    (I : Ideal R) :
    Function.Surjective (LinearMap.reduceModIdeal I (M := P) (N := N)) := by
  intro f
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R N)).mkQ
    ((f.restrictScalars R).comp (I • (⊤ : Submodule R P)).mkQ)
    (Submodule.mkQ_surjective _)
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun hg x

private def quotientHomEquiv
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Finite R P]
    (I : Ideal R) :
    ((P →ₗ[R] N) ⧸ I • (⊤ : Submodule R (P →ₗ[R] N))) ≃ₗ[R]
      ((P ⧸ I • (⊤ : Submodule R P)) →ₗ[R ⧸ I]
        (N ⧸ I • (⊤ : Submodule R N))) :=
  (Submodule.quotEquivOfEq _ _ (ker_reduceModIdeal I).symm).trans
    ((LinearMap.reduceModIdeal I).quotKerEquivOfSurjective
      (reduceModIdeal_surjective I))

end Modules

section Reduction

universe u v

variable {R : Type u} [CommRing R]

private abbrev quotientFunctor (I : Ideal R) : ModuleCat.{v} R ⥤ ModuleCat.{v} (R ⧸ I) where
  obj M := ModuleCat.of (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))
  map f := ModuleCat.ofHom (LinearMap.reduceModIdeal I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

private lemma quotientFunctor_additive (I : Ideal R) : (quotientFunctor.{u, v} I).Additive where
  map_add := by intros; exact ModuleCat.hom_ext (map_add (LinearMap.reduceModIdeal I) _ _)

private def tensorQuotientEquiv (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] (M ⧸ I • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

private lemma projective_quotient [Small.{v} R] (I : Ideal R) (M : ModuleCat.{v} R)
    [Projective M] : Projective ((quotientFunctor I).obj M) := by
  have : Module.Projective R M := inferInstance
  have : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    Module.Projective.of_equiv (tensorQuotientEquiv I M)
  exact inferInstanceAs (Projective (ModuleCat.of (R ⧸ I)
    (M ⧸ I • (⊤ : Submodule R M))))

private lemma reduceModIdeal_exact_of_range_inf
    {K L M : Type*} [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (I : Ideal R) (f : K →ₗ[R] L) (g : L →ₗ[R] M)
    (hfg : Function.Exact f g)
    (hs : g.range ⊓ I • (⊤ : Submodule R M) ≤ I • g.range) :
    Function.Exact (LinearMap.reduceModIdeal I f) (LinearMap.reduceModIdeal I g) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    constructor
    · intro hy
      have hy' : g y ∈ I • (⊤ : Submodule R M) :=
        (Submodule.Quotient.mk_eq_zero _).mp hy
      have hmap : g y ∈ Submodule.map g (I • (⊤ : Submodule R L)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact hs ⟨g.mem_range_self y, hy'⟩
      obtain ⟨z, hz, hzy⟩ := hmap
      have hyz : g (y - z) = 0 := by rw [map_sub, hzy, sub_self]
      obtain ⟨x, hx⟩ := (hfg (y - z)).mp hyz
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      simpa [hx] using (Submodule.neg_mem _ hz)
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [← hx]
        change Submodule.Quotient.mk (g (f x)) = 0
        rw [hfg.apply_apply_eq_zero x, Submodule.Quotient.mk_zero]

set_option backward.isDefEq.respectTransparency false in
private def projectiveResolutionOfExact
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (M : ModuleCat.{v} R)
    [∀ n, Projective (K.X n)] (ε : K.X 0 ⟶ M) [Epi ε]
    (hε : K.d 1 0 ≫ ε = 0)
    (h₀ : (ShortComplex.mk (K.d 1 0) ε hε).Exact)
    (h : ∀ n, K.ExactAt (n + 1)) : ProjectiveResolution M where
  complex := K
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨h₀, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
          (by
            simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
            exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero ε hε).symm)
      all_goals simp
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact h n
      · apply ChainComplex.exactAt_succ_single_obj⟩

private def homReduction (I : Ideal R) (M N : ModuleCat.{v} R) :
    (M ⟶ N) →ₗ[R] ((quotientFunctor I).obj M ⟶ (quotientFunctor I).obj N) :=
  (ModuleCat.homLinearEquiv (S := R)).symm.toLinearMap.comp
    ((LinearMap.reduceModIdeal I).comp
      (ModuleCat.homLinearEquiv (S := R)).toLinearMap)

private lemma homReduction_apply (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    homReduction I M N f = (quotientFunctor I).map f := rfl

private lemma homReduction_surjective [Small.{v} R] (I : Ideal R)
    (M N : ModuleCat.{v} R) [Projective M] : Function.Surjective (homReduction I M N) :=
  (ModuleCat.homLinearEquiv (S := R)).symm.surjective.comp
    ((reduceModIdeal_surjective I).comp (ModuleCat.homLinearEquiv (S := R)).surjective)

private lemma ker_homReduction [Small.{v} R] (I : Ideal R)
    (M N : ModuleCat.{v} R) [Projective M] [Module.Finite R M] :
    (homReduction I M N).ker = I • (⊤ : Submodule R (M ⟶ N)) := by
  ext f
  let e := ModuleCat.homLinearEquiv (S := R)
    (M := (quotientFunctor I).obj M) (N := (quotientFunctor I).obj N)
  change e.symm (LinearMap.reduceModIdeal I f.hom) = 0 ↔ _
  rw [e.symm.map_eq_zero_iff]
  change f.hom ∈ (LinearMap.reduceModIdeal I).ker ↔ _
  rw [ker_reduceModIdeal]
  constructor
  · intro h
    exact Submodule.smul_top_le_comap_smul_top I
      (ModuleCat.homLinearEquiv (S := R) (M := M) (N := N)).symm.toLinearMap h
  · intro h
    exact Submodule.smul_top_le_comap_smul_top I
      (ModuleCat.homLinearEquiv (S := R) (M := M) (N := N)).toLinearMap h

/-- Reduction of a hom modulo `I` vanishes exactly on `I • ⊤`. -/
private lemma homReduction_eq_zero_iff [Small.{v} R] (I : Ideal R)
    (M N : ModuleCat.{v} R) [Projective M] [Module.Finite R M] (f : M ⟶ N) :
    homReduction I M N f = 0 ↔ f ∈ I • (⊤ : Submodule R (M ⟶ N)) := by
  rw [← ker_homReduction, LinearMap.mem_ker]

/-- The augmentation `P₀ → M` as an `R`-linear map. -/
private abbrev augmentation {M : ModuleCat.{v} R} (P : ProjectiveResolution M) :
    P.complex.X 0 →ₗ[R] M := (P.π.f 0).hom

/-- The augmentation of a projective resolution is surjective. -/
private lemma augmentation_surjective {M : ModuleCat.{v} R} (P : ProjectiveResolution M) :
    Function.Surjective (augmentation P) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The image of `d₁₀` is the kernel of the augmentation. -/
private lemma range_d_one_zero_eq_ker {M : ModuleCat.{v} R} (P : ProjectiveResolution M) :
    (P.complex.d 1 0).hom.range = (augmentation P).ker :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp P.exact₀

/-- The image of `d (n + 2) (n + 1)` is the kernel of `d (n + 1) n`. -/
private lemma range_d_succ_eq_ker {M : ModuleCat.{v} R} (P : ProjectiveResolution M) (n : ℕ) :
    (P.complex.d (n + 2) (n + 1)).hom.range = (P.complex.d (n + 1) n).hom.ker :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (P.exact_succ n)

end Reduction

section Relative

variable {A B P M : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

private lemma flat_ker_of_surjective_restrictScalars
    [Module.Flat A P] [Module.Flat A M]
    (f : P →ₗ[B] M) (hf : Function.Surjective f) : Module.Flat A f.ker :=
  flat_ker_of_surjective (f.restrictScalars A) hf

private lemma ker_inf_smul_map_of_flat [Module.Flat A M]
    (I : Ideal A) (f : P →ₗ[B] M) (hf : Function.Surjective f) :
    f.ker ⊓ I.map (algebraMap A B) • (⊤ : Submodule B P) =
      I.map (algebraMap A B) • f.ker := by
  apply Submodule.restrictScalars_injective A B P
  simpa only [Submodule.restrictScalars_inf, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top, LinearMap.ker_restrictScalars] using
    LinearMap.ker_inf_smul_top_eq_smul_of_flat I (f.restrictScalars A) hf

end Relative

section FlatResolution

universe uA uB v

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
  [Small.{v} B] [Module.Flat A B]
  {M : ModuleCat.{v} B} [Module A M] [IsScalarTower A B M] [Module.Flat A M]
  (P : ProjectiveResolution M)
  [∀ n, Module A (P.complex.X n)] [∀ n, IsScalarTower A B (P.complex.X n)]

private lemma flat_range_d (n : ℕ) :
    Module.Flat A (P.complex.d (n + 1) n).hom.range := by
  have hflat (k : ℕ) : Module.Flat A (P.complex.X k) :=
    Module.Flat.trans A B _
  induction n with
  | zero =>
    have := flat_ker_of_surjective_restrictScalars (A := A) (augmentation P)
      (augmentation_surjective P)
    exact (Module.Flat.equiv_iff
      ((LinearEquiv.ofEq _ _ (range_d_one_zero_eq_ker P)).restrictScalars A)).mpr this
  | succ n ih =>
    let f := (P.complex.d (n + 1) n).hom
    have := flat_ker_of_surjective_restrictScalars (A := A) f.rangeRestrict
      f.surjective_rangeRestrict
    have : Module.Flat A f.ker :=
      (Module.Flat.equiv_iff ((LinearEquiv.ofEq _ _ f.ker_rangeRestrict).restrictScalars A)).mp this
    exact (Module.Flat.equiv_iff
      ((LinearEquiv.ofEq _ _ (range_d_succ_eq_ker P n)).restrictScalars A)).mpr this

private lemma range_d_inf_smul_map (I : Ideal A) (n : ℕ) :
    (P.complex.d (n + 1) n).hom.range ⊓
        I.map (algebraMap A B) • (⊤ : Submodule B (P.complex.X n)) =
      I.map (algebraMap A B) • (P.complex.d (n + 1) n).hom.range := by
  cases n with
  | zero =>
    rw [range_d_one_zero_eq_ker]
    exact ker_inf_smul_map_of_flat I (augmentation P) (augmentation_surjective P)
  | succ n =>
    let f := (P.complex.d (n + 1) n).hom
    have : Module.Flat A f.range := flat_range_d (A := A) P n
    rw [range_d_succ_eq_ker, ← f.ker_rangeRestrict]
    exact ker_inf_smul_map_of_flat I f.rangeRestrict f.surjective_rangeRestrict

private def quotientResolution (I : Ideal A) :
    ProjectiveResolution ((quotientFunctor (I.map (algebraMap A B))).obj M) := by
  let J := I.map (algebraMap A B)
  let F := quotientFunctor.{uB, v} J
  haveI : F.Additive := quotientFunctor_additive J
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  haveI hproj (n : ℕ) : Projective (K.X n) := projective_quotient J (P.complex.X n)
  let ε : K.X 0 ⟶ F.obj M := F.map (P.π.f 0)
  have hε : K.d 1 0 ≫ ε = 0 := by
    change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
    rw [← F.map_comp, P.complex_d_comp_π_f_zero, F.map_zero]
  have hπ := augmentation_surjective P
  haveI : Epi ε := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := hπ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  apply projectiveResolutionOfExact K (F.obj M) ε hε
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact LinearMap.reduceModIdeal_exact J (P.complex.d 1 0).hom (P.π.f 0).hom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀) hπ
  · intro n
    apply (HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)).mpr
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact reduceModIdeal_exact_of_range_inf J
      (P.complex.d (n + 2) (n + 1)).hom (P.complex.d (n + 1) n).hom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n))
      (le_of_eq (range_d_inf_smul_map P I n))

private lemma quotientResolution_complex (I : Ideal A) :
    letI := quotientFunctor_additive (I.map (algebraMap A B))
    (quotientResolution P I).complex =
      ((quotientFunctor (I.map (algebraMap A B))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex := rfl

private lemma quotientResolution_d (I : Ideal A) (i j : ℕ) :
    (quotientResolution P I).complex.d i j =
      (quotientFunctor (I.map (algebraMap A B))).map (P.complex.d i j) := rfl

variable [∀ n, Module.Finite B (P.complex.X n)]

/-- A hom out of `P.X n` is a cocycle modulo `J = I B` iff its reduction is a cocycle for the
reduced resolution. -/
private lemma quotientResolution_d_comp_eq_zero_iff (I : Ideal A) (Y : ModuleCat.{v} B) (n : ℕ)
    (f : P.complex.X n ⟶ Y) :
    (quotientResolution P I).complex.d (n + 1) n ≫ (quotientFunctor (I.map (algebraMap A B))).map f
      = 0 ↔ homDifferential (R := B) P Y n f ∈
        I.map (algebraMap A B) • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y)) := by
  rw [← homReduction_eq_zero_iff, homReduction_apply]
  change _ = 0 ↔ (quotientFunctor _).map (P.complex.d (n + 1) n ≫ f) = 0
  rw [Functor.map_comp]
  rfl

-- Quotient scalar structures and transported Ext actions require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
private def reducedCyclesToExt (I : Ideal A) (Y : ModuleCat.{v} B) (i : ℕ) :
    ((I.map (algebraMap A B) •
      (⊤ : Submodule B (P.complex.X (i + 1) ⟶ Y))).comap
        (homDifferential (R := B) P Y i)) →ₗ[B]
      Ext ((quotientFunctor (I.map (algebraMap A B))).obj M)
        ((quotientFunctor (I.map (algebraMap A B))).obj Y) i := by
  let J := I.map (algebraMap A B)
  let F := quotientFunctor J
  let Q := quotientResolution P I
  have hf (f : (J • (⊤ : Submodule B (P.complex.X (i + 1) ⟶ Y))).comap
      (homDifferential (R := B) P Y i)) :
      Q.complex.d (i + 1) i ≫ F.map f.1 = 0 :=
    (quotientResolution_d_comp_eq_zero_iff P I Y i f.1).mpr f.property
  exact
    { toFun := fun f => Q.extMk (F.map f.1) (i + 1) rfl (hf f)
      map_add' := fun f g => by
        have : F.Additive := quotientFunctor_additive J
        simpa only [Submodule.coe_add, F.map_add] using
          (Q.add_extMk (F.map f.1) (F.map g.1) (i + 1) rfl (hf f) (hf g)).symm
      map_smul' := fun r f => by
        have hsmul : F.map (r • f.1) = r • F.map f.1 :=
          (homReduction J _ _).map_smul r f.1
        simpa only [Submodule.coe_smul, hsmul, RingHom.id_apply] using
          smul_extMk (R := B) Q (F.obj Y) i (F.map f.1) (hf f) r }

private lemma reducedCyclesToExt_surjective (I : Ideal A) (Y : ModuleCat.{v} B) (i : ℕ) :
    Function.Surjective (reducedCyclesToExt P I Y i) := by
  let J := I.map (algebraMap A B)
  let Q := quotientResolution P I
  intro x
  obtain ⟨f, hf, hfx⟩ := Q.extMk_surjective x (i + 1) rfl
  obtain ⟨g, hg⟩ := homReduction_surjective J (P.complex.X i) Y f
  have hg' : g ∈ (J • (⊤ : Submodule B (P.complex.X (i + 1) ⟶ Y))).comap
      (homDifferential (R := B) P Y i) := by
    rw [Submodule.mem_comap, ← quotientResolution_d_comp_eq_zero_iff]
    change _ ≫ homReduction J _ _ g = 0
    rw [hg]
    exact hf
  refine ⟨⟨g, hg'⟩, ?_⟩
  change Q.extMk (homReduction J _ _ g) (i + 1) rfl (by rw [hg]; exact hf) = x
  simpa only [hg] using hfx

-- Quotient scalar structures and transported Ext actions require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
private lemma ker_reducedCyclesToExt_succ (I : Ideal A) (Y : ModuleCat.{v} B) (n : ℕ) :
    let J := I.map (algebraMap A B)
    let Z := (J • (⊤ : Submodule B (P.complex.X (n + 2) ⟶ Y))).comap
      (homDifferential (R := B) P Y (n + 1))
    (reducedCyclesToExt P I Y (n + 1)).ker =
      ((homDifferential (R := B) P Y n).range ⊔
        J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y))).comap Z.subtype := by
  let J := I.map (algebraMap A B)
  let F := quotientFunctor J
  let Q := quotientResolution P I
  ext x
  have hxcycle : Q.complex.d (n + 2) (n + 1) ≫ F.map x.1 = 0 :=
    (quotientResolution_d_comp_eq_zero_iff P I Y (n + 1) x.1).mpr x.property
  change Q.extMk (F.map x.1) (n + 1 + 1) rfl hxcycle = 0 ↔
    x.1 ∈ (homDifferential (R := B) P Y n).range ⊔
      J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y))
  rw [Q.extMk_eq_zero_iff _ _ _ _ n rfl]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ := homReduction_surjective J (P.complex.X n) Y g
    have hz : x.1 - homDifferential (R := B) P Y n h ∈
        J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y)) := by
      rw [← homReduction_eq_zero_iff, map_sub]
      change F.map x.1 - F.map (P.complex.d (n + 1) n ≫ h) = 0
      rw [F.map_comp]
      apply sub_eq_zero.mpr
      exact hg.symm.trans (congrArg (fun k => Q.complex.d (n + 1) n ≫ k) hh.symm)
    have hx : x.1 = homDifferential (R := B) P Y n h +
        (x.1 - homDifferential (R := B) P Y n h) := by abel
    rw [hx]
    exact Submodule.add_mem_sup ⟨h, rfl⟩ hz
  · intro hx
    obtain ⟨a, ⟨h, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨homReduction J _ _ h, ?_⟩
    have hb' : homReduction J (P.complex.X (n + 1)) Y b = 0 :=
      (homReduction_eq_zero_iff _ _ _ _).mpr hb
    rw [← hab]
    change F.map (P.complex.d (n + 1) n) ≫ F.map h =
      homReduction J _ _ (homDifferential (R := B) P Y n h + b)
    rw [map_add, hb', add_zero]
    exact (F.map_comp _ _).symm

private def reducedHomologyEquivExtSucc (I : Ideal A) (Y : ModuleCat.{v} B) (n : ℕ) :
    let J := I.map (algebraMap A B)
    let Z := (J • (⊤ : Submodule B (P.complex.X (n + 2) ⟶ Y))).comap
      (homDifferential (R := B) P Y (n + 1))
    (Z ⧸ ((homDifferential (R := B) P Y n).range ⊔
        J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y))).comap Z.subtype) ≃ₗ[B]
      Ext ((quotientFunctor J).obj M) ((quotientFunctor J).obj Y) (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (ker_reducedCyclesToExt_succ P I Y n).symm).trans
    ((reducedCyclesToExt P I Y (n + 1)).quotKerEquivOfSurjective
      (reducedCyclesToExt_surjective P I Y (n + 1)))

-- Reducing the cohomology quotient elaborates several compatible scalar structures.
set_option backward.isDefEq.respectTransparency false in
private lemma ker_reducedCyclesToExt (I : Ideal A) (Y : ModuleCat.{v} B) (n : ℕ) :
    let J := I.map (algebraMap A B)
    let Z := (J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y))).comap
      (homDifferential (R := B) P Y n)
    (reducedCyclesToExt P I Y n).ker =
      ((homIncoming (R := B) P Y n).range ⊔
        J • (⊤ : Submodule B (P.complex.X n ⟶ Y))).comap Z.subtype := by
  cases n with
  | succ n =>
    simpa [homIncoming, homDifferential] using ker_reducedCyclesToExt_succ P I Y n
  | zero =>
    let J := I.map (algebraMap A B)
    let F := quotientFunctor J
    let Q := quotientResolution P I
    ext x
    have hxcycle : Q.complex.d 1 0 ≫ F.map x.1 = 0 :=
      (quotientResolution_d_comp_eq_zero_iff P I Y 0 x.1).mpr x.property
    change Q.extMk (F.map x.1) 1 rfl hxcycle = 0 ↔ _
    rw [extMk_zero_eq_zero_iff]
    change homReduction J _ _ x.1 = 0 ↔ _
    rw [homReduction_eq_zero_iff]
    simp [homIncoming, J]

private def reducedHomologyEquivExt (I : Ideal A) (Y : ModuleCat.{v} B) (n : ℕ) :
    let J := I.map (algebraMap A B)
    let Z := (J • (⊤ : Submodule B (P.complex.X (n + 1) ⟶ Y))).comap
      (homDifferential (R := B) P Y n)
    (Z ⧸ ((homIncoming (R := B) P Y n).range ⊔
        J • (⊤ : Submodule B (P.complex.X n ⟶ Y))).comap Z.subtype) ≃ₗ[B]
      Ext ((quotientFunctor J).obj M) ((quotientFunctor J).obj Y) n :=
  (Submodule.quotEquivOfEq _ _ (ker_reducedCyclesToExt P I Y n).symm).trans
    ((reducedCyclesToExt P I Y n).quotKerEquivOfSurjective
      (reducedCyclesToExt_surjective P I Y n))

end FlatResolution

universe uA uB uM uN

set_option maxHeartbeats 2400000 in
-- The Ext identifications carry quotient scalar structures in four universes.
/-- **Stacks 0EH0.** Let `A → B` be a flat map of Noetherian rings, let `I` be an
ideal of `A`, and let `M` and `N` be finite `B`-modules. If `M` is flat over `A`, the
canonical reduction maps from the `I`-adic quotients of `Ext_B(M, N)` to the Ext groups over
`B / I ^ n B` are compatible with all transition maps and induce an isomorphism on inverse
limits.

The maps are given simultaneously in every degree. Their identity, composition, reduction,
and quotient-factorization laws record the canonical inverse-system structure. The induced
map on limits is an isomorphism of `A`-modules. -/
@[stacks 0EH0]
public theorem limit_ext_quotient_iso_limit_ext_baseChange
    {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    [Module.Finite B M] [Module.Finite B N] [Module.Flat A M]
    (I : Ideal A) :
    let J := I.map (algebraMap A B)
    let E : ℕ → Type (max uA uB uM uN) := fun i =>
      Ext (ModuleCat.of B (ULift.{max uA uB uM uN} M))
        (ModuleCat.of B (ULift.{max uA uB uM uN} N)) i
    let _ : ∀ i, Module A (E i) := fun i =>
      Module.compHom (E i) (algebraMap A B)
    let Q : ℕ → ℕ → Type (max uA uB uM uN) := fun i n =>
      E i ⧸ I ^ n • (⊤ : Submodule A (E i))
    let Bn : ℕ → Type uB := fun n => B ⧸ J ^ n
    let Mn : ℕ → Type uM := fun n =>
      M ⧸ J ^ n • (⊤ : Submodule B M)
    let Nn : ℕ → Type uN := fun n =>
      N ⧸ J ^ n • (⊤ : Submodule B N)
    let En : ℕ → ℕ → Type (max uA uB uM uN) := fun i n =>
      Ext (ModuleCat.of (Bn n) (ULift.{max uA uB uM uN} (Mn n)))
        (ModuleCat.of (Bn n) (ULift.{max uA uB uM uN} (Nn n))) i
    let _ : ∀ i n, Module A (En i n) := fun i n =>
      Module.compHom (En i n) (algebraMap A (Bn n))
    ∃ (extTransition : ∀ i m n, n ≤ m → En i m →ₗ[A] En i n)
      (reduction : ∀ i n, E i →ₗ[A] En i n)
      (comparison : ∀ i n, Q i n →ₗ[A] En i n),
      (∀ i n, extTransition i n n le_rfl = LinearMap.id) ∧
      (∀ i k m n (hkm : m ≤ k) (hmn : n ≤ m),
        (extTransition i m n hmn).comp (extTransition i k m hkm) =
          extTransition i k n (hmn.trans hkm)) ∧
      (∀ i m n (hmn : n ≤ m),
        (extTransition i m n hmn).comp (reduction i m) = reduction i n) ∧
      (∀ i n,
        (comparison i n).comp (I ^ n • (⊤ : Submodule A (E i))).mkQ = reduction i n) ∧
      (∀ i m n (hmn : n ≤ m),
        (extTransition i m n hmn).comp (comparison i m) =
          (comparison i n).comp (Submodule.factorPow I (E i) hmn)) ∧
      ∀ i,
        let Qsys : Functor ℕᵒᵖ (ModuleCat.{max uA uB uM uN} A) :=
          Functor.ofOpSequence
            (X := fun n => ModuleCat.of A (Q i n))
            (fun n => ModuleCat.ofHom (Submodule.factorPowSucc I (E i) n))
        let Esys : Functor ℕᵒᵖ (ModuleCat.{max uA uB uM uN} A) :=
          Functor.ofOpSequence
            (X := fun n => ModuleCat.of A (En i n))
            (fun n => ModuleCat.ofHom
              (extTransition i (n + 1) n n.le_succ))
        ∃ e : limit Qsys ≅ limit Esys,
          ∀ n, e.hom ≫ limit.π Esys (op n) =
            limit.π Qsys (op n) ≫ ModuleCat.ofHom (comparison i n) := by
  classical
  dsimp only
  let J := I.map (algebraMap A B)
  let X := ModuleCat.of B (ULift.{max uA uB uM uN} M)
  let Y := ModuleCat.of B (ULift.{max uA uB uM uN} N)
  let E (i : ℕ) := Ext X Y i
  let (i : ℕ) : Module A (E i) := Module.compHom (E i) (algebraMap A B)
  let (i : ℕ) : IsScalarTower A B (E i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let En (i n : ℕ) :=
    Ext (ModuleCat.of (B ⧸ J ^ n)
      (ULift.{max uA uB uM uN} (M ⧸ J ^ n • (⊤ : Submodule B M))))
      (ModuleCat.of (B ⧸ J ^ n)
        (ULift.{max uA uB uM uN} (N ⧸ J ^ n • (⊤ : Submodule B N)))) i
  let (i n : ℕ) : Module A (En i n) := Module.compHom (En i n) (algebraMap A (B ⧸ J ^ n))
  let (i n : ℕ) : IsScalarTower A B (En i n) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    change (algebraMap B (B ⧸ J ^ n) (algebraMap A B a)) • x =
      algebraMap A (B ⧸ J ^ n) a • x
    rw [← IsScalarTower.algebraMap_apply A B (B ⧸ J ^ n)]
  have h : ∀ i, HasAdicComparison I (E i) (En i) := by
    intro i
    obtain ⟨P, hP⟩ := exists_finite_projectiveResolution B X
    let (n : ℕ) : Module.Finite B (P.complex.X n) := hP n
    let (n : ℕ) : Module A (P.complex.X n) :=
      Module.compHom (P.complex.X n) (algebraMap A B)
    let (n : ℕ) : IsScalarTower A B (P.complex.X n) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let (n : ℕ) : Module.Finite B (P.complex.X n ⟶ Y) :=
      Module.Finite.equiv (ModuleCat.homLinearEquiv (R := B) (S := B)
        (M := P.complex.X n) (N := Y)).symm
    apply adicComparison_of_complex (En i) I
      (homIncoming (R := B) P Y i) (homDifferential (R := B) P Y i)
      (homDifferential_comp_homIncoming P Y i) (homologyEquivExt P Y i)
    intro n
    let en := reducedHomologyEquivExt (A := A) P (I ^ n) Y i
    have en' :
        (((J ^ n • (⊤ : Submodule B (P.complex.X (i + 1) ⟶ Y))).comap
          (homDifferential (R := B) P Y i)) ⧸
          ((homIncoming (R := B) P Y i).range ⊔
            J ^ n • (⊤ : Submodule B (P.complex.X i ⟶ Y))).comap
              ((J ^ n • (⊤ : Submodule B (P.complex.X (i + 1) ⟶ Y))).comap
                (homDifferential (R := B) P Y i)).subtype) ≃ₗ[B]
        Ext ((quotientFunctor (J ^ n)).obj X) ((quotientFunctor (J ^ n)).obj Y) i := by
      dsimp only [J]
      rw [← Ideal.map_pow]
      exact en
    exact en'.trans (extCongr (R := B) (Y := (quotientFunctor (J ^ n)).obj Y)
      (quotientULiftEquiv.{uB, uM, max uA uB uM uN} (J ^ n) M).toModuleIso
      (quotientULiftEquiv.{uB, uN, max uA uB uM uN} (J ^ n) N).toModuleIso i)
  choose t r f ht hc hr hf hfn he using h
  exact ⟨t, r, f, ht, hc, hr, hf, hfn, he⟩

end Stacks.AdicSystem.ExtFlatBaseChange

end

end

end
