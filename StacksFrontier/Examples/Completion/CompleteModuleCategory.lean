module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.ArtinRees.Constant
import StacksCore.Tactic.StacksAttribute

/-!
# Kernels and cokernels of adically complete modules

Let `I` be a finitely generated ideal of a commutative ring `R`. The category of `I`-adically
complete `R`-modules, realized as the full subcategory of `ModuleCat R` cut out by
`IsAdicComplete I`, has kernels and cokernels.

Kernels are computed as in `ModuleCat R`: the inclusion of `ker f` into `M` is split by the
canonical map out of the completion of `ker f`, because the composite
`ker f → (ker f)^∧ → M` lands in `ker f` again and is the identity there; a module that retracts
off a complete module is complete, and `(ker f)^∧` is complete since `I` is finitely generated.

Cokernels are the completion of the cokernel in `ModuleCat R`. The universal property is the
one of completion: a map out of a module into a complete module factors uniquely through the
completion, because it is determined stagewise and the stages are the quotients by `Iⁿ`.

## Main definitions

* `Stacks.Examples.IAdicallyCompleteModuleCat`: the category of `I`-adically complete
  `R`-modules.

## Main results

* `Stacks.Examples.isAdicComplete_of_retraction`: a module that retracts off an adically
  complete module is adically complete.
* `Stacks.Examples.isAdicComplete_of_linearEquiv`: adic completeness transfers along a linear
  equivalence.
* `Stacks.Examples.hasKernels_iAdicallyCompleteModuleCat`: the category of adically complete
  modules has kernels.
* `Stacks.Examples.hasCokernels_iAdicallyCompleteModuleCat`: it has cokernels.

## Implementation notes

The notion of completeness is `IsAdicComplete`, that of Stacks 0317. Morphisms of the full
subcategory are precisely the underlying `R`-linear maps, so no separate description of the
morphisms is needed.

## References

* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace Stacks.Examples

/-- A linear map carries `Iⁿ • ⊤` into `Iⁿ • ⊤`. This is the `t = 0` case of the general
`map_pow_smul_top_le`, whose range hypothesis is then vacuous; it is stated separately because
it takes the exponent explicitly, which is what the use sites below need. -/
theorem map_pow_smul_top_le {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    Submodule.map f (I ^ n • (⊤ : Submodule R M)) ≤ I ^ n • (⊤ : Submodule R N) :=
  _root_.map_pow_smul_top_le f (t := 0) (by simp)

/-- A linear map preserves congruence modulo `Iⁿ • ⊤`. -/
private theorem map_sModEq_pow_smul_top {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) {n : ℕ} {x y : M} (h : x ≡ y [SMOD I ^ n • (⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD I ^ n • (⊤ : Submodule R N)] :=
  SModEq.mono (map_pow_smul_top_le f n) (SModEq.map h f)

/-- A module which retracts off an `I`-adically complete module is `I`-adically complete. -/
theorem isAdicComplete_of_retraction {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (s : M →ₗ[R] N) (r : N →ₗ[R] M) (hsr : r.comp s = LinearMap.id)
    (hN : IsAdicComplete I N) : IsAdicComplete I M := by
  let _ : IsAdicComplete I N := hN
  have hHaus : IsHausdorff I M := ⟨fun x hx => by
    have hsx : s x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff I N) (s x) fun n => by
      simpa using map_sModEq_pow_smul_top s (hx n)
    simpa [← LinearMap.comp_apply, hsr] using congrArg r hsx⟩
  have hPre : IsPrecomplete I M := ⟨fun f hf => by
    have hfc : ∀ {m n}, m ≤ n → s (f m) ≡ s (f n)
        [SMOD (I ^ m • (⊤ : Submodule R N))] := fun hmn => map_sModEq_pow_smul_top s (hf hmn)
    obtain ⟨y, hy⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I N) hfc
    refine ⟨r y, fun n => ?_⟩
    have hn := map_sModEq_pow_smul_top r (hy n)
    change r (s (f n)) ≡ r y [SMOD (I ^ n • (⊤ : Submodule R M))] at hn
    simpa only [← LinearMap.comp_apply, hsr, LinearMap.id_apply] using hn⟩
  let _ := hHaus
  let _ := hPre
  exact ⟨⟩

/-- Adic completeness transfers along a linear equivalence. -/
theorem isAdicComplete_of_linearEquiv {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hN : IsAdicComplete I N) : IsAdicComplete I M :=
  isAdicComplete_of_retraction e.toLinearMap e.symm.toLinearMap (by ext x; simp) hN

/-- The category of `I`-adically complete `R`-modules. -/
abbrev IAdicallyCompleteModuleCat (R : Type u) [CommRing R] (I : Ideal R) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{v} R => IsAdicComplete I M)

private theorem isAdicComplete_ker
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hM : IsAdicComplete I M)
    (hN : IsAdicComplete I N) : IsAdicComplete I f.ker := by
  let _ : IsAdicComplete I M := hM
  let _ : IsAdicComplete I N := hN
  let eM := AdicCompletion.ofLinearEquiv I M
  let eN := AdicCompletion.ofLinearEquiv I N
  have heM : eM.toLinearMap = AdicCompletion.of I M := rfl
  have heN : eN.toLinearMap = AdicCompletion.of I N := rfl
  let K := f.ker
  let inc : K →ₗ[R] M := K.subtype
  let cMap : AdicCompletion I K →ₗ[R] AdicCompletion I M :=
    (AdicCompletion.map I inc).restrictScalars R
  let g : AdicCompletion I K →ₗ[R] M := eM.symm.toLinearMap.comp cMap
  have hzero : ∀ x, f (g x) = 0 := by
    intro x
    have hn : AdicCompletion.of I N (f (eM.symm (cMap x))) = 0 := by
      rw [← AdicCompletion.map_of I f (eM.symm (cMap x))]
      have hrec : AdicCompletion.of I M (eM.symm (cMap x)) = cMap x := by
        rw [← heM]; exact eM.apply_symm_apply _
      rw [hrec]
      show ((AdicCompletion.map I f).comp (AdicCompletion.map I inc)) x = 0
      rw [AdicCompletion.map_comp]
      have hcomp : f.comp inc = 0 := by ext z; exact z.property
      simp [hcomp, AdicCompletion.map_zero]
    have hinj : Function.Injective (AdicCompletion.of I N) := by rw [← heN]; exact eN.injective
    exact hinj hn
  let r : AdicCompletion I K →ₗ[R] K := g.codRestrict K hzero
  have hsplit : r.comp (AdicCompletion.of I K) = LinearMap.id := by
    ext x
    show eM.symm (AdicCompletion.map I inc (AdicCompletion.of I K x)) = x.val
    rw [AdicCompletion.map_of]
    have hinc : AdicCompletion.of I M (inc x) = eM (inc x) :=
      (DFunLike.congr_fun heM (inc x)).symm
    rw [hinc]
    show eM.symm (eM (inc x)) = inc x
    exact eM.symm_apply_apply _
  exact isAdicComplete_of_retraction (I := I) (AdicCompletion.of I K) r hsplit
    (AdicCompletion.isAdicComplete hI)

/-- **Stacks 07JR.** If `I` is a finitely generated ideal of `R`, then the category of
`I`-adically complete `R`-modules has kernels. -/
@[stacks 07JR "kernels"]
theorem hasKernels_iAdicallyCompleteModuleCat
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    HasKernels (IAdicallyCompleteModuleCat.{v} R I) := by
  let P : ObjectProperty (ModuleCat.{v} R) := fun M => IsAdicComplete I M
  have hP : P.IsClosedUnderKernels := by
    constructor
    rintro X ⟨f, k, hk, hM, hN⟩
    exact isAdicComplete_of_linearEquiv
      (hk.conePointUniqueUpToIso (ModuleCat.kernelIsLimit f)).toLinearEquiv
      (isAdicComplete_ker I hI f.hom hM hN)
  let _ : HasKernels (ModuleCat.{v} R) := ModuleCat.hasKernels_moduleCat
  exact P.instHasKernelsFullSubcategoryOfIsClosedUnderKernels

private noncomputable def adicCompleteFamily
    (R : Type u) [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (n : ℕ) :
    AdicCompletion I M →ₗ[R] N ⧸ (I ^ n • (⊤ : Submodule R N)) :=
  ((g.reduceModIdeal (I ^ n)).restrictScalars R).comp (AdicCompletion.eval I M n)

private theorem adicCompleteFamily_compatible
    (R : Type u) [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) {m n : ℕ} (hmn : m ≤ n) :
    Submodule.factorPow I N hmn ∘ₗ adicCompleteFamily R I M N g n =
      adicCompleteFamily R I M N g m := by
  ext x
  apply (Submodule.Quotient.eq _).2
  have hmem : g (x m - x n) ∈ I ^ m • (⊤ : Submodule R N) :=
    map_pow_smul_top_le (I := I) g m ⟨x m - x n, SModEq.sub_mem.mp (x.property hmn), rfl⟩
  simpa [map_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Submodule.neg_mem (I ^ m • (⊤ : Submodule R N)) hmem)

private noncomputable def adicCompleteLift
    (R : Type u) [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsAdicComplete I N] (g : M →ₗ[R] N) : AdicCompletion I M →ₗ[R] N :=
  IsAdicComplete.lift I
    (adicCompleteFamily R I M N g)
    (adicCompleteFamily_compatible R I M N g)

private theorem adicCompleteLift_comp_of
    (R : Type u) [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsAdicComplete I N] (g : M →ₗ[R] N) :
    (adicCompleteLift R I M N g).comp (AdicCompletion.of I M) = g := by
  refine LinearMap.ext fun x => ?_
  apply (AdicCompletion.of_injective_iff (I := I) (M := N)).2 inferInstance
  ext n
  simp [adicCompleteLift, adicCompleteFamily, LinearMap.reduceModIdeal_apply]

private theorem adicCompleteLift_of_apply
    (R : Type u) [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsAdicComplete I N] (g : M →ₗ[R] N) (x : M) :
    adicCompleteLift R I M N g (AdicCompletion.of I M x) = g x :=
  LinearMap.congr_fun (adicCompleteLift_comp_of R I M N g) x

private theorem adicCompleteLift_unique
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsAdicComplete I N] (g : M →ₗ[R] N)
    (m : AdicCompletion I M →ₗ[R] N)
    (hm : m.comp (AdicCompletion.of I M) = g) :
    m = adicCompleteLift R I M N g := by
  apply IsAdicComplete.eq_lift I (adicCompleteFamily_compatible R I M N g)
  intro n
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule R M)) (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M y ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    show AdicCompletion.eval I M n (x - AdicCompletion.of I M y) = 0
    simp [hy]
  have hmem : m (x - AdicCompletion.of I M y) ∈ I ^ n • (⊤ : Submodule R N) :=
    map_pow_smul_top_le (I := I) m n ⟨x - AdicCompletion.of I M y, hx, rfl⟩
  show Submodule.mkQ _ (m x) =
    g.reduceModIdeal (I ^ n) (AdicCompletion.eval I M n x)
  rw [← hy, LinearMap.reduceModIdeal_apply]
  apply (Submodule.Quotient.eq _).2
  rw [← LinearMap.congr_fun hm y]
  simpa only [map_sub, LinearMap.comp_apply] using hmem

/-- **Stacks 07JR.** If `I` is a finitely generated ideal of `R`, then the category of
`I`-adically complete `R`-modules has cokernels. -/
@[stacks 07JR "cokernels"]
theorem hasCokernels_iAdicallyCompleteModuleCat
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    HasCokernels (IAdicallyCompleteModuleCat.{v} R I) := by
  let _ : HasCokernels (ModuleCat R) := ModuleCat.hasCokernels_moduleCat
  refine ⟨?_⟩
  intro X Y f
  let Q : ModuleCat.{v} R := cokernel f.hom
  let K : IAdicallyCompleteModuleCat.{v} R I :=
    ⟨ModuleCat.of R (AdicCompletion I Q), AdicCompletion.isAdicComplete hI⟩
  let πₗ : Y.obj →ₗ[R] AdicCompletion I Q :=
    (AdicCompletion.of I Q).comp (cokernel.π f.hom).hom
  let π : Y ⟶ K := ObjectProperty.homMk (ModuleCat.ofHom πₗ)
  have hzero : f ≫ π = 0 := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    simp [π, πₗ]
  let c : CokernelCofork f := CokernelCofork.ofπ π hzero
  have hk' : ∀ {Z : IAdicallyCompleteModuleCat.{v} R I} {k : Y ⟶ Z}, f ≫ k = 0 →
      f.hom ≫ k.hom = 0 := fun {Z} {_} hk => by
    simpa using congrArg (fun e : X ⟶ Z => e.hom) hk
  have hc : IsColimit c := by
    refine CokernelCofork.IsColimit.ofπ π hzero
      (fun {Z} k hk => ?_) (fun {Z} k hk => ?_) (fun {Z} k hk m hm => ?_)
    · let _ : IsAdicComplete I Z.obj := Z.property
      exact ObjectProperty.homMk (ModuleCat.ofHom
        (adicCompleteLift R I Q Z.obj (cokernel.desc f.hom k.hom (hk' hk)).hom))
    · let _ : IsAdicComplete I Z.obj := Z.property
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun y => ?_
      show adicCompleteLift R I Q Z.obj (cokernel.desc f.hom k.hom (hk' hk)).hom
          (AdicCompletion.of I Q ((cokernel.π f.hom).hom y)) = k.hom y
      rw [adicCompleteLift_of_apply]
      exact congrArg (fun e : Y.obj ⟶ Z.obj => e.hom y) (cokernel.π_desc f.hom k.hom (hk' hk))
    · let _ : IsAdicComplete I Z.obj := Z.property
      let qdesc := cokernel.desc f.hom k.hom (hk' hk)
      have hfac : ModuleCat.ofHom (AdicCompletion.of I Q) ≫ m.hom = qdesc := by
        apply (cancel_epi (cokernel.π f.hom)).1
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun y => ?_
        calc
          m.hom.hom (AdicCompletion.of I Q ((cokernel.π f.hom).hom y)) = k.hom y := by
            simpa [π, πₗ, ModuleCat.comp_apply] using congrArg (fun e : Y ⟶ Z => e.hom y) hm
          _ = qdesc.hom ((cokernel.π f.hom).hom y) :=
            (congrArg (fun e : Y.obj ⟶ Z.obj => e.hom y)
              (cokernel.π_desc f.hom k.hom (hk' hk))).symm
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      exact adicCompleteLift_unique R I hI Q Z.obj qdesc.hom m.hom.hom
        (congrArg (fun e : Q ⟶ Z.obj => e.hom) hfac)
  exact HasColimit.mk ⟨c, hc⟩

end Stacks.Examples

end
