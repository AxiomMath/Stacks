module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.LinearAlgebra.Basis.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# Naturality of the canonical obstruction map

For a square-zero surjection `R' → R` of commutative rings, the canonical obstruction morphism
`ω_K : K ⟶ (K ⊗ᴸ_R I)[2]` of a bounded-above object `K` of `D(R)` is natural in `K`: for every
morphism `g : K ⟶ K'` of bounded-above objects, `g ≫ ω_{K'} = ω_K ≫ (g ⊗ᴸ 1)[2]`.

The proof is the one in the source: lift both complexes to bounded-above complexes of free
`R'`-modules, lift `g` degreewise to the free lifts, and compare the two squares of lifted
differentials. The defect of the lifted `g` from being a chain map takes values in the kernel
ideal, so it provides the homotopy that identifies the two composites in `D(R)`.

## Main results

* `Deformation.Obstruction.canonicalObstructionMap_natural`: the canonical obstruction morphisms
  commute with every morphism of bounded-above objects of `D(R)`.

## Implementation notes

The derived tensor product of a morphism with the kernel object is expressed by the canonical
derived tensor bifunctor, and then shifted by two. The underlying morphism of the specified
canonical obstruction map is its `.val` projection.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/

@[expose] public section


open CategoryTheory CategoryTheory.MonoidalCategory CochainComplex.DerivedTensor
open Deformation.Obstruction HomologicalComplex
attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Obstruction

universe u

private lemma kernelTensorInclusion_map {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (u : P ⟶ Q) (n : ℤ)
    (x : P.X n) (a : squareZeroKernelModule f hf) :
    (mapBifunctorMap u (𝟙 (kernelComplex f hf)) (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).f n (kernelTensorInclusion f hf P n (x ⊗ₜ[R] a)) =
        kernelTensorInclusion f hf Q n (u.f n x ⊗ₜ[R] a) := by
  have h : kernelTensorInclusion f hf P n ≫
      (mapBifunctorMap u (𝟙 (kernelComplex f hf)) (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).f n =
      (u.f n ⊗ₘ 𝟙 (squareZeroKernelModule f hf)) ≫ kernelTensorInclusion f hf Q n := by
    simp only [kernelTensorInclusion, Category.assoc, ι_mapBifunctorMap,
      HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map]
    simp [← Category.assoc, whisker_exchange, kernelComplex,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  exact ConcreteCategory.congr_hom h (x ⊗ₜ[R] a)

private lemma kernelEmbedding_map {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {LP : FreeDifferentialLift f P} {LQ : FreeDifferentialLift f Q}
    (cP : LiftedDifferentialCurvature f hf P LP)
    (cQ : LiftedDifferentialCurvature f hf Q LQ)
    (u : P ⟶ Q) (U : ∀ n, LP.X n →ₗ[R'] LQ.X n)
    (hU : ∀ n x, LQ.reduction n (U n x) = u.f n (LP.reduction n x))
    (n : ℤ) (z : (P ⊗ kernelComplex f hf).X n) :
    cQ.kernelEmbedding n
      ((mapBifunctorMap u (𝟙 (kernelComplex f hf)) (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).f n z) = U n (cP.kernelEmbedding n z) := by
  refine kernelTensor_induction LP n
    (fun z => cQ.kernelEmbedding n
      ((mapBifunctorMap u (𝟙 (kernelComplex f hf)) (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).f n z) = U n (cP.kernelEmbedding n z)) ?_ ?_ ?_ z
  · simp
  · intro z w hz hw
    simp only [map_add, hz, hw]
  · intro x a
    rw [kernelTensorInclusion_map, ← hU, cQ.kernelEmbedding_tmul,
      cP.kernelEmbedding_tmul, map_smul]

private lemma exists_hom_map_eq_of_isKProjective {R : Type u} [CommRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    [P.IsKProjective]
    (α : (DerivedCategory.Q).obj P ⟶ (DerivedCategory.Q).obj Q) :
    ∃ γ : P ⟶ Q, (DerivedCategory.Q).map γ = α := by
  have hbij := (Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app P)
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app Q)).bijective.comp
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj Q))
  obtain ⟨φ, hφ⟩ := hbij.surjective α
  obtain ⟨γ, hγ⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective φ
  refine ⟨γ, ?_⟩
  rw [← hφ, ← hγ]
  simp only [Function.comp_apply, Iso.homCongr_apply, Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

private noncomputable def liftComponent {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : Deformation.Obstruction.FreeDifferentialLift f P)
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (u : P ⟶ Q) (n : ℤ) : LP.X n →ₗ[R'] LQ.X n := by
  letI : Module.Free R' (LP.X n) := LP.free n
  let b := Module.Free.chooseBasis R' (LP.X n)
  exact b.constr R' (fun i => Classical.choose
    (LQ.reduction_surjective n (u.f n (LP.reduction n (b i)))))

private lemma reduction_liftComponent {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : Deformation.Obstruction.FreeDifferentialLift f P)
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (u : P ⟶ Q) (n : ℤ) (x : LP.X n) :
    LQ.reduction n (liftComponent f LP LQ u n x) =
      u.f n (LP.reduction n x) := by
  classical
  have : Module.Free R' (LP.X n) := LP.free n
  let b := Module.Free.chooseBasis R' (LP.X n)
  rw [liftComponent, b.constr_apply]
  conv_rhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Classical.choose_spec
    (LQ.reduction_surjective n (u.f n (LP.reduction n (b i))))]

private noncomputable def liftDefect {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : Deformation.Obstruction.FreeDifferentialLift f P)
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (u : P ⟶ Q) (n : ℤ) : LP.X n →ₗ[R'] LQ.X (n + 1) :=
  (LQ.d n (n + 1)).hom.comp (liftComponent f LP LQ u n) -
    (liftComponent f LP LQ u (n + 1)).comp (LP.d n (n + 1)).hom

private lemma reduction_liftDefect {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : Deformation.Obstruction.FreeDifferentialLift f P)
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (u : P ⟶ Q) (n : ℤ) (x : LP.X n) :
    LQ.reduction (n + 1) (liftDefect f LP LQ u n x) = 0 := by
  simp only [liftDefect, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    LQ.reduction_d, LP.reduction_d, reduction_liftComponent]
  exact sub_eq_zero.mpr (ConcreteCategory.congr_hom (u.comm n (n + 1)) (LP.reduction n x))

private lemma liftDefect_eq_zero_of_reduction_eq_zero {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : Deformation.Obstruction.FreeDifferentialLift f P)
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (u : P ⟶ Q) (n : ℤ) (x : LP.X n)
    (hx : LP.reduction n x = 0) : liftDefect f LP LQ u n x = 0 := by
  let I := RingHom.ker f
  have hI : I • (I • (⊤ : Submodule R' (LQ.X (n + 1)))) = ⊥ := by
    rw [smul_smul, ← pow_two I, hzero, Submodule.bot_smul]
  have hδrange (y : LP.X n) :
      liftDefect f LP LQ u n y ∈ I • (⊤ : Submodule R' (LQ.X (n + 1))) := by
    rw [← LQ.reduction_ker]
    exact LinearMap.mem_ker.mpr (reduction_liftDefect f LP LQ u n y)
  have hxI : x ∈ I • (⊤ : Submodule R' (LP.X n)) := by
    rwa [← LP.reduction_ker, LinearMap.mem_ker]
  have hvanish : I • (⊤ : Submodule R' (LP.X n)) ≤ LinearMap.ker (liftDefect f LP LQ u n) := by
    rw [Submodule.smul_le]
    intro a ha y hy
    rw [LinearMap.mem_ker, map_smul]
    simpa only [hI, Submodule.mem_bot] using Submodule.smul_mem_smul ha (hδrange y)
  exact LinearMap.mem_ker.mp (hvanish hxI)

private lemma exists_kernelEmbedding_preimage_of_reduction_eq_zero
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LQ : Deformation.Obstruction.FreeDifferentialLift f Q)
    (cQ : Deformation.Obstruction.LiftedDifferentialCurvature f hf Q LQ)
    (n : ℤ) (x : LQ.X n) (hx : LQ.reduction n x = 0) :
    ∃ z, cQ.kernelEmbedding n z = x := by
  classical
  let I := RingHom.ker f
  have hxI : x ∈ I • (⊤ : Submodule R' (LQ.X n)) := by
    rwa [← LQ.reduction_ker, LinearMap.mem_ker]
  have hxspan : x ∈ I • Submodule.span R' (Set.range (fun y : LQ.X n => y)) := by
    simpa using hxI
  obtain ⟨a, ha, hsum⟩ :=
    I.mem_ideal_smul_span_iff_exists_sum (fun y : LQ.X n => y) x |>.mp hxspan
  refine ⟨a.sum fun y _ => kernelTensorInclusion f hf Q n
      (LQ.reduction n y ⊗ₜ[R]
        (show squareZeroKernelModule f hf from
          (RingHom.ker f).toCotangent ⟨a y, ha y⟩)), ?_⟩
  rw [map_finsuppSum, ← hsum]
  exact Finsupp.sum_congr fun y _ => cQ.kernelEmbedding_tmul n y ⟨a y, ha y⟩

private noncomputable def reductionPreimage {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : FreeDifferentialLift f P) (n : ℤ) (x : P.X n) : LP.X n :=
  Classical.choose (LP.reduction_surjective n x)

private lemma reduction_reductionPreimage {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : FreeDifferentialLift f P) (n : ℤ) (x : P.X n) :
    LP.reduction n (reductionPreimage f LP n x) = x :=
  Classical.choose_spec (LP.reduction_surjective n x)

private noncomputable def kernelEmbeddingPreimage {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : FreeDifferentialLift f P) (LQ : FreeDifferentialLift f Q)
    (cQ : LiftedDifferentialCurvature f hf Q LQ) (n : ℤ)
    (δ : LP.X n →ₗ[R'] LQ.X (n + 1))
    (hδred : ∀ x, LQ.reduction (n + 1) (δ x) = 0) (x : P.X n) :
    (Q ⊗ kernelComplex f hf).X (n + 1) :=
  Classical.choose (exists_kernelEmbedding_preimage_of_reduction_eq_zero f hf LQ cQ (n + 1)
    (δ (reductionPreimage f LP n x)) (hδred (reductionPreimage f LP n x)))

private lemma kernelEmbedding_kernelEmbeddingPreimage {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : FreeDifferentialLift f P) (LQ : FreeDifferentialLift f Q)
    (cQ : LiftedDifferentialCurvature f hf Q LQ) (n : ℤ)
    (δ : LP.X n →ₗ[R'] LQ.X (n + 1))
    (hδred : ∀ x, LQ.reduction (n + 1) (δ x) = 0) (x : P.X n) :
    cQ.kernelEmbedding (n + 1) (kernelEmbeddingPreimage f hf LP LQ cQ n δ hδred x) =
      δ (reductionPreimage f LP n x) :=
  Classical.choose_spec (exists_kernelEmbedding_preimage_of_reduction_eq_zero f hf LQ cQ (n + 1)
    (δ (reductionPreimage f LP n x)) (hδred (reductionPreimage f LP n x)))

/-- A map killing the kernel of the reduction takes equal values on elements with equal
reductions. -/
private lemma eq_of_reduction_eq {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {LP : FreeDifferentialLift f P} {n : ℤ} {M : Type u} [AddCommGroup M] [Module R' M]
    (δ : LP.X n →ₗ[R'] M) (hδker : ∀ x, LP.reduction n x = 0 → δ x = 0)
    {x y : LP.X n} (h : LP.reduction n x = LP.reduction n y) : δ x = δ y :=
  sub_eq_zero.mp (by simpa only [map_sub] using hδker (x - y) (by rw [map_sub, h, sub_self]))

private noncomputable def factorThroughKernelTensor {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (LP : FreeDifferentialLift f P) (LQ : FreeDifferentialLift f Q)
    (cQ : LiftedDifferentialCurvature f hf Q LQ)
    (n : ℤ) (δ : LP.X n →ₗ[R'] LQ.X (n + 1))
    (hδred : ∀ x, LQ.reduction (n + 1) (δ x) = 0)
    (hδker : ∀ x, LP.reduction n x = 0 → δ x = 0) :
    (P.X n) →ₗ[R] ((Q ⊗ kernelComplex f hf).X (n + 1)) := by
  classical
  let rep : P.X n → LP.X n := fun x => reductionPreimage f LP n x
  let z : P.X n → (Q ⊗ kernelComplex f hf).X (n + 1) := fun x =>
    kernelEmbeddingPreimage f hf LP LQ cQ n δ hδred x
  have hrep (x : P.X n) : LP.reduction n (rep x) = x :=
    reduction_reductionPreimage f LP n x
  have hz (x : P.X n) : cQ.kernelEmbedding (n + 1) (z x) = δ (rep x) :=
    kernelEmbedding_kernelEmbeddingPreimage f hf LP LQ cQ n δ hδred x
  refine
    { toFun := z
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply cQ.kernelEmbedding_injective
    rw [map_add, hz, hz, hz, ← map_add]
    exact eq_of_reduction_eq δ hδker (by simp only [map_add, hrep])
  · intro r x
    obtain ⟨r', hr'⟩ := hf r
    apply cQ.kernelEmbedding_injective
    calc
      cQ.kernelEmbedding (n + 1) (z (r • x)) = δ (rep (r • x)) := hz _
      _ = δ (r' • rep x) :=
        eq_of_reduction_eq δ hδker (by rw [map_smulₛₗ, hr', hrep, hrep])
      _ = cQ.kernelEmbedding (n + 1) (f r' • z x) := by
        rw [map_smul, kernelEmbedding_smul cQ, hz]
      _ = cQ.kernelEmbedding (n + 1) (r • z x) := by rw [hr']

universe v

private noncomputable def homotopyOfComponents
    {V : Type u} [Category.{v} V] [Preadditive V]
    {P T : CochainComplex V ℤ} (a b : P ⟶ T⟦(2 : ℤ)⟧)
    (H : ∀ i j : ℤ, i + 1 = j → (P.X i ⟶ T.X j))
    (hH : ∀ n, a.f n = P.d n (n + 1) ≫ H (n + 1) (n + 2) (by omega) +
      H n (n + 1) rfl ≫ T.d (n + 1) (n + 2) +
        (show P.X n ⟶ T.X (n + 2) from b.f n)) : Homotopy a b where
  hom i j := if h : j + 1 = i then H i (j + 2) (by omega) else 0
  zero i j h := dite_eq_right h
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from Int.sub_add_cancel n 1),
      dite_eq_left rfl, dite_eq_left (show n - 1 + 1 = n by omega)]
    simp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_d',
      show Int.negOnePow 2 = 1 by decide, one_smul]
    have hc (j : ℤ) (h : n + 1 = j) :
        H n j h ≫ T.d j (n + 2) = H n (n + 1) rfl ≫ T.d (n + 1) (n + 2) := by
      subst j
      rfl
    rw [hc]
    exact hH n

private lemma comparison_natural_of_resolution
    {R : Type u} [CommRing R] (T : DerivedTensorProduct R)
    {P Q A B : CochainComplex (ModuleCat.{u} R) ℤ}
    (u : P ⟶ Q) (r : A ⟶ B) (hP : P.KFlat) (hQ : Q.KFlat) (hA : A.KFlat)
    [IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ r))]
    [IsIso (DerivedCategory.Q.map (𝟙 Q ⊗ₘ r))] :
    DerivedCategory.Q.map (u ⊗ₘ 𝟙 B) ≫
      inv (DerivedCategory.Q.map (𝟙 Q ⊗ₘ r)) ≫ (T.comparison Q A hQ hA).inv ≫
        (T.tensor.obj (DerivedCategory.Q.obj Q)).map (DerivedCategory.Q.map r) =
    inv (DerivedCategory.Q.map (𝟙 P ⊗ₘ r)) ≫ (T.comparison P A hP hA).inv ≫
      (T.tensor.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map r) ≫
        (T.tensor.map (DerivedCategory.Q.map u)).app (DerivedCategory.Q.obj B) := by
  have hs : DerivedCategory.Q.map (𝟙 P ⊗ₘ r) ≫ DerivedCategory.Q.map (u ⊗ₘ 𝟙 B) =
      DerivedCategory.Q.map (u ⊗ₘ 𝟙 A) ≫ DerivedCategory.Q.map (𝟙 Q ⊗ₘ r) := by
    simp only [← Functor.map_comp, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hc : DerivedCategory.Q.map (u ⊗ₘ 𝟙 A) ≫ (T.comparison Q A hQ hA).inv =
      (T.comparison P A hP hA).inv ≫
        (T.tensor.map (DerivedCategory.Q.map u)).app (DerivedCategory.Q.obj A) := by
    apply (cancel_mono (T.comparison Q A hQ hA).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := T.comparison_naturality u (𝟙 A) hP hQ hA hA
    rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj Q)).map_id,
      Category.id_comp] at h
    rw [h, Iso.inv_hom_id_assoc]
    rfl
  apply (cancel_epi (DerivedCategory.Q.map (𝟙 P ⊗ₘ r))).1
  simp only [← Category.assoc] at hs ⊢
  rw [hs]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hc, Category.assoc]
  exact congrArg ((T.comparison P A hP hA).inv ≫ ·)
    (((T.tensor.map (DerivedCategory.Q.map u)).naturality (DerivedCategory.Q.map r)).symm)

/-- The canonical obstruction morphism commutes with every morphism of bounded-above
derived complexes. -/
@[stacks 0DYR "naturality"]
theorem canonicalObstructionMap_natural
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K)
    (hL : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus L)
    (g : K ⟶ L) :
    g ≫ (Deformation.Obstruction.canonicalObstructionMap
      f hf hzero L hL).val =
      (Deformation.Obstruction.canonicalObstructionMap
        f hf hzero K hK).val ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
          (((canonicalDerivedTensorProductFunctor R).map g).app
            (Deformation.Obstruction.squareZeroKernelObject f hf)) := by
  classical
  have wK := (Deformation.Obstruction.canonicalObstructionMap f hf hzero K hK).property
  have wL := (Deformation.Obstruction.canonicalObstructionMap f hf hzero L hL).property
  obtain ⟨P, bP, hPbound, hPfree, eP⟩ := wK.exists_free_representative
  obtain ⟨Q, bQ, hQbound, hQfree, eQ⟩ := wL.exists_free_representative
  obtain ⟨LP⟩ := wK.exists_lift P hPfree
  obtain ⟨LQ⟩ := wL.exists_lift Q hQfree
  obtain ⟨cP⟩ := wK.exists_curvature P bP hPbound hPfree LP
  obtain ⟨cQ⟩ := wL.exists_curvature Q bQ hQbound hQfree LQ
  have : QuasiIso cP.kernelResolutionMap := cP.kernelResolution_quasiIso
  have : QuasiIso (𝟙 Q ⊗ₘ cP.kernelResolutionMap) :=
    quasiIso_tleft_map_of_kFlat Q cQ.isKFlat cP.kernelResolutionMap
  let cQ : LiftedDifferentialCurvature f hf Q LQ :=
    { cQ with
      kernelResolution := cP.kernelResolution
      kernelResolution_isKFlat := cP.kernelResolution_isKFlat
      kernelResolutionMap := cP.kernelResolutionMap
      kernelResolution_quasiIso := cP.kernelResolution_quasiIso
      tensorResolution_isIso := by infer_instance }
  let eP := Classical.choice eP
  let eQ := Classical.choice eQ
  have hPkproj : P.IsKProjective := by
    have : P.IsStrictlyLE bP := hPbound
    have : ∀ n : ℤ, Projective (P.X n) := by
      intro n
      let : Module.Free R (P.X n) := hPfree n
      exact ModuleCat.projective_of_free (R := R) (Module.Free.chooseBasis R (P.X n))
    exact CochainComplex.isKProjective_of_projective P bP
  let hα : (DerivedCategory.Q).obj P ⟶ (DerivedCategory.Q).obj Q :=
    eP.hom ≫ g ≫ eQ.inv
  obtain ⟨u, hu⟩ := exists_hom_map_eq_of_isKProjective hα
  let U (n : ℤ) : LP.X n →ₗ[R'] LQ.X n := liftComponent f LP LQ u n
  have hU (n : ℤ) (x : LP.X n) :
      LQ.reduction n (U n x) = u.f n (LP.reduction n x) :=
    reduction_liftComponent f LP LQ u n x
  let δ (n : ℤ) : LP.X n →ₗ[R'] LQ.X (n + 1) := liftDefect f LP LQ u n
  have hδ (n : ℤ) (x : LP.X n) : LQ.reduction (n + 1) (δ n x) = 0 :=
    reduction_liftDefect f LP LQ u n x
  have hδker (n : ℤ) (x : LP.X n) (hx : LP.reduction n x = 0) : δ n x = 0 :=
    liftDefect_eq_zero_of_reduction_eq_zero f hzero LP LQ u n x hx
  let H (n : ℤ) : P.X n →ₗ[R] (Q ⊗ kernelComplex f hf).X (n + 1) :=
    factorThroughKernelTensor f hf LP LQ cQ n (δ n) (hδ n) (hδker n)
  have hH (n : ℤ) (x : P.X n) :
      cQ.kernelEmbedding (n + 1) (H n x) = δ n (reductionPreimage f LP n x) :=
    kernelEmbedding_kernelEmbeddingPreimage f hf LP LQ cQ n (δ n) (hδ n) x
  let v : (P ⊗ kernelComplex f hf) ⟶ (Q ⊗ kernelComplex f hf) :=
    HomologicalComplex.mapBifunctorMap u (𝟙 (kernelComplex f hf))
      (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)
  have hEmbedMap (n : ℤ) (z : (P ⊗ kernelComplex f hf).X n) :
      cQ.kernelEmbedding n (v.f n z) = U n (cP.kernelEmbedding n z) := by
    simpa [v] using kernelEmbedding_map cP cQ u U hU n z
  have hHrep (n : ℤ) (x : LP.X n) :
      δ n (reductionPreimage f LP n (LP.reduction n x)) = δ n x :=
    eq_of_reduction_eq (δ n) (hδker n) (reduction_reductionPreimage f LP n _)
  let J (i j : ℤ) (h : i + 1 = j) : P.X i ⟶ (Q ⊗ kernelComplex f hf).X j := by
    subst j
    exact ModuleCat.ofHom (H i)
  have hcomm (n : ℤ) : (u ≫ cQ.hom).f n =
      P.d n (n + 1) ≫ J (n + 1) (n + 2) (by omega) +
      J n (n + 1) rfl ≫ (Q ⊗ kernelComplex f hf).d (n + 1) (n + 2) +
      (show P.X n ⟶ (Q ⊗ kernelComplex f hf).X (n + 2) from
        (cP.hom ≫ (shiftFunctor _ (2 : ℤ)).map v).f n) := by
    ext x
    obtain ⟨x, rfl⟩ := LP.reduction_surjective n x
    apply cQ.kernelEmbedding_injective (n + 2)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply, map_add]
    have hv : ((shiftFunctor _ (2 : ℤ)).map v).f n = v.f (n + 2) := rfl
    rw [hv, ← hU, cQ.hom_eq_square, hEmbedMap, cP.hom_eq_square]
    have hJ (i j : ℤ) (h : i + 1 = j) (y : LP.X i) :
        cQ.kernelEmbedding j ((J i j h).hom (LP.reduction i y)) =
          LQ.d i j (U i y) - U j (LP.d i j y) := by
      subst j
      change cQ.kernelEmbedding (i + 1) (H i (LP.reduction i y)) = _
      rw [hH, hHrep]
      rfl
    have hD (i j : ℤ) (h : i + 1 = j)
        (z : (Q ⊗ kernelComplex f hf).X i) :
        cQ.kernelEmbedding j (((Q ⊗ kernelComplex f hf).d i j).hom z) =
          LQ.d i j (cQ.kernelEmbedding i z) := by
      subst j
      exact kernelEmbedding_d cQ i z
    rw [← LP.reduction_d, hJ (n + 1) (n + 2) (by omega),
      hD (n + 1) (n + 2) (by omega), hJ n (n + 1) rfl x]
    simp only [map_sub]
    abel
  have hq := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
    (homotopyOfComponents (u ≫ cQ.hom)
      (cP.hom ≫ (shiftFunctor _ (2 : ℤ)).map v) J hcomm)
  simp only [Functor.map_comp] at hq
  have : IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ cP.kernelResolutionMap)) :=
    cP.tensorResolution_isIso
  have : IsIso (DerivedCategory.Q.map (𝟙 Q ⊗ₘ cP.kernelResolutionMap)) :=
    cQ.tensorResolution_isIso
  have hv : v = u ⊗ₘ 𝟙 (kernelComplex f hf) := rfl
  have ht : DerivedCategory.Q.map v ≫ cQ.tensorComparison =
      cP.tensorComparison ≫
        ((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map u)).app
          (squareZeroKernelObject f hf) := by
    rw [hv]
    dsimp only [LiftedDifferentialCurvature.tensorComparison, cQ,
      canonicalDerivedTensorProductFunctor]
    convert comparison_natural_of_resolution (canonicalDerivedTensorProduct R) u
      cP.kernelResolutionMap cP.isKFlat cQ.isKFlat cP.kernelResolution_isKFlat using 1
    simp only [Category.assoc]
    rfl
  rw [wK.eq_curvature P bP hPbound hPfree eP LP cP,
    wL.eq_curvature Q bQ hQbound hQfree eQ LQ cQ]
  change DerivedCategory.Q.map u = eP.hom ≫ g ≫ eQ.inv at hu
  have hue : eP.hom ≫ g = DerivedCategory.Q.map u ≫ eQ.hom := by
    simp only [hu, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi eP.hom).1
  dsimp only [LiftedDifferentialCurvature.toDerived]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hue, Iso.hom_inv_id_assoc, reassoc_of% hq]
  have hs := (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.naturality v
  change DerivedCategory.Q.map ((shiftFunctor _ (2 : ℤ)).map v) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (Q ⊗ kernelComplex f hf) =
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗ kernelComplex f hf) ≫
      (shiftFunctor _ (2 : ℤ)).map (DerivedCategory.Q.map v) at hs
  rw [reassoc_of% hs]
  congr 2
  simp only [← Functor.map_comp]
  congr 1
  simp only [LiftedDifferentialCurvature.tensorComparison, Category.assoc] at ht
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  congr 3
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← hue,
    Functor.map_comp, NatTrans.comp_app]

end Deformation.Obstruction

end
