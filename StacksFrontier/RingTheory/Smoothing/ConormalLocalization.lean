module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.Algebra.Module.StablyFree
public import StacksFrontier.LinearAlgebra.Matrix.MaximalMinors
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.Smoothing.AlgebraPresentation

/-!
# The conormal module of a presentation after inverting an element

Let `R → A` be a ring map, let `P` be a presentation `A = R[x_1, …, x_n]/(f_1, …, f_m)` in
the sense of Stacks 16.2, let `a ∈ A` and let `T = A_a`. This file records what the proof of
Stacks 16.3.7 (e) needs about the conormal module `(I/I²)_a` of such a presentation.

The naive cotangent complex `I/I² → ⊕ A dx_i` of `P` is Mathlib's
`Algebra.Extension.cotangentComplex` of the extension attached to `P`, and in the basis of
the cotangent space given by the variables its matrix is the Jacobian matrix of the
relations. After inverting `a` the classes of the relations still generate the conormal
module, so the image of the conormal map is the image of the Jacobian matrix over `T`; and
when `T` is formally smooth over `R` the conormal map is a split injection, so that the
image of the Jacobian is a direct summand of `T ^ n` with the module of differentials as
complement.

## Main definitions

* `Stacks.Smoothing.jacobianMatrixFull`: the `n × m` matrix of the differentials of all the
  relations of a presentation.
* `Stacks.Smoothing.relationClassesBaseChange`: the map `T ^ m → (I/I²)_a` given by the
  classes of the relations.

## Main results

* `Stacks.Smoothing.exists_leftInverse_cotangentComplex_baseChange`: over a formally smooth
  localization the conormal map of a presentation is a split injection.
* `Stacks.Smoothing.exists_split_jacobian`: the image of the Jacobian matrix over `T` is a
  direct summand of `T ^ n` whose complement is `T ⊗ Ω[A⁄R]`.
* `Stacks.Smoothing.maximalMinorsIdeal_map`: the ideal of maximal minors is compatible with
  a ring map.
* `Stacks.Smoothing.exists_pow_mem_of_one_mem_map`: an ideal whose extension to `A_a`
  is the unit ideal contains a power of `a`.
* `Stacks.Smoothing.exists_prod_fin_linearEquiv`: a finite stably free module becomes finite
  free after adding a finite free module, with explicit ranks.

## References

* [Stacks Project, Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ)
* [Stacks Project, Tag 07ET](https://stacks.math.columbia.edu/tag/07ET)
-/

@[expose] public section

namespace Stacks.Smoothing

open MvPolynomial
open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- The Jacobian matrix of all the relations of a presentation: the `(i, j)` entry is the
element of `A` represented by `∂f_j/∂x_i`. -/
noncomputable def jacobianMatrixFull (P : Presentation R A) : Matrix (Fin P.n) (Fin P.m) A :=
  fun i j => P.lift (pderiv i (P.f j))

/-- Localizing the conormal map of a presentation keeps it injective as soon as the
localization has vanishing first cotangent cohomology. -/
theorem injective_cotangentComplex_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] {ι : Type*} (G : Algebra.Generators R S ι)
    (M : Submonoid S) [IsLocalization M T] [Subsingleton (Algebra.H1Cotangent R T)] :
    Function.Injective (G.toExtension.cotangentComplex.baseChange T) := by
  set Q := Algebra.Generators.self R T with hQ
  have hQinj : Function.Injective Q.toExtension.cotangentComplex :=
    (Algebra.Extension.subsingleton_h1Cotangent _).mp Q.equivH1Cotangent.subsingleton
  have hbij := Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization
    (T := T) M ((Algebra.Generators.defaultHom G Q).toExtensionHom)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  refine hbij.injOn hx (zero_mem _) ?_
  have hmt := hbij.mapsTo hx
  rw [LinearMap.ker_eq_bot.mpr hQinj] at hmt
  rw [show ((Algebra.Extension.Cotangent.map _).liftBaseChange T) x = 0 from hmt, map_zero]

/-- Base change of the surjection `toKaehler` of an extension is still surjective. -/
private theorem surjective_toKaehler_baseChange
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (T : Type*) [CommRing T] [Algebra S T]
    (E : Algebra.Extension R S) : Function.Surjective (E.toKaehler.baseChange T) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_surjective T Algebra.Extension.toKaehler_surjective

/-- Base change of the exact sequence `cotangentComplex`, `toKaehler` of an extension is exact. -/
private theorem exact_cotangentComplex_baseChange_toKaehler
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (T : Type*) [CommRing T] [Algebra S T]
    (E : Algebra.Extension R S) :
    Function.Exact (E.cotangentComplex.baseChange T) (E.toKaehler.baseChange T) := by
  simp only [LinearMap.baseChange_eq_lTensor]
  exact lTensor_exact T Algebra.Extension.exact_cotangentComplex_toKaehler
    Algebra.Extension.toKaehler_surjective

/-- Over a formally smooth localization the conormal map of a presentation is a split
injection. -/
theorem exists_leftInverse_cotangentComplex_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] {ι : Type*} (G : Algebra.Generators R S ι)
    (M : Submonoid S) [IsLocalization M T] [Algebra.FormallySmooth R T] :
    ∃ l : T ⊗[S] G.toExtension.CotangentSpace →ₗ[T] T ⊗[S] G.toExtension.Cotangent,
      l ∘ₗ G.toExtension.cotangentComplex.baseChange T = LinearMap.id := by
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization M
  have : Module.Projective T Ω[T⁄R] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Module.Projective T (T ⊗[S] Ω[S⁄R]) :=
    Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id
    (surjective_toKaehler_baseChange T G.toExtension)
  have hsplit := (exact_cotangentComplex_baseChange_toKaehler T G.toExtension).split_tfae'.out 1 2
  exact (hsplit.mp ⟨injective_cotangentComplex_baseChange G M, s, hs⟩).2

section Localized

variable (T : Type v) [CommRing T] [Algebra A T]

/-- The map `T ^ m → (I/I²)_a` given by the classes of the relations of a presentation. -/
noncomputable def relationClassesBaseChange (P : Presentation R A) :
    (Fin P.m → T) →ₗ[T] T ⊗[A] (toAlgebraPresentation P).toGenerators.toExtension.Cotangent :=
  Fintype.linearCombination T fun j => (1 : T) ⊗ₜ[A]
    Algebra.Extension.Cotangent.mk (P := (toAlgebraPresentation P).toGenerators.toExtension)
      ⟨P.f j, (toAlgebraPresentation P).relation_mem_ker j⟩

variable {P : Presentation R A}

/-- For any `A`-algebra `T`, the classes of the relations generate `T ⊗[A] (I/I²)`: the map
`relationClassesBaseChange T P` is surjective. -/
theorem relationClassesBaseChange_surjective :
    Function.Surjective (relationClassesBaseChange T P) := by
  classical
  set Q := toAlgebraPresentation P with hQ
  set C := Q.toGenerators.toExtension.Cotangent with hC
  let d : Fin P.m → C := fun j =>
    Algebra.Extension.Cotangent.mk (P := Q.toGenerators.toExtension)
      ⟨P.f j, Q.relation_mem_ker j⟩
  let G : (Fin P.m → A) →ₗ[A] C := Fintype.linearCombination A d
  have hG : Function.Surjective G := relation_classes_surjective Q
  have hGT : Function.Surjective (G.baseChange T) := LinearMap.lTensor_surjective T hG
  let bPi : Module.Basis (Fin P.m) A (Fin P.m → A) := Pi.basisFun A (Fin P.m)
  let ePi : T ⊗[A] (Fin P.m → A) ≃ₗ[T] (Fin P.m → T) := (bPi.baseChange T).equivFun
  have heq : relationClassesBaseChange T P = G.baseChange T ∘ₗ ePi.symm := by
    apply LinearMap.ext
    intro x
    change (∑ j : Fin P.m, x j • ((1 : T) ⊗ₜ[A] d j)) =
      G.baseChange T ((bPi.baseChange T).equivFun.symm x)
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp only [map_smul, LinearMap.baseChange_tmul, Module.Basis.baseChange_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [G, bPi, Fintype.linearCombination_apply]
  rw [heq]
  exact hGT.comp ePi.symm.surjective

/-- For any `A`-algebra `T`, the base change `T ⊗[A] (I/I²)` of the conormal module of a
presentation is a finite `T`-module. -/
theorem finite_cotangent_baseChange :
    Module.Finite T (T ⊗[A] (toAlgebraPresentation P).toGenerators.toExtension.Cotangent) :=
  Module.Finite.of_surjective _ (relationClassesBaseChange_surjective T (P := P))

/-- In the basis of the cotangent space given by the variables, the conormal map composed
with the relation classes is the Jacobian matrix. -/
theorem cotangentSpaceBasis_comp_cotangentComplex_comp_relationClasses :
    (((toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.baseChange T).equivFun
        : T ⊗[A] (toAlgebraPresentation P).toGenerators.toExtension.CotangentSpace ≃ₗ[T]
          (Fin P.n → T)).toLinearMap ∘ₗ
      ((toAlgebraPresentation P).toGenerators.toExtension.cotangentComplex.baseChange T) ∘ₗ
        relationClassesBaseChange T P =
      Matrix.toLin' ((jacobianMatrixFull P).map (algebraMap A T)) := by
  classical
  set Q := toAlgebraPresentation P with hQ
  set E := Q.toGenerators.toExtension with hE
  let d : Fin P.m → E.Cotangent := fun j =>
    Algebra.Extension.Cotangent.mk (P := E) ⟨P.f j, Q.relation_mem_ker j⟩
  let bN : Module.Basis (Fin P.n) T (T ⊗[A] E.CotangentSpace) :=
    Q.toGenerators.cotangentSpaceBasis.baseChange T
  have hcol (j : Fin P.m) :
      bN.equivFun ((E.cotangentComplex.baseChange T) ((1 : T) ⊗ₜ[A] d j)) = fun i =>
        algebraMap A T (P.lift (pderiv i (P.f j))) := by
    ext i
    rw [Module.Basis.equivFun_apply]
    change (Q.toGenerators.cotangentSpaceBasis.baseChange T).repr
      (1 ⊗ₜ[A] E.cotangentComplex (d j)) i = _
    rw [Module.Basis.baseChange_repr_tmul, relation_coordinates,
      ← algebraMap_smul (A := T) (R := A) (P.lift (pderiv i (P.f j))) (1 : T)]
    simp
  refine (Pi.basisFun T (Fin P.m)).ext fun j => _root_.funext fun i => ?_
  change bN.equivFun ((E.cotangentComplex.baseChange T)
    (relationClassesBaseChange T P ((Pi.basisFun T (Fin P.m)) j))) i = _
  simp only [Pi.basisFun_apply]
  rw [show relationClassesBaseChange T P (Pi.single j 1) = (1 : T) ⊗ₜ[A] d j by
    simp [relationClassesBaseChange, Fintype.linearCombination_apply, Pi.single_apply, d], hcol]
  simp [Matrix.toLin'_apply, Matrix.mulVec_single, jacobianMatrixFull]

/-- **The conormal module of a presentation after inverting an element.** If `T = A_a` is
formally smooth over `R`, the image of the Jacobian matrix of a presentation over `T` is a
direct summand of `T ^ n` with complement `T ⊗ Ω[A⁄R]`. -/
theorem exists_split_jacobian [Algebra R T] [IsScalarTower R A T] (a : A)
    [IsLocalization (Submonoid.powers a) T] [Algebra.FormallySmooth R T] :
    ∃ e : (Fin P.n → T) ≃ₗ[T]
        (T ⊗[A] (toAlgebraPresentation P).toGenerators.toExtension.Cotangent) ×
          (T ⊗[A] Ω[A⁄R]),
      LinearMap.range (Matrix.toLin' ((jacobianMatrixFull P).map (algebraMap A T))) =
        LinearMap.range (e.symm.toLinearMap ∘ₗ LinearMap.inl T
          (T ⊗[A] (toAlgebraPresentation P).toGenerators.toExtension.Cotangent)
          (T ⊗[A] Ω[A⁄R])) := by
  classical
  set Q := toAlgebraPresentation P with hQ
  set E := Q.toGenerators.toExtension with hE
  let bN : Module.Basis (Fin P.n) T (T ⊗[A] E.CotangentSpace) :=
    Q.toGenerators.cotangentSpaceBasis.baseChange T
  let f : T ⊗[A] E.Cotangent →ₗ[T] (Fin P.n → T) :=
    bN.equivFun.toLinearMap ∘ₗ E.cotangentComplex.baseChange T
  let g : (Fin P.n → T) →ₗ[T] T ⊗[A] Ω[A⁄R] :=
    (E.toKaehler.baseChange T) ∘ₗ bN.equivFun.symm.toLinearMap
  have hfapp : ∀ x, f x = bN.equivFun (E.cotangentComplex.baseChange T x) := fun _ => rfl
  have hgapp : ∀ y, g y = E.toKaehler.baseChange T (bN.equivFun.symm y) := fun _ => rfl
  have hgsurj : Function.Surjective g :=
    (surjective_toKaehler_baseChange T E).comp bN.equivFun.symm.surjective
  have hex0 := exact_cotangentComplex_baseChange_toKaehler T E
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hex0 (bN.equivFun.symm y)).1 hy
      exact ⟨x, by rw [hfapp, hx, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [hgapp, hfapp, LinearEquiv.symm_apply_apply]
      exact (hex0 _).2 ⟨x, rfl⟩
  obtain ⟨l, hl⟩ := exists_leftInverse_cotangentComplex_baseChange (R := R)
    Q.toGenerators (Submonoid.powers a) (T := T)
  have hl' : (l ∘ₗ bN.equivFun.symm.toLinearMap) ∘ₗ f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change l (bN.equivFun.symm (bN.equivFun (E.cotangentComplex.baseChange T x))) = x
    rw [LinearEquiv.symm_apply_apply]
    exact congrFun (congrArg (fun φ : _ →ₗ[T] _ => (φ : _ → _)) hl) x
  obtain ⟨e, he, -⟩ := (hex.splitInjectiveEquiv hgsurj) ⟨l ∘ₗ bN.equivFun.symm.toLinearMap, hl'⟩
  refine ⟨e, ?_⟩
  rw [← he, show Matrix.toLin' ((jacobianMatrixFull P).map (algebraMap A T)) =
    f ∘ₗ relationClassesBaseChange T P from
      (cotangentSpaceBasis_comp_cotangentComplex_comp_relationClasses T).symm]
  exact LinearMap.range_comp_of_range_eq_top f
    (LinearMap.range_eq_top.2 (relationClassesBaseChange_surjective T (P := P)))

end Localized

/-- The class in the conormal module of a multiple of an element of the relation ideal is
the corresponding multiple of its class. -/
theorem cotangentMk_mul (E : Algebra.Extension R A) (w : E.Ring) (x : E.ker)
    (h : w * (x : E.Ring) ∈ E.ker) :
    Algebra.Extension.Cotangent.mk (P := E) ⟨w * (x : E.Ring), h⟩ =
      w • Algebra.Extension.Cotangent.mk (P := E) x := by
  rw [← map_smul]
  exact congrArg _ (Subtype.ext (by simp))

/-- The ideal of maximal minors is compatible with a ring map. -/
theorem maximalMinorsIdeal_map {B : Type w} [CommRing B] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (φ : A →+* B) :
    maximalMinorsIdeal (M.map φ) = Ideal.map φ (maximalMinorsIdeal M) := by
  have key (r : Fin m ↪o Fin n) :
      ((M.map φ).submatrix (r : Fin m → Fin n) id).det =
        φ ((M.submatrix (r : Fin m → Fin n) id).det) :=
    (RingHom.map_det φ (M.submatrix (r : Fin m → Fin n) id)).symm
  rw [maximalMinorsIdeal, maximalMinorsIdeal, Ideal.map_span]
  congr 1
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    exact ⟨(M.submatrix r id).det, ⟨r, rfl⟩, (key r).symm⟩
  · rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, key r⟩

/-- An ideal whose extension to `A_a` is the unit ideal contains a power of `a`. -/
theorem exists_pow_mem_of_one_mem_map (T : Type v) [CommRing T] [Algebra A T] (a : A)
    [IsLocalization (Submonoid.powers a) T] (I : Ideal A)
    (h : (1 : T) ∈ Ideal.map (algebraMap A T) I) : ∃ k : ℕ, a ^ k ∈ I := by
  rw [show (1 : T) = algebraMap A T 1 by simp,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers a)] at h
  obtain ⟨b, hb, hmem⟩ := h
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff b a).1 hb
  exact ⟨k, by simpa using hmem⟩

/-- A finite stably free module over a nontrivial commutative ring becomes finite free after
adding a finite free module, and the rank of the added module is at most the rank of the
result. -/
theorem exists_prod_fin_linearEquiv (T : Type v) [CommRing T] [Nontrivial T] (M : Type w)
    [AddCommGroup M] [Module T M] [Module.Finite T M] [Module.IsStablyFree T M] :
    ∃ (k l : ℕ) (_ : (M × (Fin k → T)) ≃ₗ[T] (Fin l → T)), k ≤ l := by
  classical
  obtain ⟨N, hNg, hNm, hNfin, hNfree, hfree⟩ := Module.IsStablyFree.exist_free_prod T M
  have hfinMN : Module.Finite T (M × N) := inferInstance
  let bN := Module.Free.chooseBasis T N
  let bP := Module.Free.chooseBasis T (M × N)
  have hiN : Finite (Module.Free.ChooseBasisIndex T N) := Module.Finite.finite_basis bN
  have hiP : Finite (Module.Free.ChooseBasisIndex T (M × N)) := Module.Finite.finite_basis bP
  let ftN : Fintype (Module.Free.ChooseBasisIndex T N) := Fintype.ofFinite _
  let ftP : Fintype (Module.Free.ChooseBasisIndex T (M × N)) := Fintype.ofFinite _
  let k := Fintype.card (Module.Free.ChooseBasisIndex T N)
  let l := Fintype.card (Module.Free.ChooseBasisIndex T (M × N))
  let eN : N ≃ₗ[T] (Fin k → T) := (bN.reindex (Fintype.equivFin _)).equivFun
  let eP : (M × N) ≃ₗ[T] (Fin l → T) := (bP.reindex (Fintype.equivFin _)).equivFun
  let e : (M × (Fin k → T)) ≃ₗ[T] (Fin l → T) :=
    ((LinearEquiv.refl T M).prodCongr eN.symm).trans eP
  refine ⟨k, l, e, ?_⟩
  have := commRing_strongRankCondition T
  have hinj : Function.Injective (e.toLinearMap ∘ₗ LinearMap.inr T M (Fin k → T)) :=
    e.injective.comp LinearMap.inr_injective
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle

end Stacks.Smoothing

end
