module

public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Splitting a complex along idempotent endomorphisms of the identity

Let `C` be an abelian category, `K` a cochain complex in `C` and `(α_n)_{n ∈ ℤ}` a family of
idempotent endomorphisms of the identity functor of `C` such that `α_n` acts on `H^k(K)` as the
identity for `k = n` and as zero otherwise. Then the summand of `K` cut out by `α_n` has
cohomology only in degree `n`, and when countable coproducts in `C` are exact,
`K ≅ ⨁_n H^n(K)[-n]` in `D(C)`.

## Main results

* `Stacks.Cohomology.InvertibleDerived.homologyMap_chainEnd`: an endomorphism of the identity
  functor commutes with taking cohomology.
* `Stacks.Cohomology.InvertibleDerived.nonempty_Q_obj_iso_sigma_single`: the splitting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.InvertibleDerived

/-! ### Endomorphisms of the identity functor on complexes -/

section EndId

variable {C : Type*} [Category* C] [Abelian C] (α : 𝟭 C ⟶ 𝟭 C)

/-- An endomorphism of the identity functor, applied termwise to a complex. -/
public def chainEnd (K : CochainComplex C ℤ) : K ⟶ K where
  f i := α.app (K.X i)
  comm' i j _ := (α.naturality (K.d i j)).symm

/-- **An endomorphism of the identity functor commutes with taking cohomology.** -/
public theorem homologyMap_chainEnd (K : CochainComplex C ℤ) (i : ℤ) :
    HomologicalComplex.homologyMap (chainEnd α K) i = α.app (K.homology i) := by
  have hc : HomologicalComplex.cyclesMap (chainEnd α K) i = α.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i]
    exact α.naturality (K.iCycles i)
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc]
  exact (α.naturality (K.homologyπ i)).symm

/-- Applying endomorphisms `α` and `β` of the identity functor termwise to `K` one after the other
is the same as applying their composite `α ≫ β` termwise. -/
public theorem chainEnd_comp (β : 𝟭 C ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    chainEnd α K ≫ chainEnd β K = chainEnd (α ≫ β) K := by
  ext i : 1
  rfl

end EndId

/-! ### Splitting an idempotent -/

section Split

variable {C : Type*} [Category* C] [Preadditive C] [HasKernels C] {K : C} (p : K ⟶ K)

/-- The image of an idempotent, as the kernel of its complement. -/
public abbrev splitObj : C := kernel (𝟙 K - p)

/-- The inclusion of the image of an idempotent. -/
public abbrev splitι : splitObj p ⟶ K := kernel.ι (𝟙 K - p)

variable {p}

/-- The projection onto the image of an idempotent. -/
public abbrev splitπ (hp : p ≫ p = p) : K ⟶ splitObj p :=
  kernel.lift _ p (by rw [Preadditive.comp_sub, Category.comp_id, hp, sub_self])

/-- For an idempotent `p`, the inclusion of its image is fixed by `p`:
`splitι p ≫ p = splitι p`. -/
public theorem splitι_comp (_hp : p ≫ p = p) : splitι p ≫ p = splitι p := by
  have h := kernel.condition (𝟙 K - p)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

/-- For an idempotent `p`, the inclusion of its image followed by the projection onto it is the
identity of the image. -/
public theorem splitι_splitπ (hp : p ≫ p = p) : splitι p ≫ splitπ hp = 𝟙 _ := by
  rw [← cancel_mono (splitι p), Category.assoc, kernel.lift_ι, Category.id_comp, splitι_comp hp]

/-- For an idempotent `p`, the projection onto its image followed by the inclusion of the image
is `p` itself. -/
public theorem splitπ_splitι (hp : p ≫ p = p) : splitπ hp ≫ splitι p = p := kernel.lift_ι _ _ _

end Split

/-! ### The splitting in the derived category -/

section Derived

variable {C : Type*} [Category* C] [Abelian C] (α : ℤ → (𝟭 C ⟶ 𝟭 C)) (K : CochainComplex C ℤ)

/-- `α n` acts on `H^k(K)` as the identity for `k = n` and as zero for `k ≠ n`. -/
public def ActsOnHomology : Prop :=
  ∀ n k : ℤ, (α n).app (K.homology k) = if k = n then 𝟙 _ else 0

variable {α K}

/-- The summand of `K` cut out by the idempotent `α n`. -/
public abbrev piece (_hα : ∀ n, α n ≫ α n = α n) (n : ℤ) : CochainComplex C ℤ :=
  splitObj (chainEnd (α n) K)

variable (hα : ∀ n, α n ≫ α n = α n)

include hα in
/-- If each `α n` is idempotent, then so is its termwise action `chainEnd (α n) K` on `K`. -/
public theorem chainEnd_idem (n : ℤ) : chainEnd (α n) K ≫ chainEnd (α n) K = chainEnd (α n) K := by
  rw [chainEnd_comp, hα n]

variable (hK : ActsOnHomology α K)

include hα hK in
/-- If the `α n` are idempotent and `α n` acts on `H^k(K)` as the identity for `k = n` and as zero
otherwise, then the inclusion of the summand cut out by `α n` into `K` induces an isomorphism on
`H^n`. -/
public theorem isIso_homologyMap_splitι (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (splitι (chainEnd (α n) K)) n) := by
  refine ⟨HomologicalComplex.homologyMap (splitπ (chainEnd_idem hα n)) n, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, splitι_splitπ, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, splitπ_splitι, homologyMap_chainEnd, hK n n,
      ite_eq_left rfl]
    rfl

include hα hK in
/-- If the `α n` are idempotent and `α n` acts on `H^k(K)` as the identity for `k = n` and as zero
otherwise, then the summand cut out by `α n` has zero cohomology in every degree `k ≠ n`. -/
public theorem isZero_homology_piece {n k : ℤ} (hkn : k ≠ n) :
    IsZero ((piece (K := K) hα n).homology k) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 : HomologicalComplex.homologyMap (splitι (chainEnd (α n) K)) k = 0 := by
    rw [← splitι_comp (chainEnd_idem hα n), HomologicalComplex.homologyMap_comp,
      homologyMap_chainEnd, hK n k, ite_eq_right hkn, Limits.comp_zero]
  rw [← HomologicalComplex.homologyMap_id, ← splitι_splitπ (chainEnd_idem hα n),
    HomologicalComplex.homologyMap_comp, h1, Limits.zero_comp]

include hK in
/-- **Each summand is a single object in the derived category**: the summand cut out by `α n` has
cohomology only in degree `n`, where it is `H^n(K)`. -/
public theorem nonempty_Q_obj_piece_iso [HasDerivedCategory C] (n : ℤ) :
    Nonempty (DerivedCategory.Q.obj (piece (K := K) hα n) ≅
      (DerivedCategory.singleFunctor C n).obj (K.homology n)) := by
  have hge : (piece (K := K) hα n).IsGE n := (CochainComplex.isGE_iff _ n).mpr fun i hi =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (isZero_homology_piece hα hK (ne_of_lt hi))
  have hle : (piece (K := K) hα n).IsLE n := (CochainComplex.isLE_iff _ n).mpr fun i hi =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (isZero_homology_piece hα hK (ne_of_gt hi))
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj (piece (K := K) hα n)) n
  have hiso := isIso_homologyMap_splitι hα hK n
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C n).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app _ ≪≫
      @asIso _ _ _ _ (HomologicalComplex.homologyMap (splitι (chainEnd (α n) K)) n) hiso)⟩

/-- The comparison from the sum of the summands to `K`. -/
public abbrev sumPieces [HasCoproduct fun n => piece (K := K) hα n] :
    (∐ fun n => piece (K := K) hα n) ⟶ K :=
  Sigma.desc fun n => splitι (chainEnd (α n) K)

include hK in
/-- **`K` is the sum of its summands**, up to quasi-isomorphism: in each degree `k` only the
summand `k` has cohomology, and there the inclusion is an isomorphism on cohomology. -/
public theorem quasiIso_sumPieces [HasColimitsOfShape (Discrete ℤ) C]
    [HasExactColimitsOfShape (Discrete ℤ) C] :
    QuasiIso (sumPieces (K := K) hα) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := C)
    (J := Discrete ℤ) (ComplexShape.up ℤ) k
  have hz : ∀ n, n ≠ k → IsZero ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).obj
      (piece (K := K) hα n)) := fun n hn => isZero_homology_piece hα hK (Ne.symm hn)
  have hι : IsIso (Sigma.ι
      (fun n => (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).obj
        (piece (K := K) hα n)) k) :=
    CategoryTheory.Limits.isIso_sigmaι_of_isZero _ k hz
  have hk := isIso_homologyMap_splitι hα hK k
  have hdesc : IsIso (Sigma.desc fun n =>
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
        (splitι (chainEnd (α n) K))) := by
    have h1 : (Sigma.desc fun n => (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
          (splitι (chainEnd (α n) K))) =
        inv (Sigma.ι (fun n => (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).obj
          (piece (K := K) hα n)) k) ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
            (splitι (chainEnd (α k) K)) := by
      rw [IsIso.eq_inv_comp, Sigma.ι_desc]
    rw [h1]
    exact IsIso.comp_isIso' inferInstance hk
  have h2 : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
        (sumPieces (K := K) hα) =
      inv (sigmaComparison (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k)
        fun n => piece (K := K) hα n) ≫ Sigma.desc fun n =>
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
            (splitι (chainEnd (α n) K)) := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [ι_comp_sigmaComparison_assoc, Sigma.ι_desc, ← Functor.map_comp, Sigma.ι_desc]
  have h3 : IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).map
      (sumPieces (K := K) hα)) := by
    rw [h2]
    exact IsIso.comp_isIso' inferInstance hdesc
  exact h3

include hα hK in
/-- **The splitting `K ≅ ⨁_n H^n(K)[-n]` in the derived category.** -/
public theorem nonempty_Q_obj_iso_sigma_single [HasDerivedCategory C]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [HasCoproductsOfShape ℤ (DerivedCategory C)]
    [PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := C))] :
    Nonempty (DerivedCategory.Q.obj K ≅
      ∐ fun n => (DerivedCategory.singleFunctor C n).obj (K.homology n)) := by
  have hq := quasiIso_sumPieces hα hK
  have : IsIso (DerivedCategory.Q.map (sumPieces (K := K) hα)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C (sumPieces (K := K) hα)).mpr hq
  exact ⟨(asIso (DerivedCategory.Q.map (sumPieces (K := K) hα))).symm ≪≫
    PreservesCoproduct.iso DerivedCategory.Q (fun n => piece (K := K) hα n) ≪≫
    Sigma.mapIso fun n => (nonempty_Q_obj_piece_iso hα hK n).some⟩

end Derived


end Stacks.Cohomology.InvertibleDerived

end
