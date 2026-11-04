module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleChainInverse
public import StacksFrontier.Homology.DerivedCategory.KProjectiveHomotopyEquiv
public import StacksFrontier.Homology.DerivedCategory.IdempotentSplitting
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# The idempotents of an invertible object of `D(R)`

Let `R` be a commutative ring and `P` a bounded above complex of projective `R`-modules which is
an invertible object of `D(R)`. By Stacks 0FNT there are finitely many orthogonal idempotents
`f_n` of `R` summing to `1` such that `f_n` acts on `H^k(P)` as the identity for `k = n` and as
zero otherwise; each `H^k(P)` is finite projective, and `P` is homotopy equivalent to the complex
with `H^k(P)` in degree `k` and zero differentials.

## References

* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace DerivedCategory.Invertible

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- Multiplication by a scalar, as an endomorphism of the identity functor of `R`-modules. -/
public def scalarNatTrans (r : R) : 𝟭 (ModuleCat.{u} R) ⟶ 𝟭 (ModuleCat.{u} R) where
  app M := ModuleCat.ofHom (LinearMap.lsmul R M r)
  naturality M N g := by
    ext m
    exact (g.hom.map_smul r m).symm

public theorem scalarNatTrans_app_apply (r : R) (M : ModuleCat.{u} R) (m : M) :
    ((scalarNatTrans r).app M).hom m = r • m := rfl

public theorem scalarNatTrans_comp (r s : R) :
    scalarNatTrans r ≫ scalarNatTrans s = scalarNatTrans (s * r) := by
  ext M m
  exact (mul_smul s r m).symm

/-- The degree-`n` idempotent of a finite product decomposition `R ≃ ∏_{n ∈ [a, b]} R_n`. -/
public def productIdempotent {a b : ℤ} {Rn : Set.Icc a b → Type u} [∀ n, CommRing (Rn n)]
    (e : R ≃+* ∀ n, Rn n) (n : ℤ) : R :=
  if h : n ∈ Set.Icc a b then e.symm (Pi.single ⟨n, h⟩ 1) else 0

section ProductIdempotent

variable {a b : ℤ} {Rn : Set.Icc a b → Type u} [∀ n, CommRing (Rn n)] (e : R ≃+* ∀ n, Rn n)

public theorem apply_productIdempotent (n : ℤ) (k : Set.Icc a b) :
    e (productIdempotent e n) k = if k.1 = n then 1 else 0 := by
  classical
  unfold productIdempotent
  split_ifs with h hk hk
  · subst hk
    rw [RingEquiv.apply_symm_apply, Pi.single_eq_same]
  · rw [RingEquiv.apply_symm_apply, Pi.single_eq_of_ne]
    exact fun h' => hk (congrArg Subtype.val h')
  · exact absurd (hk ▸ k.2) h
  · rw [map_zero]
    rfl

public theorem productIdempotent_idem (n : ℤ) : IsIdempotentElem (productIdempotent e n) :=
  e.injective (funext fun k => by
    rw [map_mul, Pi.mul_apply, apply_productIdempotent]
    split_ifs <;> simp)

public theorem productIdempotent_ortho {n m : ℤ} (h : n ≠ m) :
    productIdempotent e n * productIdempotent e m = 0 :=
  e.injective (funext fun k => by
    rw [map_mul, Pi.mul_apply, apply_productIdempotent, apply_productIdempotent, map_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    all_goals simp)

public theorem productIdempotent_eq_zero {n : ℤ} (h : n ∉ Finset.Icc a b) :
    productIdempotent e n = 0 := by
  unfold productIdempotent
  exact dif_neg (fun h' => h (Finset.mem_Icc.mpr h'))

public theorem sum_productIdempotent : ∑ n ∈ Finset.Icc a b, productIdempotent e n = 1 :=
  e.injective (funext fun k => by
    rw [map_sum, Finset.sum_apply, map_one, Pi.one_apply]
    simp_rw [apply_productIdempotent]
    rw [Finset.sum_ite_eq (Finset.Icc a b) k.1, if_pos (Finset.mem_Icc.mpr k.2)])

end ProductIdempotent

/-- `r` acts on a module obtained by restriction of scalars along `φ` as `φ r` acts. -/
public theorem scalarNatTrans_app_restrictScalars {A : Type u} [CommRing A] (φ : R →+* A)
    (L : ModuleCat.{u} A) (r : R) {s : A} (hs : φ r = s) :
    (scalarNatTrans r).app ((ModuleCat.restrictScalars φ).obj L) =
      (ModuleCat.restrictScalars φ).map (ModuleCat.ofHom (LinearMap.lsmul A L s)) := by
  ext m
  exact congrArg (fun t : A => t • (id m : L)) hs

/-- Transport of the action of a scalar along an isomorphism of modules. -/
public theorem scalarNatTrans_app_eq_of_iso (r : R) {M N : ModuleCat.{u} R} (e : M ≅ N)
    {g : N ⟶ N} (h : (scalarNatTrans r).app N = g) :
    (scalarNatTrans r).app M = e.hom ≫ g ≫ e.inv := by
  have hn : e.hom ≫ (scalarNatTrans r).app N = (scalarNatTrans r).app M ≫ e.hom :=
    ((scalarNatTrans r).naturality e.hom)
  rw [← h, ← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Stacks 0FNT, read on a bounded above complex of projectives.** If `P` is a bounded above
complex of projective `R`-modules which is invertible in `D(R)`, there are a finite set `S` of
degrees and orthogonal idempotents `f_n` of `R`, zero outside `S` and summing to `1`, such that
`f_n` acts on `H^k(P)` as the identity for `k = n` and as zero otherwise; every `H^k(P)` is finite
projective. -/
public theorem exists_idempotents_of_isInvertible (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : letI := (derivedCategory_symmetricMonoidalCategory R).choose
      MonoidalCategory.IsInvertible (DerivedCategory.Q.obj P)) :
    ∃ (S : Finset ℤ) (f : ℤ → R), (∀ n, IsIdempotentElem (f n)) ∧
      (∀ n m, n ≠ m → f n * f m = 0) ∧ (∀ n ∉ S, f n = 0) ∧ ∑ n ∈ S, f n = 1 ∧
      Stacks.Cohomology.InvertibleDerived.ActsOnHomology (fun n => scalarNatTrans (f n)) P ∧
      ∀ k, Module.Finite R (P.homology k) ∧ Module.Projective R (P.homology k) := by
  obtain ⟨-, hdec⟩ := isInvertible_iff_locallyShiftedUnit (DerivedCategory.Q.obj P)
  obtain ⟨-, -, hfp, a, b, Rn, _, e, L, -, hL, hvan⟩ := hdec hP
  let H : ∀ k : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).obj
      (DerivedCategory.Q.obj P) ≅ P.homology k :=
    fun k => (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) k).app P
  refine ⟨Finset.Icc a b, productIdempotent e, productIdempotent_idem e,
    fun n m h => productIdempotent_ortho e h, fun n h => productIdempotent_eq_zero e h,
    sum_productIdempotent e, fun n k => ?_, fun k => ?_⟩
  · by_cases hk : k ∈ Set.Icc a b
    · obtain ⟨eL⟩ := hL ⟨k, hk⟩
      have h1 := scalarNatTrans_app_restrictScalars ((Pi.evalRingHom Rn ⟨k, hk⟩).comp e.toRingHom)
        (L ⟨k, hk⟩) (productIdempotent e n) (s := if k = n then 1 else 0)
        (apply_productIdempotent e n ⟨k, hk⟩)
      rw [scalarNatTrans_app_eq_of_iso _ ((H k).symm ≪≫ eL) h1]
      split_ifs with hkn
      · rw [show ModuleCat.ofHom (LinearMap.lsmul (Rn ⟨k, hk⟩) (L ⟨k, hk⟩) 1) = 𝟙 _ by
            ext m
            exact one_smul _ m,
          CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
        rfl
      · rw [show ModuleCat.ofHom (LinearMap.lsmul (Rn ⟨k, hk⟩) (L ⟨k, hk⟩) 0) = 0 by
            ext m
            exact zero_smul _ m,
          CategoryTheory.Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    · exact ((hvan k hk).of_iso (H k).symm).eq_of_src _ _
  · exact ⟨(hfp k).1.equiv (H k).toLinearEquiv, (hfp k).2.of_equiv (H k).toLinearEquiv⟩

/-- Where an idempotent acting as the identity on a module vanishes, the module vanishes. -/
public theorem isZero_of_actsOnHomology {f : ℤ → R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : Stacks.Cohomology.InvertibleDerived.ActsOnHomology (fun n => scalarNatTrans (f n)) P)
    {k : ℤ} (hk : f k = 0) : IsZero (P.homology k) := by
  have h := hP k k
  rw [if_pos rfl] at h
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  calc 𝟙 (P.homology k) = (scalarNatTrans (f k)).app (P.homology k) := h.symm
    _ = 0 := by
      ext m
      exact (congrArg (fun t : R => t • m) hk).trans (zero_smul R m)

/-- **A bounded above complex of projectives whose cohomology is split by idempotents of `R` and
is projective is homotopy equivalent to its cohomology.** -/
public theorem nonempty_homotopyEquiv_zeroDifferential (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : ℤ) [P.IsStrictlyLE a] (hP : ∀ i, Projective (P.X i)) (f : ℤ → R)
    (hidem : ∀ n, IsIdempotentElem (f n))
    (hact : Stacks.Cohomology.InvertibleDerived.ActsOnHomology (fun n => scalarNatTrans (f n)) P)
    (hproj : ∀ k, Module.Projective R (P.homology k)) :
    Nonempty (HomotopyEquiv P (CochainComplex.zeroDifferentialComplex fun k => P.homology k)) := by
  have hα : ∀ n, scalarNatTrans (f n) ≫ scalarNatTrans (f n) = scalarNatTrans (f n) := fun n => by
    rw [scalarNatTrans_comp, (hidem n).eq]
  let _i1 : HasCoproducts.{u} (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.Injectives.hasCoproducts_derivedCategory _
  let _i2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    Stacks.Injectives.derivedCategoryQ_preservesCoproducts _ _
  let _i3 : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    preservesColimitsOfShape_discrete_shrink.{u} _ _
  obtain ⟨e⟩ := Stacks.Cohomology.InvertibleDerived.nonempty_Q_obj_iso_sigma_single hα hact
  have hKP : P.IsKProjective := CochainComplex.isKProjective_of_projective P a
  let Z := CochainComplex.zeroDifferentialComplex fun k => P.homology k
  have hZproj : ∀ i, Projective (Z.X i) := fun i =>
    (IsProjective.iff_projective (P.homology i)).mp (hproj i)
  have hZle : Z.IsStrictlyLE a := (CochainComplex.isStrictlyLE_iff Z a).mpr fun k hk =>
    (P.exactAt_of_isLE a k hk).isZero_homology
  have hKZ : Z.IsKProjective := CochainComplex.isKProjective_of_projective Z a
  exact CochainComplex.IsKProjective.nonempty_homotopyEquiv_of_iso
    (e ≪≫ CochainComplex.derivedCoproductIso fun k => P.homology k)

end DerivedCategory.Invertible

end
