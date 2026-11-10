module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.KTheory.Grothendieck.Defs

/-!
# The Euler characteristic of a perfect complex in `K₀(R)`

Let `R` be a commutative ring. A perfect complex is represented by a bounded complex of finite
projective modules, and the alternating sum of the classes of its terms is an element of
`K₀(R)` that depends only on the complex up to quasi-isomorphism: it is additive on
distinguished triangles, changes sign under a shift, and vanishes on acyclic complexes. This is
the Euler characteristic of a perfect complex.

## Main results

* `K0.exists_eulerChar_perfect`: there is a map from perfect objects of the derived category to
  `K₀(R)` which on a bounded finite-projective representative is the alternating sum of the
  classes of its terms, is additive on distinguished triangles, and is invariant under
  isomorphism.

## Implementation notes

Perfectness is the predicate `StacksDraft.Perfect.IsPerfect` on objects of the derived category.
The alternating sum is indexed by an interval `Finset.Icc a b` containing the amplitude of a chosen
representative, and the statement asserts independence of that choice.

## References

* [Stacks Project, Tag 0AFY](https://stacks.math.columbia.edu/tag/0AFY)
-/

section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

private noncomputable def eulerCharComplex (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) : K0 R :=
  ∑ᶠ i : ℤ,
    (i.negOnePow : ℤ) • K0.mk
      ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R)

private theorem isZero_X_of_notMem_Icc {R : Type u} [CommRing R]
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b) {i : ℤ}
    (hi : i ∉ (Finset.Icc a b : Set ℤ)) : Limits.IsZero (P.X i) := by
  rw [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with h | h
  · exact P.isZero_of_isStrictlyGE a i h
  · exact P.isZero_of_isStrictlyLE b i h

private theorem support_eulerSummand_subset (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    Function.support (fun i : ℤ => (i.negOnePow : ℤ) • K0.mk
      ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R)) ⊆
      (Finset.Icc a b : Set ℤ) := by
  intro i hi
  by_contra hnot
  have : Subsingleton (P.X i) :=
    ModuleCat.subsingleton_of_isZero (isZero_X_of_notMem_Icc hGE hLE hnot)
  exact hi (by simp [K0.mk_eq_zero_of_subsingleton])

private theorem eulerCharComplex_eq_sum (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    eulerCharComplex R P hfinite hprojective =
      ∑ i ∈ Finset.Icc a b,
        (i.negOnePow : ℤ) • K0.mk
          ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R) :=
  finsum_eq_sum_of_support_subset _
    (support_eulerSummand_subset R P a b hGE hLE hfinite hprojective)

private theorem eulerCharComplex_eq_of_iso (R : Type u) [CommRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ≅ Q)
    (hfiniteP : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojectiveP : ∀ i : ℤ, Module.Projective R (P.X i))
    (hfiniteQ : ∀ i : ℤ, Module.Finite R (Q.X i))
    (hprojectiveQ : ∀ i : ℤ, Module.Projective R (Q.X i)) :
    eulerCharComplex R P hfiniteP hprojectiveP =
      eulerCharComplex R Q hfiniteQ hprojectiveQ := by
  unfold eulerCharComplex
  exact finsum_congr fun i => congrArg (_ • ·) (K0.mk_eq_of_iso _ _
    ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i).mapIso e).toLinearEquiv)

private theorem finite_shift (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i)) :
    ∀ i : ℤ, Module.Finite R ((P⟦n⟧).X i) := by
  intro i
  exact (Module.Finite.equiv_iff
    (P.shiftFunctorObjXIso n i (i + n) rfl).toLinearEquiv).mpr (hfinite (i + n))

private theorem projective_shift (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    ∀ i : ℤ, Module.Projective R ((P⟦n⟧).X i) := by
  intro i
  let := hprojective (i + n)
  exact Module.Projective.of_equiv'
    (P.shiftFunctorObjXIso n i (i + n) rfl).toLinearEquiv.symm

private theorem negOnePow_smul_finsum {M : Type*} [AddCommGroup M]
    (n : ℤ) (f : ℤ → M) :
    (n.negOnePow : ℤ) • (∑ᶠ i : ℤ, f i) =
      ∑ᶠ i : ℤ, (n.negOnePow : ℤ) • f i := by
  by_cases hn : Even n
  · rw [Int.negOnePow_even n hn]
    simp
  · rw [Int.negOnePow_odd n ((Int.not_even_iff_odd).mp hn)]
    simpa using (finsum_neg_distrib f).symm

private theorem eulerCharComplex_shift (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    eulerCharComplex R (P⟦n⟧)
        (finite_shift R P n hfinite) (projective_shift R P n hprojective) =
      (n.negOnePow : ℤ) • eulerCharComplex R P hfinite hprojective := by
  unfold eulerCharComplex
  let S := P⟦n⟧
  let f : ℤ → K0 R := fun j =>
    (j.negOnePow : ℤ) • K0.mk
      ({ carrier := P.X j, finite := hfinite j, projective := hprojective j } : FGProj R)
  let g : ℤ → K0 R := fun i =>
    (i.negOnePow : ℤ) • K0.mk
      ({ carrier := (P⟦n⟧).X i, finite := finite_shift R P n hfinite i, projective :=
        projective_shift R P n hprojective i } : FGProj R)
  change (∑ᶠ i : ℤ, g i) = (n.negOnePow : ℤ) • ∑ᶠ i : ℤ, f i
  calc
    (∑ᶠ i : ℤ, g i) =
        ∑ᶠ i : ℤ, (n.negOnePow : ℤ) • f (i + n) := by
          apply finsum_congr
          intro i
          simp only [g, f]
          have hclass : K0.mk
              ({ carrier := S.X i, finite := finite_shift R P n hfinite i, projective :=
                projective_shift R P n hprojective i } : FGProj R) =
              K0.mk
                ({ carrier := P.X (i + n), finite := hfinite (i + n), projective := hprojective (i +
                  n) } : FGProj R) :=
            K0.mk_eq_of_iso _ _ (P.shiftFunctorObjXIso n i (i + n) rfl).toLinearEquiv
          rw [hclass]
          change (i.negOnePow : ℤ) • _ =
            (n.negOnePow : ℤ) • ((i + n).negOnePow : ℤ) • _
          have hs : (i.negOnePow : ℤ) =
              (n.negOnePow : ℤ) * ((i + n).negOnePow : ℤ) := by
            conv_lhs => rw [show i = i + n - n by omega, Int.negOnePow_sub]
            simp only [Units.val_mul]
            ring
          rw [hs, mul_smul]
    _ = ∑ᶠ i : ℤ, (n.negOnePow : ℤ) • f i := by
      simpa only [Equiv.coe_addRight] using
        (finsum_comp_equiv (Equiv.addRight n)
          (f := fun j : ℤ => (n.negOnePow : ℤ) • f j))
    _ = (n.negOnePow : ℤ) • (∑ᶠ i : ℤ, f i) :=
      (negOnePow_smul_finsum n f).symm

private theorem perfect_shift (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K)
    (n : ℤ) : StacksDraft.Perfect.IsPerfect (K⟦n⟧) := by
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK
  refine ⟨P⟦n⟧, a - n, b - n, ?_, ?_,
    finite_shift R P n hfinite, projective_shift R P n hprojective, ?_⟩
  · let := hGE
    exact P.isStrictlyGE_shift a n (a - n) (by omega)
  · let := hLE
    exact P.isStrictlyLE_shift b n (b - n) (by omega)
  · exact ⟨(shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app P⟩

open CategoryTheory.Limits

variable (R : Type u) [CommRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ)

private theorem cycles_retract (h : Homotopy (𝟙 P) 0) (i : ℤ) :
    ∃ r : P.X i ⟶ P.cycles i, P.iCycles i ≫ r = 𝟙 _ := by
  let k : P.X i ⟶ P.X i := h.hom i (i - 1) ≫ P.d (i - 1) i
  have hk : k ≫ P.d i (i + 1) = 0 := by
    dsimp [k]
    rw [Category.assoc, P.d_comp_d, comp_zero]
  let r : P.X i ⟶ P.cycles i := P.liftCycles k (i + 1) (by simp) hk
  refine ⟨r, ?_⟩
  have hr : r ≫ P.iCycles i = k := P.liftCycles_i k (i + 1) (by simp) hk
  have hi := h.comm i
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at hi
  simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] at hi
  have ht : P.iCycles i ≫ k = P.iCycles i := by
    dsimp [k]
    calc
      _ = P.iCycles i ≫ (P.d i (i + 1) ≫ h.hom (i + 1) i +
          h.hom i (i - 1) ≫ P.d (i - 1) i) := by simp
      _ = P.iCycles i := by rw [← hi]; simp
  apply (cancel_mono (P.iCycles i)).mp
  simpa only [Category.assoc, hr, Category.comp_id, Category.id_comp] using ht

private theorem cycles_finite (h : Homotopy (𝟙 P) 0)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i)) (i : ℤ) :
    Module.Finite R (P.cycles i) := by
  obtain ⟨r, hr⟩ := cycles_retract R P h i
  let := hfinite i
  apply Module.Finite.of_surjective r.hom
  intro x
  refine ⟨(P.iCycles i).hom x, ?_⟩
  have := congrArg ModuleCat.Hom.hom hr
  exact DFunLike.congr_fun this x

private theorem cycles_projective (h : Homotopy (𝟙 P) 0)
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) (i : ℤ) :
    Module.Projective R (P.cycles i) := by
  obtain ⟨r, hr⟩ := cycles_retract R P h i
  let := hprojective i
  apply Module.Projective.of_split (P.iCycles i).hom r.hom
  have := congrArg ModuleCat.Hom.hom hr
  exact this

private noncomputable def cyclesShortComplex (i : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (P.iCycles i) (P.toCycles i (i + 1)) (by
    apply (cancel_mono (P.iCycles (i + 1))).mp
    simp [Category.assoc, P.toCycles_i])

private theorem cyclesShortComplex_shortExact (hacyclic : P.Acyclic) (i : ℤ) :
    (cyclesShortComplex R P i).ShortExact := by
  let S := cyclesShortComplex R P i
  have hexact : S.Exact := by
    rw [S.moduleCat_exact_iff]
    intro x hx
    dsimp [S, cyclesShortComplex] at x hx
    have hd : P.d i (i + 1) x = 0 := by
      rw [← P.toCycles_i]
      exact (congrArg (P.iCycles (i + 1)) (show P.toCycles i (i + 1) x = 0 from hx)).trans
        (map_zero _)
    let f : ModuleCat.of R R ⟶ P.X i :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton R (P.X i) x)
    have hf : f ≫ P.d i (i + 1) = 0 := by
      ext
      simpa [f] using hd
    refine ⟨P.liftCycles f (i + 1) (by simp) hf (1 : R), ?_⟩
    exact (congrArg (fun q : ModuleCat.of R R ⟶ P.X i => q (1 : R))
      (P.liftCycles_i f (i + 1) (by simp) hf)).trans (by simp [f])
  have hmono : Mono S.f := by
    dsimp [S, cyclesShortComplex]
    infer_instance
  have hepi : Epi S.g := by
    dsimp [S, cyclesShortComplex]
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    have hEx : (P.sc' i (i + 1) (i + 2)).Exact :=
      (P.exactAt_iff' i (i + 1) (i + 2) (by simp) (by rw [CochainComplex.next]; omega)).mp
        ((P.acyclic_iff.mp hacyclic) (i + 1))
    have hcycle : P.d (i + 1) (i + 2) ((P.iCycles (i + 1)) x) = 0 :=
      congrArg (fun f : P.cycles (i + 1) ⟶ P.X (i + 2) => f x) (P.iCycles_d (i + 1) (i + 2))
    obtain ⟨y, hy⟩ := (P.sc' i (i + 1) (i + 2)).moduleCat_exact_iff.mp hEx
      ((P.iCycles (i + 1)) x) hcycle
    refine ⟨y, ?_⟩
    apply (ModuleCat.mono_iff_injective (P.iCycles (i + 1))).mp inferInstance
    exact (congrArg (fun f : P.X i ⟶ P.X (i + 1) => f y) (P.toCycles_i i (i + 1))).trans hy
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

/-- If `t i = u (i + 1) + v i`, the signed sum of `t` is `-(signed sum of u) + signed sum of v`. -/
private theorem finsum_negOnePow_smul_of_succ_add (t u v : ℤ → K0 R)
    (ht : ∀ i, t i = u (i + 1) + v i)
    (hu : Function.HasFiniteSupport fun i : ℤ => (i.negOnePow : ℤ) • u i)
    (hv : Function.HasFiniteSupport fun i : ℤ => (i.negOnePow : ℤ) • v i) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • t i =
      -(∑ᶠ i : ℤ, (i.negOnePow : ℤ) • u i) + ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • v i := by
  set x : ℤ → K0 R := fun i => (i.negOnePow : ℤ) • u i
  have hxshift : Function.HasFiniteSupport (fun i : ℤ => -x (i + 1)) := by
    have : Function.HasFiniteSupport (fun i : ℤ => x (i + 1)) :=
      Set.Finite.preimage (fun _ _ _ _ hij => by omega) hu
    simpa only [Function.HasFiniteSupport, Function.support, neg_ne_zero] using this
  calc
    _ = ∑ᶠ i : ℤ, (-x (i + 1) + (i.negOnePow : ℤ) • v i) := by
      refine finsum_congr fun i => ?_
      rw [ht i, smul_add]
      simp only [x, Int.negOnePow_succ, Units.val_neg, neg_smul]
      abel
    _ = _ := by
      rw [finsum_add_distrib hxshift hv, finsum_neg_distrib,
        show (∑ᶠ i : ℤ, x (i + 1)) = ∑ᶠ i : ℤ, x i from finsum_comp_equiv (Equiv.addRight 1)]

/-- The class of an object isomorphic to a product is the sum of the classes of the factors. -/
private theorem mk_eq_add_of_iso_prod (A B C : FGProj R)
    (e : C.carrier ≃ₗ[R] A.carrier × B.carrier) :
    K0.mk C = K0.mk A + K0.mk B := by
  rw [← K0.mk_directSum_eq]
  exact K0.mk_eq_of_iso C (A.directSum B) e

private theorem k0_term_eq_cycles (h : Homotopy (𝟙 P) 0)
    (hacyclic : P.Acyclic)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) (i : ℤ) :
    K0.mk ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R) =
      K0.mk ({ carrier := P.cycles i, finite := cycles_finite R P h hfinite i, projective :=
        cycles_projective R P h hprojective i } : FGProj R) +
      K0.mk ({ carrier := P.cycles (i+1), finite := cycles_finite R P h hfinite (i+1), projective :=
        cycles_projective R P h hprojective (i+1) } : FGProj R) := by
  let A : FGProj R :=
    { carrier := P.cycles i
      finite := cycles_finite R P h hfinite i
      projective := cycles_projective R P h hprojective i }
  let B : FGProj R :=
    { carrier := P.cycles (i + 1)
      finite := cycles_finite R P h hfinite (i + 1)
      projective := cycles_projective R P h hprojective (i + 1) }
  let C : FGProj R := { carrier := P.X i, finite := hfinite i, projective := hprojective i }
  have : CategoryTheory.Projective (P.cycles (i+1)) := by
    let := cycles_projective R P h hprojective (i+1)
    infer_instance
  have : CategoryTheory.Projective ((cyclesShortComplex R P i).X₃) := by
    change CategoryTheory.Projective (P.cycles (i+1))
    infer_instance
  let s := (cyclesShortComplex_shortExact R P hacyclic i).splittingOfProjective
  let e : P.X i ≅ ModuleCat.of R (P.cycles i × P.cycles (i+1)) :=
    s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _
  exact mk_eq_add_of_iso_prod R A B C e.toLinearEquiv

private theorem cycles_class_finiteSupport (h : Homotopy (𝟙 P) 0)
    (a b : ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    Function.HasFiniteSupport (fun i : ℤ =>
      (i.negOnePow : ℤ) • K0.mk
        ({ carrier := P.cycles i, finite := cycles_finite R P h hfinite i, projective :=
          cycles_projective R P h hprojective i } : FGProj R)) := by
  apply (Finset.finite_toSet (Finset.Icc a b)).subset
  intro i hi
  by_contra hnot
  have : Subsingleton (P.X i) :=
    ModuleCat.subsingleton_of_isZero (isZero_X_of_notMem_Icc hGE hLE hnot)
  have : Subsingleton (P.cycles i) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective (P.iCycles i)).mp inferInstance
      (Subsingleton.elim _ _)⟩
  exact hi (by simp [K0.mk_eq_zero_of_subsingleton])

private theorem isKProjective_of_projective_X (b : ℤ) (hLE : P.IsStrictlyLE b)
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) : P.IsKProjective :=
  have (i : ℤ) : CategoryTheory.Projective (P.X i) := by
    have := hprojective i
    infer_instance
  CochainComplex.isKProjective_of_projective P b

private theorem eulerCharComplex_eq_zero_of_acyclic
    (a b : ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i))
    (hacyclic : P.Acyclic) :
    eulerCharComplex R P hfinite hprojective = 0 := by
  classical
  have : P.IsKProjective := isKProjective_of_projective_X R P b hLE hprojective
  let h : Homotopy (𝟙 P) 0 := CochainComplex.IsKProjective.homotopyZero (𝟙 P) hacyclic
  let z : ℤ → K0 R := fun i =>
    K0.mk ({ carrier := P.cycles i, finite := cycles_finite R P h hfinite i, projective :=
      cycles_projective R P h hprojective i } : FGProj R)
  have hz : Function.HasFiniteSupport fun i : ℤ => (i.negOnePow : ℤ) • z i :=
    cycles_class_finiteSupport R P h a b hGE hLE hfinite hprojective
  unfold eulerCharComplex
  rw [finsum_negOnePow_smul_of_succ_add R _ z z
    (fun i => by rw [k0_term_eq_cycles R P h hacyclic hfinite hprojective i, add_comm]) hz hz]
  exact neg_add_cancel _

private noncomputable def coneTermIso
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ≅
      ModuleCat.of R ((P.X (i + 1)) × (Q.X i)) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp) ≪≫
    ModuleCat.biprodIsoProd _ _

private theorem cone_finite
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (hfiniteP : ∀ i : ℤ, Module.Finite R (P.X i))
    (hfiniteQ : ∀ i : ℤ, Module.Finite R (Q.X i)) :
    ∀ i : ℤ, Module.Finite R ((CochainComplex.mappingCone f).X i) := by
  intro i
  let := hfiniteP (i + 1)
  let := hfiniteQ i
  exact (Module.Finite.equiv_iff (coneTermIso R f i).toLinearEquiv).mpr inferInstance

private theorem cone_projective
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (hprojectiveP : ∀ i : ℤ, Module.Projective R (P.X i))
    (hprojectiveQ : ∀ i : ℤ, Module.Projective R (Q.X i)) :
    ∀ i : ℤ, Module.Projective R ((CochainComplex.mappingCone f).X i) := by
  intro i
  let := hprojectiveP (i + 1)
  let := hprojectiveQ i
  exact Module.Projective.of_equiv' (coneTermIso R f i).toLinearEquiv.symm

private theorem cone_class_eq
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (i : ℤ)
    (hfiniteP : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojectiveP : ∀ i : ℤ, Module.Projective R (P.X i))
    (hfiniteQ : ∀ i : ℤ, Module.Finite R (Q.X i))
    (hprojectiveQ : ∀ i : ℤ, Module.Projective R (Q.X i)) :
    K0.mk
      ({ carrier := (CochainComplex.mappingCone f).X i
         finite := cone_finite R f hfiniteP hfiniteQ i
         projective := cone_projective R f hprojectiveP hprojectiveQ i } : FGProj R) =
    K0.mk
      ({ carrier := P.X (i + 1)
         finite := hfiniteP (i + 1)
         projective := hprojectiveP (i + 1) } : FGProj R) +
    K0.mk
      ({ carrier := Q.X i
         finite := hfiniteQ i
         projective := hprojectiveQ i } : FGProj R) :=
      by
  let A : FGProj R :=
    { carrier := P.X (i + 1)
      finite := hfiniteP (i + 1)
      projective := hprojectiveP (i + 1) }
  let B : FGProj R := { carrier := Q.X i, finite := hfiniteQ i, projective := hprojectiveQ i }
  let C : FGProj R :=
    { carrier := (CochainComplex.mappingCone f).X i
      finite := cone_finite R f hfiniteP hfiniteQ i
      projective := cone_projective R f hprojectiveP hprojectiveQ i }
  exact mk_eq_add_of_iso_prod R A B C (coneTermIso R f i).toLinearEquiv

private theorem eulerSummand_finiteSupport
    (a b : ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) :
    Function.HasFiniteSupport (fun i : ℤ => (i.negOnePow : ℤ) •
      K0.mk ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R)) :=
  (Finset.finite_toSet _).subset (support_eulerSummand_subset R P a b hGE hLE hfinite hprojective)

private theorem eulerCharComplex_cone
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (aP bP aQ bQ : ℤ)
    (hGEP : P.IsStrictlyGE aP) (hLEP : P.IsStrictlyLE bP)
    (hGEQ : Q.IsStrictlyGE aQ) (hLEQ : Q.IsStrictlyLE bQ)
    (hfiniteP : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojectiveP : ∀ i : ℤ, Module.Projective R (P.X i))
    (hfiniteQ : ∀ i : ℤ, Module.Finite R (Q.X i))
    (hprojectiveQ : ∀ i : ℤ, Module.Projective R (Q.X i)) :
    eulerCharComplex R (CochainComplex.mappingCone f)
      (cone_finite R f hfiniteP hfiniteQ)
      (cone_projective R f hprojectiveP hprojectiveQ) =
    -eulerCharComplex R P hfiniteP hprojectiveP +
      eulerCharComplex R Q hfiniteQ hprojectiveQ := by
  change (∑ᶠ i : ℤ, (i.negOnePow : ℤ) •
    K0.mk
      ({ carrier := (CochainComplex.mappingCone f).X i
         finite := cone_finite R f hfiniteP hfiniteQ i
         projective := cone_projective R f hprojectiveP hprojectiveQ i } : FGProj R)) =
    -(∑ᶠ i : ℤ, (i.negOnePow : ℤ) •
      K0.mk ({ carrier := P.X i, finite := hfiniteP i, projective := hprojectiveP i } : FGProj R)) +
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) •
      K0.mk ({ carrier := Q.X i, finite := hfiniteQ i, projective := hprojectiveQ i } : FGProj R)
  exact finsum_negOnePow_smul_of_succ_add R _ _ _
    (cone_class_eq R f · hfiniteP hprojectiveP hfiniteQ hprojectiveQ)
    (eulerSummand_finiteSupport R P aP bP hGEP hLEP hfiniteP hprojectiveP)
    (eulerSummand_finiteSupport R Q aQ bQ hGEQ hLEQ hfiniteQ hprojectiveQ)

private theorem cone_isStrictlyGE
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (aP aQ : ℤ) (hP : P.IsStrictlyGE aP) (hQ : Q.IsStrictlyGE aQ) :
    (CochainComplex.mappingCone f).IsStrictlyGE (min (aP - 1) aQ) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · let := hP
    exact P.isZero_of_isStrictlyGE aP (i + 1) (by omega)
  · let := hQ
    exact Q.isZero_of_isStrictlyGE aQ i (by omega)

private theorem cone_isStrictlyLE
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (bP bQ : ℤ) (hP : P.IsStrictlyLE bP) (hQ : Q.IsStrictlyLE bQ) :
    (CochainComplex.mappingCone f).IsStrictlyLE (max (bP - 1) bQ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · let := hP
    exact P.isZero_of_isStrictlyLE bP (i + 1) (by omega)
  · let := hQ
    exact Q.isZero_of_isStrictlyLE bQ i (by omega)

private theorem acyclic_of_isZero_Q_obj
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : IsZero (DerivedCategory.Q.obj P)) : P.Acyclic := by
  intro i
  exact (P.exactAt_iff_isZero_homology i).mpr
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P).isZero_iff.mp
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map_isZero h))

private theorem cone_acyclic_of_isIso_Q_map
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (h : IsIso (DerivedCategory.Q.map f)) :
    (CochainComplex.mappingCone f).Acyclic := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  have hzero : IsZero ((DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle f)).obj₃) :=
    Triangle.isZero₃_of_isIso₁ _ hT h
  exact acyclic_of_isZero_Q_obj R _ hzero

private theorem exists_cochainMap_of_derivedMap
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    [P.IsKProjective] (g₀ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :
    ∃ f : P ⟶ Q, DerivedCategory.Q.map f = g₀ := by
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let η := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let g : DerivedCategory.Qh.obj (H.obj P) ⟶ DerivedCategory.Qh.obj (H.obj Q) :=
    (η.app P).hom ≫ g₀ ≫ (η.app Q).inv
  obtain ⟨h, hh⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj Q)).surjective g
  obtain ⟨f, rfl⟩ := H.map_surjective h
  refine ⟨f, ?_⟩
  apply (cancel_epi (η.app P).hom).mp
  calc
    (η.app P).hom ≫ DerivedCategory.Q.map f =
        DerivedCategory.Qh.map (H.map f) ≫ (η.app Q).hom :=
      (DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} R) f).symm
    _ = (η.app P).hom ≫ g₀ := by
      rw [hh]
      simp [g, Category.assoc]

private theorem eulerCharComplex_eq_of_derivedIso
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (aP bP aQ bQ : ℤ)
    (hGEP : P.IsStrictlyGE aP) (hLEP : P.IsStrictlyLE bP)
    (hGEQ : Q.IsStrictlyGE aQ) (hLEQ : Q.IsStrictlyLE bQ)
    (hfiniteP : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojectiveP : ∀ i : ℤ, Module.Projective R (P.X i))
    (hfiniteQ : ∀ i : ℤ, Module.Finite R (Q.X i))
    (hprojectiveQ : ∀ i : ℤ, Module.Projective R (Q.X i))
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    eulerCharComplex R P hfiniteP hprojectiveP =
      eulerCharComplex R Q hfiniteQ hprojectiveQ := by
  have : P.IsKProjective := isKProjective_of_projective_X R P bP hLEP hprojectiveP
  obtain ⟨f, hf⟩ := exists_cochainMap_of_derivedMap R e.hom
  have hiso : IsIso (DerivedCategory.Q.map f) := by
    rw [hf]
    infer_instance
  have hacyclic := cone_acyclic_of_isIso_Q_map R f hiso
  have hzero := eulerCharComplex_eq_zero_of_acyclic R
    (CochainComplex.mappingCone f)
    (min (aP - 1) aQ) (max (bP - 1) bQ)
    (cone_isStrictlyGE R f aP aQ hGEP hGEQ)
    (cone_isStrictlyLE R f bP bQ hLEP hLEQ)
    (cone_finite R f hfiniteP hfiniteQ)
    (cone_projective R f hprojectiveP hprojectiveQ) hacyclic
  rw [eulerCharComplex_cone R f aP bP aQ bQ hGEP hLEP hGEQ hLEQ
    hfiniteP hprojectiveP hfiniteQ hprojectiveQ] at hzero
  exact (eq_of_sub_eq_zero (by simpa only [neg_add_eq_sub] using hzero)).symm

private theorem exists_eulerChar_representative
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K) :
    ∃ x : K0 R, ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
      (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ Nonempty (K ≅ DerivedCategory.Q.obj P) ∧
        x = eulerCharComplex R P hfinite hprojective := by
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, e⟩ := hK
  exact ⟨eulerCharComplex R P hfinite hprojective,
    P, a, b, hfinite, hprojective, hGE, hLE, e, rfl⟩

private noncomputable def eulerCharPerfect
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : {K : DerivedCategory (ModuleCat.{u} R) // StacksDraft.Perfect.IsPerfect K}) : K0 R :=
  Classical.choose (exists_eulerChar_representative R K.1 K.2)

private theorem eulerCharPerfect_eq
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (P.X i))
    (e : K ≅ DerivedCategory.Q.obj P) :
    eulerCharPerfect R ⟨K, hK⟩ = eulerCharComplex R P hfinite hprojective := by
  obtain ⟨Q, aQ, bQ, hfiniteQ, hprojectiveQ, hGEQ, hLEQ, ⟨eQ⟩, heq⟩ :=
    Classical.choose_spec (exists_eulerChar_representative R K hK)
  change Classical.choose (exists_eulerChar_representative R K hK) = _
  rw [heq]
  exact eulerCharComplex_eq_of_derivedIso R aQ bQ a b hGEQ hLEQ hGE hLE
    hfiniteQ hprojectiveQ hfinite hprojective (eQ.symm ≪≫ e)

private theorem eulerCharPerfect_shift
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K)
    (n : ℤ) :
    eulerCharPerfect R ⟨K⟦n⟧, perfect_shift R K hK n⟩ =
      (n.negOnePow : ℤ) • eulerCharPerfect R ⟨K, hK⟩ := by
  have hK' := hK
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK'
  have hGES : (P⟦n⟧).IsStrictlyGE (a - n) := by
    let := hGE
    exact P.isStrictlyGE_shift a n (a - n) (by omega)
  have hLES : (P⟦n⟧).IsStrictlyLE (b - n) := by
    let := hLE
    exact P.isStrictlyLE_shift b n (b - n) (by omega)
  let eS : K⟦n⟧ ≅ DerivedCategory.Q.obj (P⟦n⟧) :=
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app P
  calc
    _ = eulerCharComplex R (P⟦n⟧)
        (finite_shift R P n hfinite) (projective_shift R P n hprojective) :=
      eulerCharPerfect_eq R (K⟦n⟧) (perfect_shift R K hK n)
        (P⟦n⟧) (a - n) (b - n) hGES hLES _ _ eS
    _ = (n.negOnePow : ℤ) • eulerCharComplex R P hfinite hprojective :=
      eulerCharComplex_shift R P n hfinite hprojective
    _ = (n.negOnePow : ℤ) • eulerCharPerfect R ⟨K, hK⟩ := by
      rw [eulerCharPerfect_eq R K hK P a b hGE hLE hfinite hprojective e]

private theorem eulerCharPerfect_triangle
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)))
    (h₁ : StacksDraft.Perfect.IsPerfect T.obj₁) (h₂ : StacksDraft.Perfect.IsPerfect T.obj₂)
    (h₃ : StacksDraft.Perfect.IsPerfect T.obj₃) :
    eulerCharPerfect R ⟨T.obj₂, h₂⟩ =
      eulerCharPerfect R ⟨T.obj₁, h₁⟩ + eulerCharPerfect R ⟨T.obj₃, h₃⟩ := by
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨P, aP, bP, hGEP, hLEP, hfiniteP, hprojectiveP, ⟨eP⟩⟩ := h₁'
  obtain ⟨Q, aQ, bQ, hGEQ, hLEQ, hfiniteQ, hprojectiveQ, ⟨eQ⟩⟩ := h₂'
  have : P.IsKProjective := isKProjective_of_projective_X R P bP hLEP hprojectiveP
  let g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q :=
    eP.inv ≫ T.mor₁ ≫ eQ.hom
  obtain ⟨f, hf⟩ := exists_cochainMap_of_derivedMap R g
  have hcomm : T.mor₁ ≫ eQ.hom = eP.hom ≫ DerivedCategory.Q.map f := by
    rw [hf]
    simp [g]
  let U := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let eT : T ≅ U := isoTriangleOfIso₁₂ T U hT
    (DerivedCategory.mappingCone_triangle_distinguished f) eP eQ hcomm
  have e₃ : T.obj₃ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone f) :=
    Triangle.π₃.mapIso eT
  have hGEC := cone_isStrictlyGE R f aP aQ hGEP hGEQ
  have hLEC := cone_isStrictlyLE R f bP bQ hLEP hLEQ
  have h₁eq := eulerCharPerfect_eq R T.obj₁ h₁ P aP bP
    hGEP hLEP hfiniteP hprojectiveP eP
  have h₂eq := eulerCharPerfect_eq R T.obj₂ h₂ Q aQ bQ
    hGEQ hLEQ hfiniteQ hprojectiveQ eQ
  have h₃eq := eulerCharPerfect_eq R T.obj₃ h₃ (CochainComplex.mappingCone f)
    (min (aP - 1) aQ) (max (bP - 1) bQ) hGEC hLEC
    (cone_finite R f hfiniteP hfiniteQ)
    (cone_projective R f hprojectiveP hprojectiveQ) e₃
  rw [h₁eq, h₂eq, h₃eq,
    eulerCharComplex_cone R f aP bP aQ bQ hGEP hLEP hGEQ hLEQ
      hfiniteP hprojectiveP hfiniteQ hprojectiveQ]
  abel

/-- **Stacks 0AFY.** Perfect complexes over `R` have an Euler characteristic in `K₀(R)` which
changes by `(-1)ⁿ` under a shift by `n`, is additive in distinguished triangles, and is the
alternating sum of the classes of the terms of every bounded finite-projective representative. -/
@[stacks 0AFY, sga "6 0 3.1" "special case"]
public theorem K0.exists_eulerChar_perfect (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ∃ c : {K : DerivedCategory (ModuleCat.{u} R) // StacksDraft.Perfect.IsPerfect K} → K0 R,
      (∀ (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K) (n : ℤ),
        ∃ hKn : StacksDraft.Perfect.IsPerfect (K⟦n⟧),
          c ⟨K⟦n⟧, hKn⟩ = (n.negOnePow : ℤ) • c ⟨K, hK⟩) ∧
      (∀ (T : Triangle (DerivedCategory (ModuleCat.{u} R))),
        T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) →
        ∀ (h₁ : StacksDraft.Perfect.IsPerfect T.obj₁) (h₂ : StacksDraft.Perfect.IsPerfect T.obj₂)
          (h₃ : StacksDraft.Perfect.IsPerfect T.obj₃),
          c ⟨T.obj₂, h₂⟩ = c ⟨T.obj₁, h₁⟩ + c ⟨T.obj₃, h₃⟩) ∧
      (∀ (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K)
        (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
        P.IsStrictlyGE a → P.IsStrictlyLE b →
        (hfinite : ∀ i : ℤ, Module.Finite R (P.X i)) →
        (hprojective : ∀ i : ℤ, Module.Projective R (P.X i)) →
        Nonempty (K ≅ DerivedCategory.Q.obj P) →
        c ⟨K, hK⟩ = ∑ i ∈ Finset.Icc a b,
          (i.negOnePow : ℤ) • K0.mk
            ({ carrier := P.X i, finite := hfinite i, projective := hprojective i } : FGProj R))
    := by
  refine ⟨eulerCharPerfect R, ?_, ?_, ?_⟩
  · intro K hK n
    exact ⟨perfect_shift R K hK n, eulerCharPerfect_shift R K hK n⟩
  · intro T hT h₁ h₂ h₃
    exact eulerCharPerfect_triangle R T hT h₁ h₂ h₃
  · intro K hK P a b hGE hLE hfinite hprojective ⟨e⟩
    rw [eulerCharPerfect_eq R K hK P a b hGE hLE hfinite hprojective e]
    exact eulerCharComplex_eq_sum R P a b hGE hLE hfinite hprojective

end
