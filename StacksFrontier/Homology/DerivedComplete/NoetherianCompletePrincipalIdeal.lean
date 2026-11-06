module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.CountableMilnorTower
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.ProIsoBoundedTorsion
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor



/-!
# Naive and derived completion for a principal ideal

Let `f` be an element of a commutative ring `A`. The canonical natural transformation from
derived completion at `(f)` to the derived inverse limit of tensor products with `A/(f^n)` is an
isomorphism exactly when the `f`-power torsion in `A` is bounded.

## Main definitions

No new definitions are introduced.

## Main results

* `PrincipalNaiveCompletion.derivedCompletionToNaive_isIso_iff_torsionBounded` characterizes when
  naive derived
  completion agrees with derived completion at a principal ideal.

## Implementation notes

Positive powers are indexed by `n : ℕ` using exponent `n + 1`. Both completion functors are
specified by their Milnor triangles. The equations after the two product projections say that
the displayed natural transformation is the canonical one induced by the Koszul augmentation,
not merely an unrelated transformation between two choices of derived limits. Derived completion
also retains its adjunction to the inclusion of derived-complete objects from Tag 0920.

## References

* [The Stacks Project, Tag 0923](https://stacks.math.columbia.edu/tag/0923)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace PrincipalNaiveCompletion

end PrincipalNaiveCompletion
end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite ProTorsion
open HomologicalComplex (doubleIsoOfIsZero singleMap singleConeNegOneIso
  singleConeZeroIso singleCone_d singleConeDoubleIso)

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace PrincipalNaiveCompletion

/-- Instance search no longer unfolds `Functor.const` to see the commutative ring `A`. -/
local instance constRingCatObjCommRing (A : Type u) [CommRing A] (n : ℕᵒᵖ) :
    CommRing (((Functor.const ℕᵒᵖ).obj (RingCat.of A)).obj n) :=
  inferInstanceAs (CommRing A)

private abbrev tensorTowerIso (A : Type u) [CommRing A]
    (T U : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (E : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)) :
    E ⋙ T.tensor.obj K ≅ E ⋙ U.tensor.obj K :=
  Functor.isoWhiskerLeft E (AdicCompletionTor.tensorFunctorIso A T U K)

private abbrev koszulTensorTowerIso (A : Type u) [CommRing A] (f : A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (NoetherianKoszulProIso.koszulPowerSystem (fun _ : Fin 1 ↦ f) ⋙ T.tensor.obj K) ≅
      (NoetherianKoszulProIso.koszulPowerSystem (fun _ : Fin 1 ↦ f) ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K) :=
  tensorTowerIso A T (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A) K _

/-- The tower isomorphisms intertwine every morphism of towers. -/
private theorem tensorTowerIso_naturality (A : Type u) [CommRing A]
    (T U : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A))
    {E F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)} (φ : E ⟶ F) :
    Functor.whiskerRight φ (T.tensor.obj K) ≫ (tensorTowerIso A T U K F).hom =
      (tensorTowerIso A T U K E).hom ≫ Functor.whiskerRight φ (U.tensor.obj K) := by
  ext n
  exact (AdicCompletionTor.tensorFunctorIso A T U K).hom.naturality (φ.app n)


/-- The torsion tower `(A[f^n])`, with transition maps multiplication by `f`, is zero as a
pro-object exactly when the `f`-power torsion of `A` is bounded. -/
private theorem torsion_proZero_iff_torsionBounded (A : Type u) [CommRing A] (f : A) :
    (∀ n : ℕ, ∃ k : ℕ, ∀ x ∈ Submodule.torsionBy A A (f ^ (n + k)), f ^ k * x = 0) ↔
      TorsionBounded A f := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h 1
    have step : ∀ j, Submodule.torsionBy A A (f ^ (k + 1 + j)) ≤
        Submodule.torsionBy A A (f ^ (k + 1)) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih =>
        intro x hx
        apply ih
        simp only [Submodule.mem_torsionBy_iff, smul_eq_mul] at hx ⊢
        have hy : f ^ (j + 1) * x ∈ Submodule.torsionBy A A (f ^ (1 + k)) := by
          simp only [Submodule.mem_torsionBy_iff, smul_eq_mul]
          rw [← mul_assoc, ← pow_add, ← hx]
          ring_nf
        rw [← hk _ hy]
        ring_nf
    refine ⟨k + 1, by omega, fun m hm => le_antisymm (torsion_mono A f hm) ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact step j
  · rintro ⟨c, -, hc⟩ n
    refine ⟨c, fun x hx => ?_⟩
    have hx' : x ∈ Submodule.torsionBy A A (f ^ c) := by rwa [hc (n + c) (by omega)]
    simpa [Submodule.mem_torsionBy_iff, smul_eq_mul] using hx'

/-- Multiplication by the difference of the powers maps one power-torsion submodule to another. -/
private def torsionByPowTransition {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) {m n : ℕ} (h : n ≤ m) :
    Submodule.torsionBy R M (f ^ m) →ₗ[R] Submodule.torsionBy R M (f ^ n) :=
  (((DistribSMul.toLinearMap R M (f ^ (m - n))).comp
    (Submodule.torsionBy R M (f ^ m)).subtype)).codRestrict _ (by
      intro x
      change f ^ n • (f ^ (m - n) • (x : M)) = 0
      rw [← mul_smul, ← pow_add, Nat.add_sub_of_le h]
      exact x.property)

private theorem torsionByPowTransition_apply {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) {m n : ℕ} (h : n ≤ m)
    (x : Submodule.torsionBy R M (f ^ m)) :
    (torsionByPowTransition f h x : M) = f ^ (m - n) • (x : M) := rfl

private theorem torsionByPowTransition_id {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) (n : ℕ) :
    torsionByPowTransition (M := M) f (le_refl n) = LinearMap.id := by
  ext x
  simp [torsionByPowTransition_apply]

private theorem torsionByPowTransition_comp {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) {m n k : ℕ} (h : n ≤ m) (h' : k ≤ n) :
    (torsionByPowTransition (M := M) f h').comp (torsionByPowTransition f h) =
      torsionByPowTransition f (h'.trans h) := by
  ext x
  show f ^ (n - k) • (f ^ (m - n) • (x : M)) = f ^ (m - k) • (x : M)
  rw [← mul_smul, ← pow_add, show n - k + (m - n) = m - k by omega]

/-- The positive power-torsion tower, with multiplication transitions. -/
private def torsionPowerSystem {R : Type u} [CommRing R] (f : R)
    (M : ModuleCat.{v} R) : ℕᵒᵖ ⥤ ModuleCat.{v} R where
  obj n := ModuleCat.of R (Submodule.torsionBy R M (f ^ (n.unop + 1)))
  map {n m} φ := ModuleCat.ofHom (torsionByPowTransition f
    (Nat.add_le_add_right (leOfHom φ.unop) 1))
  map_id n := by
    apply ModuleCat.hom_ext
    exact torsionByPowTransition_id f _
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    exact (torsionByPowTransition_comp f
      (Nat.add_le_add_right (leOfHom φ.unop) 1)
      (Nat.add_le_add_right (leOfHom ψ.unop) 1)).symm

private theorem torsionPowerSystem_map_apply {R : Type u} [CommRing R] (f : R)
    (M : ModuleCat.{v} R) {m n : ℕ} (h : n ≤ m)
    (x : Submodule.torsionBy R M (f ^ (m + 1))) :
    Subtype.val (((torsionPowerSystem f M).map (homOfLE h).op).hom x) = f ^ (m - n) • (x : M) := by
  show f ^ ((m + 1) - (n + 1)) • (x : M) = _
  rw [Nat.add_sub_add_right]


/-- The positive power-torsion tower is pro-zero exactly when power torsion is bounded. -/
private theorem torsionPowerSystem_proZero_iff (A : Type u) [CommRing A] (f : A) :
    (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (torsionPowerSystem f (ModuleCat.of A A)).map (homOfLE h).op = 0) ↔
        ProTorsion.TorsionBounded A f := by
  constructor
  · intro h
    apply (torsion_proZero_iff_torsionBounded A f).mp
    intro n
    by_cases hn : n = 0
    · subst n
      refine ⟨0, fun x hx ↦ ?_⟩
      simpa [Submodule.mem_torsionBy_iff, smul_eq_mul] using hx
    · obtain ⟨m, hm, hmap⟩ := h (n - 1)
      refine ⟨m - (n - 1), fun x hx ↦ ?_⟩
      have hx' : x ∈ Submodule.torsionBy A A (f ^ (m + 1)) := by
        simpa only [show n + (m - (n - 1)) = m + 1 by omega, smul_eq_mul,
          Submodule.mem_torsionBy_iff] using hx
      calc
        f ^ (m - (n - 1)) * x =
            Subtype.val (((torsionPowerSystem f (ModuleCat.of A A)).map
              (homOfLE hm).op).hom ⟨x, hx'⟩) :=
          (torsionPowerSystem_map_apply f (ModuleCat.of A A) hm ⟨x, hx'⟩).symm
        _ = 0 := by
          rw [hmap]
          rfl
  · intro h n
    obtain ⟨k, hk⟩ := (torsion_proZero_iff_torsionBounded A f).mpr h (n + 1)
    refine ⟨n + k, Nat.le_add_right n k, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    let x' : Submodule.torsionBy A A (f ^ (n + k + 1)) := x
    show f ^ ((n + k + 1) - (n + 1)) * (x' : A) = 0
    rw [show (n + k + 1) - (n + 1) = k by omega]
    apply hk
    have hx : f ^ (n + k + 1) * (x' : A) = 0 := x'.property
    show f ^ (n + 1 + k) * (x' : A) = 0
    simpa only [show n + k + 1 = n + 1 + k by omega] using hx

section Milnor

variable {C : Type*} [Category C]

private lemma pi_π_map_congr (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)]
    {a b n : ℕ} (e : a = b) (h : n ≤ a) (h' : n ≤ b) :
    Pi.π (fun n : ℕ ↦ F.obj (op n)) a ≫ F.map (homOfLE h).op =
      Pi.π (fun n : ℕ ↦ F.obj (op n)) b ≫ F.map (homOfLE h').op := by
  subst e; rfl

private lemma tower_map_comp (F : ℕᵒᵖ ⥤ C) {a b c : ℕ} (h : b ≤ a) (h' : c ≤ b) (h'' : c ≤ a) :
    F.map (homOfLE h).op ≫ F.map (homOfLE h').op = F.map (homOfLE h'').op := by
  rw [← F.map_comp]; rfl

variable [Preadditive C]

/-- The Milnor endomorphism `1 - shift` of the product of the terms of a tower. -/
private noncomputable abbrev milnorEndo (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)] :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
      Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op

/-- The endomorphism of the product of a tower shifting indices by `c`. -/
private noncomputable abbrev shiftEndo (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)]
    (c : ℕ) : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  Pi.lift fun n ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + c) ≫
    F.map (homOfLE (Nat.le_add_right n c)).op

/-- The partial-sum homotopy between the identity and `shiftEndo F c`. -/
private noncomputable abbrev shiftHomotopy (F : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ F.obj (op n)] (c : ℕ) :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  Pi.lift fun n ↦ ∑ k ∈ Finset.range c,
    Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + k) ≫ F.map (homOfLE (Nat.le_add_right n k)).op

private lemma telescope (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)] (c n : ℕ) :
    ∑ k ∈ Finset.range c,
        (Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + k) ≫ F.map (homOfLE (Nat.le_add_right n k)).op -
          Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + (k + 1)) ≫
            F.map (homOfLE (Nat.le_add_right n (k + 1))).op) =
      Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + c) ≫ F.map (homOfLE (Nat.le_add_right n c)).op := by
  rw [Finset.sum_range_sub', pi_π_map_congr F (add_zero n) _ le_rfl]
  show _ ≫ F.map (𝟙 _) - _ = _
  rw [F.map_id, Category.comp_id]

private lemma milnorEndo_comp_shiftHomotopy (F : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ F.obj (op n)] (c : ℕ) :
    milnorEndo F ≫ shiftHomotopy F c = 𝟙 _ - shiftEndo F c := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, Preadditive.comp_sum,
    Preadditive.sub_comp, Category.id_comp]
  rw [← telescope F c n]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Category.assoc, limit.lift_π]
  simp only [Fan.mk_π_app, Preadditive.sub_comp, Category.assoc]
  rw [tower_map_comp F _ _ (Nat.le_add_right n (k + 1))]
  exact congrArg (_ - ·) (pi_π_map_congr F (show n + k + 1 = n + (k + 1) by omega) _ _)

private lemma shiftHomotopy_comp_milnorEndo (F : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ F.obj (op n)] (c : ℕ) :
    shiftHomotopy F c ≫ milnorEndo F = 𝟙 _ - shiftEndo F c := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.id_comp]
  rw [← Category.assoc (shiftHomotopy F c), limit.lift_π, Fan.mk_π_app, Preadditive.sum_comp,
    ← Finset.sum_sub_distrib, ← telescope F c n]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Category.assoc, ← F.map_comp]
  exact congrArg (_ - ·) (pi_π_map_congr F (show n + 1 + k = n + (k + 1) by omega) _ _)

end Milnor

section Triangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An endomorphism of the first vertex of a distinguished triangle is invertible when it
extends to an endomorphism of the triangle whose other two components differ from the
identity by a homotopy `h` from the third vertex to the second. -/
private lemma isIso_of_triangle_endo_homotopic {T : Triangle C} (hT : T ∈ distTriang C)
    (z : T.obj₁ ⟶ T.obj₁) (h : T.obj₃ ⟶ T.obj₂)
    (h₁ : z ≫ T.mor₁ = T.mor₁ ≫ (𝟙 _ - T.mor₂ ≫ h))
    (h₃ : T.mor₃ ≫ z⟦(1 : ℤ)⟧' = (𝟙 _ - h ≫ T.mor₂) ≫ T.mor₃) : IsIso z := by
  set e := z - 𝟙 _ with he
  have e₁ : e ≫ T.mor₁ = 0 := by
    simp only [he, Preadditive.sub_comp, h₁, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, comp_distTriang_mor_zero₁₂_assoc _ hT, zero_comp, sub_zero, sub_self]
  have e₃ : T.mor₃ ≫ e⟦(1 : ℤ)⟧' = 0 := by
    simp only [he, Functor.map_sub, Preadditive.comp_sub, h₃,
      Preadditive.sub_comp, Category.id_comp, Category.assoc,
      comp_distTriang_mor_zero₂₃ _ hT, Limits.comp_zero, sub_zero]
    simp
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) (e⟦(1 : ℤ)⟧') e₃
  have hrot : e⟦(1 : ℤ)⟧' ≫ T.rotate.mor₃ = 0 := by
    show e⟦(1 : ℤ)⟧' ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) = 0
    rw [Preadditive.comp_neg, ← Functor.map_comp, e₁, Functor.map_zero, neg_zero]
  have hee : (e ≫ e)⟦(1 : ℤ)⟧' = 0 :=
    ((Functor.map_comp _ _ _).trans (congrArg (fun x ↦ e⟦(1 : ℤ)⟧' ≫ x) hg)).trans
      ((Category.assoc _ _ _).symm.trans (by rw [hrot, zero_comp]))
  have hee' : e ≫ e = 0 :=
    (shiftFunctor C (1 : ℤ)).map_injective (by rw [hee, Functor.map_zero])
  clear_value e
  obtain rfl : z = 𝟙 _ + e := by rw [he]; abel
  refine ⟨𝟙 _ - e, ?_, ?_⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_sub, hee', Category.id_comp,
      Category.comp_id]
    abel
  · simp only [Preadditive.sub_comp, Preadditive.comp_add, hee', Category.id_comp,
      Category.comp_id]
    abel

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
private lemma milnorEndo_naturality {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ ↦ F.obj (op n)]
    [HasProduct fun n : ℕ ↦ G.obj (op n)] (φ : F ⟶ G) :
    milnorEndo F ≫ Limits.Pi.map (fun n ↦ φ.app (op n)) =
      Limits.Pi.map (fun n ↦ φ.app (op n)) ≫ milnorEndo G := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, Limits.Pi.map_π, limit.lift_π_assoc, limit.lift_π, Fan.mk_π_app,
    Preadditive.sub_comp, Preadditive.comp_sub, Limits.Pi.map_π_assoc, NatTrans.naturality]

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
private lemma milnorEndo_comp_lift {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ ↦ F.obj (op n)]
    [HasProduct fun n : ℕ ↦ G.obj (op n)] (c : ℕ)
    (ψ : ∀ n, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hψ : ∀ n, G.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    milnorEndo G ≫ Pi.lift (fun n ↦ Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + c) ≫ ψ n) =
      Pi.lift (fun n ↦ Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + c) ≫ ψ n) ≫ milnorEndo F := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, Preadditive.comp_sub,
    limit.lift_π_assoc, Preadditive.sub_comp]
  congr 1
  rw [← hψ, ← Category.assoc, ← Category.assoc]
  congr 1
  exact pi_π_map_congr G (by omega) _ _

/-- Let `φ : F ⟶ G` be a morphism of towers which is an isomorphism of pro-objects,
witnessed by compatible maps `ψ n : G (n + c) ⟶ F n` whose composites with `φ` are the
transition maps. Then any morphism of Milnor triangles extending `∏ φ` is an isomorphism on
the derived limits. -/
private theorem isIso_of_milnor_triangle_morphism {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (φ : F ⟶ G) (c : ℕ) (ψ : ∀ n, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hψφ : ∀ n, φ.app (op (n + c)) ≫ ψ n = F.map (homOfLE (Nat.le_add_right n c)).op)
    (hφψ : ∀ n, ψ n ≫ φ.app (op n) = G.map (homOfLE (Nat.le_add_right n c)).op)
    (hψ : ∀ n, G.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    {X Y : C} {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)} {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    {q : Y ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n)} {ε : (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ Y⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C)
    (hq : Triangle.mk q (milnorEndo G) ε ∈ distTriang C)
    (a : X ⟶ Y) (ha₁ : a ≫ q = p ≫ Limits.Pi.map (fun n ↦ φ.app (op n)))
    (ha₃ : δ ≫ a⟦(1 : ℤ)⟧' = Limits.Pi.map (fun n ↦ φ.app (op n)) ≫ ε) : IsIso a := by
  set Φ := Limits.Pi.map (fun n ↦ φ.app (op n))
  set Ψ := Pi.lift (fun n ↦ Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + c) ≫ ψ n)
  obtain ⟨b, hb₁, hb₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hq hp Ψ Ψ
    (milnorEndo_comp_lift c ψ hψ)
  dsimp at hb₁ hb₃
  have hΦΨ : Φ ≫ Ψ = shiftEndo F c := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [Φ, Ψ, hψφ]
  have hΨΦ : Ψ ≫ Φ = shiftEndo G c := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [Φ, Ψ, hφψ]
  have hF₁ : shiftEndo F c = 𝟙 _ - milnorEndo F ≫ shiftHomotopy F c := by
    rw [milnorEndo_comp_shiftHomotopy]; abel
  have hF₃ : shiftEndo F c = 𝟙 _ - shiftHomotopy F c ≫ milnorEndo F := by
    rw [shiftHomotopy_comp_milnorEndo]; abel
  have hG₁ : shiftEndo G c = 𝟙 _ - milnorEndo G ≫ shiftHomotopy G c := by
    rw [milnorEndo_comp_shiftHomotopy]; abel
  have hG₃ : shiftEndo G c = 𝟙 _ - shiftHomotopy G c ≫ milnorEndo G := by
    rw [shiftHomotopy_comp_milnorEndo]; abel
  have hab : IsIso (a ≫ b) := by
    refine isIso_of_triangle_endo_homotopic hp (a ≫ b) (shiftHomotopy F c) ?_ ?_
    · dsimp
      rw [Category.assoc, ← hb₁, reassoc_of% ha₁, hΦΨ, hF₁]
    · dsimp
      rw [Functor.map_comp, reassoc_of% ha₃, hb₃, reassoc_of% hΦΨ, hF₃]
  have hba : IsIso (b ≫ a) := by
    refine isIso_of_triangle_endo_homotopic hq (b ≫ a) (shiftHomotopy G c) ?_ ?_
    · dsimp
      rw [Category.assoc, ha₁, ← reassoc_of% hb₁, hΨΦ, hG₁]
    · dsimp
      rw [Functor.map_comp, reassoc_of% hb₃, ha₃, reassoc_of% hΨΦ, hG₃]
  have : Mono a := mono_of_mono a b
  have : Epi a := epi_of_epi b a
  exact isIso_of_mono_of_epi a

/-- A pro-isomorphism of towers induces an isomorphism of their derived limits, compatible
with the projections to the products of the towers. -/
private theorem exists_iso_of_milnor_triangles {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (φ : F ⟶ G) (c : ℕ) (ψ : ∀ n, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hψφ : ∀ n, φ.app (op (n + c)) ≫ ψ n = F.map (homOfLE (Nat.le_add_right n c)).op)
    (hφψ : ∀ n, ψ n ≫ φ.app (op n) = G.map (homOfLE (Nat.le_add_right n c)).op)
    (hψ : ∀ n, G.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    {X Y : C} {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)} {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    {q : Y ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n)} {ε : (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ Y⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C)
    (hq : Triangle.mk q (milnorEndo G) ε ∈ distTriang C) :
    ∃ a : X ≅ Y, a.hom ≫ q = p ≫ Limits.Pi.map (fun n ↦ φ.app (op n)) := by
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hp hq
    (Limits.Pi.map (fun n ↦ φ.app (op n))) (Limits.Pi.map (fun n ↦ φ.app (op n)))
    (milnorEndo_naturality φ)
  dsimp at ha₁ ha₃
  have := isIso_of_milnor_triangle_morphism φ c ψ hψφ hφψ hψ hp hq a ha₁.symm ha₃
  exact ⟨asIso a, ha₁.symm⟩

/-- Under a pro-isomorphism `φ : F ⟶ G` of towers, a derived limit of `F` is also a derived limit
of `G`, with projection `p ≫ ∏ φ`. This lets both towers share a single derived-limit object,
with the identity as comparison map. -/
private theorem exists_milnor_triangle_comp_piMap {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (φ : F ⟶ G) (c : ℕ) (ψ : ∀ n, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hψφ : ∀ n, φ.app (op (n + c)) ≫ ψ n = F.map (homOfLE (Nat.le_add_right n c)).op)
    (hφψ : ∀ n, ψ n ≫ φ.app (op n) = G.map (homOfLE (Nat.le_add_right n c)).op)
    (hψ : ∀ n, G.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    {X Y : C} {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)} {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    {q : Y ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n)} {ε : (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ Y⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C)
    (hq : Triangle.mk q (milnorEndo G) ε ∈ distTriang C) :
    ∃ ε' : (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ X⟦(1 : ℤ)⟧,
      Triangle.mk (p ≫ Limits.Pi.map (fun n ↦ φ.app (op n))) (milnorEndo G) ε' ∈
        distTriang C := by
  obtain ⟨a, ha⟩ := exists_iso_of_milnor_triangles φ c ψ hψφ hφψ hψ hp hq
  refine ⟨ε ≫ a.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ hq _ ?_⟩
  refine Triangle.isoMk _ _ a (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_
  · simp [← ha]
  · simp [← Functor.map_comp]

/-- A derived limit specified by a Milnor triangle vanishes exactly when the Milnor
endomorphism `1 - shift` of the product of the tower is an isomorphism. -/
private theorem isZero_milnor_iff_isIso_milnorEndo {F : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] {X : C}
    {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)} {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C) :
    IsZero X ↔ IsIso (milnorEndo F) :=
  Triangle.isZero₁_iff_isIso₂ _ hp

/-- Transport a Milnor triangle along an isomorphism of its tower, retaining its projection. -/
private theorem exists_milnor_triangle_of_iso {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (e : F ≅ G) {X : C}
    {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)}
    {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C) :
    ∃ ε : (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ X⟦(1 : ℤ)⟧,
      Triangle.mk (p ≫ Limits.Pi.map (fun n ↦ e.hom.app (op n))) (milnorEndo G) ε ∈
        distTriang C := by
  let eP : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ≅ (∏ᶜ fun n : ℕ ↦ G.obj (op n)) :=
    HasLimit.isoOfNatIso (Discrete.natIso (fun n : Discrete ℕ ↦ e.app (op n.as)))
  have heP : eP.hom = Limits.Pi.map (fun n ↦ e.hom.app (op n)) := by
    apply Pi.hom_ext
    intro n
    simp [eP]
  refine ⟨eP.inv ≫ δ, isomorphic_distinguished _ hp _ ?_⟩
  refine (Triangle.isoMk _ _ (Iso.refl X) eP eP ?_ ?_ ?_).symm
  · simp [heP]
  · simpa only [Triangle.mk_mor₂, heP] using milnorEndo_naturality e.hom
  · simp

/-- Derived limits are invariant under isomorphism of towers. -/
private theorem isDerivedLimit_of_towerIso {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (e : F ≅ G) {X : C} (h : IsDerivedLimit F X) : IsDerivedLimit G X := by
  obtain ⟨p, δ, hp⟩ := h
  obtain ⟨ε, hε⟩ := exists_milnor_triangle_of_iso e hp
  exact ⟨_, ε, hε⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_milnor_triangle_of_objectIso {F : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] {X Y : C} (e : X ≅ Y)
    {p : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)}
    {δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧}
    (hp : Triangle.mk p (milnorEndo F) δ ∈ distTriang C) :
    ∃ ε : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ Y⟦(1 : ℤ)⟧,
      Triangle.mk (e.inv ≫ p) (milnorEndo F) ε ∈ distTriang C := by
  refine ⟨δ ≫ e.hom⟦(1 : ℤ)⟧', isomorphic_distinguished
    (Triangle.mk p (milnorEndo F) δ) hp
    (Triangle.mk (e.inv ≫ p) (milnorEndo F) (δ ≫ e.hom⟦(1 : ℤ)⟧')) ?_⟩
  refine (Triangle.isoMk (Triangle.mk p (milnorEndo F) δ)
    (Triangle.mk (e.inv ≫ p) (milnorEndo F) (δ ≫ e.hom⟦(1 : ℤ)⟧'))
      e (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_).symm
  · simp
  · simp

end Triangulated

/-- A fixed tower determines a functor of its tensor-derived limits for any tensor model. -/
private theorem exists_functor_isDerivedLimit_tensor (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    ∃ F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A),
      ∀ K, IsDerivedLimit (E ⋙ T.tensor.obj K) (F.obj K) := by
  obtain ⟨ρ, hL, Δ, hΔeval, hΔdiagram, Etilde, hEtilde, RF, α, hRFShift,
      hRFderived, hRFexact, hlimits, htensorEval, htensorDiagram, hFShift, hFexact,
      hFcompute⟩ := ModuleSystemRlimTensor.exists_exactFunctor_isDerivedLimit_tensor A E
  let AR := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} AR
  let : (ModuleCat.restrictScalars.{u} ρ.inv.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv ρ.symm.ringCatIsoToRingEquiv
  let U := (ModuleCat.restrictScalars.{u} ρ.inv.hom).mapDerivedCategory
  refine ⟨(Δ ⋙ S.tensor.flip.obj Etilde) ⋙ RF ⋙ U, fun K ↦ ?_⟩
  obtain ⟨hprod, hlim⟩ := hFcompute K
  exact isDerivedLimit_of_towerIso
    (tensorTowerIso A (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A) T K E) hlim


private theorem completionFunctor_isDerivedComplete (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedComplete (Ideal.span (Set.range f))
      ((KoszulCompletion.completionFunctor f).obj K) :=
  koszulPowerCompletion_complete A f (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
    (ULift.{u} A))
    (KoszulCompletion.completionData f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A))) K

private abbrev completion (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) :=
  ObjectProperty.lift (fun K : DerivedCategory (ModuleCat.{u} A) ↦
    IsDerivedComplete (Ideal.span (Set.range f)) K)
      (KoszulCompletion.completionFunctor f) (completionFunctor_isDerivedComplete A f)

private def completionAdjunction (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) :
    completion A f ⊣ ObjectProperty.ι (fun K : DerivedCategory (ModuleCat.{u} A) ↦
      IsDerivedComplete (Ideal.span (Set.range f)) K) :=
  AdicKoszulAdjunction.reflectionOfCompletion _ (KoszulCompletion.completionFunctor f)
    (KoszulCompletion.completionUnit f) (completionFunctor_isDerivedComplete A f)
    (fun K hK ↦ (canonicalCompletion_criterion f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)) K).mp hK)
    (canonicalCompletion_map_unit_isIso f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)))


section ModuleSystems

attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits

private abbrev ModuleSystems (A : Type u) [Ring A] :=
  PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A))

private abbrev systemMilnor (A : Type u) [Ring A] :
    CochainComplex (ModuleSystems A) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  ModuleSystemRlimTensor.complexEvaluationDiagram A ⋙
    CountableMilnorTower.countableMilnorFunctor ⋙ DerivedCategory.Q

/-- The strict Milnor construction sends quasi-isomorphisms of systems to isomorphisms. -/
private theorem systemMilnor_inverts (A : Type u) [Ring A] :
    (HomologicalComplex.quasiIso (ModuleSystems A) (ComplexShape.up ℤ)).IsInvertedBy
      (systemMilnor A) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have h : QuasiIso (CountableMilnorTower.countableMilnorFunctor.map
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map f)) := by
    apply CountableMilnorTower.map_quasiIso_and_milnor_triangle.1
    intro n
    show QuasiIso (((PresheafOfModules.evaluation
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) (op n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
    infer_instance
  show IsIso ((DerivedCategory.Q (C := ModuleCat.{u} A)).map
    (CountableMilnorTower.countableMilnorFunctor.map
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map f)))
  infer_instance

/-- The strict Milnor construction descended to the derived category of systems. -/
private def derivedSystemMilnor (A : Type u) [Ring A] :
    DerivedCategory (ModuleSystems A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (systemMilnor A) (systemMilnor_inverts A) DerivedCategory.Q

private def derivedSystemMilnorFactors (A : Type u) [Ring A] :
    DerivedCategory.Q ⋙ derivedSystemMilnor A ≅ systemMilnor A :=
  Localization.fac _ (systemMilnor_inverts A) _


private abbrev systemTensor (A : Type u) [CommRing A] :=
  ModuleSystemKFlatComparison.derivedTensorProduct.{u, u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))

private abbrev tensorSystemLimit (A : Type u) [CommRing A]
    (E : CochainComplex (ModuleSystems A) ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  ((ModuleSystemRlimTensor.constantSystem A).mapDerivedCategory ⋙
    (systemTensor A).tensor.flip.obj (DerivedCategory.Q.obj E)) ⋙ derivedSystemMilnor A

private abbrev tensorSystemLimitMap (A : Type u) [CommRing A]
    {E F : CochainComplex (ModuleSystems A) ℤ} (f : E ⟶ F) :
    tensorSystemLimit A E ⟶ tensorSystemLimit A F :=
  Functor.whiskerRight
    (Functor.whiskerLeft (ModuleSystemRlimTensor.constantSystem A).mapDerivedCategory
      ((systemTensor A).tensor.flip.map (DerivedCategory.Q.map f))) (derivedSystemMilnor A)

private theorem tensorSystemLimitMap_app (A : Type u) [CommRing A]
    {E F : CochainComplex (ModuleSystems A) ℤ} (f : E ⟶ F)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (tensorSystemLimitMap A f).app K = (derivedSystemMilnor A).map
      (((systemTensor A).tensor.obj ((ModuleSystemRlimTensor.constantSystem
        A).mapDerivedCategory.obj K)).map
        (DerivedCategory.Q.map f)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The K-flat system comparison is natural in the other complex. -/
private def systemTensorComparison (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleSystems A) ℤ)
    (hP : ∀ n : ℕ, CochainComplex.KFlat (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj
      P).obj (op n))) :
    DerivedCategory.Q ⋙ (systemTensor A).tensor.obj (DerivedCategory.Q.obj P) ≅
      (ModuleSystemKFlatComparison.totalTensorSystem.{u, u}
        ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj P ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun E ↦ (systemTensor A).comparison P E hP) (by
    intro E F f
    have h := (systemTensor A).comparison_naturality P P E F hP hP (𝟙 P) f
    simpa using h)

/-- Tensor-Milnor functors are computed on a K-flat representative naturally in the system. -/
private def tensorSystemLimitRepresentativeNatIso (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (DerivedCategory.Q ⋙ (systemTensor A).tensor.obj
      ((ModuleSystemRlimTensor.constantSystem A).mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
        ⋙
        derivedSystemMilnor A ≅
      (ModuleSystemKFlatComparison.totalTensorSystem.{u, u}
        ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj
          (((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P) ⋙
            systemMilnor A := by
  let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    P
  let eZ := (ModuleSystemRlimTensor.constantSystem A).mapDerivedCategoryFactors.app P
  have hZ (n : ℕ) : CochainComplex.KFlat (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj
    Z).obj (op n)) :=
    CochainComplex.KFlat.of_iso ((ModuleSystemRlimTensor.constantComplexEvaluationIso A
      P).app (op n)).symm hP
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft DerivedCategory.Q ((systemTensor A).tensor.mapIso eZ)) _ ≪≫
    Functor.isoWhiskerRight (systemTensorComparison A Z hZ) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (derivedSystemMilnorFactors A)

private abbrev tensorSystemLimitRepresentativeIso (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    (E : CochainComplex (ModuleSystems A) ℤ) :=
  (tensorSystemLimitRepresentativeNatIso A P hP).app E

private theorem tensorSystemLimitRepresentativeIso_naturality (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    {E F : CochainComplex (ModuleSystems A) ℤ} (f : E ⟶ F) :
    let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj P
    let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u, u}
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj Z
    (tensorSystemLimitMap A f).app (DerivedCategory.Q.obj P) ≫
        (tensorSystemLimitRepresentativeIso A P hP F).hom =
      (tensorSystemLimitRepresentativeIso A P hP E).hom ≫ (systemMilnor A).map (B.map f) :=
  (tensorSystemLimitRepresentativeNatIso A P hP).hom.naturality f

open MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
-- The naturality squares below unfold the total tensor complex degreewise over `ℤ`, which
-- exceeds the default heartbeat budget.
private theorem totalTensorEvaluationIso_naturality_right (A : Type u) [CommRing A]
    (P : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ)
    {E F : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ}
    (f : E ⟶ F) (n : ℕ) :
    let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u,u} ((Functor.const ℕᵒᵖ).obj
      (CommRingCat.of A))
    let V := (PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
      (op n)).mapHomologicalComplex (ComplexShape.up ℤ)
    let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj P
    V.map (B.map f) ≫ (S.totalTensorEvaluationIso P F n).hom =
      (S.totalTensorEvaluationIso P E n).hom ≫ (TleftCochain (V.obj P)).map (V.map f) := by
  dsimp only
  let : (curriedTensor (ModuleCat.{u} A)).PreservesZeroMorphisms := inferInstance
  let : ∀ M : ModuleCat.{u} A, ((curriedTensor (ModuleCat.{u} A)).obj M).PreservesZeroMorphisms :=
    fun M ↦ inferInstance
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u,u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let V : PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ⥤ ModuleCat.{u} A :=
    PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) (op n)
  let : V.PreservesZeroMorphisms := { map_zero := by intros; rfl }
  let VC := V.mapHomologicalComplex (ComplexShape.up ℤ)
  let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj P
  let AR := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
  let : (ModuleSystemKFlatComparison.systemTensor.{u, u} AR).PreservesZeroMorphisms :=
    { map_zero := by
        intro source target
        apply NatTrans.ext
        funext other
        apply PresheafOfModules.hom_ext
        intro stage
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext left right
        simp [ModuleSystemKFlatComparison.systemTensor, ModuleSystemKFlatComparison.tensorSystemMap]
          }
  let : ∀ other, ((ModuleSystemKFlatComparison.systemTensor.{u, u} AR).obj
    other).PreservesZeroMorphisms := by
    intro other
    refine { map_zero := ?_ }
    intro source target
    apply PresheafOfModules.hom_ext
    intro stage
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext left right
    simp [ModuleSystemKFlatComparison.systemTensor, ModuleSystemKFlatComparison.tensorSystemMap]
  ext k : 1
  let e := (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).mapIso
    (S.totalTensorEvaluationIso P E n)
  apply (cancel_epi e.inv).mp
  show e.inv ≫ (VC.map (B.map f)).f k ≫
      (S.totalTensorEvaluationIso P F n).hom.f k =
    e.inv ≫ e.hom ≫ ((TleftCochain (VC.obj P)).map (VC.map f)).f k
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := VC.obj P) (K₂ := VC.obj E)
    (F := curriedTensor (ModuleCat.{u} A))
  intro p q hpq
  have hE : V.map (HomologicalComplex.ιMapBifunctor P E
      (ModuleSystemKFlatComparison.systemTensor.{u,u} AR) (ComplexShape.up ℤ) p q k hpq) ≫ e.hom =
      HomologicalComplex.ιMapBifunctor (VC.obj P) (VC.obj E)
        (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) p q k hpq := by
    convert S.totalTensorEvaluationIso_ι P E n p q k hpq using 1 <;> rfl
  have hF : V.map (HomologicalComplex.ιMapBifunctor P F
      (ModuleSystemKFlatComparison.systemTensor.{u,u} AR) (ComplexShape.up ℤ) p q k hpq) ≫
        (S.totalTensorEvaluationIso P F n).hom.f k =
      HomologicalComplex.ιMapBifunctor (VC.obj P) (VC.obj F)
        (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) p q k hpq := by
    convert S.totalTensorEvaluationIso_ι P F n p q k hpq using 1 <;> rfl
  rw [← hE]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  show V.map (HomologicalComplex.ιMapBifunctor P E _ _ p q k hpq) ≫
      V.map ((B.map f).f k) ≫ _ = _
  rw [← V.map_comp_assoc]
  show V.map (HomologicalComplex.ιMapBifunctor P E _ _ p q k hpq ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 P) f _ _).f k) ≫ _ = _
  rw [HomologicalComplex.ι_mapBifunctorMap, V.map_comp, V.map_comp]
  simp only [Category.assoc]
  rw [hF, reassoc_of% hE]
  show _ = HomologicalComplex.ιMapBifunctor (VC.obj P) (VC.obj E)
    (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) p q k hpq ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 (VC.obj P)) (VC.map f)
        (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ)).f k
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem constantTensorComplexDiagramIso_naturality (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {E F : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ} (f : E ⟶ F) :
    let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj P
    let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj Z
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).map (B.map f) ≫
        (ModuleSystemRlimTensor.constantTensorComplexDiagramIso A P F).hom =
      (ModuleSystemRlimTensor.constantTensorComplexDiagramIso A P E).hom ≫
        Functor.whiskerRight ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map f)
          (TleftCochain P) := by
  dsimp only
  let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    P
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u,u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj Z
  let c := ModuleSystemRlimTensor.constantComplexEvaluationIso A P
  apply NatTrans.ext
  funext n
  let V := (PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
    n).mapHomologicalComplex (ComplexShape.up ℤ)
  show V.map (B.map f) ≫ ((S.totalTensorEvaluationIso Z F n.unop).hom ≫
      ((c.app n).hom ⊗ₘ 𝟙 (V.obj F))) =
    ((S.totalTensorEvaluationIso Z E n.unop).hom ≫
      ((c.app n).hom ⊗ₘ 𝟙 (V.obj E))) ≫ (𝟙 P ⊗ₘ V.map f)
  rw [← Category.assoc, totalTensorEvaluationIso_naturality_right]
  simp only [Category.assoc]
  congr 1
  show (𝟙 (V.obj Z) ⊗ₘ V.map f) ≫ ((c.app n).hom ⊗ₘ 𝟙 (V.obj F)) =
    ((c.app n).hom ⊗ₘ 𝟙 (V.obj E)) ≫ (𝟙 P ⊗ₘ V.map f)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp

end ModuleSystems

section StrictTowers

set_option backward.isDefEq.respectTransparency false in
private def complexSystemMap (A : Type u) [Ring A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ} (φ : E ⟶ F) :
    ModuleSystemRlimTensor.complexSystemOfDiagram A E ⟶
      ModuleSystemRlimTensor.complexSystemOfDiagram A F where
  f i :=
    { app n := (φ.app n).f i
      naturality ψ := by
        ext x
        exact ConcreteCategory.congr_hom
          (congrArg (fun g ↦ g.f i) (φ.naturality ψ)) x }
  comm' i j hij := by
    apply PresheafOfModules.hom_ext
    intro n
    exact (φ.app n).comm i j

set_option backward.isDefEq.respectTransparency false in
private def complexSystemEvaluationIso (A : Type u) [Ring A]
    (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj
        (ModuleSystemRlimTensor.complexSystemOfDiagram A E) ≅ E :=
  NatIso.ofComponents
    (fun n ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by intros; ext x; rfl))
    (by intros; ext i x; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem complexSystemEvaluationIso_naturality (A : Type u) [Ring A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ} (φ : E ⟶ F) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).map (complexSystemMap A φ) ≫
        (complexSystemEvaluationIso A F).hom =
      (complexSystemEvaluationIso A E).hom ≫ φ := by
  ext n i x
  rfl

set_option backward.isDefEq.respectTransparency false in
private def koszulComplexTower {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n ↦
    (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).extend ComplexShape.embeddingDownNat)
      (fun n ↦ HomologicalComplex.extendMap
        (NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n (Nat.le_succ n))
          ComplexShape.embeddingDownNat)

set_option backward.isDefEq.respectTransparency false in
private def quotientComplexTower {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n ↦
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A (A ⧸ Ideal.span (Set.range fun i ↦ f i ^ (n + 1))))).extend
        ComplexShape.embeddingDownNat))
      (fun n ↦ HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat.{u} A)).map
          (NoetherianKoszulProIso.quotientPowerTransition f (n + 1) n (Nat.le_succ n)))
        ComplexShape.embeddingDownNat)

set_option backward.isDefEq.respectTransparency false in
private def koszulComplexComparison {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    koszulComplexTower f ⟶ quotientComplexTower f :=
  NatTrans.ofOpSequence
    (fun n ↦ HomologicalComplex.extendMap
      (Koszul.koszulAugmentation (fun i ↦ f i ^ (n + 1)))
        ComplexShape.embeddingDownNat)
    (fun n ↦ by
      simp only [koszulComplexTower, quotientComplexTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
        NoetherianKoszulProIso.koszulQuotientAugmentation_naturality])

set_option backward.isDefEq.respectTransparency false in
private def mapOfOpSequenceIso {C D : Type*} [Category* C] [Category* D]
    {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n) (G : C ⥤ D) :
    Functor.ofOpSequence f ⋙ G ≅ Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f
      n)) := by
  let α : Functor.ofOpSequence f ⋙ G ⟶ Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦
    G.map (f n)) :=
    NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp,
        Category.comp_id])
  exact NatIso.ofComponents (fun n ↦ Iso.refl _) (fun {x y} g ↦ α.naturality g)

set_option backward.isDefEq.respectTransparency false in
private def koszulComplexTowerDerivedIso {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    koszulComplexTower f ⋙ DerivedCategory.Q ≅ NoetherianKoszulProIso.koszulPowerSystem f :=
  mapOfOpSequenceIso _ DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private def quotientComplexTowerDerivedIso {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    quotientComplexTower f ⋙ DerivedCategory.Q ≅ NoetherianKoszulProIso.quotientPowerSystem f :=
  mapOfOpSequenceIso _ DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private theorem koszulComplexComparison_compatibility {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) :
    Functor.whiskerRight (koszulComplexComparison f) DerivedCategory.Q ≫
        (quotientComplexTowerDerivedIso f).hom =
      (koszulComplexTowerDerivedIso f).hom ≫ NoetherianKoszulProIso.koszulQuotientComparison f := by
  ext n
  dsimp [koszulComplexTowerDerivedIso, quotientComplexTowerDerivedIso, mapOfOpSequenceIso,
    koszulComplexTower, quotientComplexTower, koszulComplexComparison,
    NoetherianKoszulProIso.koszulPowerSystem, NoetherianKoszulProIso.quotientPowerSystem,
      NoetherianKoszulProIso.koszulQuotientComparison]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end StrictTowers

section CanonicalMilnor

open CountableMilnorTower

variable {A : Type u} [Ring A]
local instance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
  moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
variable [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]

set_option backward.isDefEq.respectTransparency false in
private def coconeTriangleMap {F G : Tower (A := A)} (f : F ⟶ G) :
    CochainComplex.mappingCocone.triangle (oneMinusShift F) ⟶
      CochainComplex.mappingCocone.triangle (oneMinusShift G) :=
  Triangle.homMk _ _ (countableMilnorFunctor.map f) (towerProductMap f) (towerProductMap f)
    (mappingCoconeMap_fst f).symm (towerProduct_map_naturality f).symm (by
      let e := shiftFunctorCompIsoId (CochainComplex (ModuleCat.{u} A) ℤ) (-1 : ℤ) 1 (by omega)
      have h := e.inv.naturality (mappingConeMap f)
      change mappingConeMap f ≫ e.inv.app (CochainComplex.mappingCone (oneMinusShift G)) =
        e.inv.app (CochainComplex.mappingCone (oneMinusShift F)) ≫
          ((countableMilnorFunctor.map f)⟦(1 : ℤ)⟧') at h
      change (CochainComplex.mappingCone.inr (oneMinusShift F) ≫
        e.inv.app (CochainComplex.mappingCone (oneMinusShift F))) ≫
          ((countableMilnorFunctor.map f)⟦(1 : ℤ)⟧') =
            towerProductMap f ≫ CochainComplex.mappingCone.inr (oneMinusShift G) ≫
              e.inv.app (CochainComplex.mappingCone (oneMinusShift G))
      exact (Category.assoc _ _ _).trans
        ((congrArg (CochainComplex.mappingCone.inr (oneMinusShift F) ≫ ·) h.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ e.inv.app (CochainComplex.mappingCone (oneMinusShift G)))
              (HomologicalComplex.homotopyCofiber.inr_desc _ _ _)).trans
                (Category.assoc _ _ _)))))

set_option backward.isDefEq.respectTransparency false in
private def milnorProductDerivedIso (F : Tower (A := A)) :
    DerivedCategory.Q.obj (towerProductObj F) ≅
      ∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n)) :=
  (Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory
    (fun n : ℕ ↦ F.obj (op n)))).conePointUniqueUpToIso (productIsProduct _)

set_option backward.isDefEq.respectTransparency false in
private theorem milnorProductDerivedIso_π (F : Tower (A := A)) (n : ℕ) :
    (milnorProductDerivedIso F).hom ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n))) n =
      DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ F.obj (op n)) n) :=
  (Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory
    (fun n : ℕ ↦ F.obj (op n)))).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨n⟩

set_option backward.isDefEq.respectTransparency false in
private theorem milnorProductDerivedIso_naturality {F G : Tower (A := A)} (f : F ⟶ G) :
    DerivedCategory.Q.map (towerProductMap f) ≫ (milnorProductDerivedIso G).hom =
      (milnorProductDerivedIso F).hom ≫ Limits.Pi.map (fun n : ℕ ↦ DerivedCategory.Q.map (f.app (op
        n))) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, milnorProductDerivedIso_π, Limits.Pi.map_π]
  rw [← Functor.map_comp, Limits.Pi.map_π, Functor.map_comp,
    ← Category.assoc, milnorProductDerivedIso_π]

set_option backward.isDefEq.respectTransparency false in
private abbrev rawMilnorTriangle (F : Tower (A := A)) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (oneMinusShift F))

set_option backward.isDefEq.respectTransparency false in
private def milnorDerivedTriangle (F : Tower (A := A)) :
    Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  Triangle.mk (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map ((projection n).app F))
    (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n))) n -
        Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj (op n))) (n + 1) ≫
          DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op))
    ((milnorProductDerivedIso F).inv ≫ (rawMilnorTriangle F).mor₃)

set_option backward.isDefEq.respectTransparency false in
private def milnorDerivedTriangleIso (F : Tower (A := A)) :
    rawMilnorTriangle F ≅ milnorDerivedTriangle F := by
  refine Triangle.isoMk _ _ (Iso.refl _) (milnorProductDerivedIso F) (milnorProductDerivedIso F) ?_
    ?_ ?_
  · change DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (oneMinusShift F)) ≫
        (milnorProductDerivedIso F).hom = 𝟙 _ ≫
          Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map ((projection n).app F))
    rw [Category.id_comp]
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, milnorProductDerivedIso_π]
    simp [projection]
  · apply Pi.hom_ext
    intro n
    change (DerivedCategory.Q.map (oneMinusShift F) ≫ (milnorProductDerivedIso F).hom) ≫ _ = _
    rw [Category.assoc, milnorProductDerivedIso_π, ← Functor.map_comp,
      oneMinusShift_π, Functor.map_sub, Functor.map_comp]
    dsimp only [milnorDerivedTriangle, Triangle.mk_mor₂]
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
      milnorProductDerivedIso_π, ← Category.assoc, milnorProductDerivedIso_π]
  · simp [milnorDerivedTriangle]

set_option backward.isDefEq.respectTransparency false in
private theorem milnorDerivedTriangle_distinguished (F : Tower (A := A)) :
    milnorDerivedTriangle F ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
  isomorphic_distinguished _
    (DerivedCategory.mappingCocone_triangle_distinguished (oneMinusShift F)) _
    (milnorDerivedTriangleIso F).symm

set_option backward.isDefEq.respectTransparency false in
private def milnorDerivedTriangleMap {F G : Tower (A := A)} (f : F ⟶ G) :
    milnorDerivedTriangle F ⟶ milnorDerivedTriangle G :=
  (milnorDerivedTriangleIso F).inv ≫ DerivedCategory.Q.mapTriangle.map (coconeTriangleMap f) ≫
    (milnorDerivedTriangleIso G).hom

set_option backward.isDefEq.respectTransparency false in
private theorem milnorDerivedTriangleMap_hom₁ {F G : Tower (A := A)} (f : F ⟶ G) :
    (milnorDerivedTriangleMap f).hom₁ = DerivedCategory.Q.map (countableMilnorFunctor.map f) := by
  show 𝟙 (DerivedCategory.Q.obj (countableMilnorFunctor.obj F)) ≫
    DerivedCategory.Q.map (countableMilnorFunctor.map f) ≫
      𝟙 (DerivedCategory.Q.obj (countableMilnorFunctor.obj G)) = _
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem milnorDerivedTriangleMap_hom₂ {F G : Tower (A := A)} (f : F ⟶ G) :
    (milnorDerivedTriangleMap f).hom₂ = Limits.Pi.map (fun n : ℕ ↦ DerivedCategory.Q.map (f.app (op
      n))) := by
  show (milnorProductDerivedIso F).inv ≫
    DerivedCategory.Q.map (towerProductMap f) ≫ (milnorProductDerivedIso G).hom = _
  rw [milnorProductDerivedIso_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem milnorDerivedTriangleMap_hom₃ {F G : Tower (A := A)} (f : F ⟶ G) :
    (milnorDerivedTriangleMap f).hom₃ = Limits.Pi.map (fun n : ℕ ↦ DerivedCategory.Q.map (f.app (op
      n))) :=
  milnorDerivedTriangleMap_hom₂ f

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_milnorMap_of_proIso {F G : Tower.{u, u} (A := A)} (f : F ⟶ G)
    (c : ℕ) (ψ : ∀ n, DerivedCategory.Q.obj (G.obj (op (n + c))) ⟶
      DerivedCategory.Q.obj (F.obj (op n)))
    (hψφ : ∀ n, DerivedCategory.Q.map (f.app (op (n + c))) ≫ ψ n =
      DerivedCategory.Q.map (F.map (homOfLE (Nat.le_add_right n c)).op))
    (hφψ : ∀ n, ψ n ≫ DerivedCategory.Q.map (f.app (op n)) =
      DerivedCategory.Q.map (G.map (homOfLE (Nat.le_add_right n c)).op))
    (hψ : ∀ n, DerivedCategory.Q.map
        (G.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op) ≫ ψ n =
      ψ (n + 1) ≫ DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map f)) := by
  let a := milnorDerivedTriangleMap (A := A) (F := F) (G := G) f
  have h₁ := a.comm₁
  have h₃ := a.comm₃
  rw [milnorDerivedTriangleMap_hom₁, milnorDerivedTriangleMap_hom₂] at h₁
  rw [milnorDerivedTriangleMap_hom₁, milnorDerivedTriangleMap_hom₃] at h₃
  exact isIso_of_milnor_triangle_morphism (Functor.whiskerRight f DerivedCategory.Q)
    c ψ hψφ hφψ hψ (milnorDerivedTriangle_distinguished F)
      (milnorDerivedTriangle_distinguished G) _ h₁.symm h₃

set_option backward.isDefEq.respectTransparency false in
private theorem exists_milnor_triangle_comparison
    {E F : Tower.{u, u} (A := A)} (μ : E ⟶ F)
    {U V : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)}
    (iU : E ⋙ DerivedCategory.Q ≅ U) (iV : F ⋙ DerivedCategory.Q ≅ V)
    (φ : U ⟶ V)
    (hφ : Functor.whiskerRight μ DerivedCategory.Q ≫ iV.hom = iU.hom ≫ φ)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (a : X ⟶ Y)
    (eX : X ≅ DerivedCategory.Q.obj (countableMilnorFunctor.obj E))
    (eY : Y ≅ DerivedCategory.Q.obj (countableMilnorFunctor.obj F))
    (ha : a ≫ eY.hom = eX.hom ≫ DerivedCategory.Q.map (countableMilnorFunctor.map μ)) :
    ∃ (p : X ⟶ ∏ᶜ fun n : ℕ ↦ U.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ U.obj (op n)) ⟶ X⟦(1 : ℤ)⟧)
      (q : Y ⟶ ∏ᶜ fun n : ℕ ↦ V.obj (op n))
      (ε : (∏ᶜ fun n : ℕ ↦ V.obj (op n)) ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk p (milnorEndo U) δ ∈ distTriang _ ∧
      Triangle.mk q (milnorEndo V) ε ∈ distTriang _ ∧
      ∀ n : ℕ, a ≫ q ≫ Pi.π _ n = p ≫ Pi.π _ n ≫ φ.app (op n) := by
  obtain ⟨δ, hp⟩ := exists_milnor_triangle_of_iso iU (milnorDerivedTriangle_distinguished E)
  obtain ⟨δ', hp'⟩ := exists_milnor_triangle_of_objectIso eX.symm hp
  obtain ⟨ε, hq⟩ := exists_milnor_triangle_of_iso iV (milnorDerivedTriangle_distinguished F)
  obtain ⟨ε', hq'⟩ := exists_milnor_triangle_of_objectIso eY.symm hq
  refine ⟨_, δ', _, ε', hp', hq', ?_⟩
  intro n
  dsimp only [Iso.symm_inv]
  have hπ (L : Tower.{u,u} (A := A)) (j : ℕ) :
      (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map ((projection n).app L)) ≫
        Pi.π (fun n : ℕ ↦ (L ⋙ DerivedCategory.Q).obj (op n)) j =
          DerivedCategory.Q.map ((projection j).app L) :=
    Pi.lift_comp_π _ j
  simp only [Category.assoc, Pi.map_π_assoc, Pi.map_π]
  rw [← Category.assoc, ← Category.assoc, ha]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (hπ F n), reassoc_of% (hπ E n)]
  have hμ := (projection n).naturality μ
  change (countableMilnorFunctor.map μ) ≫ (projection n).app F =
    (projection n).app E ≫ μ.app (op n) at hμ
  rw [← Functor.map_comp_assoc, hμ, Functor.map_comp]
  simp only [Category.assoc]
  have hφn := congrArg (fun η ↦ η.app (op n)) hφ
  change DerivedCategory.Q.map (μ.app (op n)) ≫ iV.hom.app (op n) =
    iU.hom.app (op n) ≫ φ.app (op n) at hφn
  rw [hφn]

end CanonicalMilnor

section StrictTensorLimit

attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits
open CountableMilnorTower

private abbrev strictTensorLimit (A : Type u) [CommRing A]
    (E : Tower.{u, u} (A := A)) :=
  tensorSystemLimit A (ModuleSystemRlimTensor.complexSystemOfDiagram A E)

private abbrev strictTensorLimitMap (A : Type u) [CommRing A]
    {E F : Tower.{u, u} (A := A)} (f : E ⟶ F) :=
  tensorSystemLimitMap A (complexSystemMap A f)

private def strictTensorLimitRepresentativeIso (A : Type u) [CommRing A]
    (E : Tower.{u, u} (A := A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (strictTensorLimit A E).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (countableMilnorFunctor.obj (E ⋙ TleftCochain P)) :=
  tensorSystemLimitRepresentativeIso A P hP
      (ModuleSystemRlimTensor.complexSystemOfDiagram A E) ≪≫
    (countableMilnorFunctor ⋙ DerivedCategory.Q).mapIso
      (ModuleSystemRlimTensor.constantTensorComplexDiagramIso A P
          (ModuleSystemRlimTensor.complexSystemOfDiagram A E) ≪≫
        Functor.isoWhiskerRight (complexSystemEvaluationIso A E) (TleftCochain P))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- The naturality squares below unfold the total tensor complex degreewise over `ℤ`, which
-- exceeds the default heartbeat budget.
private theorem strictTensorLimitRepresentativeIso_naturality (A : Type u) [CommRing A]
    {E F : Tower.{u, u} (A := A)} (f : E ⟶ F)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (strictTensorLimitMap A f).app (DerivedCategory.Q.obj P) ≫
        (strictTensorLimitRepresentativeIso A F P hP).hom =
      (strictTensorLimitRepresentativeIso A E P hP).hom ≫
        DerivedCategory.Q.map
          (countableMilnorFunctor.map (Functor.whiskerRight f (TleftCochain P))) := by
  let H := countableMilnorFunctor ⋙ DerivedCategory.Q (C := ModuleCat.{u} A)
  let m := complexSystemMap A f
  let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    P
  let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj Z
  have h₁ := tensorSystemLimitRepresentativeIso_naturality A P hP m
  have h₂ := constantTensorComplexDiagramIso_naturality A P m
  have h₃ := complexSystemEvaluationIso_naturality A f
  dsimp only [strictTensorLimitRepresentativeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  show _ ≫ H.map ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map (B.map m)) ≫ H.map _ =
    _ ≫ H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  congr 2
  simp only [Functor.isoWhiskerRight_hom]
  rw [← Category.assoc, h₂]
  simp only [Category.assoc]
  congr 1
  show Functor.whiskerRight ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map m)
    (TleftCochain P) ≫
      Functor.whiskerRight (complexSystemEvaluationIso A F).hom (TleftCochain P) =
    Functor.whiskerRight (complexSystemEvaluationIso A E).hom (TleftCochain P) ≫
      Functor.whiskerRight f (TleftCochain P)
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, h₃]

private def strictTensorTowerIso (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) (E : Tower.{u, u} (A := A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (E ⋙ TleftCochain P) ⋙ DerivedCategory.Q ≅
      (E ⋙ DerivedCategory.Q) ⋙ T.tensor.obj (DerivedCategory.Q.obj P) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E (ModuleSystemRlimTensor.derivedTensorComplexComparison A T P hP).symm
      ≪≫
      (Functor.associator _ _ _).symm

private theorem strictTensorTowerIso_naturality (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) {E F : Tower.{u, u} (A := A)}
    (f : E ⟶ F)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    Functor.whiskerRight (Functor.whiskerRight f (TleftCochain P)) DerivedCategory.Q ≫
        (strictTensorTowerIso A T F P hP).hom =
      (strictTensorTowerIso A T E P hP).hom ≫
        Functor.whiskerRight (Functor.whiskerRight f DerivedCategory.Q)
          (T.tensor.obj (DerivedCategory.Q.obj P)) := by
  ext n
  simpa [strictTensorTowerIso] using
    (ModuleSystemRlimTensor.derivedTensorComplexComparison A T P hP).inv.naturality (f.app n)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_strictTensorLimit_milnorComparison (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    {E F : Tower.{u, u} (A := A)} (μ : E ⟶ F)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    let U := (E ⋙ DerivedCategory.Q) ⋙ T.tensor.obj K
    let V := (F ⋙ DerivedCategory.Q) ⋙ T.tensor.obj K
    ∃ (p : (strictTensorLimit A E).obj K ⟶ ∏ᶜ fun n : ℕ ↦ U.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ U.obj (op n)) ⟶ ((strictTensorLimit A E).obj K)⟦(1 : ℤ)⟧)
      (q : (strictTensorLimit A F).obj K ⟶ ∏ᶜ fun n : ℕ ↦ V.obj (op n))
      (ε : (∏ᶜ fun n : ℕ ↦ V.obj (op n)) ⟶ ((strictTensorLimit A F).obj K)⟦(1 : ℤ)⟧),
      Triangle.mk p (milnorEndo U) δ ∈ distTriang _ ∧
      Triangle.mk q (milnorEndo V) ε ∈ distTriang _ ∧
      ∀ n : ℕ, (strictTensorLimitMap A μ).app K ≫ q ≫ Pi.π _ n =
        p ≫ Pi.π _ n ≫ (T.tensor.obj K).map (DerivedCategory.Q.map (μ.app (op n))) := by
  obtain ⟨P, pP, hP, _, hpP, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage K)
  have := hpP
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map pP) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let j (L : Tower.{u, u} (A := A)) :
      (L ⋙ TleftCochain P) ⋙ DerivedCategory.Q ≅
        (L ⋙ DerivedCategory.Q) ⋙ T.tensor.obj K :=
    strictTensorTowerIso A T L P hP ≪≫
      Functor.isoWhiskerLeft (L ⋙ DerivedCategory.Q) (T.tensor.mapIso e)
  let l (L : Tower.{u, u} (A := A)) :
      (strictTensorLimit A L).obj K ≅
        DerivedCategory.Q.obj (countableMilnorFunctor.obj (L ⋙ TleftCochain P)) :=
    (strictTensorLimit A L).mapIso e.symm ≪≫ strictTensorLimitRepresentativeIso A L P hP
  have hμ : Functor.whiskerRight (Functor.whiskerRight μ (TleftCochain P)) DerivedCategory.Q ≫
      (j F).hom = (j E).hom ≫
        Functor.whiskerRight (Functor.whiskerRight μ DerivedCategory.Q) (T.tensor.obj K) := by
    dsimp only [j, Iso.trans_hom]
    rw [← Category.assoc, strictTensorTowerIso_naturality]
    simp only [Category.assoc]
    congr 1
    ext n
    exact (T.tensor.map e.hom).naturality (DerivedCategory.Q.map (μ.app n))
  have ha : (strictTensorLimitMap A μ).app K ≫ (l F).hom =
      (l E).hom ≫ DerivedCategory.Q.map
        (countableMilnorFunctor.map (Functor.whiskerRight μ (TleftCochain P))) := by
    dsimp only [l, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← (strictTensorLimitMap A μ).naturality e.inv, Category.assoc,
      strictTensorLimitRepresentativeIso_naturality]
    simp only [Category.assoc]
  exact exists_milnor_triangle_comparison (Functor.whiskerRight μ (TleftCochain P))
    (j E) (j F)
    (Functor.whiskerRight (Functor.whiskerRight μ DerivedCategory.Q) (T.tensor.obj K))
    hμ ((strictTensorLimitMap A μ).app K) (l E) (l F) ha


set_option backward.isDefEq.respectTransparency false in
private theorem exists_strictTensorLimit_milnorComparison_of_isos (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    {E F : Tower.{u, u} (A := A)} (μ : E ⟶ F)
    {U V : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)}
    (iU : E ⋙ DerivedCategory.Q ≅ U) (iV : F ⋙ DerivedCategory.Q ≅ V)
    (φ : U ⟶ V)
    (hφ : Functor.whiskerRight μ DerivedCategory.Q ≫ iV.hom = iU.hom ≫ φ)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    let Ut := U ⋙ T.tensor.obj K
    let Vt := V ⋙ T.tensor.obj K
    ∃ (p : (strictTensorLimit A E).obj K ⟶ ∏ᶜ fun n : ℕ ↦ Ut.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ Ut.obj (op n)) ⟶ ((strictTensorLimit A E).obj K)⟦(1 : ℤ)⟧)
      (q : (strictTensorLimit A F).obj K ⟶ ∏ᶜ fun n : ℕ ↦ Vt.obj (op n))
      (ε : (∏ᶜ fun n : ℕ ↦ Vt.obj (op n)) ⟶ ((strictTensorLimit A F).obj K)⟦(1 : ℤ)⟧),
      Triangle.mk p (milnorEndo Ut) δ ∈ distTriang _ ∧
      Triangle.mk q (milnorEndo Vt) ε ∈ distTriang _ ∧
      ∀ n : ℕ, (strictTensorLimitMap A μ).app K ≫ q ≫ Pi.π _ n =
        p ≫ Pi.π _ n ≫ (T.tensor.obj K).map (φ.app (op n)) := by
  obtain ⟨p, δ, q, ε, hp, hq, hπ⟩ := exists_strictTensorLimit_milnorComparison A T μ K
  let bU := Functor.isoWhiskerRight iU (T.tensor.obj K)
  let bV := Functor.isoWhiskerRight iV (T.tensor.obj K)
  obtain ⟨δ', hp'⟩ := exists_milnor_triangle_of_iso bU hp
  obtain ⟨ε', hq'⟩ := exists_milnor_triangle_of_iso bV hq
  refine ⟨_, δ', _, ε', hp', hq', ?_⟩
  intro n
  simp only [Category.assoc, Pi.map_π_assoc, Pi.map_π]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (hπ n)]
  show _ ≫ _ ≫ (T.tensor.obj K).map (DerivedCategory.Q.map (μ.app (op n))) ≫
      (T.tensor.obj K).map (iV.hom.app (op n)) =
    _ ≫ _ ≫ (T.tensor.obj K).map (iU.hom.app (op n)) ≫
      (T.tensor.obj K).map (φ.app (op n))
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hφn := congrArg (fun η ↦ η.app (op n)) hφ
  change DerivedCategory.Q.map (μ.app (op n)) ≫ iV.hom.app (op n) =
    iU.hom.app (op n) ≫ φ.app (op n) at hφn
  rw [hφn]


private abbrev tensorKoszulLimit (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) :=
  strictTensorLimit A (koszulComplexTower f)

private abbrev tensorQuotientLimit (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) :=
  strictTensorLimit A (quotientComplexTower f)

private abbrev tensorKoszulQuotientComparison (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) : tensorKoszulLimit A f ⟶ tensorQuotientLimit A f :=
  strictTensorLimitMap A (koszulComplexComparison f)

private theorem tensorKoszulLimit_isDerivedLimit (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedLimit (NoetherianKoszulProIso.koszulPowerSystem f ⋙ T.tensor.obj K)
      ((tensorKoszulLimit A f).obj K) := by
  obtain ⟨p, δ, q, ε, hp, hq, hπ⟩ :=
    exists_strictTensorLimit_milnorComparison_of_isos A T (koszulComplexComparison f)
      (koszulComplexTowerDerivedIso f) (quotientComplexTowerDerivedIso f)
      (NoetherianKoszulProIso.koszulQuotientComparison f) (koszulComplexComparison_compatibility f)
        K
  exact ⟨p, δ, hp⟩

private theorem tensorKoszulLimit_isDerivedComplete (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedComplete (Ideal.span (Set.range f))
      ((tensorKoszulLimit A f).obj K) :=
  AdicKoszul.rlim_derivedTensor_koszulPowers_isDerivedComplete f
    (fun n ↦ NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n (Nat.le_succ n))
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A) K ((tensorKoszulLimit A f).obj K)
    (tensorKoszulLimit_isDerivedLimit A f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A) K)


end StrictTensorLimit

section PrincipalKoszul

open scoped ExteriorAlgebra

private theorem koszulPowerTransition_one (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m)
    (x : ⋀[A]^1 (Fin r → A)) (i : Fin r) :
    exteriorPower.oneEquiv A (Fin r → A)
        ((NoetherianKoszulProIso.koszulPowerTransition f m n h).f 1 x) i =
      f i ^ (m - n) * exteriorPower.oneEquiv A (Fin r → A) x i := by
  obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv A (Fin r → A)).symm.surjective x
  rw [exteriorPower.oneEquiv_symm_apply]
  have ht := NoetherianKoszulProIso.koszulPowerTransition_apply_ιMulti f m n h 1 (fun _ ↦ v)
  change (NoetherianKoszulProIso.koszulPowerTransition f m n h).f 1
      (exteriorPower.ιMulti A 1 (fun _ ↦ v)) =
    exteriorPower.ιMulti A 1 (fun _ j ↦ f j ^ (m - n) * v j) at ht
  rw [ht, exteriorPower.oneEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti]

private theorem exteriorPower_pi_isZero_of_lt (A : Type u) [CommRing A]
    (r n : ℕ) (h : r < n) :
    IsZero (ModuleCat.of A (⋀[A]^n (Fin r → A))) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (fun i : Fin r ↦ (Pi.basisFun A (Fin r)) i) (Pi.basisFun A (Fin r)).span_eq n
  simpa using h

private theorem relSpan_eq_bot_of_subsingleton (A : Type u) [CommRing A]
    {r : ℕ} [Subsingleton (Fin r)] (f : Fin r → A) : Koszul.relSpan f = ⊥ := by
  apply bot_unique
  rw [Koszul.relSpan, Submodule.span_le]
  rintro x ⟨⟨i,j⟩, rfl⟩
  have h : i = j := Subsingleton.elim _ _
  simp [Koszul.trivRel, h]

private def kerSeqDualSingleEquiv (A : Type u) [CommRing A] (f : A) :
    LinearMap.ker (Koszul.seqDual (fun _ : Fin 1 ↦ f)) ≃ₗ[A]
      Submodule.torsionBy A A f where
  toFun x := ⟨x.1 0, by
    change f * x.1 0 = 0
    have hx : Koszul.seqDual (fun _ : Fin 1 ↦ f) x.1 = 0 := x.2
    simpa only [Koszul.seqDual_apply, Fin.sum_univ_one, mul_comm] using hx⟩
  invFun y := ⟨fun _ ↦ y.1, by
    change Koszul.seqDual (fun _ : Fin 1 ↦ f) (fun _ ↦ y.1) = 0
    have hy : f * y.1 = 0 := y.2
    simpa only [Koszul.seqDual_apply, Fin.sum_univ_one, mul_comm] using hy⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.1 (Subsingleton.elim _ _)
  right_inv y := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def koszulSingleHomologyOneIso (A : Type u) [CommRing A] (f : A) :
    (Koszul.seqComplex (fun _ : Fin 1 ↦ f)).homology 1 ≅
      ModuleCat.of A (Submodule.torsionBy A A f) :=
  ((Koszul.h1ConcreteIso (fun _ : Fin 1 ↦ f)).symm.trans
    ((Submodule.quotEquivOfEqBot _ (by
      rw [relSpan_eq_bot_of_subsingleton A]
      simp)).trans (kerSeqDualSingleEquiv A f))).toModuleIso

section DoubleIsoComponents
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} {X₀ X₁ : C}
  (f : X₀ ⟶ X₁) (h : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
  (K : HomologicalComplex C c) (e₀ : X₀ ≅ K.X i₀) (e₁ : X₁ ≅ K.X i₁)
  (hcomm : e₀.hom ≫ K.d i₀ i₁ = f ≫ e₁.hom)
  (hout : ∀ j, c.Rel i₁ j → e₁.hom ≫ K.d i₁ j = 0)
  (hsupport : ∀ j, j ≠ i₀ → j ≠ i₁ → IsZero (K.X j))

private theorem doubleIsoOfIsZero_hom_f₀ :
    (doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport).hom.f i₀ =
      (HomologicalComplex.doubleXIso₀ f h).hom ≫ e₀.hom := by
  simp only [doubleIsoOfIsZero, asIso_hom, HomologicalComplex.mkHomFromDouble_f₀]

private theorem doubleIsoOfIsZero_hom_f₁ :
    (doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport).hom.f i₁ =
      (HomologicalComplex.doubleXIso₁ f h hne).hom ≫ e₁.hom := by
  simp only [doubleIsoOfIsZero, asIso_hom, HomologicalComplex.mkHomFromDouble_f₁]

private theorem doubleIsoOfIsZero_inv_f₀ :
    (doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport).inv.f i₀ =
      e₀.inv ≫ (HomologicalComplex.doubleXIso₀ f h).inv := by
  let e := doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport
  apply (cancel_epi (e.hom.f i₀)).mp
  show (HomologicalComplex.Hom.isoApp e i₀).hom ≫
    (HomologicalComplex.Hom.isoApp e i₀).inv = _
  rw [Iso.hom_inv_id]
  dsimp only [e]
  rw [doubleIsoOfIsZero_hom_f₀]
  simp

private theorem doubleIsoOfIsZero_inv_f₁ :
    (doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport).inv.f i₁ =
      e₁.inv ≫ (HomologicalComplex.doubleXIso₁ f h hne).inv := by
  let e := doubleIsoOfIsZero f h hne K e₀ e₁ hcomm hout hsupport
  apply (cancel_epi (e.hom.f i₁)).mp
  show (HomologicalComplex.Hom.isoApp e i₁).hom ≫
    (HomologicalComplex.Hom.isoApp e i₁).inv = _
  rw [Iso.hom_inv_id]
  dsimp only [e]
  rw [doubleIsoOfIsZero_hom_f₁]
  simp
end DoubleIsoComponents

private abbrev koszulSingleOneIso (A : Type u) [CommRing A] (f : A) :
    (Koszul.seqComplex (fun _ : Fin 1 ↦ f)).X 1 ≅ ModuleCat.of A A :=
  ((exteriorPower.oneEquiv A (Fin 1 → A)).trans (LinearEquiv.funUnique (Fin 1) A A)).toModuleIso

private abbrev koszulSingleZeroIso (A : Type u) [CommRing A] (f : A) :
    (Koszul.seqComplex (fun _ : Fin 1 ↦ f)).X 0 ≅ ModuleCat.of A A :=
  (exteriorPower.zeroEquiv A (Fin 1 → A)).toModuleIso

private theorem koszulSingle_d (A : Type u) [CommRing A] (f : A) :
    (koszulSingleOneIso A f).inv ≫ (Koszul.seqComplex (fun _ : Fin 1 ↦ f)).d 1 0 =
      (f • 𝟙 (ModuleCat.of A A)) ≫ (koszulSingleZeroIso A f).inv := by
  apply (cancel_mono (koszulSingleZeroIso A f).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  show exteriorPower.zeroEquiv A (Fin 1 → A)
    (Koszul.d (Koszul.seqDual (fun _ : Fin 1 ↦ f)) 0
      ((exteriorPower.oneEquiv A (Fin 1 → A)).symm
        ((LinearEquiv.funUnique (Fin 1) A A).symm a))) = f * a
  rw [Koszul.zeroEquiv_d_zero, LinearEquiv.apply_symm_apply, Koszul.seqDual_apply]
  simp [LinearEquiv.funUnique_symm_apply, mul_comm]

private def koszulSingleDoubleIso (A : Type u) [CommRing A] (f : A) :
    HomologicalComplex.double (f • 𝟙 (ModuleCat.of A A))
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) ≅
      Koszul.seqComplex (fun _ : Fin 1 ↦ f) :=
  doubleIsoOfIsZero _ rfl (by decide) _
    (koszulSingleOneIso A f).symm (koszulSingleZeroIso A f).symm
    (koszulSingle_d A f)
    (fun j hj ↦ by have : j + 1 = 0 := hj; omega)
    (fun j hj₁ hj₀ ↦ exteriorPower_pi_isZero_of_lt A 1 j (by omega))

section ConeDouble

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {X Y : C} (f : X ⟶ Y)

variable {X' Y' : C} (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)

private def singleConeMap :
    CochainComplex.mappingCone (singleMap f) ⟶ CochainComplex.mappingCone (singleMap g) :=
  CochainComplex.mappingCone.map (singleMap f) (singleMap g) (singleMap a) (singleMap b)
    (by dsimp only [singleMap]; rw [← Functor.map_comp, ← Functor.map_comp, h])

set_option backward.isDefEq.respectTransparency false in
private theorem singleConeMap_negOne :
    (singleConeNegOneIso f).hom ≫ (singleConeMap f g a b h).f (-1) =
      a ≫ (singleConeNegOneIso g).hom := by
  dsimp only [singleConeNegOneIso]
  rw [Category.assoc]
  show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
    (CochainComplex.mappingCone.inl (singleMap f)).v 0 (-1) (by decide) ≫
      (singleConeMap f g a b h).f (-1) = _
  simp [singleConeMap, CochainComplex.mappingCone.map, singleMap,
    HomologicalComplex.single_map_f_self]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem singleConeMap_zero :
    (singleConeZeroIso f).hom ≫ (singleConeMap f g a b h).f 0 =
      b ≫ (singleConeZeroIso g).hom := by
  dsimp only [singleConeZeroIso]
  rw [Category.assoc]
  show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv ≫
    (CochainComplex.mappingCone.inr (singleMap f)).f 0 ≫
      (singleConeMap f g a b h).f 0 = _
  rw [← HomologicalComplex.comp_f]
  rw [singleConeMap, CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_desc]
  simp only [HomologicalComplex.comp_f, singleMap, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end ConeDouble

private def doubleExtendIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') {i₀ i₁ : ι} {X₀ X₁ : C} (f : X₀ ⟶ X₁)
    (h : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    HomologicalComplex.double f (e.rel h) ≅ (HomologicalComplex.double f h).extend e := by
  let K := HomologicalComplex.double f h
  let a := K.extendXIso e (rfl : e.f i₀ = e.f i₀) ≪≫
    HomologicalComplex.doubleXIso₀ f h
  let b := K.extendXIso e (rfl : e.f i₁ = e.f i₁) ≪≫
    HomologicalComplex.doubleXIso₁ f h hne
  refine doubleIsoOfIsZero f (e.rel h) (fun he ↦ hne (e.injective_f he)) _
    a.symm b.symm ?_ ?_ ?_
  · dsimp only [a, b, Iso.symm_hom, Iso.trans_inv]
    rw [HomologicalComplex.extend_d_eq _ e rfl rfl]
    simp only [Category.assoc]
    dsimp only [K]
    rw [HomologicalComplex.double_d _ _ hne]
    simp
  · intro j hj
    by_cases he : ∃ i, e.f i = j
    · obtain ⟨i, rfl⟩ := he
      rw [HomologicalComplex.extend_d_eq _ e rfl rfl]
      dsimp only [b, Iso.symm_hom, Iso.trans_inv]
      simp only [Category.assoc]
      dsimp only [K]
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hne.symm]
      simp
    · exact (K.isZero_extend_X e j (fun i hi ↦ he ⟨i, hi⟩)).eq_of_tgt _ _
  · intro j hj₀ hj₁
    by_cases he : ∃ i, e.f i = j
    · obtain ⟨i, rfl⟩ := he
      exact (HomologicalComplex.isZero_double_X f h i
        (fun hi ↦ hj₀ (congrArg e.f hi)) (fun hi ↦ hj₁ (congrArg e.f hi))).of_iso
          (K.extendXIso e rfl)
    · exact K.isZero_extend_X e j (fun i hi ↦ he ⟨i, hi⟩)

section DoubleExtendComponents
variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') {i₀ i₁ : ι} {X₀ X₁ : C} (f : X₀ ⟶ X₁)
  (h : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
private theorem doubleExtendIso_inv_f₀ :
    (doubleExtendIso e f h hne).inv.f (e.f i₀) =
      ((HomologicalComplex.double f h).extendXIso e rfl).hom ≫
        (HomologicalComplex.doubleXIso₀ f h).hom ≫
          (HomologicalComplex.doubleXIso₀ f (e.rel h)).inv := by
  simp only [doubleExtendIso, doubleIsoOfIsZero_inv_f₀, Iso.symm_inv, Iso.trans_hom,
    Category.assoc]
private theorem doubleExtendIso_inv_f₁ :
    (doubleExtendIso e f h hne).inv.f (e.f i₁) =
      ((HomologicalComplex.double f h).extendXIso e rfl).hom ≫
        (HomologicalComplex.doubleXIso₁ f h hne).hom ≫
          (HomologicalComplex.doubleXIso₁ f (e.rel h) (fun he ↦ hne (e.injective_f he))).inv := by
  simp only [doubleExtendIso, doubleIsoOfIsZero_inv_f₁, Iso.symm_inv, Iso.trans_hom,
    Category.assoc]
end DoubleExtendComponents

private def koszulSingleConeIso (A : Type u) [CommRing A] (f : A) :
    (Koszul.seqComplex (fun _ : Fin 1 ↦ f)).extend ComplexShape.embeddingDownNat ≅
      CochainComplex.mappingCone
        ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).map
          (f • 𝟙 (ModuleCat.of A A))) :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
    (koszulSingleDoubleIso A f).symm ≪≫
  (doubleExtendIso ComplexShape.embeddingDownNat (f • 𝟙 (ModuleCat.of A A))
    (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)).symm ≪≫
  singleConeDoubleIso (f • 𝟙 (ModuleCat.of A A))

private def koszulPowerConeIso (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (Koszul.seqComplex (fun _ : Fin 1 ↦ f ^ n)).extend ComplexShape.embeddingDownNat ≅
      ProTorsion.Kcx A f n := koszulSingleConeIso A (f ^ n)

set_option backward.isDefEq.respectTransparency false in
private theorem koszulSingleConeIso_hom_f_negOne (A : Type u) [CommRing A] (f : A) :
    (koszulSingleConeIso A f).hom.f (-1) =
      ((Koszul.seqComplex (fun _ : Fin 1 ↦ f)).extendXIso
        ComplexShape.embeddingDownNat (show ComplexShape.embeddingDownNat.f 1 = -1 from rfl)).hom ≫
      (koszulSingleOneIso A f).hom ≫ (singleConeNegOneIso (f • 𝟙 (ModuleCat.of A A))).hom := by
  dsimp only [koszulSingleConeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.comp_f]
  dsimp only [ComplexShape.Embedding.extendFunctor]
  rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 1 = -1 from rfl)]
  have he := doubleExtendIso_inv_f₀ ComplexShape.embeddingDownNat
    (f • 𝟙 (ModuleCat.of A A)) (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)
  change (doubleExtendIso ComplexShape.embeddingDownNat (f • 𝟙 (ModuleCat.of A A))
    (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)).inv.f (-1) = _ at he
  rw [he]
  simp only [koszulSingleDoubleIso, doubleIsoOfIsZero_inv_f₀, singleConeDoubleIso,
    doubleIsoOfIsZero_hom_f₀,
    Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulSingleConeIso_hom_f_zero (A : Type u) [CommRing A] (f : A) :
    (koszulSingleConeIso A f).hom.f 0 =
      ((Koszul.seqComplex (fun _ : Fin 1 ↦ f)).extendXIso
        ComplexShape.embeddingDownNat (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl)).hom ≫
      (koszulSingleZeroIso A f).hom ≫ (singleConeZeroIso (f • 𝟙 (ModuleCat.of A A))).hom := by
  dsimp only [koszulSingleConeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.comp_f]
  dsimp only [ComplexShape.Embedding.extendFunctor]
  rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl)]
  have he := doubleExtendIso_inv_f₁ ComplexShape.embeddingDownNat
    (f • 𝟙 (ModuleCat.of A A)) (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)
  change (doubleExtendIso ComplexShape.embeddingDownNat (f • 𝟙 (ModuleCat.of A A))
    (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)).inv.f 0 = _ at he
  rw [he]
  simp only [koszulSingleDoubleIso, doubleIsoOfIsZero_inv_f₁, singleConeDoubleIso,
    doubleIsoOfIsZero_hom_f₁,
    Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]

private theorem koszulPowerTransition_zero (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) (x : ⋀[A]^0 (Fin r → A)) :
    (NoetherianKoszulProIso.koszulPowerTransition f m n h).f 0 x = x := by
  let t : (⋀[A]^0 (Fin r → A)) →ₗ[A] (⋀[A]^0 (Fin r → A)) :=
    ((NoetherianKoszulProIso.koszulPowerTransition f m n h).f 0).hom
  show t x = x
  obtain ⟨a, rfl⟩ := (exteriorPower.zeroEquiv A (Fin r → A)).symm.surjective x
  rw [exteriorPower.zeroEquiv_symm_apply, map_smul]
  congr 1
  have ht := NoetherianKoszulProIso.koszulPowerTransition_apply_ιMulti f m n h 0 (fun i ↦ Fin.elim0
    i)
  have he : (fun (k : Fin 0) (i : Fin r) ↦ f i ^ (m - n) * (Fin.elim0 k : Fin r → A) i) =
      (fun k : Fin 0 ↦ (Fin.elim0 k : Fin r → A)) := Subsingleton.elim _ _
  rw [he] at ht
  exact ht

private theorem koszulSingleExtended_isZero_X (A : Type u) [CommRing A] (f : A)
    (i : ℤ) (hi₀ : i ≠ -1) (hi₁ : i ≠ 0) :
    IsZero (((Koszul.seqComplex (fun _ : Fin 1 ↦ f)).extend ComplexShape.embeddingDownNat).X i) :=
      by
  have hz := HomologicalComplex.isZero_double_X (f • 𝟙 (ModuleCat.of A A))
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) i hi₀ hi₁
  exact (hz.of_iso (HomologicalComplex.Hom.isoApp
    (singleConeDoubleIso (f • 𝟙 (ModuleCat.of A A))) i).symm).of_iso
      (HomologicalComplex.Hom.isoApp (koszulSingleConeIso A f) i)

set_option backward.isDefEq.respectTransparency false in
private theorem koszulSingleConeIso_naturality (A : Type u) [CommRing A] (f g : A)
    (μ : Koszul.seqComplex (fun _ : Fin 1 ↦ f) ⟶ Koszul.seqComplex (fun _ : Fin 1 ↦ g))
    (a b : ModuleCat.of A A ⟶ ModuleCat.of A A)
    (h : (f • 𝟙 (ModuleCat.of A A)) ≫ b = a ≫ (g • 𝟙 (ModuleCat.of A A)))
    (h₁ : μ.f 1 ≫ (koszulSingleOneIso A g).hom = (koszulSingleOneIso A f).hom ≫ a)
    (h₀ : μ.f 0 ≫ (koszulSingleZeroIso A g).hom = (koszulSingleZeroIso A f).hom ≫ b) :
    HomologicalComplex.extendMap μ ComplexShape.embeddingDownNat ≫ (koszulSingleConeIso A g).hom =
      (koszulSingleConeIso A f).hom ≫ singleConeMap (f • 𝟙 (ModuleCat.of A A))
        (g • 𝟙 (ModuleCat.of A A)) a b h := by
  ext i : 1
  by_cases hi₀ : i = -1
  · subst i
    simp only [HomologicalComplex.comp_f, koszulSingleConeIso_hom_f_negOne]
    rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 1 = -1 from rfl)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% h₁, singleConeMap_negOne]
  · by_cases hi₁ : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, koszulSingleConeIso_hom_f_zero]
      rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h₀, singleConeMap_zero]
    · exact (koszulSingleExtended_isZero_X A f i hi₀ hi₁).eq_of_src _ _


private def principalQuotientIso (A : Type u) [CommRing A] (f : A) :
    ModuleCat.of A (A ⧸ Ideal.span (Set.range (fun _ : Fin 1 ↦ f))) ≅
      ModuleCat.of A (A ⧸ Ideal.span {f}) :=
  (Submodule.quotEquivOfEq _ _ (by rw [Set.range_const])).toModuleIso

private theorem principalQuotientIso_mkQ (A : Type u) [CommRing A] (f : A) :
    ModuleCat.ofHom (Ideal.span (Set.range (fun _ : Fin 1 ↦ f))).mkQ ≫
      (principalQuotientIso A f).hom = ModuleCat.ofHom (Ideal.span {f}).mkQ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private def quotientPowerSingleIso (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A (A ⧸ Ideal.span (Set.range fun _ : Fin 1 ↦ f ^ n))))).extend
        ComplexShape.embeddingDownNat ≅ (ProTorsion.single0 A).obj (ProTorsion.Qmod A f n) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0
    (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl) ≪≫
    (ProTorsion.single0 A).mapIso (principalQuotientIso A (f ^ n))

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerConeIso_augmentation (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    HomologicalComplex.extendMap
      (Koszul.koszulAugmentation (fun _ : Fin 1 ↦ f ^ n))
      ComplexShape.embeddingDownNat ≫ (quotientPowerSingleIso A f n).hom =
    (koszulPowerConeIso A f n).hom ≫ ProTorsion.alphaCx A f n := by
  apply HomologicalComplex.to_single_hom_ext (j := (0 : ℤ))
  simp only [HomologicalComplex.comp_f, quotientPowerSingleIso, Iso.trans_hom,
    Functor.mapIso_hom, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl),
    HomologicalComplex.extendSingleIso_hom_f]
  show _ = (koszulSingleConeIso A (f ^ n)).hom.f 0 ≫ (ProTorsion.alphaCx A f n).f 0
  rw [koszulSingleConeIso_hom_f_zero]
  simp only [ProTorsion.single0, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  have ha : (singleConeZeroIso (f ^ n • 𝟙 (ModuleCat.of A A))).hom ≫
      (ProTorsion.alphaCx A f n).f 0 =
      ProTorsion.quotMap A f n ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
        0 (ProTorsion.Qmod A f n)).inv := by
    dsimp only [singleConeZeroIso]
    rw [Category.assoc]
    show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
      (CochainComplex.mappingCone.inr ((ProTorsion.single0 A).map (ProTorsion.smulMap A f n))).f 0 ≫
        (ProTorsion.alphaCx A f n).f 0 = _
    rw [ProTorsion.alphaCx, CochainComplex.mappingCone.inr_f_desc_f]
    simp only [ProTorsion.single0, HomologicalComplex.single_map_f_self,
      Iso.inv_hom_id_assoc]
  rw [ha]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerTransition_single (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) (n + 1) n (Nat.le_succ n) ≫
      (principalQuotientIso A (f ^ (n + 1))).hom =
      (principalQuotientIso A (f ^ (n + 1 + 1))).hom ≫ ProTorsion.QtransMod A f (n + 1) 1 := by
  let q := ModuleCat.ofHom (Ideal.span (Set.range (fun _ : Fin 1 ↦ f ^ (n + 1 + 1)))).mkQ
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 (Submodule.mkQ_surjective _)
  apply (cancel_epi q).mp
  dsimp only [q, ProTorsion.Qmod]
  rw [← Category.assoc, NoetherianKoszulProIso.quotientPowerTransition_comp_mkQ,
    principalQuotientIso_mkQ, ← Category.assoc, principalQuotientIso_mkQ]
  exact (ProTorsion.quotMap_QtransMod A f (n + 1) 1).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extendSingleIso_naturality {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') {X Y : C} (a : X ⟶ Y) :
    HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map a) e ≫
      (HomologicalComplex.extendSingleIso e Y i i' h).hom =
      (HomologicalComplex.extendSingleIso e X i i' h).hom ≫
        (HomologicalComplex.single C c' i').map a := by
  apply HomologicalComplex.to_single_hom_ext (j := i')
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ h,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerSingleIso_transition (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    HomologicalComplex.extendMap
      ((ChainComplex.single₀ (ModuleCat A)).map
        (NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) (n + 1) n (Nat.le_succ
          n)))
      ComplexShape.embeddingDownNat ≫ (quotientPowerSingleIso A f (n + 1)).hom =
      (quotientPowerSingleIso A f (n + 1 + 1)).hom ≫
        (ProTorsion.single0 A).map (ProTorsion.QtransMod A f (n + 1) 1) := by
  dsimp only [quotientPowerSingleIso, Iso.trans_hom, Functor.mapIso_hom, ProTorsion.single0]
  rw [← Category.assoc, extendSingleIso_naturality ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl), Category.assoc, ← Functor.map_comp,
    quotientPowerTransition_single, Functor.map_comp]
  simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private theorem ofOpSequence_map_of_transition {C : Type*} [Category* C]
    {X : ℕ → C} (t : ∀ m n, n ≤ m → (X m ⟶ X n))
    (hid : ∀ n, t n n (le_refl n) = 𝟙 _)
    (hcomp : ∀ k m n (hkm : m ≤ k) (hmn : n ≤ m),
      t k m hkm ≫ t m n hmn = t k n (hmn.trans hkm))
    (m n : ℕ) (h : n ≤ m) :
    (Functor.ofOpSequence (fun n ↦ t (n + 1) n (Nat.le_succ n))).map (homOfLE h).op = t m n h := by
  induction m, h using Nat.le_induction with
  | base =>
    show (Functor.ofOpSequence _).map (𝟙 (op n)) = _
    rw [hid]
    exact (Functor.ofOpSequence (fun n ↦ t (n + 1) n (Nat.le_succ n))).map_id _
  | succ m hnm ih =>
    have he : (homOfLE (Nat.le_succ_of_le hnm)).op =
      (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ, ih]
    exact hcomp (m + 1) m n (Nat.le_succ m) hnm

private theorem quotientPowerTransition_id
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    NoetherianKoszulProIso.quotientPowerTransition f n n (le_refl n) = 𝟙 _ := by
  unfold NoetherianKoszulProIso.quotientPowerTransition
  rcases Classical.choose_spec (Classical.choose_spec
    (_root_.koszulPowerComplexes_form_inverseSystem f)) with
    ⟨e, η, hid, hcomp, hsid, hscomp, hformula, hη, hητ, hσ, he, hlast⟩
  exact hsid n

private theorem quotientPowerTransition_comp
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m) :
    NoetherianKoszulProIso.quotientPowerTransition f k m hkm ≫
        NoetherianKoszulProIso.quotientPowerTransition f m n hmn =
      NoetherianKoszulProIso.quotientPowerTransition f k n (hmn.trans hkm) := by
  unfold NoetherianKoszulProIso.quotientPowerTransition
  rcases Classical.choose_spec (Classical.choose_spec
    (_root_.koszulPowerComplexes_form_inverseSystem f)) with
    ⟨e, η, hid, hcomp, hsid, hscomp, hformula, hη, hητ, hσ, he, hlast⟩
  exact hscomp k m n hkm hmn

set_option backward.isDefEq.respectTransparency false in
private theorem koszulComplexTower_map
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    (koszulComplexTower f).map (homOfLE h).op =
      HomologicalComplex.extendMap (NoetherianKoszulProIso.koszulPowerTransition f m n h)
        ComplexShape.embeddingDownNat := by
  refine ofOpSequence_map_of_transition
    (fun m n h ↦ HomologicalComplex.extendMap (NoetherianKoszulProIso.koszulPowerTransition f m n h)
      ComplexShape.embeddingDownNat) ?_ ?_ m n h
  · intro k
    rw [NoetherianKoszulProIso.koszulPowerTransition_id, HomologicalComplex.extendMap_id]
  · intro k m n hkm hmn
    rw [← HomologicalComplex.extendMap_comp, NoetherianKoszulProIso.koszulPowerTransition_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientComplexTower_map
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    (quotientComplexTower f).map (homOfLE h).op =
      HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map
        (NoetherianKoszulProIso.quotientPowerTransition f m n h)) ComplexShape.embeddingDownNat :=
          by
  refine ofOpSequence_map_of_transition
    (fun m n h ↦ HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map
      (NoetherianKoszulProIso.quotientPowerTransition f m n h)) ComplexShape.embeddingDownNat) ?_ ?_
        m n h
  · intro k
    rw [quotientPowerTransition_id, CategoryTheory.Functor.map_id, HomologicalComplex.extendMap_id]
  · intro k m n hkm hmn
    rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp, quotientPowerTransition_comp]


/-- Multiplication by `f ^ (n + c)` factors as multiplication by `f ^ c` then by `f ^ n`. -/
private theorem pow_smul_square (A : Type u) [CommRing A] (f : A) (m n c : ℕ) (h : m = n + c) :
    (f ^ m • 𝟙 (ModuleCat.of A A)) ≫ 𝟙 _ = (f ^ c • 𝟙 _) ≫ (f ^ n • 𝟙 _) := by
  subst h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show f ^ (n + c) * x = f ^ n * (f ^ c * x)
  rw [pow_add, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem singleConeMap_eq_KtransCx (A : Type u) [CommRing A] (f : A)
    (m n c : ℕ) (hm : m = n + c)
    (h : (f ^ m • 𝟙 (ModuleCat.of A A)) ≫ 𝟙 _ =
      (f ^ c • 𝟙 (ModuleCat.of A A)) ≫ (f ^ n • 𝟙 (ModuleCat.of A A))) :
    singleConeMap (f ^ m • 𝟙 (ModuleCat.of A A)) (f ^ n • 𝟙 (ModuleCat.of A A))
      (f ^ c • 𝟙 (ModuleCat.of A A)) (𝟙 _) h =
      eqToHom (congrArg (ProTorsion.Kcx A f) hm) ≫ ProTorsion.KtransCx A f n c := by
  subst m
  dsimp only [singleConeMap, singleMap, ProTorsion.KtransCx, ProTorsion.Kcx, ProTorsion.single0]
  simp only [eqToHom_refl, Category.id_comp]
  congr 1
  exact (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).map_id _

set_option backward.isDefEq.respectTransparency false in
-- The naturality squares below unfold the total tensor complex degreewise over `ℤ`, which
-- exceeds the default heartbeat budget.
private theorem koszulPowerConeIso_transition (A : Type u) [CommRing A] (f : A) (n c : ℕ) :
    HomologicalComplex.extendMap
      (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n (Nat.le_add_right
        n c))
      ComplexShape.embeddingDownNat ≫ (koszulPowerConeIso A f (n + 1)).hom =
    (koszulPowerConeIso A f (n + c + 1)).hom ≫
      eqToHom (congrArg (ProTorsion.Kcx A f) (show n + c + 1 = n + 1 + c by omega)) ≫
        ProTorsion.KtransCx A f (n + 1) c := by
  have he : n + c + 1 = n + 1 + c := by omega
  -- Compare the two supported components, then retain the cone square.
  have h := pow_smul_square A f (n + c + 1) (n + 1) c he
  have hm := koszulSingleConeIso_naturality A (f ^ (n + c + 1)) (f ^ (n + 1))
    (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n (Nat.le_add_right n
      c))
    (f ^ c • 𝟙 (ModuleCat.of A A)) (𝟙 _) h
  have h₁ : (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n
      (Nat.le_add_right n c)).f 1 ≫ (koszulSingleOneIso A (f ^ (n + 1))).hom =
      (koszulSingleOneIso A (f ^ (n + c + 1))).hom ≫ (f ^ c • 𝟙 (ModuleCat.of A A)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show exteriorPower.oneEquiv A (Fin 1 → A)
      ((NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n
        (Nat.le_add_right n c)).f 1 x) 0 =
      f ^ c * exteriorPower.oneEquiv A (Fin 1 → A) x 0
    simpa only [Nat.add_sub_cancel_left] using
      koszulPowerTransition_one A (fun _ : Fin 1 ↦ f) (n + c) n (Nat.le_add_right n c) x 0
  have h₀ : (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n
      (Nat.le_add_right n c)).f 0 ≫ (koszulSingleZeroIso A (f ^ (n + 1))).hom =
      (koszulSingleZeroIso A (f ^ (n + c + 1))).hom ≫ 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show exteriorPower.zeroEquiv A (Fin 1 → A)
      ((NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n
        (Nat.le_add_right n c)).f 0 x) = exteriorPower.zeroEquiv A (Fin 1 → A) x
    rw [koszulPowerTransition_zero]
  have hn := hm h₁ h₀
  rw [singleConeMap_eq_KtransCx A f (n + c + 1) (n + 1) c he h] at hn
  exact hn


private theorem quotMap_cast (A : Type u) [CommRing A] (f : A) (m k : ℕ) (h : m = k) :
    ProTorsion.quotMap A f m ≫ eqToHom (congrArg (ProTorsion.Qmod A f) h) =
      ProTorsion.quotMap A f k := by
  subst k
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerTransition_shift (A : Type u) [CommRing A] (f : A) (n c : ℕ) :
    NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n (Nat.le_add_right n
      c) ≫
      (principalQuotientIso A (f ^ (n + 1))).hom =
      (principalQuotientIso A (f ^ (n + c + 1))).hom ≫
        eqToHom (congrArg (ProTorsion.Qmod A f) (show n + c + 1 = n + 1 + c by omega)) ≫
          ProTorsion.QtransMod A f (n + 1) c := by
  let q := ModuleCat.ofHom (Ideal.span (Set.range (fun _ : Fin 1 ↦ f ^ (n + c + 1)))).mkQ
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 (Submodule.mkQ_surjective _)
  apply (cancel_epi q).mp
  dsimp only [q, ProTorsion.Qmod]
  rw [← Category.assoc, NoetherianKoszulProIso.quotientPowerTransition_comp_mkQ,
    principalQuotientIso_mkQ, ← Category.assoc, principalQuotientIso_mkQ]
  show ProTorsion.quotMap A f (n + 1) =
    ProTorsion.quotMap A f (n + c + 1) ≫
      eqToHom (congrArg (ProTorsion.Qmod A f) (show n + c + 1 = n + 1 + c by omega)) ≫
        ProTorsion.QtransMod A f (n + 1) c
  rw [← Category.assoc, quotMap_cast A f (n + c + 1) (n + 1 + c) (by omega),
    ProTorsion.quotMap_QtransMod]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerSingleIso_shift (A : Type u) [CommRing A] (f : A) (n c : ℕ) :
    HomologicalComplex.extendMap
      ((ChainComplex.single₀ (ModuleCat A)).map
        (NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) (n + c) n
          (Nat.le_add_right n c)))
      ComplexShape.embeddingDownNat ≫ (quotientPowerSingleIso A f (n + 1)).hom =
      (quotientPowerSingleIso A f (n + c + 1)).hom ≫
        (ProTorsion.single0 A).map
          (eqToHom (congrArg (ProTorsion.Qmod A f) (show n + c + 1 = n + 1 + c by omega)) ≫
            ProTorsion.QtransMod A f (n + 1) c) := by
  dsimp only [quotientPowerSingleIso, Iso.trans_hom, Functor.mapIso_hom, ProTorsion.single0]
  rw [← Category.assoc, extendSingleIso_naturality ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl), Category.assoc,
    ← Functor.map_comp, quotientPowerTransition_shift, Functor.map_comp]
  simp only [Category.assoc]


end PrincipalKoszul

section ProZeroDetection
variable {A : Type u} [Ring A] (E : ℕᵒᵖ ⥤ ModuleCat.{v} A)
private abbrev transition {n m : ℕ} (h : n ≤ m) : E.obj (op m) →ₗ[A] E.obj (op n) :=
  (E.map (homOfLE h).op).hom
private theorem transition_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k)
    (x : E.obj (op k)) : transition E h (transition E h' x) = transition E (h.trans h') x := by
  show (E.map (homOfLE h').op ≫ E.map (homOfLE h).op) x = _
  rw [← E.map_comp]
  rfl
private theorem transition_self (n : ℕ) (x : E.obj (op n)) : transition E (le_refl n) x = x := by
  show E.map (𝟙 (op n)) x = x
  rw [E.map_id]
  rfl

private theorem transition_eq_of_compatible
    (z : ∀ n : ℕ, E.obj (op n)) {m k : ℕ} (h : m ≤ k)
    (hz : ∀ n, m ≤ n → n < k → z n = transition E (Nat.le_succ n) (z (n + 1))) :
    z m = transition E h (z k) := by
  induction k, h using Nat.le_induction with
  | base => exact (transition_self E m (z m)).symm
  | succ k hmk ih =>
    rw [ih (fun n hn hn' => hz n hn (Nat.lt_succ_of_lt hn')),
      hz k hmk (Nat.lt_succ_self k), transition_comp]

private theorem compatible_tail_eq_zero
    (hinj : ∀ x : ∀ n, E.obj (op n),
      (∀ n, x n = transition E (Nat.le_succ n) (x (n + 1))) → ∀ n, x n = 0)
    (z : ∀ n, E.obj (op n)) (k : ℕ)
    (hz : ∀ n, k ≤ n → z n = transition E (Nat.le_succ n) (z (n + 1))) : z k = 0 := by
  let y : ∀ n, E.obj (op n) := fun n ↦ if h : n ≤ k then transition E h (z k) else z n
  have hy (n : ℕ) : y n = transition E (Nat.le_succ n) (y (n + 1)) := by
    by_cases h : n < k
    · have hn : n ≤ k := Nat.le_of_lt h
      have hn' : n + 1 ≤ k := h
      simp only [y, dite_eq_left hn, dite_eq_left hn', transition_comp]
    · by_cases he : n = k
      · subst n
        simp only [y, dite_eq_left (le_refl k), dite_eq_right (show ¬k + 1 ≤ k by omega),
          transition_self]
        exact hz k (le_refl k)
      · have hn : ¬n ≤ k := by omega
        have hn' : ¬n + 1 ≤ k := by omega
        simp only [y, dite_eq_right hn, dite_eq_right hn']
        exact hz n (by omega)
  have h := hinj y hy k
  simpa only [y, dite_eq_left (le_refl k), transition_self] using h

private theorem proZero_of_delta_injective_of_finsupp_delta_surjective
    (hinj : ∀ x : ∀ n, E.obj (op n),
      (∀ n, x n = transition E (Nat.le_succ n) (x (n + 1))) → ∀ n, x n = 0)
    (hsurj : ∀ y : ∀ n, ℕ →₀ E.obj (op n), ∃ z : ∀ n, ℕ →₀ E.obj (op n),
      ∀ n i, z n i - transition E (Nat.le_succ n) (z (n + 1) i) = y n i) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), E.map (homOfLE h).op = 0 := by
  classical
  intro n
  by_contra h
  have bad : ∀ m : ℕ, ∃ x : E.obj (op m), ∀ hnm : n ≤ m, transition E hnm x ≠ 0 := by
    intro m
    by_cases hnm : n ≤ m
    · have hnz : E.map (homOfLE hnm).op ≠ 0 := by
        intro he
        exact h ⟨m, hnm, he⟩
      have hx : ∃ x : E.obj (op m), transition E hnm x ≠ 0 := by
        by_contra hh
        push Not at hh
        apply hnz
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact hh
      obtain ⟨x, hx⟩ := hx
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun hh ↦ (hnm hh).elim⟩
  choose x hx using bad
  obtain ⟨z, hz⟩ := hsurj (fun m ↦ Finsupp.single m (x m))
  have step (m i : ℕ) (hmi : m ≠ i) :
      z m i = transition E (Nat.le_succ m) (z (m + 1) i) := by
    apply sub_eq_zero.mp
    simpa only [Finsupp.single_apply, ite_eq_right hmi] using hz m i
  let i := max n ((z n).support.sup id + 1)
  have hni : n ≤ i := le_max_left _ _
  have hzero : z n i = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hi
    have hb : i ≤ (z n).support.sup id := Finset.le_sup (f := id) hi
    have hi' : (z n).support.sup id + 1 ≤ i := le_max_right _ _
    omega
  have htail : z (i + 1) i = 0 :=
    compatible_tail_eq_zero E hinj (fun m ↦ z m i) (i + 1)
      (fun m hm ↦ step m i (by omega))
  have hii : z i i = x i := by
    have hh := hz i i
    simpa only [htail, map_zero, sub_zero, Finsupp.single_eq_same] using hh
  have hbefore : z n i = transition E hni (z i i) :=
    transition_eq_of_compatible E (fun m ↦ z m i) hni
      (fun m _ hm ↦ step m i (ne_of_lt hm))
  exact hx i hni (by rw [← hii, ← hbefore, hzero])

end ProZeroDetection

section ShiftedProInverse
private theorem familyMap_cast {C : Type*} [Category* C] {X Y : ℕ → C}
    (t : ∀ n, X n ⟶ Y n) (m k : ℕ) (h : m = k) :
    t m ≫ eqToHom (congrArg Y h) = eqToHom (congrArg X h) ≫ t k := by
  subst k
  simp
private theorem sequenceMap_cast {C : Type*} [Category* C] {X : ℕ → C}
    (t : ∀ n, X (n + 1) ⟶ X n) (m k : ℕ) (h : m = k) :
    eqToHom (congrArg X (congrArg (fun n ↦ n + 1) h)) ≫ t k =
      t m ≫ eqToHom (congrArg X h) := by
  subst k
  simp

variable (A : Type u) [CommRing A] (f : A) (c : ℕ)
  (hstab : ∀ m : ℕ, c ≤ m → Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m))
private def shiftedBeta (n : ℕ) :
    ProTorsion.Qobj A f (n + c + 1) ⟶ ProTorsion.Kobj A f (n + 1) :=
  eqToHom (congrArg (ProTorsion.Qobj A f) (show n + c + 1 = n + 1 + c by omega)) ≫
    ProTorsion.beta A f c hstab (n + 1)

private theorem alpha_shiftedBeta (n : ℕ) :
    ProTorsion.alpha A f (n + c + 1) ≫ shiftedBeta A f c hstab n =
      eqToHom (congrArg (ProTorsion.Kobj A f) (show n + c + 1 = n + 1 + c by omega)) ≫
        ProTorsion.Ktrans A f (n + 1) c := by
  dsimp only [shiftedBeta]
  rw [← Category.assoc, familyMap_cast (ProTorsion.alpha A f)
    (n + c + 1) (n + 1 + c) (by omega), Category.assoc,
    (ProTorsion.proIso_of_torsionBounded A f c hstab).2.1]

private theorem shiftedBeta_alpha (n : ℕ) :
    shiftedBeta A f c hstab n ≫ ProTorsion.alpha A f (n + 1) =
      eqToHom (congrArg (ProTorsion.Qobj A f) (show n + c + 1 = n + 1 + c by omega)) ≫
        ProTorsion.Qtrans A f (n + 1) c := by
  dsimp only [shiftedBeta]
  rw [Category.assoc, (ProTorsion.proIso_of_torsionBounded A f c hstab).1]

private theorem shiftedBeta_transition (n : ℕ) :
    eqToHom (congrArg (ProTorsion.Qobj A f)
      (show n + 1 + c + 1 = n + c + 1 + 1 by omega)) ≫
      ProTorsion.QtransOne A f (n + c + 1) ≫ shiftedBeta A f c hstab n =
        shiftedBeta A f c hstab (n + 1) ≫ ProTorsion.KtransOne A f (n + 1) := by
  dsimp only [shiftedBeta]
  rw [← Category.assoc, sequenceMap_cast (ProTorsion.QtransOne A f)
    (n + 1 + c) (n + c + 1) (by omega)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (ProTorsion.proIso_of_torsionBounded A f c hstab).2.2.2 (n + 1)


end ShiftedProInverse
section BoundedProInverse
private abbrev principalKoszulDerivedIso (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (NoetherianKoszulProIso.koszulPowerSystem (fun _ : Fin 1 ↦ f)).obj (op n) ≅ ProTorsion.Kobj A f
      (n + 1) :=
  DerivedCategory.Q.mapIso (koszulPowerConeIso A f (n + 1))
private abbrev principalQuotientDerivedIso (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (NoetherianKoszulProIso.quotientPowerSystem (fun _ : Fin 1 ↦ f)).obj (op n) ≅ ProTorsion.Qobj A
      f (n + 1) :=
  DerivedCategory.Q.mapIso (quotientPowerSingleIso A f (n + 1))

set_option backward.isDefEq.respectTransparency false in
private theorem principalDerivedIso_comparison (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (NoetherianKoszulProIso.koszulQuotientComparison (fun _ : Fin 1 ↦ f)).app (op n) ≫
      (principalQuotientDerivedIso A f n).hom =
      (principalKoszulDerivedIso A f n).hom ≫ ProTorsion.alpha A f (n + 1) := by
  show (DerivedCategory.Q (C := ModuleCat A)).map _ ≫ (DerivedCategory.Q (C := ModuleCat A)).map _
    =
    (DerivedCategory.Q (C := ModuleCat A)).map _ ≫ (DerivedCategory.Q (C := ModuleCat A)).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    koszulPowerConeIso_augmentation]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerSystem_map
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    (NoetherianKoszulProIso.koszulPowerSystem f).map (homOfLE h).op =
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        (NoetherianKoszulProIso.koszulPowerTransition f m n h) ComplexShape.embeddingDownNat) := by
  refine ofOpSequence_map_of_transition
    (fun m n h ↦ DerivedCategory.Q.map (HomologicalComplex.extendMap
      (NoetherianKoszulProIso.koszulPowerTransition f m n h) ComplexShape.embeddingDownNat)) ?_ ?_ m
        n h
  · intro k
    rw [NoetherianKoszulProIso.koszulPowerTransition_id, HomologicalComplex.extendMap_id,
      CategoryTheory.Functor.map_id]
  · intro k m n hkm hmn
    rw [← CategoryTheory.Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      NoetherianKoszulProIso.koszulPowerTransition_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerSystem_map
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    (NoetherianKoszulProIso.quotientPowerSystem f).map (homOfLE h).op =
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat A)).map
          (NoetherianKoszulProIso.quotientPowerTransition f m n h)) ComplexShape.embeddingDownNat)
            := by
  refine ofOpSequence_map_of_transition
    (fun m n h ↦ DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((ChainComplex.single₀ (ModuleCat A)).map (NoetherianKoszulProIso.quotientPowerTransition f m
        n h))
        ComplexShape.embeddingDownNat)) ?_ ?_ m n h
  · intro k
    rw [quotientPowerTransition_id, CategoryTheory.Functor.map_id,
      HomologicalComplex.extendMap_id, CategoryTheory.Functor.map_id]
  · intro k m n hkm hmn
    rw [← CategoryTheory.Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      ← CategoryTheory.Functor.map_comp, quotientPowerTransition_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem principalKoszulDerivedIso_shift (A : Type u) [CommRing A] (f : A) (n c : ℕ) :
    (NoetherianKoszulProIso.koszulPowerSystem (fun _ : Fin 1 ↦ f)).map (homOfLE (Nat.le_add_right n
      c)).op ≫
      (principalKoszulDerivedIso A f n).hom =
      (principalKoszulDerivedIso A f (n + c)).hom ≫
        eqToHom (congrArg (ProTorsion.Kobj A f) (show n + c + 1 = n + 1 + c by omega)) ≫
          ProTorsion.Ktrans A f (n + 1) c := by
  rw [koszulPowerSystem_map]
  show (DerivedCategory.Q (C := ModuleCat A)).map _ ≫ (DerivedCategory.Q (C := ModuleCat A)).map _
    = _
  rw [← CategoryTheory.Functor.map_comp, koszulPowerConeIso_transition,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    eqToHom_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerTransition_eq_QtransMod (A : Type u) [CommRing A] (f : A)
    (m n c : ℕ) (hm : n ≤ m) (he : m + 1 = n + 1 + c) :
    NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) m n hm ≫
      (principalQuotientIso A (f ^ (n + 1))).hom =
      (principalQuotientIso A (f ^ (m + 1))).hom ≫
        eqToHom (congrArg (ProTorsion.Qmod A f) he) ≫ ProTorsion.QtransMod A f (n + 1) c := by
  let q := ModuleCat.ofHom (Ideal.span (Set.range (fun _ : Fin 1 ↦ f ^ (m + 1)))).mkQ
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 (Submodule.mkQ_surjective _)
  apply (cancel_epi q).mp
  dsimp only [q, ProTorsion.Qmod]
  rw [← Category.assoc, NoetherianKoszulProIso.quotientPowerTransition_comp_mkQ,
    principalQuotientIso_mkQ, ← Category.assoc, principalQuotientIso_mkQ]
  show ProTorsion.quotMap A f (n + 1) =
    ProTorsion.quotMap A f (m + 1) ≫ eqToHom (congrArg (ProTorsion.Qmod A f) he) ≫ _
  rw [← Category.assoc, quotMap_cast A f (m + 1) (n + 1 + c) he,
    ProTorsion.quotMap_QtransMod]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowerSingleIso_map (A : Type u) [CommRing A] (f : A)
    (m n c : ℕ) (hm : n ≤ m) (he : m + 1 = n + 1 + c) :
    HomologicalComplex.extendMap
      ((ChainComplex.single₀ (ModuleCat A)).map
        (NoetherianKoszulProIso.quotientPowerTransition (fun _ : Fin 1 ↦ f) m n hm))
      ComplexShape.embeddingDownNat ≫ (quotientPowerSingleIso A f (n + 1)).hom =
      (quotientPowerSingleIso A f (m + 1)).hom ≫
        (ProTorsion.single0 A).map
          (eqToHom (congrArg (ProTorsion.Qmod A f) he) ≫ ProTorsion.QtransMod A f (n + 1) c) := by
  dsimp only [quotientPowerSingleIso, Iso.trans_hom, Functor.mapIso_hom, ProTorsion.single0]
  rw [← Category.assoc, extendSingleIso_naturality ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl), Category.assoc,
    ← CategoryTheory.Functor.map_comp, quotientPowerTransition_eq_QtransMod A f m n c hm he,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem principalQuotientDerivedIso_map (A : Type u) [CommRing A] (f : A)
    (m n c : ℕ) (hm : n ≤ m) (he : m + 1 = n + 1 + c) :
    (NoetherianKoszulProIso.quotientPowerSystem (fun _ : Fin 1 ↦ f)).map (homOfLE hm).op ≫
      (principalQuotientDerivedIso A f n).hom =
      (principalQuotientDerivedIso A f m).hom ≫
        eqToHom (congrArg (ProTorsion.Qobj A f) he) ≫ ProTorsion.Qtrans A f (n + 1) c := by
  rw [quotientPowerSystem_map]
  show (DerivedCategory.Q (C := ModuleCat A)).map _ ≫ (DerivedCategory.Q (C := ModuleCat A)).map _
    = _
  rw [← CategoryTheory.Functor.map_comp, quotientPowerSingleIso_map A f m n c hm he,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, eqToHom_map,
    eqToHom_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem koszulQuotientComparison_uniformProInverse_of_torsionBounded
    (A : Type u) [CommRing A] (f : A) (hf : ProTorsion.TorsionBounded A f) :
    let E := NoetherianKoszulProIso.koszulPowerSystem (fun _ : Fin 1 ↦ f)
    let F := NoetherianKoszulProIso.quotientPowerSystem (fun _ : Fin 1 ↦ f)
    let α := NoetherianKoszulProIso.koszulQuotientComparison (fun _ : Fin 1 ↦ f)
    ∃ (c : ℕ) (ψ : ∀ n, F.obj (op (n + c)) ⟶ E.obj (op n)),
      (∀ n, α.app (op (n + c)) ≫ ψ n = E.map (homOfLE (Nat.le_add_right n c)).op) ∧
      (∀ n, ψ n ≫ α.app (op n) = F.map (homOfLE (Nat.le_add_right n c)).op) ∧
      (∀ n, F.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
        ψ (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨c, hc, hstab⟩ := hf
  let ψ (n : ℕ) := (principalQuotientDerivedIso A f (n + c)).hom ≫
    shiftedBeta A f c hstab n ≫ (principalKoszulDerivedIso A f n).inv
  refine ⟨c, ψ, ?_, ?_, ?_⟩
  · intro n
    apply (cancel_mono (principalKoszulDerivedIso A f n).hom).mp
    dsimp only [ψ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% (principalDerivedIso_comparison A f (n + c)), alpha_shiftedBeta]
    exact (principalKoszulDerivedIso_shift A f n c).symm
  · intro n
    apply (cancel_mono (principalQuotientDerivedIso A f n).hom).mp
    dsimp only [ψ]
    simp only [Category.assoc]
    rw [principalDerivedIso_comparison]
    simp only [Iso.inv_hom_id_assoc]
    rw [shiftedBeta_alpha]
    exact (principalQuotientDerivedIso_map A f (n + c) n c (Nat.le_add_right n c)
      (by omega)).symm
  · intro n
    apply (cancel_mono (principalKoszulDerivedIso A f n).hom).mp
    dsimp only [ψ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% (principalQuotientDerivedIso_map A f (n + 1 + c) (n + c) 1
        (by omega) (by omega)), principalKoszulDerivedIso_shift A f n 1]
    simp only [Iso.inv_hom_id_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (fun k ↦ (principalQuotientDerivedIso A f (n + 1 + c)).hom ≫ k)
      (shiftedBeta_transition A f c hstab n)

end BoundedProInverse

section MilnorExactness
open CountableMilnorTower
universe w x

private theorem isZero_localization_of_acyclic
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  have hq : QuasiIso (0 : K ⟶ K) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt (0 : K ⟶ K) i (hK i)).mpr (hK i)
  have h : IsIso (0 : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K) := by
    simpa using (inferInstance : IsIso (DerivedCategory.Q.map (0 : K ⟶ K)))
  exact (IsZero.iff_id_eq_zero _).mpr (isIsoZeroSelfEquiv _ h)

private theorem isZero_milnor_of_shortExact_of_isIso
    {A : Type u} [Ring A] (S : ShortComplex (Tower.{u, u} (A := A)))
    (hS : S.ShortExact)
    [IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map S.g))] :
    IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj S.X₁)) := by
  have hq : QuasiIso (countableMilnorFunctor.map S.g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  exact isZero_localization_of_acyclic _
    ((countableMilnorFunctor_map_shortExact S hS).acyclic_X₁ hq)


set_option backward.isDefEq.respectTransparency false in
private theorem map_milnorEndo_piComparison
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{x} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (E : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ E.obj (op n)]
    [HasProductsOfShape ℕ D] :
    F.map (milnorEndo E) ≫ piComparison F (fun n : ℕ ↦ E.obj (op n)) =
      piComparison F (fun n : ℕ ↦ E.obj (op n)) ≫ milnorEndo (E ⋙ F) := by
  dsimp only [milnorEndo, Functor.comp_obj, Functor.comp_map]
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π,
    Preadditive.comp_sub, ← F.map_comp]
  simp only [F.map_sub, F.map_comp]
  rw [← Category.assoc, piComparison_comp_π]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_milnorEndo_of_isIso_map
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{x} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms] (E : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ E.obj (op n)]
    [HasProductsOfShape ℕ D]
    [IsIso (piComparison F (fun n : ℕ ↦ E.obj (op n)))]
    [IsIso (milnorEndo (E ⋙ F))] : IsIso (milnorEndo E) := by
  have h : IsIso (F.map (milnorEndo E)) := by
    rw [← isIso_comp_right_iff _ (piComparison F (fun n : ℕ ↦ E.obj (op n))),
      map_milnorEndo_piComparison]
    infer_instance
  exact isIso_of_reflects_iso (milnorEndo E) F


end MilnorExactness

section BoundedComparison
open CountableMilnorTower

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_milnorMap_of_proIso_of_isos
    {A : Type u} [Ring A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] {F G : Tower.{u, u} (A := A)}
    (μ : F ⟶ G)
    {E H : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)} (φ : E ⟶ H)
    (iF : F ⋙ DerivedCategory.Q ≅ E) (iG : G ⋙ DerivedCategory.Q ≅ H)
    (hμ : Functor.whiskerRight μ DerivedCategory.Q ≫ iG.hom = iF.hom ≫ φ)
    (c : ℕ) (ψ : ∀ n, H.obj (op (n + c)) ⟶ E.obj (op n))
    (hψφ : ∀ n, φ.app (op (n + c)) ≫ ψ n = E.map (homOfLE (Nat.le_add_right n c)).op)
    (hφψ : ∀ n, ψ n ≫ φ.app (op n) = H.map (homOfLE (Nat.le_add_right n c)).op)
    (hψ : ∀ n, H.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) :
    IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map μ)) := by
  have hm (n : ℕ) : DerivedCategory.Q.map (μ.app (op n)) ≫ iG.hom.app (op n) =
      iF.hom.app (op n) ≫ φ.app (op n) := congrArg (fun a ↦ a.app (op n)) hμ
  apply isIso_milnorMap_of_proIso μ c
    (fun n ↦ iG.hom.app (op (n + c)) ≫ ψ n ≫ iF.inv.app (op n))
  · intro n
    rw [← Category.assoc, hm]
    simp only [Category.assoc]
    rw [reassoc_of% (hψφ n)]
    rw [← Category.assoc, ← iF.hom.naturality]
    simp
  · intro n
    apply (cancel_mono (iG.hom.app (op n))).mp
    simp only [Category.assoc, hm, Iso.inv_hom_id_app_assoc, hφψ]
    exact (iG.hom.naturality _).symm
  · intro n
    have hiG := iG.hom.naturality (homOfLE (show n + c ≤ n + 1 + c by omega)).op
    change DerivedCategory.Q.map _ ≫ _ = _ at hiG
    rw [← Category.assoc, hiG]
    simp only [Category.assoc]
    rw [reassoc_of% (hψ n)]
    have hiF := iF.inv.naturality (homOfLE (Nat.le_succ n)).op
    change _ = _ ≫ DerivedCategory.Q.map _ at hiF
    rw [hiF]

set_option backward.isDefEq.respectTransparency false in
private theorem strictTensorLimitMap_isIso_of_uniformProInverse
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] {F G : Tower.{u, u} (A := A)}
    (μ : F ⟶ G)
    {E H : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)} (φ : E ⟶ H)
    (iF : F ⋙ DerivedCategory.Q ≅ E) (iG : G ⋙ DerivedCategory.Q ≅ H)
    (hμ : Functor.whiskerRight μ DerivedCategory.Q ≫ iG.hom = iF.hom ≫ φ)
    (c : ℕ) (ψ : ∀ n, H.obj (op (n + c)) ⟶ E.obj (op n))
    (hψφ : ∀ n, φ.app (op (n + c)) ≫ ψ n = E.map (homOfLE (Nat.le_add_right n c)).op)
    (hφψ : ∀ n, ψ n ≫ φ.app (op n) = H.map (homOfLE (Nat.le_add_right n c)).op)
    (hψ : ∀ n, H.map (homOfLE (show n + c ≤ n + 1 + c by omega)).op ≫ ψ n =
      ψ (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) :
    IsIso (strictTensorLimitMap A μ) := by
  suffices h : ∀ K, IsIso ((strictTensorLimitMap A μ).app K) from by
    let := h
    exact NatIso.isIso_of_isIso_app _
  intro K
  obtain ⟨P, pP, hP, _, hpP, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage K)
  have := hpP
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map pP) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let B := T.tensor.obj (DerivedCategory.Q.obj P)
  let jF := strictTensorTowerIso A T F P hP ≪≫ Functor.isoWhiskerRight iF B
  let jG := strictTensorTowerIso A T G P hP ≪≫ Functor.isoWhiskerRight iG B
  have hm : Functor.whiskerRight (Functor.whiskerRight μ (TleftCochain P)) DerivedCategory.Q ≫
      jG.hom = jF.hom ≫ Functor.whiskerRight φ B := by
    dsimp only [jF, jG, Iso.trans_hom]
    rw [← Category.assoc, strictTensorTowerIso_naturality]
    simp only [Category.assoc, Functor.isoWhiskerRight_hom]
    rw [← Functor.whiskerRight_comp, hμ, Functor.whiskerRight_comp]
  have hmIso : IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight μ (TleftCochain P)))) :=
    isIso_milnorMap_of_proIso_of_isos _ (Functor.whiskerRight φ B) jF jG hm c
      (fun n ↦ B.map (ψ n))
      (fun n ↦ by simpa only [Functor.map_comp, Functor.comp_obj, Functor.comp_map,
        Functor.whiskerRight_app] using congrArg B.map (hψφ n))
      (fun n ↦ by simpa only [Functor.map_comp, Functor.comp_obj, Functor.comp_map,
        Functor.whiskerRight_app] using congrArg B.map (hφψ n))
      (fun n ↦ by simpa only [Functor.map_comp, Functor.comp_obj, Functor.comp_map,
        Functor.whiskerRight_app] using congrArg B.map (hψ n))
  have hrep : IsIso ((strictTensorLimitMap A μ).app (DerivedCategory.Q.obj P)) := by
    have h := strictTensorLimitRepresentativeIso_naturality A μ P hP
    rw [← isIso_comp_right_iff _ (strictTensorLimitRepresentativeIso A G P hP).hom, h]
    infer_instance
  have h := (strictTensorLimitMap A μ).naturality e.hom
  rw [← isIso_comp_left_iff ((strictTensorLimit A F).map e.hom) _, h]
  infer_instance

private theorem tensorKoszulQuotientComparison_isIso_of_torsionBounded
    (A : Type u) [CommRing A] (f : A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hf : ProTorsion.TorsionBounded A f) :
    IsIso (tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f)) := by
  obtain ⟨c, ψ, hψφ, hφψ, hψ⟩ :=
    koszulQuotientComparison_uniformProInverse_of_torsionBounded A f hf
  exact strictTensorLimitMap_isIso_of_uniformProInverse A
    (koszulComplexComparison (fun _ : Fin 1 ↦ f))
    (NoetherianKoszulProIso.koszulQuotientComparison (fun _ : Fin 1 ↦ f))
    (koszulComplexTowerDerivedIso _) (quotientComplexTowerDerivedIso _)
    (koszulComplexComparison_compatibility _) c ψ hψφ hφψ hψ

end BoundedComparison

section RightRepresentative
attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private def tensorSystemLimitRightRepresentativeNatIso (A : Type u) [CommRing A]
    (E : CochainComplex (ModuleSystems A) ℤ)
    (hE : ∀ n : ℕ, CochainComplex.KFlat
      (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj E).obj (op n))) :
    DerivedCategory.Q ⋙ tensorSystemLimit A E ≅
      (ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
          ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj E ⋙ systemMilnor A := by
  let Δ := ModuleSystemRlimTensor.constantSystem A
  let ΔC := Δ.mapHomologicalComplex (ComplexShape.up ℤ)
  let B := (systemTensor A).tensor.flip.obj (DerivedCategory.Q.obj E)
  let C := (systemTensor A).tensor.obj (DerivedCategory.Q.obj E)
  let EC := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj E
  let i : B ≅ C := ((systemTensor A).symmetry.app (DerivedCategory.Q.obj E)).symm
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerRight Δ.mapDerivedCategoryFactors B ≪≫
        Functor.associator ΔC DerivedCategory.Q B ≪≫
          Functor.isoWhiskerLeft ΔC
            (Functor.isoWhiskerLeft DerivedCategory.Q i ≪≫ systemTensorComparison A E hE))
        (derivedSystemMilnor A) ≪≫
      Functor.associator ΔC (EC ⋙ DerivedCategory.Q) (derivedSystemMilnor A) ≪≫
        Functor.isoWhiskerLeft ΔC (Functor.associator EC DerivedCategory.Q
          (derivedSystemMilnor A) ≪≫ Functor.isoWhiskerLeft EC (derivedSystemMilnorFactors A))

end RightRepresentative

section MilnorModuleDetection
open CountableMilnorTower

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_delta_of_isIso_milnorEndo
    {A : Type u} [Ring A] (E : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    [IsIso (milnorEndo E)] :
    Function.Bijective (fun x : ∀ n : ℕ, E.obj (op n) ↦
      fun n ↦ x n - (E.map (homOfLE (Nat.le_succ n)).op) (x (n + 1))) := by
  let e := ModuleCat.piIsoPi (fun n : ℕ ↦ E.obj (op n))
  let d := e.inv ≫ milnorEndo E ≫ e.hom
  have hd : Function.Bijective d := ConcreteCategory.bijective_of_isIso d
  have hπ (n : ℕ) : d ≫ ModuleCat.ofHom (LinearMap.proj n) =
      ModuleCat.ofHom (LinearMap.proj n) -
        ModuleCat.ofHom (LinearMap.proj (n+1)) ≫ E.map (homOfLE (Nat.le_succ n)).op := by
    dsimp only [d, e]
    rw [Category.assoc, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    dsimp only [milnorEndo]
    rw [Pi.lift_comp_π, Preadditive.comp_sub, ← Category.assoc]
    simp only [ModuleCat.piIsoPi_inv_kernel_ι]
  have hdFun : (fun x : ∀ n : ℕ, E.obj (op n) ↦
      fun n ↦ x n - (E.map (homOfLE (Nat.le_succ n)).op) (x (n+1))) = d := by
    funext x n
    exact (congrArg (fun k ↦ k x) (hπ n)).symm
  rw [hdFun]
  exact hd

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_milnorEndo_of_isZero_singleMilnor_at
    {ring : Type u} [Ring ring] (system : ℕᵒᵖ ⥤ ModuleCat.{u} ring) (degree : ℤ)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} ring))]
    (vanishing : IsZero (DerivedCategory.Q.obj
      (countableMilnorFunctor.obj
        (system ⋙ HomologicalComplex.single (ModuleCat.{u} ring) (.up ℤ) degree)))) :
    IsIso (milnorEndo system) := by
  let embedding := DerivedCategory.singleFunctor (ModuleCat.{u} ring) degree
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} ring) :=
    moduleCat_hasExactLimitsOfShape_discrete.{u} ring ℕ
  let := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{u} ring) (I := ℕ)
  let : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (ModuleCat.{u} ring) degree) := by
    show PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.single (ModuleCat.{u} ring) (.up ℤ) degree)
    infer_instance
  let : PreservesLimitsOfShape (Discrete ℕ) embedding :=
    preservesLimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} ring) degree).symm
  let tower := system ⋙ HomologicalComplex.single (ModuleCat.{u} ring) (.up ℤ) degree
  obtain ⟨boundary, distinguished⟩ := (map_quasiIso_and_milnor_triangle (A := ring)).2 tower
  have derivedLimit : IsDerivedLimit (system ⋙ embedding)
      (DerivedCategory.Q.obj (countableMilnorFunctor.obj tower)) :=
    isDerivedLimit_of_towerIso
      (Functor.associator system _ _ ≪≫ Functor.isoWhiskerLeft system
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} ring) degree).symm)
      ⟨Pi.lift (fun stage ↦ DerivedCategory.Q.map ((projection stage).app tower)),
        boundary, distinguished⟩
  obtain ⟨projectionMap, connectingMap, triangle⟩ := derivedLimit
  have : IsIso (milnorEndo (system ⋙ embedding)) :=
    (isZero_milnor_iff_isIso_milnorEndo triangle).mp vanishing
  exact isIso_milnorEndo_of_isIso_map embedding system

end MilnorModuleDetection

section FinsuppDetection
open CountableMilnorTower
universe wF

private def finsuppFunctor (R : Type u) [Ring R] (ι : Type v) :
    ModuleCat.{wF} R ⥤ ModuleCat.{max v wF} R where
  obj M := ModuleCat.of R (ι →₀ M)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
  map_id M := by ext x i; rfl
  map_comp f g := by ext x i; rfl

private theorem finsuppFunctor_map_apply (R : Type u) [Ring R] (ι : Type v)
    {M N : ModuleCat.{wF} R} (f : M ⟶ N) (x : ι →₀ M) (i : ι) :
    (show ι →₀ N from (finsuppFunctor R ι).map f x) i = f (x i) := rfl

/-- A tower is pro-zero when the Milnor endomorphisms of it and of its finitely supported
sequences are isomorphisms. -/
private theorem proZero_of_isIso_milnorEndo_finsupp
    {A : Type u} [Ring A] (E : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [IsIso (milnorEndo E)] [IsIso (milnorEndo (E ⋙ finsuppFunctor A ℕ))] :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), E.map (homOfLE h).op = 0 := by
  have hinj := (bijective_delta_of_isIso_milnorEndo E).injective
  have hsurj := (bijective_delta_of_isIso_milnorEndo (E ⋙ finsuppFunctor A ℕ)).surjective
  apply proZero_of_delta_injective_of_finsupp_delta_surjective E
  · intro x hx n
    have hzero : x = 0 := hinj (by
      funext k
      show x k - (E.map (homOfLE (Nat.le_succ k)).op) (x (k+1)) = 0 - _
      have hk := hx k
      change x k = (E.map (homOfLE (Nat.le_succ k)).op).hom (x (k+1)) at hk
      simpa only [Pi.zero_apply, map_zero, sub_zero] using sub_eq_zero.mpr hk)
    exact congrFun hzero n
  · intro y
    obtain ⟨z, hz⟩ := hsurj y
    refine ⟨z, fun n i ↦ ?_⟩
    exact congrArg (fun w : ∀ n : ℕ, ℕ →₀ E.obj (op n) ↦ w n i) hz

set_option backward.isDefEq.respectTransparency false in
private theorem proZero_of_isZero_singleMilnor_and_finsupp
    {A : Type u} [Ring A] (E : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
      (E ⋙ HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0))))
    (hfree : IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
      ((E ⋙ finsuppFunctor A ℕ) ⋙ HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0)))) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), E.map (homOfLE h).op = 0 := by
  have := isIso_milnorEndo_of_isZero_singleMilnor_at E 0 hE
  have := isIso_milnorEndo_of_isZero_singleMilnor_at (E ⋙ finsuppFunctor A ℕ) 0 hfree
  exact proZero_of_isIso_milnorEndo_finsupp E

end FinsuppDetection

section RightModel
open CategoryTheory.MonoidalCategory CountableMilnorTower
attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- The naturality squares below unfold the total tensor complex degreewise over `ℤ`, which
-- exceeds the default heartbeat budget.
private def constantRightTensorComplexDiagramIso (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleSystems A) ℤ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj
      (((ModuleSystemKFlatComparison.totalTensorSystem.{u,u} ((Functor.const ℕᵒᵖ).obj
        (CommRingCat.of A))).obj M).obj
        (((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj M ⋙ TrightCochain P := by
  let Z := ((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ)).obj P
  let S := systemTensor A
  let D := (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj M
  let c := ModuleSystemRlimTensor.constantComplexEvaluationIso A P
  refine NatIso.ofComponents (fun n ↦ S.totalTensorEvaluationIso M Z n.unop ≪≫
    tensorIso (Iso.refl (D.obj n)) (c.app n)) ?_
  intro n m f
  change _ ≫ ((S.totalTensorEvaluationIso M Z m.unop).hom ≫
      (𝟙 (D.obj m) ⊗ₘ (c.app m).hom)) =
    ((S.totalTensorEvaluationIso M Z n.unop).hom ≫
      (𝟙 (D.obj n) ⊗ₘ (c.app n).hom)) ≫ (D.map f ⊗ₘ 𝟙 P)
  rw [← Category.assoc, ModuleSystemRlimTensor.totalTensorEvaluation_naturality,
    Category.assoc, Category.assoc]
  congr 1
  change (D.map f ⊗ₘ ((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj Z).map f) ≫
    (𝟙 (D.obj m) ⊗ₘ (c.app m).hom) =
    (𝟙 (D.obj n) ⊗ₘ (c.app n).hom) ≫ (D.map f ⊗ₘ 𝟙 P)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have hc := c.hom.naturality f
  dsimp only [Functor.const_obj_map] at hc
  simp only [Category.comp_id, Category.id_comp] at hc ⊢
  change D.map f ⊗ₘ (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj Z).map f ≫ c.hom.app
    m) =
    D.map f ⊗ₘ (c.hom.app n ≫ 𝟙 P)
  rw [hc]

private theorem constantComplexEvaluationIso_naturality (A : Type u) [Ring A]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (g : P ⟶ Q) (n : ℕᵒᵖ) :
    ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map
      (((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ)).map g)).app n ≫
        (ModuleSystemRlimTensor.constantComplexEvaluationIso A Q).hom.app n =
      (ModuleSystemRlimTensor.constantComplexEvaluationIso A P).hom.app n ≫ g := by
  ext i x
  rfl

set_option backward.isDefEq.respectTransparency false in
-- The naturality squares below unfold the total tensor complex degreewise over `ℤ`, which
-- exceeds the default heartbeat budget.
private theorem constantRightTensorComplexDiagramIso_naturality (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleSystems A) ℤ)
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (g : P ⟶ Q) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).map
      (((ModuleSystemKFlatComparison.totalTensorSystem.{u,u} ((Functor.const ℕᵒᵖ).obj
        (CommRingCat.of A))).obj M).map
        (((ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ)).map g)) ≫
      (constantRightTensorComplexDiagramIso A M Q).hom =
    (constantRightTensorComplexDiagramIso A M P).hom ≫
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj M ⋙
        curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip.map g := by
  apply NatTrans.ext
  funext n
  let V := (PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
    n).mapHomologicalComplex (.up ℤ)
  let Δ := (ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ)
  let S := systemTensor A
  let B := (ModuleSystemKFlatComparison.totalTensorSystem.{u,u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))).obj M
  show V.map (B.map (Δ.map g)) ≫ ((S.totalTensorEvaluationIso M (Δ.obj Q) n.unop).hom ≫
      (𝟙 (V.obj M) ⊗ₘ (ModuleSystemRlimTensor.constantComplexEvaluationIso A Q).hom.app n)) =
    ((S.totalTensorEvaluationIso M (Δ.obj P) n.unop).hom ≫
      (𝟙 (V.obj M) ⊗ₘ (ModuleSystemRlimTensor.constantComplexEvaluationIso A P).hom.app n)) ≫
        (𝟙 (V.obj M) ⊗ₘ g)
  rw [← Category.assoc, totalTensorEvaluationIso_naturality_right]
  simp only [Category.assoc]
  congr 1
  show (𝟙 _ ⊗ₘ V.map (Δ.map g)) ≫ (𝟙 _ ⊗ₘ _) = (𝟙 _ ⊗ₘ _) ≫ (𝟙 _ ⊗ₘ g)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  have h := constantComplexEvaluationIso_naturality A g n
  change V.map (Δ.map g) ≫ _ = _ at h
  rw [h]

end RightModel

section RightAssembly
open scoped ExteriorAlgebra
open CategoryTheory.MonoidalCategory CountableMilnorTower
attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private def constantRightTensorComplexDiagramNatIso (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleSystems A) ℤ) :
    (ModuleSystemRlimTensor.constantSystem A).mapHomologicalComplex (.up ℤ) ⋙
      (ModuleSystemKFlatComparison.totalTensorSystem.{u,u} ((Functor.const ℕᵒᵖ).obj (CommRingCat.of
        A))).obj M ⋙
        ModuleSystemRlimTensor.complexEvaluationDiagram A ≅
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj M ⋙
        curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip :=
  NatIso.ofComponents (constantRightTensorComplexDiagramIso A M) (fun g ↦
    constantRightTensorComplexDiagramIso_naturality A M g)

set_option backward.isDefEq.respectTransparency false in
private def strictTensorLimitRightRepresentativeNatIso (A : Type u) [CommRing A]
    (E : Tower.{u, u} (A := A)) (hE : ∀ n : ℕ, (E.obj (op n)).KFlat) :
    DerivedCategory.Q ⋙ strictTensorLimit A E ≅
      (E ⋙ curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip ⋙
        countableMilnorFunctor ⋙ DerivedCategory.Q := by
  let M := ModuleSystemRlimTensor.complexSystemOfDiagram A E
  have hM (n : ℕ) : CochainComplex.KFlat
      (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj M).obj (op n)) :=
    CochainComplex.KFlat.of_iso ((complexSystemEvaluationIso A E).app (op n)).symm (hE n)
  let e := constantRightTensorComplexDiagramNatIso A M ≪≫
    (flipFunctor _ _ _).mapIso
      (Functor.isoWhiskerRight (complexSystemEvaluationIso A E)
        (curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)))
  exact tensorSystemLimitRightRepresentativeNatIso A M hM ≪≫
    Functor.isoWhiskerRight e (countableMilnorFunctor ⋙ DerivedCategory.Q)

private theorem koszulComplexTower_kFlat (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (n : ℕ) : ((koszulComplexTower f).obj (op n)).KFlat := by
  let C := Koszul.seqComplex (fun i ↦ f i ^ (n + 1))
  let (j : ℕ) : Projective (C.X j) := by
    show Projective (ModuleCat.of A (⋀[A]^j (Fin r → A)))
    exact ModuleCat.projective_of_free ((Pi.basisFun A (Fin r)).exteriorPower j)
  let (j : ℤ) : Module.Flat A ((C.extend ComplexShape.embeddingDownNat).X j) := by
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat (C.extend ComplexShape.embeddingDownNat) 0

end RightAssembly

section LiftTensor
open CategoryTheory.MonoidalCategory
local instance (A : Type u) [CommRing A] :
    RingHomInvPair (ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toRingHom
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (ULift.ringEquiv : ULift.{u} A ≃+* A)
local instance (A : Type u) [CommRing A] :
    RingHomInvPair (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom
      (ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (ULift.ringEquiv : ULift.{u} A ≃+* A)

set_option backward.isDefEq.respectTransparency false in
private def moduleUniverseLiftEquiv {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    M ≃ₛₗ[(ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toRingHom]
      (AdicKoszul.moduleUniverseLift.{u,u} A).obj M where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private def moduleUniverseLiftTensorIso {A : Type u} [CommRing A]
    (M N : ModuleCat.{u} A) :
    (AdicKoszul.moduleUniverseLift.{u,u} A).obj (M ⊗ N) ≅
      (AdicKoszul.moduleUniverseLift.{u,u} A).obj M ⊗
        (AdicKoszul.moduleUniverseLift.{u,u} A).obj N :=
  ((moduleUniverseLiftEquiv (M ⊗ N)).symm.trans
    (TensorProduct.congr (moduleUniverseLiftEquiv M) (moduleUniverseLiftEquiv N))).toModuleIso

private theorem moduleUniverseLiftTensorIso_tmul {A : Type u} [CommRing A]
    (M N : ModuleCat.{u} A) (m : M) (n : N) :
    (moduleUniverseLiftTensorIso M N).hom (ULift.up (m ⊗ₜ[A] n)) =
      (ULift.up m ⊗ₜ[ULift.{u} A] ULift.up n) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem moduleUniverseLiftTensorIso_naturality {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat.{u} A} (f : M ⟶ M') (g : N ⟶ N') :
    (AdicKoszul.moduleUniverseLift.{u,u} A).map (f ⊗ₘ g) ≫
        (moduleUniverseLiftTensorIso M' N').hom =
      (moduleUniverseLiftTensorIso M N).hom ≫
        ((AdicKoszul.moduleUniverseLift.{u,u} A).map f ⊗ₘ
          (AdicKoszul.moduleUniverseLift.{u,u} A).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  induction x using TensorProduct.induction_on with
  | zero =>
    show ((AdicKoszul.moduleUniverseLift.{u,u} A).map (f ⊗ₘ g) ≫
      (moduleUniverseLiftTensorIso M' N').hom).hom 0 =
      ((moduleUniverseLiftTensorIso M N).hom ≫
        ((AdicKoszul.moduleUniverseLift.{u,u} A).map f ⊗ₘ
          (AdicKoszul.moduleUniverseLift.{u,u} A).map g)).hom 0
    simp only [map_zero]
  | tmul m n => rfl
  | add x y hx hy =>
    show ((AdicKoszul.moduleUniverseLift.{u,u} A).map (f ⊗ₘ g) ≫
        (moduleUniverseLiftTensorIso M' N').hom).hom (ULift.up x + ULift.up y) =
      ((moduleUniverseLiftTensorIso M N).hom ≫
        ((AdicKoszul.moduleUniverseLift.{u,u} A).map f ⊗ₘ
          (AdicKoszul.moduleUniverseLift.{u,u} A).map g)).hom (ULift.up x + ULift.up y)
    simp only [map_add, hx, hy]

end LiftTensor

section LiftComplex
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory
private abbrev tensorBicomplex {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) :=
  (((curriedTensor (ModuleCat.{u} A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj M).obj N

private def moduleUniverseLiftTensorBicomplexIso {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomologicalComplex₂.TotalMap.mapBicomplex (AdicKoszul.moduleUniverseLift.{u,u} A)
      (tensorBicomplex M N) ≅
    tensorBicomplex
      (((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj M)
      (((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => moduleUniverseLiftTensorIso (M.X p) (N.X q))
      (by
        intro q q' h
        have hn := moduleUniverseLiftTensorIso_naturality (𝟙 (M.X p)) (N.d q q')
        have hi := (AdicKoszul.moduleUniverseLift.{u,u} A).map_id (M.X p)
        rw [hi, id_tensorHom, id_tensorHom] at hn
        exact hn.symm))
    (by
      intro p p' h
      apply HomologicalComplex.hom_ext
      intro q
      have hn := moduleUniverseLiftTensorIso_naturality (M.d p p') (𝟙 (N.X q))
      have hi := (AdicKoszul.moduleUniverseLift.{u,u} A).map_id (N.X q)
      rw [hi, tensorHom_id, tensorHom_id] at hn
      exact hn.symm)

private def moduleUliftFunctorIso (A : Type u) [Ring A] :
    ModuleCat.uliftFunctor.{u,u} A ≅ 𝟭 (ModuleCat.{u} A) :=
  NatIso.ofComponents (fun M => ULift.moduleEquiv.toModuleIso)
    (by intro M N f; ext x; rfl)

private def complexUniverseLiftTensorIso {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj
      (M ⊗ N) ≅
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj M ⊗
      ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj N :=
  by
  letI : (ModuleCat.uliftFunctor.{u,u} A).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleUliftFunctorIso A).symm
  letI : (AdicKoszul.moduleUniverseLift.{u,u} A).IsEquivalence := inferInstance
  letI (n : ℤ) : PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n}))
      (AdicKoszul.moduleUniverseLift.{u,u} A) := inferInstance
  exact (HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ)
      (AdicKoszul.moduleUniverseLift.{u,u} A)
    (tensorBicomplex M N)).symm ≪≫
      HomologicalComplex₂.total.mapIso (moduleUniverseLiftTensorBicomplexIso M N) (.up ℤ)
end LiftComplex

section LiftNatural
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory

private abbrev tensorBicomplexMap {A : Type u} [CommRing A]
    {M M' N N' : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ M') (g : N ⟶ N') :
    tensorBicomplex M N ⟶ tensorBicomplex M' N' :=
  ((((curriedTensor (ModuleCat.{u} A)).mapBifunctorHomologicalComplex _ _).map f).app N) ≫
    ((((curriedTensor (ModuleCat.{u} A)).mapBifunctorHomologicalComplex _ _).obj M').map g)

private theorem moduleUniverseLiftTensorBicomplexIso_naturality
    {A : Type u} [CommRing A] {M M' N N' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : M ⟶ M') (g : N ⟶ N') :
    let U := AdicKoszul.moduleUniverseLift.{u,u} A
    let UC := U.mapHomologicalComplex (.up ℤ)
    (UC.mapHomologicalComplex (.up ℤ)).map (tensorBicomplexMap f g) ≫
        (moduleUniverseLiftTensorBicomplexIso M' N').hom =
      (moduleUniverseLiftTensorBicomplexIso M N).hom ≫
        tensorBicomplexMap (UC.map f) (UC.map g) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  show (AdicKoszul.moduleUniverseLift.{u,u} A).map
      ((f.f p ▷ N.X q) ≫ (M'.X p ◁ g.f q)) ≫ _ = _ ≫
    (((AdicKoszul.moduleUniverseLift.{u,u} A).map (f.f p) ▷
        (AdicKoszul.moduleUniverseLift.{u,u} A).obj (N.X q)) ≫
      ((AdicKoszul.moduleUniverseLift.{u,u} A).obj (M'.X p) ◁
        (AdicKoszul.moduleUniverseLift.{u,u} A).map (g.f q)))
  simpa only [MonoidalCategory.tensorHom_def, moduleUniverseLiftTensorBicomplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f] using moduleUniverseLiftTensorIso_naturality (f.f
      p) (g.f q)

private theorem complexUniverseLiftTensorIso_naturality
    {A : Type u} [CommRing A] {M M' N N' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : M ⟶ M') (g : N ⟶ N') :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    UC.map (f ⊗ₘ g) ≫ (complexUniverseLiftTensorIso M' N').hom =
      (complexUniverseLiftTensorIso M N).hom ≫ (UC.map f ⊗ₘ UC.map g) := by
  dsimp only
  let U := AdicKoszul.moduleUniverseLift.{u,u} A
  let UC := U.mapHomologicalComplex (.up ℤ)
  let : (ModuleCat.uliftFunctor.{u,u} A).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleUliftFunctorIso A).symm
  let : U.IsEquivalence := inferInstance
  let (n : ℤ) : PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n})) U := inferInstance
  let e := HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ) U (tensorBicomplex M N)
  let e' := HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ) U (tensorBicomplex M' N')
  let b := moduleUniverseLiftTensorBicomplexIso M N
  let b' := moduleUniverseLiftTensorBicomplexIso M' N'
  show UC.map (f ⊗ₘ g) ≫ e'.inv ≫ (HomologicalComplex₂.total.map b'.hom (.up ℤ)) =
    (e.inv ≫ HomologicalComplex₂.total.map b.hom (.up ℤ)) ≫ (UC.map f ⊗ₘ UC.map g)
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hn := HomologicalComplex₂.TotalMap.totalMap_naturality (c₁₂ := .up ℤ) U
    (tensorBicomplex M N) (tensorBicomplexMap f g)
  change HomologicalComplex₂.total.map ((UC.mapHomologicalComplex (.up ℤ)).map
      (tensorBicomplexMap f g)) (.up ℤ) ≫ e'.hom =
    e.hom ≫ UC.map (f ⊗ₘ g) at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  show HomologicalComplex₂.total.map _ (.up ℤ) ≫
      HomologicalComplex₂.total.map b'.hom (.up ℤ) =
    HomologicalComplex₂.total.map b.hom (.up ℤ) ≫
      HomologicalComplex₂.total.map (tensorBicomplexMap (UC.map f) (UC.map g)) (.up ℤ)
  rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp,
    moduleUniverseLiftTensorBicomplexIso_naturality]

end LiftNatural

section LiftKoszul
set_option backward.isDefEq.respectTransparency false

private lemma isIso_mappingCone_map
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} [IsIso a] [IsIso b]
    (comm : φ₁ ≫ b = a ≫ φ₂) : IsIso (CochainComplex.mappingCone.map φ₁ φ₂ a b comm) := by
  refine ⟨CochainComplex.mappingCone.map φ₂ φ₁ (inv a) (inv b) (by
    rw [IsIso.comp_inv_eq, Category.assoc, comm, IsIso.inv_hom_id_assoc]), ?_, ?_⟩ <;>
      rw [← CochainComplex.mappingCone.map_comp] <;> simp [CochainComplex.mappingCone.map_id]

private def moduleUniverseLiftRingIso (A : Type u) [CommRing A] :
    (AdicKoszul.moduleUniverseLift.{u,u} A).obj (ModuleCat.of A A) ≅
      ModuleCat.of (ULift.{u} A) (ULift.{u} A) := Iso.refl _

private def complexUniverseLiftRingIso (A : Type u) [CommRing A] :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) ≅
    ((HomologicalComplex.single (ModuleCat.{u} (ULift.{u} A)) (.up ℤ) 0).obj
      (ModuleCat.of (ULift.{u} A) (ULift.{u} A))) :=
  (HomologicalComplex.singleMapHomologicalComplex (AdicKoszul.moduleUniverseLift.{u,u} A)
    (.up ℤ) 0).app (ModuleCat.of A A)

private theorem complexUniverseLiftRingIso_scalar (A : Type u) [CommRing A] (f : A) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
        (f • 𝟙 (ModuleCat.of A A))) ≫ (complexUniverseLiftRingIso A).hom =
    (complexUniverseLiftRingIso A).hom ≫
      (HomologicalComplex.single (ModuleCat.{u} (ULift.{u} A)) (.up ℤ) 0).map
        ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A))) := by
  have h := (HomologicalComplex.singleMapHomologicalComplex
    (AdicKoszul.moduleUniverseLift.{u,u} A) (.up ℤ) 0).hom.naturality
      (f • 𝟙 (ModuleCat.of A A))
  change _ ≫ _ = _ ≫
    (HomologicalComplex.single (ModuleCat.{u} (ULift.{u} A)) (.up ℤ) 0).map
      ((AdicKoszul.moduleUniverseLift.{u,u} A).map (f • 𝟙 (ModuleCat.of A A))) at h
  have he : (AdicKoszul.moduleUniverseLift.{u,u} A).map (f • 𝟙 (ModuleCat.of A A)) =
      ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A))) := by
    ext
    rfl
  rwa [he] at h

private def complexUniverseLiftKoszulConeIso (A : Type u) [CommRing A] (f : A) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
        (f • 𝟙 (ModuleCat.of A A)))) ≅
    CochainComplex.mappingCone
      ((HomologicalComplex.single (ModuleCat.{u} (ULift.{u} A)) (.up ℤ) 0).map
        ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A)))) := by
  let U := AdicKoszul.moduleUniverseLift.{u,u} A
  let e := complexUniverseLiftRingIso A
  let φ := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
    (f • 𝟙 (ModuleCat.of A A))
  let ψ := (HomologicalComplex.single (ModuleCat.{u} (ULift.{u} A)) (.up ℤ) 0).map
    ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A)))
  have h := complexUniverseLiftRingIso_scalar A f
  letI := isIso_mappingCone_map ((U.mapHomologicalComplex (.up ℤ)).map φ) ψ h
  exact CochainComplex.mappingCone.mapHomologicalComplexIso φ U ≪≫
    asIso (CochainComplex.mappingCone.map _ ψ e.hom e.hom h)

private def complexUniverseLiftKoszulIso (A : Type u) [CommRing A] (f : A) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj
      ((Koszul.seqComplex (fun _ : Fin 1 ↦ f)).extend ComplexShape.embeddingDownNat) ≅
    ((Koszul.seqComplex (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A))).extend
      ComplexShape.embeddingDownNat) :=
  ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).mapIso
      (koszulSingleConeIso A f) ≪≫ complexUniverseLiftKoszulConeIso A f ≪≫
        (koszulSingleConeIso (ULift.{u} A) (ULift.up f)).symm
end LiftKoszul

section ConeNatural
set_option backward.isDefEq.respectTransparency false
open CochainComplex CochainComplex.mappingCone CochainComplex.HomComplex

private theorem mappingCone_map_f
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : φ₁ ≫ b = a ≫ φ₂) (p : ℤ) :
    (mappingCone.map φ₁ φ₂ a b h).f p =
      (fst φ₁).1.v p (p + 1) rfl ≫ a.f (p + 1) ≫
        (inl φ₂).v (p + 1) p (by omega) +
      (snd φ₁).v p p (add_zero p) ≫ b.f p ≫ (inr φ₂).f p := by
  simp only [mappingCone.map, desc_f _ _ _ _ p (p + 1) rfl,
    Cochain.comp_v _ _ (zero_add (-1)) (p + 1) (p + 1) p (add_zero _) (by omega),
    Cochain.ofHom_v, HomologicalComplex.comp_f]

private theorem mappingCone_mapHomologicalComplexIso_naturality
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (H : C ⥤ D) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : φ₁ ≫ b = a ≫ φ₂) :
    let HC := H.mapHomologicalComplex (.up ℤ)
    HC.map (mappingCone.map φ₁ φ₂ a b h) ≫ (mapHomologicalComplexIso φ₂ H).hom =
      (mapHomologicalComplexIso φ₁ H).hom ≫
        mappingCone.map (HC.map φ₁) (HC.map φ₂) (HC.map a) (HC.map b)
          (by rw [← HC.map_comp, ← HC.map_comp, h]) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro p
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    mapHomologicalComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    mapHomologicalComplexXIso, mapHomologicalComplexXIso'_hom]
  simp only [mappingCone_map_f, H.map_add, H.map_comp, Preadditive.add_comp,
    Preadditive.comp_add, Category.assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
    inl_v_snd_v_assoc, inr_f_snd_v_assoc,
    zero_comp, comp_zero, add_zero, zero_add,
    Functor.mapHomologicalComplex_map_f]
  have h11 : H.map ((inl φ₂).v (p + 1) p (by omega)) ≫
      H.map ((fst φ₂).1.v p (p + 1) rfl) = 𝟙 _ := by
    rw [← H.map_comp, inl_v_fst_v, H.map_id]
  have h21 : H.map ((inr φ₂).f p) ≫
      H.map ((fst φ₂).1.v p (p + 1) rfl) = 0 := by
    rw [← H.map_comp, inr_f_fst_v, H.map_zero]
  have h12 : H.map ((inl φ₂).v (p + 1) p (by omega)) ≫
      H.map ((snd φ₂).v p p (add_zero p)) = 0 := by
    rw [← H.map_comp, inl_v_snd_v, H.map_zero]
  have h22 : H.map ((inr φ₂).f p) ≫
      H.map ((snd φ₂).v p p (add_zero p)) = 𝟙 _ := by
    rw [← H.map_comp, inr_f_snd_v, H.map_id]
  simp only [reassoc_of% h11, reassoc_of% h21, reassoc_of% h12, reassoc_of% h22,
    zero_comp, comp_zero, add_zero, zero_add]
end ConeNatural

section LiftKoszulNatural
set_option backward.isDefEq.respectTransparency false

private theorem complexUniverseLiftKoszulConeIso_naturality (A : Type u) [CommRing A]
    (f g a b : A)
    (h : (f • 𝟙 (ModuleCat.of A A)) ≫ (b • 𝟙 _) =
      (a • 𝟙 _) ≫ (g • 𝟙 (ModuleCat.of A A)))
    (h' : ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A))) ≫
        ((ULift.up b : ULift.{u} A) • 𝟙 _) =
      ((ULift.up a : ULift.{u} A) • 𝟙 _) ≫
        ((ULift.up g : ULift.{u} A) • 𝟙 _)) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).map
      (singleConeMap (f • 𝟙 (ModuleCat.of A A)) (g • 𝟙 _)
        (a • 𝟙 _) (b • 𝟙 _) h) ≫ (complexUniverseLiftKoszulConeIso A g).hom =
    (complexUniverseLiftKoszulConeIso A f).hom ≫
      singleConeMap
        ((ULift.up f : ULift.{u} A) • 𝟙 (ModuleCat.of (ULift.{u} A) (ULift.{u} A)))
        ((ULift.up g : ULift.{u} A) • 𝟙 _) ((ULift.up a : ULift.{u} A) • 𝟙 _)
        ((ULift.up b : ULift.{u} A) • 𝟙 _) h' := by
  dsimp only [complexUniverseLiftKoszulConeIso, Iso.trans_hom, asIso_hom, singleConeMap]
  rw [← Category.assoc, mappingCone_mapHomologicalComplexIso_naturality]
  simp only [Category.assoc]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 2
  · exact complexUniverseLiftRingIso_scalar A a
  · exact complexUniverseLiftRingIso_scalar A b

end LiftKoszulNatural

section CoefficientStage
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory

private def rightTensorUniverseLiftIso {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    TrightCochain P ⋙ (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ) ≅
      (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ) ⋙
        TrightCochain (((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).obj
          P) :=
  NatIso.ofComponents (fun K => complexUniverseLiftTensorIso K P) (by
    intro K L f
    have h := complexUniverseLiftTensorIso_naturality f (𝟙 P)
    dsimp only at h
    rw [((AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)).map_id P,
      tensorHom_id, tensorHom_id] at h
    exact h)

private def coefficientPrincipalKoszulStageIso (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    KoszulCoefficientTower.coefficientKoszulTower (fun _ : Fin 1 ↦ f) ⋙
        (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{u} A) ℤ)).obj (Opposite.op n) ≅
      TrightCochain ((koszulComplexTower (fun _ : Fin 1 ↦ f)).obj (Opposite.op n)) := by
  let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
  let P := (koszulComplexTower (fun _ : Fin 1 ↦ f)).obj (Opposite.op n)
  let P' := KoszulCoefficientTower.standardKoszulStage
    (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A)) none n
  let e : UC.obj P ≅ P' := complexUniverseLiftKoszulIso A (f ^ (n + 1))
  let e₁ := Functor.associator _ _ _ ≪≫
    KoszulCoefficientTower.coefficientKoszulComparison (fun _ : Fin 1 ↦ f) none n
  let e₂ := Functor.isoWhiskerLeft UC
    ((curriedTensor (CochainComplex (ModuleCat.{u} (ULift.{u} A)) ℤ)).flip.mapIso e.symm)
  let e₃ := (rightTensorUniverseLiftIso P).symm
  exact ((Functor.whiskeringRight _ _ _).obj UC).preimageIso (e₁ ≪≫ e₂ ≪≫ e₃)

end CoefficientStage


section LiftTransition
set_option backward.isDefEq.respectTransparency false

private theorem scalarPowerSquare (A : Type u) [CommRing A] (f : A)
    (m n : ℕ) (h : n ≤ m) :
    (f ^ (m + 1) • 𝟙 (ModuleCat.of A A)) ≫ 𝟙 _ =
      (f ^ (m - n) • 𝟙 _) ≫ (f ^ (n + 1) • 𝟙 _) :=
  pow_smul_square A f _ _ _ (by omega)

private theorem koszulPowerTransition_cone (A : Type u) [CommRing A] (f : A)
    (m n : ℕ) (h : n ≤ m) :
    HomologicalComplex.extendMap
      (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) m n h)
      ComplexShape.embeddingDownNat ≫ (koszulSingleConeIso A (f ^ (n + 1))).hom =
    (koszulSingleConeIso A (f ^ (m + 1))).hom ≫
      singleConeMap (f ^ (m + 1) • 𝟙 (ModuleCat.of A A)) (f ^ (n + 1) • 𝟙 _)
        (f ^ (m - n) • 𝟙 _) (𝟙 _) (scalarPowerSquare A f m n h) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  have hcone := singleConeMap_eq_KtransCx A f (n + c + 1) (n + 1) c (by omega)
  have hs := scalarPowerSquare A f (n + c) n (Nat.le_add_right n c)
  simp only [Nat.add_sub_cancel_left] at hs ⊢
  rw [hcone hs]
  exact koszulPowerConeIso_transition A f n c

private theorem complexUniverseLiftKoszulIso_transition (A : Type u) [CommRing A] (f : A)
    (m n : ℕ) (h : n ≤ m) :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    UC.map (HomologicalComplex.extendMap
      (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ f) m n h)
      ComplexShape.embeddingDownNat) ≫ (complexUniverseLiftKoszulIso A (f ^ (n + 1))).hom =
    (complexUniverseLiftKoszulIso A (f ^ (m + 1))).hom ≫
      HomologicalComplex.extendMap
        (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A)) m
          n h)
        ComplexShape.embeddingDownNat := by
  let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
  have upOne : (ULift.up (1 : A) : ULift.{u} A) = 1 := rfl
  have upPow (k : ℕ) : (ULift.up (f ^ k) : ULift.{u} A) = ULift.up f ^ k := rfl
  let hA := scalarPowerSquare A f m n h
  let hU := scalarPowerSquare (ULift.{u} A) (ULift.up f) m n h
  have hc := complexUniverseLiftKoszulConeIso_naturality A (f ^ (m + 1))
    (f ^ (n + 1)) (f ^ (m - n)) 1 (by simpa only [one_smul] using hA)
    (by simpa only [upOne, upPow, one_smul] using hU)
  simp only [upOne, upPow, one_smul] at hc
  have hs := koszulPowerTransition_cone A f m n h
  have ht := koszulPowerTransition_cone (ULift.{u} A) (ULift.up f) m n h
  dsimp only
  dsimp only [complexUniverseLiftKoszulIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  apply (cancel_mono (koszulSingleConeIso (ULift.{u} A)
    ((ULift.up f : ULift.{u} A) ^ (n + 1))).hom).mp
  simp only [Category.assoc]
  rw [← UC.map_comp_assoc, hs, UC.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc, ht]
  have he (k : ℕ) : (koszulSingleConeIso (ULift.{u} A) (ULift.up (f ^ k))).inv ≫
      (koszulSingleConeIso (ULift.{u} A) ((ULift.up f : ULift.{u} A) ^ k)).hom = 𝟙 _ :=
    (koszulSingleConeIso (ULift.{u} A) (ULift.up (f ^ k))).inv_hom_id
  simp only [he, reassoc_of% he, Category.comp_id]
  rfl
end LiftTransition

section CoefficientStageMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory

private theorem whiskeringRight_preimageIso_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : D ⥤ E) [U.Full] [U.Faithful] {F G : C ⥤ D}
    (e : F ⋙ U ≅ G ⋙ U) (K : C) :
    U.map ((((Functor.whiskeringRight C D E).obj U).preimageIso e).hom.app K) =
      e.hom.app K :=
  congrArg (fun η : F ⋙ U ⟶ G ⋙ U => η.app K)
    (((Functor.whiskeringRight C D E).obj U).map_preimage e.hom)

private theorem coefficientPrincipalKoszulStageIso_map (A : Type u) [CommRing A]
    (f : A) (n : ℕ) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    UC.map ((coefficientPrincipalKoszulStageIso A f n).hom.app K) =
      (KoszulCoefficientTower.coefficientKoszulComparison
          (fun _ : Fin 1 ↦ f) none n).hom.app K ≫
        (UC.obj K ◁ (complexUniverseLiftKoszulIso A (f ^ (n + 1))).inv) ≫
        (complexUniverseLiftTensorIso K
          ((koszulComplexTower (fun _ : Fin 1 ↦ f)).obj (Opposite.op n))).inv := by
  dsimp only
  dsimp only [coefficientPrincipalKoszulStageIso]
  rw [whiskeringRight_preimageIso_hom_app]
  rfl

end CoefficientStageMap


section PrincipalTensorLift
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory

private def principalTensorUniverseLiftIso (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    UC.obj (K ⊗ (koszulComplexTower (fun _ : Fin 1 ↦ f)).obj (Opposite.op n)) ≅
      UC.obj K ⊗ KoszulCoefficientTower.standardKoszulStage
        (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A)) none n :=
  complexUniverseLiftTensorIso K _ ≪≫
    (tensorLeft _).mapIso (complexUniverseLiftKoszulIso A (f ^ (n + 1)))

private theorem principalTensorUniverseLiftIso_transition (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (m n : ℕ) (h : n ≤ m) :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    let s := (koszulComplexTower (fun _ : Fin 1 ↦ f)).map (homOfLE h).op
    let t := KoszulCoefficientTower.standardKoszulTransition
      (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A)) none m n h
    UC.map (K ◁ s) ≫ (principalTensorUniverseLiftIso A f K n).hom =
      (principalTensorUniverseLiftIso A f K m).hom ≫ (UC.obj K ◁ t) := by
  dsimp only
  let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
  let s := (koszulComplexTower (fun _ : Fin 1 ↦ f)).map (homOfLE h).op
  have hn := complexUniverseLiftTensorIso_naturality (𝟙 K) s
  dsimp only at hn
  rw [UC.map_id, id_tensorHom, id_tensorHom] at hn
  have hs := complexUniverseLiftKoszulIso_transition A f m n h
  dsimp only at hs
  rw [← koszulComplexTower_map (fun _ : Fin 1 ↦ f) m n h] at hs
  dsimp only [principalTensorUniverseLiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  congr 1
  have hstd : KoszulCoefficientTower.standardKoszulTransition
      (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A)) none m n h =
        HomologicalComplex.extendMap
          (NoetherianKoszulProIso.koszulPowerTransition (fun _ : Fin 1 ↦ (ULift.up f : ULift.{u} A))
            m n h)
          ComplexShape.embeddingDownNat := rfl
  rw [hstd]
  have he := congrArg (tensorLeft (UC.obj K)).map hs
  rw [Functor.map_comp, Functor.map_comp] at he
  exact he

end PrincipalTensorLift

section CoefficientTower
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory

private theorem coefficientPrincipalKoszulStageIso_map' (A : Type u) [CommRing A]
    (f : A) (n : ℕ) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
    UC.map ((coefficientPrincipalKoszulStageIso A f n).hom.app K) =
      (KoszulCoefficientTower.coefficientKoszulComparison
        (fun _ : Fin 1 ↦ f) none n).hom.app K ≫
      (principalTensorUniverseLiftIso A f K n).inv :=
  coefficientPrincipalKoszulStageIso_map A f n K

private theorem coefficientPrincipalKoszulStageIso_transition (A : Type u) [CommRing A]
    (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (m n : ℕ) (h : n ≤ m) :
    (((KoszulCoefficientTower.coefficientKoszulTower
      (fun _ : Fin 1 ↦ f)).obj K).map (homOfLE h).op) ≫
        (coefficientPrincipalKoszulStageIso A f n).hom.app K =
      (coefficientPrincipalKoszulStageIso A f m).hom.app K ≫
        (K ◁ (koszulComplexTower (fun _ : Fin 1 ↦ f)).map (homOfLE h).op) := by
  let UC := (AdicKoszul.moduleUniverseLift.{u,u} A).mapHomologicalComplex (.up ℤ)
  apply UC.map_injective
  rw [UC.map_comp, UC.map_comp,
    coefficientPrincipalKoszulStageIso_map', coefficientPrincipalKoszulStageIso_map']
  apply (cancel_mono (principalTensorUniverseLiftIso A f K n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [principalTensorUniverseLiftIso_transition]
  simp only [Iso.inv_hom_id_assoc]
  simpa only [id_tensorHom] using
    KoszulCoefficientTower.coefficientKoszulComparison_transition
      (fun _ : Fin 1 ↦ f) m n h K

private def coefficientPrincipalKoszulRightTowerIso (A : Type u) [CommRing A] (f : A) :
    KoszulCoefficientTower.coefficientKoszulTower (fun _ : Fin 1 ↦ f) ≅
      (koszulComplexTower (fun _ : Fin 1 ↦ f) ⋙
        (curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip).flip :=
  NatIso.ofComponents (fun K => NatIso.ofComponents
    (fun n => (coefficientPrincipalKoszulStageIso A f n.unop).app K)
    (by
      intro m n h
      exact coefficientPrincipalKoszulStageIso_transition A f K m.unop n.unop
        (leOfHom h.unop)))
    (by
      intro K L g
      apply NatTrans.ext
      funext n
      exact (coefficientPrincipalKoszulStageIso A f n.unop).hom.naturality g)

private def coefficientPrincipalKoszulTowerIso (A : Type u) [CommRing A] (f : A) :
    KoszulCoefficientTower.coefficientKoszulTower (fun _ : Fin 1 ↦ f) ≅
      (koszulComplexTower (fun _ : Fin 1 ↦ f) ⋙
        curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip := by
  letI := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  exact coefficientPrincipalKoszulRightTowerIso A f ≪≫
    (flipFunctor _ _ _).mapIso (Functor.isoWhiskerLeft
      (koszulComplexTower (fun _ : Fin 1 ↦ f))
      (BraidedCategory.curriedBraidingNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).symm)

end CoefficientTower

section ReflectorAssembly
set_option backward.isDefEq.respectTransparency false
open CountableMilnorTower
attribute [local instance] HasDerivedCategory.standard

private def principalCompletionIso (A : Type u) [CommRing A] (f : A) :
    KoszulCompletion.completionFunctor (fun _ : Fin 1 ↦ f) ≅
      tensorKoszulLimit A (fun _ : Fin 1 ↦ f) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let e₁ : Q ⋙ KoszulCompletion.completionFunctor (fun _ : Fin 1 ↦ f) ≅
      KoszulCompletion.coefficientCompletionComplex (fun _ : Fin 1 ↦ f) ⋙ Q :=
    Localization.fac _ (KoszulCompletion.coefficientCompletion_isInvertedBy
      (fun _ : Fin 1 ↦ f)) Q
  let e₂ := Functor.isoWhiskerRight (coefficientPrincipalKoszulTowerIso A f)
    (countableMilnorFunctor ⋙ Q)
  let e₃ := strictTensorLimitRightRepresentativeNatIso A
    (koszulComplexTower (fun _ : Fin 1 ↦ f)) (koszulComplexTower_kFlat A _)
  exact (Localization.fullyFaithfulWhiskeringLeft Q W
    (DerivedCategory (ModuleCat.{u} A))).preimageIso
      (e₁ ≪≫ Functor.associator _ _ _ ≪≫ e₂ ≪≫ e₃.symm)
end ReflectorAssembly


section LocalConverse

open CountableMilnorTower CategoryTheory.MonoidalCategory

private theorem tensorMilnorMap_isIso_of_comparison_isIso
    (ring : Type u) [CommRing ring]
    {source target : Tower.{u, u} (A := ring)} (comparison : source ⟶ target)
    (coefficient : CochainComplex (ModuleCat.{u} ring) ℤ)
    (flat : coefficient.KFlat)
    [IsIso ((strictTensorLimitMap ring comparison).app (DerivedCategory.Q.obj coefficient))] :
    IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight comparison (TleftCochain coefficient)))) := by
  have square := strictTensorLimitRepresentativeIso_naturality ring comparison coefficient flat
  have equation : DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight comparison (TleftCochain coefficient))) =
      (strictTensorLimitRepresentativeIso ring source coefficient flat).inv ≫
        (strictTensorLimitMap ring comparison).app (DerivedCategory.Q.obj coefficient) ≫
          (strictTensorLimitRepresentativeIso ring target coefficient flat).hom := by
    rw [square, Iso.inv_hom_id_assoc]
  rw [equation]
  infer_instance

private theorem milnorMap_isIso_of_tensorUnitComparison_isIso
    (ring : Type u) [CommRing ring]
    {source target : Tower.{u, u} (A := ring)} (comparison : source ⟶ target)
    [IsIso ((strictTensorLimitMap ring comparison).app
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} ring) ℤ))))] :
    IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map comparison)) := by
  let coefficient := 𝟙_ (CochainComplex (ModuleCat.{u} ring) ℤ)
  have flat : coefficient.KFlat := by
    intro complex acyclic
    exact acyclic.of_iso (ρ_ complex).symm
  have := tensorMilnorMap_isIso_of_comparison_isIso ring comparison coefficient flat
  let sourceIso : source ⋙ TleftCochain coefficient ≅ source :=
    NatIso.ofComponents (fun stage ↦ λ_ (source.obj stage)) (by
      intro first second transition
      exact leftUnitor_naturality (source.map transition))
  let targetIso : target ⋙ TleftCochain coefficient ≅ target :=
    NatIso.ofComponents (fun stage ↦ λ_ (target.obj stage)) (by
      intro first second transition
      exact leftUnitor_naturality (target.map transition))
  let milnor := countableMilnorFunctor ⋙ DerivedCategory.Q (C := ModuleCat.{u} ring)
  have square : Functor.whiskerRight comparison (TleftCochain coefficient) ≫ targetIso.hom =
      sourceIso.hom ≫ comparison := by
    apply NatTrans.ext
    funext stage
    exact leftUnitor_naturality (comparison.app stage)
  have equation : milnor.map comparison =
      (milnor.mapIso sourceIso).inv ≫
        milnor.map (Functor.whiskerRight comparison (TleftCochain coefficient)) ≫
          (milnor.mapIso targetIso).hom := by
    simp only [Functor.mapIso_inv, Functor.mapIso_hom, ← milnor.map_comp]
    rw [square, Iso.inv_hom_id_assoc]
  show IsIso (milnor.map comparison)
  rw [equation]
  show IsIso ((milnor.mapIso sourceIso).inv ≫
    DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight comparison (TleftCochain coefficient))) ≫
        (milnor.mapIso targetIso).hom)
  infer_instance

private theorem kernelι_quasiIsoAt_of_exactAt
    {category : Type u} [Category.{v} category] [Abelian category]
    {source target : CochainComplex category ℤ} (comparison : source ⟶ target)
    [Epi comparison] (degree : ℤ)
    (previousExact : target.ExactAt (degree - 1))
    (currentExact : target.ExactAt degree) :
    QuasiIsoAt (kernel.ι comparison) degree := by
  let sequence := ShortComplex.mk (kernel.ι comparison) comparison (kernel.condition comparison)
  have shortExact : sequence.ShortExact := { exact := ShortComplex.exact_kernel comparison }
  have : Mono (HomologicalComplex.homologyMap (kernel.ι comparison) degree) :=
    (shortExact.homology_exact₁ (degree - 1) degree
      (by change degree - 1 + 1 = degree; omega)).mono_g
      (previousExact.isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap (kernel.ι comparison) degree) :=
    (shortExact.homology_exact₂ degree).epi_f (currentExact.isZero_homology.eq_of_tgt _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_of_mono_of_epi _

private theorem kernelLift_quasiIso_of_singleFiber
    {category : Type u} [Category.{v} category] [Abelian category]
    {source : CochainComplex category ℤ} (torsion quotient : category)
    (comparison : source ⟶ (HomologicalComplex.single category (.up ℤ) 0).obj quotient)
    [Epi comparison]
    (inclusion : (HomologicalComplex.single category (.up ℤ) (-1)).obj torsion ⟶ source)
    (compositeZero : inclusion ≫ comparison = 0)
    (fiberHomology : QuasiIsoAt inclusion (-1))
    (otherHomology : ∀ degree : ℤ, degree ≠ -1 → QuasiIsoAt comparison degree) :
    QuasiIso (kernel.lift comparison inclusion compositeZero) := by
  let sequence := ShortComplex.mk (kernel.ι comparison) comparison (kernel.condition comparison)
  have shortExact : sequence.ShortExact := { exact := ShortComplex.exact_kernel comparison }
  rw [quasiIso_iff]
  intro degree
  by_cases exceptional : degree = -1
  · subst degree
    have := kernelι_quasiIsoAt_of_exactAt comparison (-1)
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by decide))
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by decide))
    have := fiberHomology
    have : QuasiIsoAt
        (kernel.lift comparison inclusion compositeZero ≫ kernel.ι comparison) (-1) := by
      simpa only [kernel.lift_ι] using fiberHomology
    exact quasiIsoAt_of_comp_right (kernel.lift comparison inclusion compositeZero)
      (kernel.ι comparison) (-1)
  · apply (quasiIsoAt_iff_exactAt _ degree
      (HomologicalComplex.exactAt_single_obj _ _ _ _ exceptional)).mpr
    refine shortExact.exactAt_X₁ degree ?_ ?_
    · have := otherHomology degree exceptional
      infer_instance
    · intro previous adjacent
      by_cases previousExceptional : previous = -1
      · subst previous
        exact (HomologicalComplex.exactAt_single_obj (.up ℤ) 0 quotient (-1)
          (by decide)).isZero_homology.epi _
      · have := otherHomology previous previousExceptional
        infer_instance

end LocalConverse

section SingleFiberExactness
set_option backward.isDefEq.respectTransparency false
private theorem quasiIsoAt_mkHomFromSingle_of_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (j : ℤ) (X : C) (ι : X ⟶ K.X j)
    (hι : ∀ k, (ComplexShape.up ℤ).Rel j k → ι ≫ K.d j k = 0)
    (hprev : K.d (j - 1) j = 0)
    (hex : (ShortComplex.mk ι (K.d j (j + 1)) (hι _ rfl)).Exact)
    [Mono ι] : QuasiIsoAt (HomologicalComplex.mkHomFromSingle ι hι) j := by
  rw [quasiIsoAt_iff' _ (j-1) j (j+1) (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros _
    (by simp) (by simp) hprev]
  have he : (ShortComplex.mk
      ((HomologicalComplex.singleObjXSelf (.up ℤ) j X).hom ≫ ι)
      (K.d j (j+1)) (by simp [hι])).Exact := by
    apply ShortComplex.exact_of_iso _ hex
    exact ShortComplex.isoMk
      (HomologicalComplex.singleObjXSelf (.up ℤ) j X).symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)
  have hm : Mono ((HomologicalComplex.singleObjXSelf (.up ℤ) j X).hom ≫ ι) :=
    inferInstance
  simpa only [HomologicalComplex.shortComplexFunctor',
    HomologicalComplex.mkHomFromSingle_f] using And.intro he hm

private theorem quasiIsoAt_toSingle_of_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (j : ℤ) (X : C)
    (π : K ⟶ (HomologicalComplex.single C (.up ℤ) j).obj X)
    (hnext : K.d j (j + 1) = 0)
    (hex : (ShortComplex.mk (K.d (j - 1) j) (π.f j)
      (by rw [← π.comm, HomologicalComplex.single_obj_d, comp_zero])).Exact)
    [Epi (π.f j)] : QuasiIsoAt π j := by
  rw [quasiIsoAt_iff' _ (j-1) j (j+1) (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros' _ hnext (by simp) (by simp)]
  exact ⟨hex, (inferInstance : Epi (π.f j))⟩

end SingleFiberExactness

section PrincipalFiber
set_option backward.isDefEq.respectTransparency false
open CountableMilnorTower

private theorem principalCone_isZero_X (A : Type u) [CommRing A] (f : A) (n : ℕ)
    (j : ℤ) (hj : j ≠ -1) (hj' : j ≠ 0) : IsZero ((ProTorsion.Kcx A f n).X j) :=
  (HomologicalComplex.isZero_double_X (f ^ n • 𝟙 (ModuleCat.of A A))
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) j hj hj').of_iso
      (HomologicalComplex.Hom.isoApp (singleConeDoubleIso
        (f ^ n • 𝟙 (ModuleCat.of A A))) j).symm

private theorem principalAugmentation_f_zero (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (ProTorsion.alphaCx A f n).f 0 =
      (singleConeZeroIso (f ^ n • 𝟙 (ModuleCat.of A A))).inv ≫
        ProTorsion.quotMap A f n ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ProTorsion.Qmod A f n)).inv := by
  apply (cancel_epi (singleConeZeroIso (f ^ n • 𝟙 (ModuleCat.of A A))).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  dsimp only [singleConeZeroIso]
  rw [Category.assoc]
  show (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv ≫
    (CochainComplex.mappingCone.inr ((ProTorsion.single0 A).map
      (ProTorsion.smulMap A f n))).f 0 ≫ (ProTorsion.alphaCx A f n).f 0 = _
  rw [ProTorsion.alphaCx, CochainComplex.mappingCone.inr_f_desc_f]
  simp only [ProTorsion.single0, HomologicalComplex.single_map_f_self,
    Iso.inv_hom_id_assoc]

private theorem principalAugmentation_epi (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    Epi (ProTorsion.alphaCx A f n) := by
  have he (j : ℤ) : Epi ((ProTorsion.alphaCx A f n).f j) := by
    by_cases hj : j = 0
    · subst j
      rw [principalAugmentation_f_zero]
      have : Epi (ProTorsion.quotMap A f n) :=
        (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ProTorsion.Qmod A f n) j hj).epi _
  exact HomologicalComplex.epi_of_epi_f _ he

private def principalTorsionInclusion (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) (-1)).obj
      (ModuleCat.of A (Submodule.torsionBy A A (f ^ n))) ⟶ ProTorsion.Kcx A f n :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (Submodule.torsionBy A A (f ^ n)).subtype ≫
      (singleConeNegOneIso (f ^ n • 𝟙 (ModuleCat.of A A))).hom)
    (by
      intro j hj
      obtain rfl : j = 0 := by change (-1 : ℤ) + 1 = j at hj; omega
      change (ModuleCat.ofHom (Submodule.torsionBy A A (f ^ n)).subtype ≫
        (singleConeNegOneIso (f ^ n • 𝟙 (ModuleCat.of A A))).hom) ≫
          (CochainComplex.mappingCone (singleMap (f ^ n • 𝟙 (ModuleCat.of A A)))).d (-1) 0 = 0
      rw [Category.assoc, singleCone_d, ← Category.assoc]
      have hz : ModuleCat.ofHom (Submodule.torsionBy A A (f ^ n)).subtype ≫
          (f ^ n • 𝟙 (ModuleCat.of A A)) = 0 := by
        ext x
        exact x.property
      rw [hz, zero_comp])

private theorem principalTorsionInclusion_comp (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    principalTorsionInclusion A f n ≫ ProTorsion.alphaCx A f n = 0 := by
  apply HomologicalComplex.from_single_hom_ext (j := (-1 : ℤ))
  exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
    (ProTorsion.Qmod A f n) (-1) (by decide)).eq_of_tgt _ _

private theorem torsionSubtype_smul_exact (A : Type u) [CommRing A] (f : A) :
    (ShortComplex.mk (ModuleCat.ofHom (Submodule.torsionBy A A f).subtype)
      (f • 𝟙 (ModuleCat.of A A)) (by ext x; exact x.property)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem principalTorsionInclusion_quasiIsoAt (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : QuasiIsoAt (principalTorsionInclusion A f n) (-1) := by
  have : Mono (ModuleCat.ofHom (Submodule.torsionBy A A (f ^ n)).subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  apply quasiIsoAt_mkHomFromSingle_of_exact
  · exact (principalCone_isZero_X A f n (-1 - 1) (by decide) (by decide)).eq_of_src _ _
  · apply ShortComplex.exact_of_iso _ (torsionSubtype_smul_exact A (f ^ n))
    exact ShortComplex.isoMk (Iso.refl _)
      (singleConeNegOneIso (f ^ n • 𝟙 (ModuleCat.of A A)))
      (singleConeZeroIso (f ^ n • 𝟙 (ModuleCat.of A A)))
      (by simp) (singleCone_d _)

private theorem smul_quotMap_exact (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (ShortComplex.mk (f ^ n • 𝟙 (ModuleCat.of A A)) (ProTorsion.quotMap A f n)
      (ProTorsion.smul_quot_zero A f n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : x ∈ Ideal.span {f ^ n} := (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx'
  exact ⟨y, hy.symm⟩

private theorem principalAugmentation_quasiIsoAt_zero (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : QuasiIsoAt (ProTorsion.alphaCx A f n) 0 := by
  have := principalAugmentation_epi A f n
  apply quasiIsoAt_toSingle_of_exact
  · exact (principalCone_isZero_X A f n (0+1) (by decide) (by decide)).eq_of_tgt _ _
  · apply ShortComplex.exact_of_iso _ (smul_quotMap_exact A f n)
    refine ShortComplex.isoMk
      (singleConeNegOneIso (f ^ n • 𝟙 (ModuleCat.of A A)))
      (singleConeZeroIso (f ^ n • 𝟙 (ModuleCat.of A A)))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ProTorsion.Qmod A f n)).symm
      (singleCone_d _) ?_
    simp only [principalAugmentation_f_zero, Iso.hom_inv_id_assoc, Iso.symm_hom]

private theorem principalAugmentation_quasiIsoAt_other (A : Type u) [CommRing A]
    (f : A) (n : ℕ) (j : ℤ) (hj : j ≠ -1) :
    QuasiIsoAt (ProTorsion.alphaCx A f n) j := by
  by_cases hj' : j = 0
  · subst j; exact principalAugmentation_quasiIsoAt_zero A f n
  · apply (quasiIsoAt_iff_exactAt _ j
      (HomologicalComplex.ExactAt.of_isZero
        (principalCone_isZero_X A f n j hj hj'))).mpr
    exact HomologicalComplex.exactAt_single_obj _ _ _ _ hj'

private theorem principalTorsionKernelLift_quasiIso (A : Type u) [CommRing A]
    (f : A) (n : ℕ) :
    QuasiIso (kernel.lift (ProTorsion.alphaCx A f n)
      (principalTorsionInclusion A f n) (principalTorsionInclusion_comp A f n)) := by
  have := principalAugmentation_epi A f n
  exact kernelLift_quasiIso_of_singleFiber _ _ (ProTorsion.alphaCx A f n)
    (principalTorsionInclusion A f n) (principalTorsionInclusion_comp A f n)
    (principalTorsionInclusion_quasiIsoAt A f n)
    (principalAugmentation_quasiIsoAt_other A f n)

end PrincipalFiber

section TensorSingle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory


private theorem tensorSingleInclusion_naturality {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    ((tensorRight M).mapHomologicalComplex (.up ℤ)).map f ≫
      AdicCompletionTor.tensorSingleInclusion M L =
      AdicCompletionTor.tensorSingleInclusion M K ≫
        (f ▷ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  ext n : 1
  have h := HomologicalComplex.ι_mapBifunctorMap f
    (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))
    (curriedTensor (ModuleCat.{u} R)) (.up ℤ) n 0 n (add_zero n)
  change (HomologicalComplex.ιTensorObj K
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n)) ≫
      (f ▷ ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).f n =
        (f.f n ▷ M) ≫ (L.X n ◁ 𝟙 M) ≫
          HomologicalComplex.ιTensorObj L
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n) at h
  show (f.f n ▷ M) ≫ HomologicalComplex.ιTensorObj L
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n) =
    HomologicalComplex.ιTensorObj K
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n) ≫
        (f ▷ ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).f n
  simpa only [whiskerLeft_id, Category.comp_id, Category.id_comp] using h.symm

private def tensorSingleRightIso {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (tensorRight M).mapHomologicalComplex (.up ℤ) ≅
      tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
  NatIso.ofComponents (fun K ↦ by
    haveI := AdicCompletionTor.tensorSingleInclusion_isIso M K
    exact asIso (AdicCompletionTor.tensorSingleInclusion M K))
    (fun f ↦ tensorSingleInclusion_naturality M f)

private def tensorSingleLeftIso {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      (tensorRight M).mapHomologicalComplex (.up ℤ) := by
  letI := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  exact (BraidedCategory.curriedBraidingNatIso _).app _ ≪≫ (tensorSingleRightIso M).symm

private theorem kFlat_single_of_flat {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) [Module.Flat R M] :
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M).KFlat := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hflat : ∀ n : ℤ, Module.Flat R (S.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).toLinearEquiv
    · have : Subsingleton (S.X n) := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn)
      infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat S 0

end TensorSingle

section PrincipalFiberTower
set_option backward.isDefEq.respectTransparency false

private def principalConeTower (A : Type u) [CommRing A] (f : A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ ProTorsion.Kcx A f (n + 1))
    (fun n ↦ ProTorsion.KtransCx A f (n + 1) 1)

private def principalQuotientConeTower (A : Type u) [CommRing A] (f : A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ (ProTorsion.single0 A).obj (ProTorsion.Qmod A f (n+1)))
    (fun n ↦ (ProTorsion.single0 A).map (ProTorsion.QtransMod A f (n+1) 1))

private def principalConeAugmentation (A : Type u) [CommRing A] (f : A) :
    principalConeTower A f ⟶ principalQuotientConeTower A f :=
  NatTrans.ofOpSequence (fun n ↦ ProTorsion.alphaCx A f (n+1)) (by
    intro n
    simpa only [principalConeTower, principalQuotientConeTower,
      Functor.ofOpSequence_map_homOfLE_succ] using ProTorsion.KtransCx_alphaCx A f (n+1))

private theorem principalConeAugmentation_epi (A : Type u) [CommRing A] (f : A) :
    Epi (principalConeAugmentation A f) := by
  have (n : ℕᵒᵖ) : Epi ((principalConeAugmentation A f).app n) :=
    principalAugmentation_epi A f (n.unop+1)
  exact NatTrans.epi_of_epi_app _

private theorem principalConeTransition_negOne (A : Type u) [CommRing A]
    (f : A) (n c : ℕ) :
    (singleConeNegOneIso (f ^ (n+c) • 𝟙 (ModuleCat.of A A))).hom ≫
        (ProTorsion.KtransCx A f n c).f (-1) =
      (f ^ c • 𝟙 (ModuleCat.of A A)) ≫
        (singleConeNegOneIso (f ^ n • 𝟙 (ModuleCat.of A A))).hom := by
  have h := pow_smul_square A f (n + c) n c rfl
  have e := singleConeMap_negOne (f ^ (n+c) • 𝟙 (ModuleCat.of A A))
    (f ^ n • 𝟙 _) (f ^ c • 𝟙 _) (𝟙 _) h
  rw [singleConeMap_eq_KtransCx A f (n+c) n c rfl h] at e
  simpa only [eqToHom_refl, Category.id_comp] using e

private def principalTorsionTowerInclusion (A : Type u) [CommRing A] (f : A) :
    torsionPowerSystem f (ModuleCat.of A A) ⋙
      HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) (-1) ⟶
        principalConeTower A f :=
  NatTrans.ofOpSequence (fun n ↦ principalTorsionInclusion A f (n+1)) (by
    intro n
    apply HomologicalComplex.from_single_hom_ext (j := (-1 : ℤ))
    simp only [torsionPowerSystem, Functor.comp_map, principalConeTower,
      Functor.ofOpSequence_map_homOfLE_succ, HomologicalComplex.comp_f,
      HomologicalComplex.single_map_f_self, principalTorsionInclusion,
      HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]
    rw [principalConeTransition_negOne]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    apply (cancel_mono (singleConeNegOneIso (f ^ (n+1) • 𝟙 (ModuleCat.of A A))).hom).mpr
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f ^ ((n+1+1)-(n+1)) * (x : A) = f ^ 1 * (x : A)
    rw [Nat.add_sub_cancel_left])


private theorem principalTorsionTowerInclusion_comp (A : Type u) [CommRing A] (f : A) :
    principalTorsionTowerInclusion A f ≫ principalConeAugmentation A f = 0 := by
  apply NatTrans.ext
  funext n
  exact principalTorsionInclusion_comp A f (n.unop+1)

private def principalTorsionTowerKernelLift (A : Type u) [CommRing A] (f : A) :=
  kernel.lift (principalConeAugmentation A f) (principalTorsionTowerInclusion A f)
    (principalTorsionTowerInclusion_comp A f)

private theorem principalTorsionTowerKernelLift_quasiIso (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : QuasiIso ((principalTorsionTowerKernelLift A f).app (op n)) := by
  let ev := (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{u} A) ℤ)).obj (op n)
  let α := principalConeAugmentation A f
  let j := principalTorsionTowerKernelLift A f
  have he : j.app (op n) ≫ kernelComparison α ev =
      kernel.lift (ProTorsion.alphaCx A f (n+1))
        (principalTorsionInclusion A f (n+1)) (principalTorsionInclusion_comp A f (n+1)) := by
    apply (cancel_mono (kernel.ι (ProTorsion.alphaCx A f (n+1)))).mp
    have hc : kernelComparison α ev ≫ kernel.ι (ProTorsion.alphaCx A f (n+1)) =
        (kernel.ι α).app (op n) := kernelComparison_comp_ι α ev
    rw [Category.assoc, hc, kernel.lift_ι]
    exact congrArg (fun t ↦ t.app (op n))
      (kernel.lift_ι α (principalTorsionTowerInclusion A f)
        (principalTorsionTowerInclusion_comp A f))
  have : QuasiIso (j.app (op n) ≫ kernelComparison α ev) := by
    rw [he]
    exact principalTorsionKernelLift_quasiIso A f (n+1)
  exact quasiIso_of_comp_right (j.app (op n)) (kernelComparison α ev)

end PrincipalFiberTower

section FinsuppTensor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

private def tensorRightFinsuppIso (R : Type u) [CommRing R] :
    tensorRight (ModuleCat.of R (ℕ →₀ R)) ≅ finsuppFunctor R ℕ :=
  NatIso.ofComponents
    (fun M ↦ (TensorProduct.finsuppScalarRight R R M ℕ).toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      apply Finsupp.ext
      intro i
      change (TensorProduct.finsuppScalarRight R R N ℕ)
          (f x ⊗ₜ[R] y) i =
        f ((TensorProduct.finsuppScalarRight R R M ℕ) (x ⊗ₜ[R] y) i)
      simp only [TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_apply,
        Finsupp.single_apply, map_finsuppSum]
      congr 1
      funext a b
      split_ifs <;> simp)

end FinsuppTensor

section PrincipalFiberMilnor
set_option backward.isDefEq.respectTransparency false
open CountableMilnorTower

private theorem isZero_principalTorsionMilnor_of_isIso
    (A : Type u) [CommRing A] (f : A)
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight (principalConeAugmentation A f)
        (F.mapHomologicalComplex (.up ℤ)))))] :
    IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
      ((torsionPowerSystem f (ModuleCat.of A A) ⋙
        HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) (-1)) ⋙
          F.mapHomologicalComplex (.up ℤ)))) := by
  let α := principalConeAugmentation A f
  let j := principalTorsionTowerKernelLift A f
  let G := (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (ModuleCat.{u} A) ℤ)
    (CochainComplex (ModuleCat.{u} A) ℤ)).obj (F.mapHomologicalComplex (.up ℤ))
  have := principalConeAugmentation_epi A f
  let S := ShortComplex.mk (kernel.ι α) α (kernel.condition α)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel α }
  let : PreservesFiniteLimits G := ⟨fun J ↦ by dsimp [G]; infer_instance⟩
  let : PreservesFiniteColimits G := ⟨fun J ↦ by dsimp [G]; infer_instance⟩
  have : IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map (S.map G).g)) := by
    show IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight (principalConeAugmentation A f) (F.mapHomologicalComplex (.up ℤ)))))
    infer_instance
  have hzero := isZero_milnor_of_shortExact_of_isIso (S.map G) (hS.map_of_exact G)
  have : QuasiIso (countableMilnorFunctor.map (G.map j)) := by
    apply (map_quasiIso_and_milnor_triangle (A := A)).1
    intro n
    have := principalTorsionTowerKernelLift_quasiIso A f n
    show QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (j.app (op n)))
    infer_instance
  exact hzero.of_iso (asIso (DerivedCategory.Q.map (countableMilnorFunctor.map (G.map j))))

end PrincipalFiberMilnor

section PrincipalComparison
set_option backward.isDefEq.respectTransparency false

private abbrev principalComparison (A : Type u) [CommRing A] (f : A) :=
  (principalCompletionIso A f).hom ≫
    tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f)

private theorem completionAdjunction_unit (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) :
    (completionAdjunction A f).unit = KoszulCompletion.completionUnit f := by
  apply NatTrans.ext
  funext X
  simp only [completionAdjunction, AdicKoszulAdjunction.reflectionOfCompletion,
    Adjunction.mkOfHomEquiv_unit_app, AdicKoszulAdjunction.completionHomEquiv_apply,
    ObjectProperty.FullSubcategory.id_hom]
  exact Category.comp_id _

private theorem principalComparison_isIso_iff (A : Type u) [CommRing A] (f : A) :
    IsIso (principalComparison A f) ↔
      IsIso (tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f)) :=
  isIso_comp_left_iff _ _

private theorem principalComparison_milnorTriangles (A : Type u) [CommRing A] (f : A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    let generators : Fin 1 → A := fun _ ↦ f
    let U := NoetherianKoszulProIso.koszulPowerSystem generators ⋙ T.tensor.obj K
    let V := NoetherianKoszulProIso.quotientPowerSystem generators ⋙ T.tensor.obj K
    ∃ (p : (KoszulCompletion.completionFunctor generators).obj K ⟶
          ∏ᶜ fun n : ℕ ↦ U.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ U.obj (op n)) ⟶
          ((KoszulCompletion.completionFunctor generators).obj K)⟦(1 : ℤ)⟧)
      (q : (tensorQuotientLimit A generators).obj K ⟶ ∏ᶜ fun n : ℕ ↦ V.obj (op n))
      (ε : (∏ᶜ fun n : ℕ ↦ V.obj (op n)) ⟶
          ((tensorQuotientLimit A generators).obj K)⟦(1 : ℤ)⟧),
      Triangle.mk p (milnorEndo U) δ ∈ distTriang _ ∧
      Triangle.mk q (milnorEndo V) ε ∈ distTriang _ ∧
      ∀ n : ℕ, (principalComparison A f).app K ≫ q ≫ Pi.π _ n =
        p ≫ Pi.π _ n ≫ (T.tensor.obj K).map
          ((NoetherianKoszulProIso.koszulQuotientComparison generators).app (op n)) := by
  let generators : Fin 1 → A := fun _ ↦ f
  obtain ⟨p, δ, q, ε, hp, hq, he⟩ :=
    exists_strictTensorLimit_milnorComparison_of_isos A T (koszulComplexComparison generators)
      (koszulComplexTowerDerivedIso generators) (quotientComplexTowerDerivedIso generators)
      (NoetherianKoszulProIso.koszulQuotientComparison generators)
      (koszulComplexComparison_compatibility generators) K
  obtain ⟨δ', hp'⟩ := exists_milnor_triangle_of_objectIso
    ((principalCompletionIso A f).app K).symm hp
  refine ⟨_, δ', q, ε, hp', hq, ?_⟩
  intro n
  show ((principalCompletionIso A f).hom.app K ≫
      (tensorKoszulQuotientComparison A generators).app K) ≫ q ≫ Pi.π _ n = _
  simp only [Category.assoc]
  rw [he n]
  rfl

end PrincipalComparison

section PrincipalComparisonModels
set_option backward.isDefEq.respectTransparency false
open CountableMilnorTower CategoryTheory.MonoidalCategory

private def principalConeTowerIso (A : Type u) [CommRing A] (f : A) :
    koszulComplexTower (fun _ : Fin 1 ↦ f) ≅ principalConeTower A f := by
  let α : koszulComplexTower (fun _ : Fin 1 ↦ f) ⟶ principalConeTower A f :=
    NatTrans.ofOpSequence (fun n ↦ (koszulPowerConeIso A f (n+1)).hom) (by
      intro n
      simpa only [koszulComplexTower, principalConeTower,
        Functor.ofOpSequence_map_homOfLE_succ, eqToHom_refl, Category.id_comp] using
          koszulPowerConeIso_transition A f n 1)
  exact NatIso.ofComponents (fun n ↦ koszulPowerConeIso A f (n.unop+1))
    (fun g ↦ α.naturality g)

private def principalQuotientTowerIso (A : Type u) [CommRing A] (f : A) :
    quotientComplexTower (fun _ : Fin 1 ↦ f) ≅ principalQuotientConeTower A f := by
  let α : quotientComplexTower (fun _ : Fin 1 ↦ f) ⟶ principalQuotientConeTower A f :=
    NatTrans.ofOpSequence (fun n ↦ (quotientPowerSingleIso A f (n+1)).hom) (by
      intro n
      simpa only [quotientComplexTower, principalQuotientConeTower,
        Functor.ofOpSequence_map_homOfLE_succ] using quotientPowerSingleIso_transition A f n)
  exact NatIso.ofComponents (fun n ↦ quotientPowerSingleIso A f (n.unop+1))
    (fun g ↦ α.naturality g)

private theorem principalConeTowerIso_augmentation (A : Type u) [CommRing A] (f : A) :
    koszulComplexComparison (fun _ : Fin 1 ↦ f) ≫ (principalQuotientTowerIso A f).hom =
      (principalConeTowerIso A f).hom ≫ principalConeAugmentation A f := by
  apply NatTrans.ext
  funext n
  exact koszulPowerConeIso_augmentation A f (n.unop+1)

private theorem isIso_map_of_commutative_square
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (h : f ≫ eY.hom = eX.hom ≫ g)
    [IsIso (H.map f)] : IsIso (H.map g) :=
  (Arrow.isIso_hom_iff_isIso_hom_of_isIso
    (H.mapArrow.mapIso (Arrow.isoMk (f := Arrow.mk f) (g := Arrow.mk g) eX eY h.symm)).hom).mp
      (inferInstance : IsIso (H.map f))

private theorem principalConeMilnor_isIso_of_comparison_isIso
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A) [Module.Flat A M]
    [IsIso (tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f))] :
    IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map
      (Functor.whiskerRight (principalConeAugmentation A f)
        ((tensorRight M).mapHomologicalComplex (.up ℤ))))) := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let μ := koszulComplexComparison (fun _ : Fin 1 ↦ f)
  let H := countableMilnorFunctor ⋙ DerivedCategory.Q (C := ModuleCat.{u} A)
  have : IsIso (H.map (Functor.whiskerRight μ (TleftCochain S))) :=
    tensorMilnorMap_isIso_of_comparison_isIso A μ S (kFlat_single_of_flat M)
  let t : TleftCochain S ≅
      (tensorRight M).mapHomologicalComplex (.up ℤ) := tensorSingleLeftIso M
  let eX := Functor.isoWhiskerRight (principalConeTowerIso A f) (TleftCochain S) ≪≫
    Functor.isoWhiskerLeft (principalConeTower A f) t
  let eY := Functor.isoWhiskerRight (principalQuotientTowerIso A f) (TleftCochain S) ≪≫
    Functor.isoWhiskerLeft (principalQuotientConeTower A f) t
  apply isIso_map_of_commutative_square H (Functor.whiskerRight μ (TleftCochain S))
    (Functor.whiskerRight (principalConeAugmentation A f)
      ((tensorRight M).mapHomologicalComplex (.up ℤ))) eX eY
  dsimp only [eX, eY]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  rw [← Category.assoc, ← Functor.whiskerRight_comp,
    principalConeTowerIso_augmentation, Functor.whiskerRight_comp]
  simp only [Category.assoc]
  congr 1
  apply NatTrans.ext
  funext n
  exact t.hom.naturality ((principalConeAugmentation A f).app n)

end PrincipalComparisonModels

section PrincipalTorsionDetection
set_option backward.isDefEq.respectTransparency false
open CountableMilnorTower CategoryTheory.MonoidalCategory

private theorem isIso_milnorEndo_of_towerIso
    {C : Type*} [Category* C] [Preadditive C] [HasProductsOfShape ℕ C]
    {E F : ℕᵒᵖ ⥤ C} (e : E ≅ F) [IsIso (milnorEndo E)] :
    IsIso (milnorEndo F) := by
  let p := Limits.Pi.mapIso (fun n : ℕ ↦ e.app (op n))
  exact (Arrow.isIso_hom_iff_isIso_hom_of_isIso
    (Arrow.isoMk (f := Arrow.mk (milnorEndo E)) (g := Arrow.mk (milnorEndo F))
      p p (milnorEndo_naturality e.hom).symm).hom).mp
        (inferInstance : IsIso (milnorEndo E))

private theorem torsionTensor_milnorEndo_isIso
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A) [Module.Flat A M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    [IsIso (tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f))] :
    IsIso (milnorEndo (torsionPowerSystem f (ModuleCat.of A A) ⋙ tensorRight M)) := by
  have := principalConeMilnor_isIso_of_comparison_isIso A f M
  have hz := isZero_principalTorsionMilnor_of_isIso A f (tensorRight M)
  let E := torsionPowerSystem f (ModuleCat.of A A)
  let F := tensorRight M
  let S := HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) (-1)
  let e : (E ⋙ S) ⋙ F.mapHomologicalComplex (.up ℤ) ≅ (E ⋙ F) ⋙ S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) (-1)) ≪≫
        (Functor.associator _ _ _).symm
  apply isIso_milnorEndo_of_isZero_singleMilnor_at (E ⋙ F) (-1)
  exact hz.of_iso (DerivedCategory.Q.mapIso (countableMilnorFunctor.mapIso e)).symm

private theorem tensorKoszulQuotientComparison_torsionBounded
    (A : Type u) [CommRing A] (f : A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    [IsIso (tensorKoszulQuotientComparison A (fun _ : Fin 1 ↦ f))] :
    ProTorsion.TorsionBounded A f := by
  let E := torsionPowerSystem f (ModuleCat.of A A)
  have := torsionTensor_milnorEndo_isIso A f (ModuleCat.of A A)
  have := torsionTensor_milnorEndo_isIso A f (ModuleCat.of A (ℕ →₀ A))
  let e : E ⋙ tensorRight (ModuleCat.of A A) ≅ E :=
    NatIso.ofComponents (fun n ↦ ρ_ (E.obj n))
      (fun g ↦ rightUnitor_naturality (E.map g))
  have : IsIso (milnorEndo E) := isIso_milnorEndo_of_towerIso e
  have : IsIso (milnorEndo (E ⋙ finsuppFunctor A ℕ)) :=
    isIso_milnorEndo_of_towerIso (Functor.isoWhiskerLeft E (tensorRightFinsuppIso A))
  exact (torsionPowerSystem_proZero_iff A f).mp (proZero_of_isIso_milnorEndo_finsupp E)

end PrincipalTorsionDetection

public theorem solution
    (A : Type u) [CommRing A] (f : A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let D := DerivedCategory (ModuleCat.{u} A)
    let generators : Fin 1 → A := fun _ ↦ f
    let P : ObjectProperty D :=
      fun K ↦ IsDerivedComplete (Ideal.span (Set.range generators)) K
    ∃ (completion : D ⥤ P.FullSubcategory) (naiveCompletion : D ⥤ D)
      (comparison : completion ⋙ P.ι ⟶ naiveCompletion),
      Nonempty (completion ⊣ P.ι) ∧
        (∀ K : D,
          let koszulTower := NoetherianKoszulProIso.koszulPowerSystem generators ⋙ T.tensor.obj K
          let quotientTower := NoetherianKoszulProIso.quotientPowerSystem generators ⋙ T.tensor.obj
            K
          ∃ (p : (completion ⋙ P.ι).obj K ⟶
                ∏ᶜ fun n : ℕ ↦ koszulTower.obj (op n))
            (δ : (∏ᶜ fun n : ℕ ↦ koszulTower.obj (op n)) ⟶
                ((completion ⋙ P.ι).obj K)⟦(1 : ℤ)⟧)
            (q : naiveCompletion.obj K ⟶
                ∏ᶜ fun n : ℕ ↦ quotientTower.obj (op n))
            (ε : (∏ᶜ fun n : ℕ ↦ quotientTower.obj (op n)) ⟶
                (naiveCompletion.obj K)⟦(1 : ℤ)⟧),
            Triangle.mk p
                (Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) n -
                    Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) (n + 1) ≫
                      koszulTower.map (homOfLE (Nat.le_succ n)).op)
                δ ∈ distTriang D ∧
              Triangle.mk q
                (Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) n -
                    Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) (n + 1) ≫
                      quotientTower.map (homOfLE (Nat.le_succ n)).op)
                ε ∈ distTriang D ∧
              ∀ n : ℕ,
                comparison.app K ≫ q ≫
                    Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) n =
                  p ≫ Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) n ≫
                    (T.tensor.obj K).map
                      ((NoetherianKoszulProIso.koszulQuotientComparison generators).app (op n))) ∧
        (IsIso comparison ↔ ProTorsion.TorsionBounded A f) := by
  dsimp only
  refine ⟨completion A (fun _ : Fin 1 ↦ f), tensorQuotientLimit A (fun _ : Fin 1 ↦ f),
    principalComparison A f, ⟨completionAdjunction A (fun _ : Fin 1 ↦ f)⟩, ?_, ?_⟩
  · exact fun K ↦ principalComparison_milnorTriangles A f T K
  · rw [principalComparison_isIso_iff]
    constructor
    · intro h
      have := h
      exact tensorKoszulQuotientComparison_torsionBounded A f
    · exact tensorKoszulQuotientComparison_isIso_of_torsionBounded A f

end PrincipalNaiveCompletion

end




@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace PrincipalNaiveCompletion

/-- **Stacks 0923.** For `f ∈ A`, the canonical natural transformation from derived completion
at `(f)` to the naive derived completion formed from the quotients `A/(f^(n+1))` is an
isomorphism if and only if the `f`-power torsion of `A` is bounded. -/
@[stacks 0923]
public theorem derivedCompletionToNaive_isIso_iff_torsionBounded
    (A : Type u) [CommRing A] (f : A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let D := DerivedCategory (ModuleCat.{u} A)
    let generators : Fin 1 → A := fun _ ↦ f
    let P : ObjectProperty D :=
      fun K ↦ IsDerivedComplete (Ideal.span (Set.range generators)) K
    ∃ (completion : D ⥤ P.FullSubcategory) (naiveCompletion : D ⥤ D)
      (comparison : completion ⋙ P.ι ⟶ naiveCompletion),
      Nonempty (completion ⊣ P.ι) ∧
        (∀ K : D,
          let koszulTower := NoetherianKoszulProIso.koszulPowerSystem generators ⋙ T.tensor.obj K
          let quotientTower := NoetherianKoszulProIso.quotientPowerSystem generators ⋙ T.tensor.obj
            K
          ∃ (p : (completion ⋙ P.ι).obj K ⟶
                ∏ᶜ fun n : ℕ ↦ koszulTower.obj (op n))
            (δ : (∏ᶜ fun n : ℕ ↦ koszulTower.obj (op n)) ⟶
                ((completion ⋙ P.ι).obj K)⟦(1 : ℤ)⟧)
            (q : naiveCompletion.obj K ⟶
                ∏ᶜ fun n : ℕ ↦ quotientTower.obj (op n))
            (ε : (∏ᶜ fun n : ℕ ↦ quotientTower.obj (op n)) ⟶
                (naiveCompletion.obj K)⟦(1 : ℤ)⟧),
            Triangle.mk p
                (Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) n -
                    Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) (n + 1) ≫
                      koszulTower.map (homOfLE (Nat.le_succ n)).op)
                δ ∈ distTriang D ∧
              Triangle.mk q
                (Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) n -
                    Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) (n + 1) ≫
                      quotientTower.map (homOfLE (Nat.le_succ n)).op)
                ε ∈ distTriang D ∧
              ∀ n : ℕ,
                comparison.app K ≫ q ≫
                    Pi.π (fun n : ℕ ↦ quotientTower.obj (op n)) n =
                  p ≫ Pi.π (fun n : ℕ ↦ koszulTower.obj (op n)) n ≫
                    (T.tensor.obj K).map
                      ((NoetherianKoszulProIso.koszulQuotientComparison generators).app (op n))) ∧
        (IsIso comparison ↔ ProTorsion.TorsionBounded A f) :=
  PrincipalNaiveCompletion.solution A f T

end PrincipalNaiveCompletion

end
