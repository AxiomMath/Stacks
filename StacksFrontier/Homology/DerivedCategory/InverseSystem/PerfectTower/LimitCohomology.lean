module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.PadicTrace

/-!
# The cohomology inverse system of a perfect tower

The inverse system `Hⁱ(Kₙ)` of a `PerfectTower` with its canonical transitions, the limit
cohomology `Hⁱ_∞ = limₙ Hⁱ(Kₙ)` as a `ℤ_[ℓ]`-module, the fact that only finitely many `Hⁱ_∞` are
nonzero (Stacks 03V4, part (2)), and the endomorphism `πⁱ_∞` of `Hⁱ_∞` (part (3)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Trace
open scoped BigOperators TensorProduct

universe u w v

namespace Stacks.InverseSystem

open CategoryTheory.FilteredDerived (finite_nonzero_degrees)

attribute [local instance] HasDerivedCategory.standard

/-! ### The cohomology inverse system -/

/-- The cohomology `Hⁱ(Kₙ)` at level `n`, a `ℤ/ℓⁿ⁺¹ℤ`-module. -/
public abbrev levelCohomology {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (i : ℤ) (n : ℕ) :
    ModuleCat.{v} (ZMod (ℓ ^ (n + 1))) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) i).obj (T.obj n)

/-- The canonical transition `Hⁱ(Kₙ₊₁) → Hⁱ(Kₙ)`: apply `Hⁱ` to the transition of the tower,
then identify the cohomology of a restriction of scalars with the restriction of scalars of the
cohomology. -/
public def levelCohomologyTransition {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (i : ℤ) (n : ℕ) :
    levelCohomology T i (n + 1) ⟶
      (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).obj (levelCohomology T i n) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) i).map
      (T.transition n) ≫
    (restrictHomologyIsoOfHom.{v} (levelCast ℓ n) i).hom.app (T.obj n)

/-- The endomorphism `Hⁱ(πₙ)` of the level `n` cohomology. -/
public abbrev levelCohomologyEndoHom {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (i : ℤ) (n : ℕ) :
    levelCohomology T i n ⟶ levelCohomology T i n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) i).map (T.endo n)

/-- **Stacks 03V4, part (3).** The operators `Hⁱ(πₙ)` are compatible with the canonical
transitions of the cohomology inverse system. -/
public theorem levelCohomologyEndoHom_transition {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (i : ℤ)
    (n : ℕ) :
    levelCohomologyEndoHom T i (n + 1) ≫ levelCohomologyTransition T i n =
      levelCohomologyTransition T i n ≫
        (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).map (levelCohomologyEndoHom T i n) := by
  dsimp only [levelCohomologyTransition]
  rw [← Category.assoc, ← Functor.map_comp, T.endo_compatible n, Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact (restrictHomologyIsoOfHom.{v} (levelCast ℓ n) i).hom.naturality (T.endo n)

/-- `ℤ_[ℓ]` acts on the level `n` cohomology through reduction modulo `ℓⁿ⁺¹`. -/
public instance levelCohomologyPadicModule {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (i : ℤ) (n : ℕ) : Module ℤ_[ℓ] (levelCohomology T i n) :=
  Module.compHom _ (PadicInt.toZModPow (n + 1))

/-- The transition of the cohomology inverse system, as a map of `ℤ_[ℓ]`-modules. -/
public def levelCohomologyTransitionₗ {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (i : ℤ) (n : ℕ) :
    levelCohomology T i (n + 1) →ₗ[ℤ_[ℓ]] levelCohomology T i n where
  toFun := (levelCohomologyTransition T i n).hom
  map_add' a b := map_add _ _ _
  map_smul' c a := by
    change (levelCohomologyTransition T i n).hom ((PadicInt.toZModPow (n + 1 + 1) c) • a) =
      (PadicInt.toZModPow (n + 1) c) • (levelCohomologyTransition T i n).hom a
    rw [map_smul]
    change (levelCast ℓ n (PadicInt.toZModPow (n + 1 + 1) c)) •
      (levelCohomologyTransition T i n).hom a =
      (PadicInt.toZModPow (n + 1) c) • (levelCohomologyTransition T i n).hom a
    rw [show levelCast ℓ n (PadicInt.toZModPow (n + 1 + 1) c) = PadicInt.toZModPow (n + 1) c from
      PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) c]

/-- The endomorphism `Hⁱ(πₙ)`, as a map of `ℤ_[ℓ]`-modules. -/
public def levelCohomologyEndoₗ {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (i : ℤ) (n : ℕ) :
    levelCohomology T i n →ₗ[ℤ_[ℓ]] levelCohomology T i n where
  toFun := (levelCohomologyEndoHom T i n).hom
  map_add' a b := map_add _ _ _
  map_smul' c a := by
    change (levelCohomologyEndoHom T i n).hom ((PadicInt.toZModPow (n + 1) c) • a) =
      (PadicInt.toZModPow (n + 1) c) • (levelCohomologyEndoHom T i n).hom a
    rw [map_smul]

/-- The compatibility of `Hⁱ(πₙ)` with the transitions, read on elements. -/
public theorem levelCohomologyTransitionₗ_endo {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (i : ℤ) (n : ℕ) (x : levelCohomology T i (n + 1)) :
    levelCohomologyTransitionₗ T i n (levelCohomologyEndoₗ T i (n + 1) x) =
      levelCohomologyEndoₗ T i n (levelCohomologyTransitionₗ T i n x) := by
  have h := congrArg (fun φ : levelCohomology T i (n + 1) ⟶
      (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).obj (levelCohomology T i n) => φ.hom x)
    (levelCohomologyEndoHom_transition T i n)
  exact h

/-- The compatible families inside the product of the level cohomologies. -/
public def limitCohomologySubmodule {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    Submodule ℤ_[ℓ] (∀ n, levelCohomology T i n) where
  carrier := {a | ∀ n, levelCohomologyTransitionₗ T i n (a (n + 1)) = a n}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro a b ha hb n
    simp [map_add, ha n, hb n]
  smul_mem' := by
    intro c a ha n
    simp [map_smul, ha n]

/-- **Stacks 03V4.** The `ℤ_[ℓ]`-module `Hⁱ_∞ = limₙ Hⁱ(Kₙ)`. -/
public abbrev limitCohomology {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    Type v :=
  ↥(limitCohomologySubmodule T i)

/-- The projection of `Hⁱ_∞` to the level `n` cohomology. -/
public def limitCohomologyProjection {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (i : ℤ) (n : ℕ) :
    limitCohomology T i →ₗ[ℤ_[ℓ]] levelCohomology T i n where
  toFun a := a.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### Part (2): only finitely many limit cohomology modules are nonzero -/

private lemma isNilpotent_ker_levelCast {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ) :
    IsNilpotent (RingHom.ker (levelCast ℓ n)) := by
  refine ⟨2, le_antisymm ?_ bot_le⟩
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hval (z : ZMod (ℓ ^ (n + 1 + 1)))
      (hz : z ∈ RingHom.ker (levelCast ℓ n)) : ℓ ^ (n + 1) ∣ z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have h : levelCast ℓ n z = 0 := hz
    rw [← ZMod.natCast_zmod_val z, map_natCast] at h
    exact h
  obtain ⟨a, ha⟩ := hval x hx
  obtain ⟨b, hb⟩ := hval y hy
  show x * y = 0
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  rw [ha, hb]
  have hpow : ℓ ^ (n + 1 + 1) ∣ ℓ ^ (n + 1) * ℓ ^ (n + 1) := by
    rw [← pow_add]
    exact pow_dvd_pow ℓ (by omega)
  rw [mul_mul_mul_comm]
  exact hpow.trans (dvd_mul_right _ (a * b))

private lemma isZero_of_isZero_extendScalars
    {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (M : ModuleCat.{max u v w} R)
    (hM : IsZero ((ModuleCat.extendScalars.{u, w, max u v w} f).obj M)) :
    IsZero M := by
  let : Algebra R S := f.toAlgebra
  let eRing := RingHom.quotientKerEquivOfSurjective hf
  let eLin : (R ⧸ RingHom.ker f) ≃ₗ[R] S :=
    eRing.toAddEquiv.toLinearEquiv fun r x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      show f (r * x) = f r * f x
      exact map_mul f r x
  let : Module R ((ModuleCat.extendScalars f).obj M : Type _) := Module.compHom _ f
  have : IsScalarTower R S ((ModuleCat.extendScalars f).obj M : Type _) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : ((ModuleCat.extendScalars f).obj M : Type _) ≃ₗ[R]
      M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) :=
    (TensorProduct.AlgebraTensorModule.congr eLin.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f))
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  have : Subsingleton (M ⧸ (RingHom.ker f • (⊤ : Submodule R M))) :=
    e.symm.injective.subsingleton
  have htop : (⊤ : Submodule R M) ≤ RingHom.ker f • (⊤ : Submodule R M) := by
    intro x _
    rw [← Submodule.Quotient.mk_eq_zero]
    exact Subsingleton.elim _ _
  have hz := Submodule.eq_bot_of_le_smul_of_isNilpotent (RingHom.ker f) ⊤ hnil htop
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => sub_eq_zero.mp (by
    have hxy : x - y ∈ (⊤ : Submodule R M) := trivial
    rw [hz] at hxy
    exact hxy)⟩

private lemma exists_uniformly_bounded_projective_models {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) :
    ∃ a b : ℤ, ∀ n : ℕ, ∃ P : CochainComplex (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) ℤ,
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective (ZMod (ℓ ^ (n + 1))) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ T.obj n) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := (FilteredDerived.isPerfect_iff _ _).mp (T.isPerfect 0)
  obtain ⟨a, ha⟩ := hE.1.1
  obtain ⟨b, hb⟩ := hE.1.2
  refine ⟨a, b, ?_⟩
  intro n
  induction n with
  | zero => exact ⟨E, ha, hb, fun i => (hE.2 i).1, ⟨eE⟩⟩
  | succ n ih =>
      obtain ⟨E, hEa, hEb, hEp, ⟨eE⟩⟩ := ih
      let f := levelCast ℓ n
      have hf : Function.Surjective f := ZMod.castHom_surjective _
      let β := ((levelAdjunction.{v} ℓ n).homEquiv _ _).symm (T.transition n)
      have : IsIso β := T.comparison_isIso n
      obtain ⟨P, _, hPp, hPK, ⟨eRed⟩⟩ :=
        StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing_of_surjective
          f hf E (T.obj (n + 1)) ⟨b, hEb⟩ hEp
          ⟨eE ≪≫ (asIso β).symm⟩ (isNilpotent_ker_levelCast n)
      have hzero (i : ℤ) (hi : IsZero (E.X i)) : IsZero (P.X i) := by
        apply isZero_of_isZero_extendScalars f hf (isNilpotent_ker_levelCast n)
        exact (Iso.isZero_iff ((HomologicalComplex.eval _ _ i).mapIso eRed)).mpr hi
      refine ⟨P, ?_, ?_, hPp, hPK⟩
      · exact (CochainComplex.isStrictlyGE_iff _ _).mpr fun i hi =>
          hzero i (E.isZero_of_isStrictlyGE a i hi)
      · exact (CochainComplex.isStrictlyLE_iff _ _).mpr fun i hi =>
          hzero i (E.isZero_of_isStrictlyLE b i hi)

/-- **Stacks 03V4, part (2).** Only finitely many `Hⁱ_∞` are nonzero. -/
public theorem finite_setOf_nontrivial_limitCohomology {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) :
    {i : ℤ | Nontrivial (limitCohomology T i)}.Finite := by
  obtain ⟨a, b, hmodels⟩ := exists_uniformly_bounded_projective_models T
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra h
  have hzero (n : ℕ) : Subsingleton (levelCohomology T i n) := by
    obtain ⟨P, ha, hb, _, ⟨e⟩⟩ := hmodels n
    have hPi : IsZero (P.X i) := by
      by_cases hia : i < a
      · exact P.isZero_of_isStrictlyGE a i hia
      · exact P.isZero_of_isStrictlyLE b i (by simp only [Set.mem_Icc] at h; omega)
    have hH : IsZero (P.homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ hPi
    let eH := ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) i).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app P
    exact ModuleCat.isZero_iff_subsingleton.mp ((Iso.isZero_iff eH).mpr hH)
  have : Subsingleton (limitCohomology T i) := by
    constructor
    intro x y
    apply Subtype.ext
    funext n
    exact @Subsingleton.elim _ (hzero n) _ _
  exact not_nontrivial (limitCohomology T i) hi

/-! ### Part (3): the endomorphism of the limit cohomology -/

/-- **Stacks 03V4, part (3).** The endomorphism `πⁱ_∞` of `Hⁱ_∞` defined by the compatible
family `Hⁱ(πₙ)`. -/
public def limitCohomologyEndo {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    limitCohomology T i →ₗ[ℤ_[ℓ]] limitCohomology T i where
  toFun a := ⟨fun n => levelCohomologyEndoₗ T i n (a.1 n), by
    intro n
    rw [levelCohomologyTransitionₗ_endo T i n (a.1 (n + 1)), a.2 n]⟩
  map_add' a b := by
    ext n
    exact map_add (levelCohomologyEndoₗ T i n) _ _
  map_smul' c a := by
    ext n
    exact map_smul (levelCohomologyEndoₗ T i n) c _

/-- `πⁱ_∞` acts levelwise by `Hⁱ(πₙ)`. -/
@[simp]
public theorem limitCohomologyProjection_limitCohomologyEndo {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) (i : ℤ) (n : ℕ) (a : limitCohomology T i) :
    limitCohomologyProjection T i n (limitCohomologyEndo T i a) =
      levelCohomologyEndoₗ T i n (limitCohomologyProjection T i n a) :=
  rfl

end Stacks.InverseSystem

end
