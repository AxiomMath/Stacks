module

public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.HomologyColimits
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# Matlis duality on the quotients `A/𝔪^(n+1)`

Let `(A, 𝔪, κ)` be a Noetherian local ring and `E` an injective hull of `κ`. This file shows that
the quotients `A/𝔪^(n+1)` have finite length, identifies `Hom_A(A/𝔪^(n+1), E)` with the
`𝔪^(n+1)`-torsion submodule of `E`, shows that `E` is the colimit of these torsion submodules, and
that derived Hom from `A/𝔪^(n+1)` into a normalized dualizing complex is this torsion submodule
placed in degree zero.

This file was split from
`StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing.LocalDuality

open CochainComplex.HomComplex StacksDraft.DerivedHom

universe u v w

/-- A quotient of a Noetherian local ring by a power of its maximal ideal has finite length. -/
private theorem maximalIdealPowerQuotient_isFiniteLength
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) : IsFiniteLength A (A ⧸ IsLocalRing.maximalIdeal A ^ n) := by
  cases n with
  | zero =>
      let : Subsingleton (A ⧸ IsLocalRing.maximalIdeal A ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact .of_subsingleton
  | succ n =>
      let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
      have hI : I ≠ ⊤ := by
        intro ht
        have hle : I ≤ IsLocalRing.maximalIdeal A :=
          Ideal.pow_le_self (Nat.succ_ne_zero n)
        have hm : IsLocalRing.maximalIdeal A = ⊤ := top_unique (ht ▸ hle)
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hm
      have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
      have : IsLocalRing (A ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have : IsNoetherianRing (A ⧸ I) := inferInstance
      have hnil : IsNilpotent (IsLocalRing.maximalIdeal (A ⧸ I)) := by
        use n + 1
        rw [← IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
          ← Ideal.map_pow]
        change Ideal.map (Ideal.Quotient.mk I)
          (IsLocalRing.maximalIdeal A ^ (n + 1)) = ⊥
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      have : IsArtinianRing (A ⧸ I) :=
        (isArtinianRing_iff_isNilpotent_maximalIdeal (A ⧸ I)).mpr hnil
      change IsFiniteLength A (A ⧸ I)
      exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_quotient I,
          isArtinian_of_surjective_algebraMap
            (Ideal.Quotient.mk_surjective (I := I))⟩

/-- The `A`-linear map `A/I → E` sending `1` to a prescribed element of the `I`-torsion of `E`. -/
noncomputable def quotientLiftHomToTorsion
    (A : Type u) [CommRing A] (I : Ideal A)
    (E : Type (max v u)) [AddCommGroup E] [Module A E]
    (e : Submodule.torsionBySet A E (I : Set A)) :
    (A ⧸ I) →ₗ[A] E := by
  let f : A →ₗ[A] E := LinearMap.toSpanSingleton A E e.1
  have hf : I ≤ LinearMap.ker f := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact (Submodule.mem_torsionBySet_iff (I : Set A) e.1).mp e.2 ⟨a, ha⟩
  exact I.liftQ f hf

/-- Homomorphisms `A/I → E` are the elements of `E` annihilated by `I`, by evaluation at `1`. -/
noncomputable def quotientHomEquivTorsion
    (A : Type u) [CommRing A] (I : Ideal A)
    (E : Type (max v u)) [AddCommGroup E] [Module A E] :
    ((A ⧸ I) →ₗ[A] E) ≃ₗ[A]
      Submodule.torsionBySet A E (I : Set A) where
  toFun f := ⟨f 1, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have hq : Ideal.Quotient.mk I (a : A) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr a.property
    have hzero : (a : A) • (1 : A ⧸ I) = 0 := by
      simpa [Algebra.smul_def] using hq
    calc
      (a : A) • f 1 = f ((a : A) • (1 : A ⧸ I)) := by rw [f.map_smul]
      _ = 0 := by rw [hzero, map_zero]
    ⟩
  invFun := quotientLiftHomToTorsion A I E
  left_inv f := by
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (I.liftQ (LinearMap.toSpanSingleton A E (f 1)) _)
        (Submodule.Quotient.mk a) = f (Ideal.Quotient.mk I a)
    rw [Submodule.liftQ_apply]
    have hq : Ideal.Quotient.mk I a = (a : A) • (1 : A ⧸ I) := by
      simp [Algebra.smul_def]
    rw [LinearMap.toSpanSingleton_apply, hq, f.map_smul]
  right_inv e := by
    apply Subtype.ext
    change (I.liftQ (LinearMap.toSpanSingleton A E e.1) _)
        (Submodule.Quotient.mk (1 : A)) = e.1
    rw [Submodule.liftQ_apply]
    simp [LinearMap.toSpanSingleton_apply]
  map_add' f g := by
    ext
    rfl
  map_smul' r f := by
    ext
    rfl

/-- The universe-lifted quotient `A/𝔪^(n+1)`, as an object of the enlarged module category. -/
noncomputable abbrev maximalIdealPowerQuotientModule
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    ModuleCat.{max v u} A :=
  (ModuleCat.uliftFunctor.{v} A).obj
    (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)))

/-- The universe-lifted quotient `A/𝔪^(n+1)` has finite length over a Noetherian local ring. -/
theorem maximalIdealPowerQuotientModule_isFiniteLength
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) :
    IsFiniteLength A (maximalIdealPowerQuotientModule A n : Type (max v u)) :=
  (ULift.moduleEquiv :
    ULift.{v} (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) ≃ₗ[A]
      A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)).symm.isFiniteLength
    (maximalIdealPowerQuotient_isFiniteLength A (n + 1))

/-- The forgetful functor on modules in an enlarged universe preserves sequential colimits. -/
theorem highUniverse_forget_preservesSequentialColimits
    (A : Type u) [CommRing A] :
    PreservesColimitsOfShape ℕ (forget (ModuleCat.{max v u} A)) := by
  let e := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max v u, v} A
  have : PreservesColimitsOfShape ℕ
      (forget (ModuleCat.{max v u} (ULift.{v} A))) := by
    let := preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget (ModuleCat.{max v u} (ULift.{v} A)))
    infer_instance
  have : PreservesColimitsOfShape ℕ e.inverse := by infer_instance
  change PreservesColimitsOfShape ℕ
    (e.inverse ⋙ forget (ModuleCat.{max v u} (ULift.{v} A)))
  infer_instance

/-- Sequential colimits of modules in an enlarged universe are exact. -/
theorem highUniverse_hasExactSequentialColimits
    (A : Type u) [CommRing A] :
    HasExactColimitsOfShape ℕ (ModuleCat.{max v u} A) := by
  let e := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max v u, v} A
  let F := e.inverse
  have : HasExactColimitsOfShape ℕ
      (ModuleCat.{max v u} (ULift.{v} A)) :=
    (AB5OfSize_of_univLE.{0, 0, max v u, max v u}
      (ModuleCat.{max v u} (ULift.{v} A))).ofShape ℕ
  exact HasExactColimitsOfShape.domain_of_functor ℕ F

/-- The sequential diagram of modules given by a monotone family of submodules of `N`. -/
def submoduleSequenceDiagram
    {A : Type u} [Ring A] (N : ModuleCat.{w} A)
    (P : ℕ →o Submodule A N) : ℕ ⥤ ModuleCat.{w} A where
  obj n := ModuleCat.of A (P n)
  map f := ModuleCat.ofHom (Submodule.inclusion (P.monotone (leOfHom f)))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The cocone on a monotone family of submodules of `N` whose components are the inclusions. -/
def submoduleSequenceCocone
    {A : Type u} [Ring A] (N : ModuleCat.{w} A)
    (P : ℕ →o Submodule A N) : Cocone (submoduleSequenceDiagram N P) where
  pt := N
  ι := { app := fun n ↦ ModuleCat.ofHom (P n).subtype
         naturality := fun _ _ _ ↦ by ext; rfl }

/-- A module is the colimit of a monotone family of submodules which exhausts it. -/
noncomputable def isColimit_submoduleSequenceCocone
    {A : Type u} [Ring A] (N : ModuleCat.{w} A)
    (P : ℕ →o Submodule A N)
    (hP : ∀ x : N, ∃ n, x ∈ P n) :
    IsColimit (submoduleSequenceCocone N P) := by
  classical
  choose σ hσ using hP
  have hex (d : Cocone (submoduleSequenceDiagram N P)) :
      ∃ f : N ⟶ d.pt, ∀ n,
        (submoduleSequenceCocone N P).ι.app n ≫ f = d.ι.app n := by
    let v (x : N) := d.ι.app (σ x) ⟨x, hσ x⟩
    have hw (i j : ℕ) (hij : i ≤ j) (x : P i) :
        d.ι.app j ⟨x, P.monotone hij x.property⟩ = d.ι.app i x :=
      congr($(d.w (homOfLE hij)).hom x)
    have hv (i : ℕ) (x : N) (hx : x ∈ P i) :
        v x = d.ι.app i ⟨x, hx⟩ := by
      obtain ⟨j, h₁, h₂⟩ := exists_ge_ge (σ x) i
      exact (hw (σ x) j h₁ ⟨x, hσ x⟩).symm.trans (hw i j h₂ ⟨x, hx⟩)
    let f : N ⟶ d.pt := ModuleCat.ofHom {
      toFun := v
      map_add' := by
        intro x y
        obtain ⟨i, hx, hy⟩ := exists_ge_ge (σ x) (σ y)
        have hx' := P.monotone hx (hσ x)
        have hy' := P.monotone hy (hσ y)
        rw [hv i (x + y) ((P i).add_mem hx' hy'), hv i x hx', hv i y hy']
        exact (d.ι.app i).hom.map_add ⟨x, hx'⟩ ⟨y, hy'⟩
      map_smul' := by
        intro r x
        rw [hv (σ x) (r • x) ((P (σ x)).smul_mem r (hσ x)), hv (σ x) x (hσ x)]
        exact (d.ι.app (σ x)).hom.map_smul r ⟨x, hσ x⟩ }
    exact ⟨f, fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ hv n x.val x.property)⟩
  refine { desc := fun d ↦ (hex d).choose
           fac := fun d n ↦ (hex d).choose_spec n
           uniq := ?_ }
  intro d f hf
  ext x
  exact (congr($(hf (σ x)).hom ⟨x, hσ x⟩)).trans
    (congr($( (hex d).choose_spec (σ x) ).hom ⟨x, hσ x⟩)).symm

/-- The `𝔪^(n+1)`-torsion submodules of `E`, as a monotone family indexed by `n`. -/
noncomputable def maximalIdealPowTorsionOrderHom
    (A : Type u) [CommRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) : ℕ →o Submodule A E where
  toFun := maximalIdealPowTorsion A E
  monotone' := fun n m h ↦ Submodule.torsionBySet_le_torsionBySet_pow
    (n + 1) (m + 1) (Nat.add_le_add_right h 1) _

/-- An injective hull of the residue field is the colimit of its `𝔪^(n+1)`-torsion submodules. -/
noncomputable def maximalIdealPowTorsion_isColimit
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K E : ModuleCat.{max v u} A)
    (e : IsLocalRing.ResidueField A ≃ₗ[A] K)
    (i : K ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    IsColimit (submoduleSequenceCocone E (maximalIdealPowTorsionOrderHom A E)) := by
  apply isColimit_submoduleSequenceCocone
  intro x
  have htop := iSup_maximalIdealPowTorsion_eq_top A K E e i hi
  have hx : x ∈ (⨆ n : ℕ, maximalIdealPowTorsion A E n) := by
    rw [htop]
    trivial
  rw [Submodule.mem_iSup_of_directed] at hx
  · exact hx
  · intro n m
    refine ⟨max n m, ?_, ?_⟩
    · exact (maximalIdealPowTorsionOrderHom A E).monotone (Nat.le_max_left n m)
    · exact (maximalIdealPowTorsionOrderHom A E).monotone (Nat.le_max_right n m)

/-- Homomorphisms from `A/𝔪^(n+1)` to `E` are the `𝔪^(n+1)`-torsion submodule of `E`. -/
noncomputable def matlisPowerModuleIso
    (A : Type u) [CommRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) (n : ℕ) :
    ModuleCat.of A (maximalIdealPowerQuotientModule A n ⟶ E) ≅
      ModuleCat.of A (maximalIdealPowTorsion A E n) :=
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let hQ : ULift.{v} (A ⧸ I) ≃ₗ[A] A ⧸ I := ULift.moduleEquiv
  let e₁ : (maximalIdealPowerQuotientModule A n →ₗ[A] E) ≃ₗ[A]
      ((A ⧸ I) →ₗ[A] E) :=
    LinearEquiv.arrowCongr hQ (LinearEquiv.refl A E)
  let e₂ : ((A ⧸ I) →ₗ[A] E) ≃ₗ[A]
      maximalIdealPowTorsion A E n :=
    quotientHomEquivTorsion A I E
  (ModuleCat.homLinearEquiv.trans (e₁.trans e₂)).toModuleIso

/-- An object concentrated in degree zero has no cohomology in any nonzero degree. -/
private theorem single_derived_homology_isZero_of_ne_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (M : C) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C q).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) := by
  let e : (DerivedCategory.homologyFunctor C q).obj
        ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (((CochainComplex.singleFunctors C).functor 0).obj M).homology q :=
    (DerivedCategory.homologyFunctor C q).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫
      (DerivedCategory.homologyFunctorFactors C q).app _
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M q hq).of_iso e

/-- Derived Hom from `A/𝔪^(n+1)` into a normalized dualizing complex has no cohomology outside
degree zero. -/
theorem derivedHom_maximalIdealPower_homology_isZero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj
      ((derivedHomFiniteLengthFunctor.{u, v} A K).obj
        (Opposite.op (⟨maximalIdealPowerQuotientModule A n,
          maximalIdealPowerQuotientModule_isFiniteLength A n⟩ :
            FiniteLengthModules.{u, v} A)))) := by
  obtain ⟨e⟩ := derivedHomFiniteLengthIsoMatlisDual.{u, v} A K hK E i hi
  exact (single_derived_homology_isZero_of_ne_zero
    (ModuleCat.of A (maximalIdealPowTorsion A E n)) q hq).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).mapIso
        (e.app _ ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso
          (matlisPowerModuleIso A E n)))

end Dualizing.LocalDuality

end
