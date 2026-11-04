module

public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.Homology.Perfect.FreeComplexLength
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Minimal complexes with projective cohomology have zero differentials

Let `A` be a local ring with maximal ideal `𝔪` and let `F` be a bounded above complex of finite
`A`-modules which is *minimal*: every differential has image in `𝔪 F`. If every cohomology module
of `F` is projective then every differential of `F` vanishes.

The argument is a descending induction on the degree. Once the differential out of degree `i`
vanishes, `H^i(F)` is the cokernel of the differential into degree `i`; if it is projective, the
image of that differential is a direct summand of `F^i`, contained in `𝔪 F^i` by minimality,
hence zero by Nakayama's lemma.

This is the algebra behind the reduction of the finite local freeness of the de Rham cohomology
sheaves of a proper smooth morphism over `ℚ` ([Stacks, Tag 0FMN], which defers the proof) to the
Artinian local case: a minimal complex over a Noetherian local ring whose reductions modulo every
power of the maximal ideal have free cohomology has zero differentials, by this file and Krull's
intersection theorem.

## Main results

* `CategoryTheory.ShortComplex.moduleCat_f_eq_zero_of_projective_homology`: a short complex of
  modules over a local ring, with finite middle term, zero second map, first map into `𝔪 X₂` and
  projective homology, has zero first map.
* `CochainComplex.moduleCat_d_eq_zero_of_projective_homology`: a bounded above minimal complex of
  finite modules over a local ring with projective cohomology has zero differentials.
* `CochainComplex.quasiIso_toOfHomologySections`: a complex whose cohomology objects are projective
  receives a quasi-isomorphism from its cohomology with zero differentials.
* `StacksDraft.Perfect.exists_minimal_free_complex_iso`: the minimal model of a perfect object over
  a local ring ([Stacks, Tag 0BCC]), with its minimality read on the differentials.
* `StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_projective` and
  `StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_flat`: for a perfect
  `M` with projective cohomology, or along a flat ring map,
  `H^i(M ⊗ᴸ_A B) ≅ B ⊗_A H^i(M)`; the field case is
  `StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_field`.
* `StacksDraft.Perfect.free_homology_of_forall_quotient_pow`: over a Noetherian local ring, a
  perfect object whose reductions modulo every `𝔪^k` have projective cohomology has finite free
  cohomology.

No `@[stacks]` attribute is carried: these are tools.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **A split summand inside `𝔪 X₂` is zero.** Let `S` be a short complex of modules over a local
ring whose middle term is finite, whose second map vanishes, whose first map has image in
`𝔪 X₂`, and whose homology is projective. Then the first map vanishes: the homology is the
cokernel of the first map, so projectivity splits the image off as a direct summand of `X₂`,
which lies in `𝔪 X₂` and is therefore zero by Nakayama's lemma. -/
theorem moduleCat_f_eq_zero_of_projective_homology (S : ShortComplex (ModuleCat.{v} A))
    [Module.Finite A S.X₂] (hg : S.g = 0)
    (hf : LinearMap.range S.f.hom ≤ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A S.X₂))
    [Projective S.homology] : S.f = 0 := by
  have : IsIso S.homologyι := S.isIso_homologyι hg
  have : Projective S.opcycles := Projective.of_iso (asIso S.homologyι) inferInstance
  let s : S.opcycles ⟶ S.X₂ := Projective.factorThru (𝟙 _) S.pOpcycles
  have hs : ∀ y, S.pOpcycles.hom (s.hom y) = y := fun y =>
    congrArg (fun φ => φ.hom y) (Projective.factorThru_comp (𝟙 S.opcycles) S.pOpcycles)
  let e : S.X₂ →ₗ[A] S.X₂ := LinearMap.id - s.hom ∘ₗ S.pOpcycles.hom
  have he : ∀ z, e z = z - s.hom (S.pOpcycles.hom z) := fun _ => rfl
  have hpe : ∀ z, S.pOpcycles.hom (e z) = 0 := fun z => by
    rw [he, map_sub, hs, sub_self]
  have hee : ∀ z, e (e z) = e z := fun z => by
    rw [he (e z), hpe, map_zero, sub_zero]
  have hrange : ∀ z, e z ∈ LinearMap.range S.f.hom := fun z =>
    (S.moduleCat_pOpcycles_eq_zero_iff (e z)).1 (hpe z)
  have hN : LinearMap.range e ≤ (IsLocalRing.maximalIdeal A) • LinearMap.range e := by
    rintro _ ⟨z, rfl⟩
    have h2 : e (e z) ∈ ((IsLocalRing.maximalIdeal A) • (⊤ : Submodule A S.X₂)).map e :=
      Submodule.mem_map_of_mem (hf (hrange z))
    rwa [Submodule.map_smul'', Submodule.map_top, hee] at h2
  have hNfg : (LinearMap.range e).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map e
  have hbot : LinearMap.range e = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hNfg hN
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  ext x
  have hex : e (S.f.hom x) = S.f.hom x := by
    rw [he, (S.moduleCat_pOpcycles_eq_zero_iff _).2 ⟨x, rfl⟩, map_zero, sub_zero]
  have hmem : e (S.f.hom x) ∈ LinearMap.range e := ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot, hex] at hmem
  simpa using hmem

end CategoryTheory.ShortComplex

namespace CochainComplex

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **A minimal complex with projective cohomology has zero differentials.** Let `F` be a bounded
above complex of finite modules over a local ring `A` all of whose differentials have image in
`𝔪 F`. If every cohomology module `H^i(F)` is projective, then every differential of `F` vanishes.

The proof is a descending induction on the degree, the inductive step being
`CategoryTheory.ShortComplex.moduleCat_f_eq_zero_of_projective_homology` at the short complex
`F^{i-1} ⟶ F^i ⟶ F^{i+1}`. -/
theorem moduleCat_d_eq_zero_of_projective_homology (F : CochainComplex (ModuleCat.{v} A) ℤ)
    (b : ℤ) [F.IsStrictlyLE b] [∀ i, Module.Finite A (F.X i)]
    (hmin : ∀ i j, LinearMap.range (F.d i j).hom ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j)))
    [∀ i, Projective (F.homology i)] (i j : ℤ) : F.d i j = 0 := by
  by_cases hij : i + 1 = j
  swap
  · exact F.shape _ _ hij
  subst hij
  suffices H : ∀ n : ℕ, ∀ i : ℤ, b - n ≤ i → F.d i (i + 1) = 0 from
    H (b - i).toNat i (by omega)
  intro n
  induction n with
  | zero =>
    intro i hi
    exact (F.isZero_of_isStrictlyLE b (i + 1) (by omega)).eq_of_tgt _ _
  | succ n ih =>
    intro i hi
    by_cases h : b - n ≤ i
    · exact ih i h
    · let S := F.sc' i (i + 1) (i + 1 + 1)
      have : Projective S.homology :=
        Projective.of_iso (F.homologyIsoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp))
          inferInstance
      have : Module.Finite A S.X₂ := inferInstanceAs (Module.Finite A (F.X (i + 1)))
      exact S.moduleCat_f_eq_zero_of_projective_homology (ih (i + 1) (by omega)) (hmin i (i + 1))

end CochainComplex

namespace CochainComplex

variable {C : Type*} [Category.{v} C] [Abelian C]

/-- **The cohomology of a cochain complex, as a complex with zero differentials**: its term in
degree `i` is `H^i(K)`. -/
@[ega "0 11.2.1" "partial, special case"]
noncomputable abbrev zeroDifferentialHomology (K : CochainComplex C ℤ) : CochainComplex C ℤ where
  X i := K.homology i
  d _ _ := 0

/-- Given a section `s_i` of `Z^i(K) ⟶ H^i(K)` in every degree, the chain map
`(H^i(K), 0) ⟶ K` choosing the cycles `s_i`. -/
noncomputable def toOfHomologySections (K : CochainComplex C ℤ)
    (s : ∀ i, K.homology i ⟶ K.cycles i) : K.zeroDifferentialHomology ⟶ K where
  f i := s i ≫ K.iCycles i
  comm' i j _ := by
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
    exact (zero_comp).symm

/-- The degree-`i` component of `toOfHomologySections K s` is `s i ≫ K.iCycles i`. -/
theorem toOfHomologySections_f (K : CochainComplex C ℤ) (s : ∀ i, K.homology i ⟶ K.cycles i)
    (i : ℤ) : (K.toOfHomologySections s).f i = s i ≫ K.iCycles i :=
  rfl

/-- **A choice of cycle representatives of the cohomology is a quasi-isomorphism**
`(H^•(K), 0) ⟶ K`. -/
theorem quasiIso_toOfHomologySections (K : CochainComplex C ℤ)
    (s : ∀ i, K.homology i ⟶ K.cycles i) (hs : ∀ i, s i ≫ K.homologyπ i = 𝟙 _) :
    QuasiIso (K.toOfHomologySections s) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := K.zeroDifferentialHomology
  have hπ : IsIso (H.homologyπ i) := H.isIso_homologyπ (i - 1) i (by simp) rfl
  have hι : IsIso (H.iCycles i) := H.isIso_iCycles i (i + 1) (by simp) rfl
  have hc : HomologicalComplex.cyclesMap (K.toOfHomologySections s) i = H.iCycles i ≫ s i := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, toOfHomologySections_f,
      Category.assoc]
  have hcomp : H.homologyπ i ≫ HomologicalComplex.homologyMap (K.toOfHomologySections s) i =
      H.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality, hc]
    simp only [Category.assoc, hs]
    exact Category.comp_id _
  have : IsIso (H.homologyπ i ≫
      HomologicalComplex.homologyMap (K.toOfHomologySections s) i) := by
    rwa [hcomp]
  exact IsIso.of_isIso_comp_left (H.homologyπ i) _

end CochainComplex

namespace ModuleCat

open scoped ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **Extension of scalars carries a map with image in `I N` to a map with image in
`I B ⊗ N`.** -/
theorem range_extendScalars_map_le_smul (ψ : A →+* B) {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (I : Ideal A) (hf : LinearMap.range f.hom ≤ I • (⊤ : Submodule A N)) :
    LinearMap.range ((ModuleCat.extendScalars ψ).map f).hom ≤
      (I.map ψ) • (⊤ : Submodule B ((ModuleCat.extendScalars ψ).obj N)) := by
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero =>
    have e := ((ModuleCat.extendScalars ψ).map f).hom.map_zero
    exact e ▸ zero_mem _
  | tmul s x =>
    revert s
    intro (s : B)
    let := ψ.toAlgebra
    have hx : f.hom x ∈ I • (⊤ : Submodule A N) := hf ⟨x, rfl⟩
    show s ⊗ₜ[A,ψ] f.hom x ∈ _
    let T : (ModuleCat.extendScalars ψ).obj N → Prop :=
      (· ∈ (I.map ψ) • (⊤ : Submodule B ((ModuleCat.extendScalars ψ).obj N)))
    refine Submodule.smul_induction_on (p := fun z => T (s ⊗ₜ[A,ψ] z))
      hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · have h2 : T (ψ a • (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] y)) :=
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem ψ ha) trivial
      have e : (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] (a • y)) =
          ψ a • (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] y) :=
        (TensorProduct.smul_tmul (R := A) (R' := A) a s y).symm
      exact (congrArg T e).mpr h2
    · have h2 : T ((show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] y) +
          (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] z)) := add_mem hy hz
      have e : (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] (y + z)) =
          (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] y) +
            (show (ModuleCat.extendScalars ψ).obj N from s ⊗ₜ[A,ψ] z) :=
        TensorProduct.tmul_add (R := A) s y z
      exact (congrArg T e).mpr h2
  | add t t' ht ht' =>
    have e := ((ModuleCat.extendScalars ψ).map f).hom.map_add t t'
    exact e ▸ add_mem ht ht'

end ModuleCat

namespace StacksDraft.Perfect

open CochainComplex.DerivedExtensionScalars

universe w w'

variable {A : Type u} [CommRing A]

/-- **The minimal model of a perfect object over a local ring, with its minimality read on the
differentials.** A perfect object `M` of `D(A)`, for any model of `D(A)`, is isomorphic to the
image of a bounded above complex `F` with `F^i ≅ A^{r_i}` all of whose differentials have image in
`𝔪 F`. This is [Stacks, Tag 0BCC] (`StacksDraft.Perfect.FibreCycleLift.exists_minimal_model`):
the ranks are the fibre dimensions `dim_κ H^i(F ⊗ κ)`, which forces the differentials of
`F ⊗ κ` to vanish. -/
theorem exists_minimal_free_complex_iso [IsLocalRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M) :
    ∃ (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) (r : ℤ → ℕ), F.IsStrictlyLE b ∧
      (∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A)))) ∧
      (∀ i j, LinearMap.range (F.d i j).hom ≤
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j))) ∧
      Nonempty (M ≅ DerivedCategory.Q.obj F) := by
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨eM⟩⟩ := hM
  obtain ⟨F, r, hX, hr, ⟨h⟩⟩ := FibreCycleLift.exists_minimal_model P a b hfin hproj
  let κ := IsLocalRing.residue A
  let hκ : HomotopyEquiv (FibreCycleLift.fibreComplex κ F) (FibreCycleLift.fibreComplex κ P) :=
    (ModuleCat.extendScalars κ).mapHomotopyEquiv h
  -- the ranks vanish above `b`
  have hr0 : ∀ i, b < i → r i = 0 := fun i hi => by
    rw [← hr i]
    have hz : IsZero ((FibreCycleLift.fibreComplex κ P).homology i) := by
      have : IsZero ((FibreCycleLift.fibreComplex κ P).X i) :=
        (ModuleCat.extendScalars κ).map_isZero (P.isZero_of_isStrictlyLE b i hi)
      exact ShortComplex.isZero_homology_of_isZero_X₂ _ this
    rw [(hκ.toHomologyIso i).toLinearEquiv.finrank_eq]
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  have hF : F.IsStrictlyLE b := (F.isStrictlyLE_iff b).2 fun i hi => by
    refine IsZero.of_iso ?_ (hX i).some
    rw [hr0 i hi]
    exact ModuleCat.isZero_of_subsingleton _
  -- the fibre has zero differentials
  have hκX : ∀ i, Nonempty ((FibreCycleLift.fibreComplex κ F).X i ≅
      ModuleCat.of (IsLocalRing.ResidueField A) (ULift.{u} (Fin (r i) → _))) := fun i =>
    ⟨(ModuleCat.extendScalars κ).mapIso (hX i).some ≪≫
      (extendScalars_standard_free_iso.{u, u} κ (r i)).some⟩
  have hfinX : ∀ i, Module.Finite (IsLocalRing.ResidueField A)
      ((FibreCycleLift.fibreComplex κ F).X i) := fun i =>
    Module.Finite.equiv (hκX i).some.toLinearEquiv.symm
  have hfinH : ∀ i, Module.Finite (IsLocalRing.ResidueField A)
      ((FibreCycleLift.fibreComplex κ F).homology i) := fun i => by
    have hle := (FibreCycleLift.fibreComplex κ F).moduleCat_length_homology_le i
    have : IsFiniteLength (IsLocalRing.ResidueField A)
        ((FibreCycleLift.fibreComplex κ F).homology i) := by
      refine Module.length_ne_top_iff.1 (ne_top_of_le_ne_top ?_ hle)
      rw [Module.length_eq_finrank]
      exact ENat.coe_ne_top _
    have : IsNoetherian (IsLocalRing.ResidueField A)
        ((FibreCycleLift.fibreComplex κ F).homology i) :=
      ((isFiniteLength_iff_isNoetherian_isArtinian).1 this).1
    infer_instance
  have hdκ : ∀ i j, (FibreCycleLift.fibreComplex κ F).d i j = 0 :=
    (FibreCycleLift.fibreComplex κ F).moduleCat_d_eq_zero_of_forall_length_homology_eq
      (fun i => by
        rw [Module.length_eq_finrank, Module.length_eq_finrank, hr i,
          (hκX i).some.toLinearEquiv.finrank_eq, ULift.moduleEquiv.finrank_eq,
          Module.finrank_fin_fun])
      (fun i => by rw [Module.length_eq_finrank]; exact ENat.coe_ne_top _)
  refine ⟨F, b, r, hF, hX, fun i j => ?_, ⟨eM ≪≫ ?_⟩⟩
  · exact LinearMap.range_le_smul_top_of_extendScalars_map_eq_zero (F.d i j)
      (IsLocalRing.maximalIdeal A) (hdκ i j)
  · exact ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv h.symm) ≪≫
      (DerivedCategory.quotientCompQhIso _).app F

/-- The standard free module `A^r` is a projective object of `ModuleCat A`. -/
theorem projective_ulift_fin_fun (r : ℕ) :
    Projective (ModuleCat.of A (ULift.{u} (Fin r → A))) :=
  ModuleCat.projective_of_free ((Pi.basisFun A (Fin r)).map ULift.moduleEquiv.symm)

/-- A module isomorphic to a standard finite free module is free and finite. -/
private theorem free_and_finite_of_iso {R : Type u} [CommRing R] {X : ModuleCat.{u} R} {r : ℕ}
    (e : X ≅ ModuleCat.of R (ULift.{u} (Fin r → R))) : Module.Free R X ∧ Module.Finite R X :=
  ⟨Module.Free.of_equiv e.toLinearEquiv.symm, Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- The cohomology of a complex `F` is the cohomology of any object `M ≅ Q F` of the derived
category. -/
private noncomputable def homologyIsoOfIsoQ [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {F : CochainComplex (ModuleCat.{u} A) ℤ} {M : DerivedCategory (ModuleCat.{u} A)}
    (eM : M ≅ DerivedCategory.Q.obj F) (i : ℤ) :
    F.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app F).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eM.symm

/-- **A perfect object over a local ring with projective cohomology has finite free
cohomology**: its minimal model has zero differentials, so `H^i(M) ≅ F^i ≅ A^{r_i}`. -/
theorem free_finite_homology_of_projective [IsLocalRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (hH : ∀ i, Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M))
    (i : ℤ) :
    Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) ∧
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) := by
  obtain ⟨F, b, r, hF, hX, hmin, ⟨eM⟩⟩ := exists_minimal_free_complex_iso M hM
  have : ∀ i, Module.Finite A (F.X i) := fun i => (free_and_finite_of_iso (hX i).some).2
  let eH := homologyIsoOfIsoQ eM
  have : ∀ i, Projective (F.homology i) := fun i =>
    Projective.of_iso (eH i).symm inferInstance
  have hd : ∀ i j, F.d i j = 0 := F.moduleCat_d_eq_zero_of_projective_homology b hmin
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M ≅
      ModuleCat.of A (ULift.{u} (Fin (r i) → A)) :=
    (eH i).symm ≪≫ F.moduleCatHomologyIsoXOfDEqZero hd i ≪≫ (hX i).some
  exact free_and_finite_of_iso e

/-- **The cohomology of a perfect object over a Noetherian ring is finite**: it is a subquotient
of a term of a bounded complex of finite modules. -/
theorem module_finite_homology_of_isPerfect {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsPerfect M) (i : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) := by
  obtain ⟨P, a, b, -, -, hfin, -, ⟨eM⟩⟩ := hM
  have := hfin i
  have : IsNoetherian R (P.cycles i) :=
    isNoetherian_of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective (P.iCycles i)).1 inferInstance)
  have : Module.Finite R (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective (P.homologyπ i)).1 inferInstance)
  have : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj P) :=
    inferInstanceAs (Module.Finite R (P.homology i))
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eM.symm).toLinearEquiv

section BaseChange

variable {B : Type u} [CommRing B] (φ : A →+* B)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (ModuleCat.{u} B)]

/-- On a bounded above complex of projectives, the cohomology of the derived base change is the
cohomology of the termwise base change. -/
noncomputable def homologyTotalDerivedExtensionScalarsQIso
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [F.IsStrictlyLE b]
    [∀ i, Projective (F.X i)] (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (D.functor.obj (DerivedCategory.Q.obj F)) ≅
      (FibreCycleLift.fibreComplex φ F).homology i :=
  have := D.comparison_isIso_of_projective F b
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso (asIso (D.comparison.app F)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app
      (FibreCycleLift.fibreComplex φ F)

/-- **Projective cohomology commutes with derived base change.** Let `M` be a perfect object of
`D(A)` all of whose cohomology modules are projective. Then for every ring map `φ : A → B` the
cohomology of `M ⊗ᴸ_A B` is the base change of the cohomology of `M`:
`H^i(M ⊗ᴸ_A B) ≅ B ⊗_A H^i(M)`.

Choosing cycle representatives of the projective cohomology modules gives a quasi-isomorphism
from the complex `(H^•(M), 0)` with zero differentials to a bounded complex of projectives
representing `M` (`CochainComplex.quasiIso_toOfHomologySections`); both are bounded above
complexes of projectives, so both compute `M ⊗ᴸ_A B` termwise, and the first has zero
differentials after base change. -/
theorem nonempty_homology_totalDerivedExtensionScalars_iso_of_projective
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (hH : ∀ i, Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M))
    (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M) ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)) := by
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨eM⟩⟩ := hM
  let eH := homologyIsoOfIsoQ eM
  have : ∀ i, Projective (P.homology i) := fun i =>
    Projective.of_iso (eH i).symm inferInstance
  let s : ∀ i, P.homology i ⟶ P.cycles i := fun i => Projective.factorThru (𝟙 _) (P.homologyπ i)
  have hs : ∀ i, s i ≫ P.homologyπ i = 𝟙 _ := fun i => Projective.factorThru_comp _ _
  let H := P.zeroDifferentialHomology
  have := P.quasiIso_toOfHomologySections s hs
  have : H.IsStrictlyLE b := (H.isStrictlyLE_iff b).2 fun j hj =>
    ShortComplex.isZero_homology_of_isZero_X₂ _ (P.isZero_of_isStrictlyLE b j hj)
  have : ∀ j, Projective (H.X j) := fun j => inferInstanceAs (Projective (P.homology j))
  have hdB : ∀ j k, (FibreCycleLift.fibreComplex φ H).d j k = 0 := fun j k => by
    show (ModuleCat.extendScalars φ).map (H.d j k) = 0
    exact Functor.map_zero _ _ _
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
      (D.functor.mapIso
        (eM ≪≫ (asIso (DerivedCategory.Q.map (P.toOfHomologySections s))).symm)) ≪≫
    homologyTotalDerivedExtensionScalarsQIso φ D H b i ≪≫
    (FibreCycleLift.fibreComplex φ H).moduleCatHomologyIsoXOfDEqZero hdB i ≪≫
    (ModuleCat.extendScalars φ).mapIso (eH i)⟩

/-- **Projective cohomology stays projective under derived base change.** -/
theorem projective_homology_totalDerivedExtensionScalars_of_projective
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (hH : ∀ i, Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M))
    (i : ℤ) :
    Module.Projective B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) := by
  obtain ⟨e⟩ := nonempty_homology_totalDerivedExtensionScalars_iso_of_projective φ D M hM hH i
  have := hH i
  let := φ.toAlgebra
  have : Module.Projective B ((ModuleCat.extendScalars φ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)) :=
    inferInstanceAs (Module.Projective B
      (TensorProduct A B ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)))
  exact Module.Projective.of_equiv e.toLinearEquiv.symm

/-- **Finite projective cohomology stays finite projective under derived base change.** -/
theorem finite_projective_homology_totalDerivedExtensionScalars
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (hH : ∀ i, Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M))
    (i : ℤ) [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)] :
    Module.Finite B
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) ∧
      Module.Projective B
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) := by
  obtain ⟨e⟩ := nonempty_homology_totalDerivedExtensionScalars_iso_of_projective φ D M hM hH i
  let := φ.toAlgebra
  have : Module.Finite B ((ModuleCat.extendScalars φ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)) :=
    inferInstanceAs (Module.Finite B
      (TensorProduct A B ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)))
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
    projective_homology_totalDerivedExtensionScalars_of_projective φ D M hM hH i⟩

/-- **Free cohomology is preserved by derived base change**, over a local ring: if the cohomology
modules of a perfect `M` are projective, those of `M ⊗ᴸ_A B` are free of finite type whenever
those of `M` are finite. -/
theorem free_homology_totalDerivedExtensionScalars_of_projective [IsLocalRing A]
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (hH : ∀ i, Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M))
    (i : ℤ) :
    Module.Free B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) ∧
      Module.Finite B
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) := by
  obtain ⟨F, b, r, hF, hX, hmin, ⟨eM⟩⟩ := exists_minimal_free_complex_iso M hM
  obtain ⟨e⟩ := nonempty_homology_totalDerivedExtensionScalars_iso_of_projective φ D M hM hH i
  let eH := homologyIsoOfIsoQ eM
  have : ∀ i, Projective (F.X i) := fun i =>
    Projective.of_iso (hX i).some.symm (projective_ulift_fin_fun (r i))
  have : ∀ i, Module.Finite A (F.X i) := fun i => (free_and_finite_of_iso (hX i).some).2
  have : ∀ i, Projective (F.homology i) := fun i => Projective.of_iso (eH i).symm inferInstance
  let e' : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M) ≅
      (ModuleCat.extendScalars φ).obj (ModuleCat.of A (ULift.{u} (Fin (r i) → A))) :=
    e ≪≫ (ModuleCat.extendScalars φ).mapIso ((eH i).symm ≪≫
      F.moduleCatHomologyIsoXOfDEqZero (F.moduleCat_d_eq_zero_of_projective_homology b hmin) i ≪≫
        (hX i).some)
  let e'' := e' ≪≫ (extendScalars_standard_free_iso.{u, u} φ (r i)).some
  exact free_and_finite_of_iso e''

/-- **Flat derived base change commutes with cohomology**: for a flat ring map `φ : A → B` and a
perfect object `M` of `D(A)`, `H^i(M ⊗ᴸ_A B) ≅ B ⊗_A H^i(M)`. The derived base change is computed
termwise on a bounded complex of projectives representing `M`, and extension of scalars along a
flat map is exact. -/
theorem nonempty_homology_totalDerivedExtensionScalars_iso_of_flat (hφ : φ.Flat)
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M) ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M)) := by
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨eM⟩⟩ := hM
  have : ∀ j, Projective (P.X j) := fun j => inferInstance
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : (ModuleCat.extendScalars.{u, u, u} φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isLeftAdjoint
  have : (ModuleCat.extendScalars.{u, u, u} φ).PreservesHomology := inferInstance
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso (D.functor.mapIso eM) ≪≫
    homologyTotalDerivedExtensionScalarsQIso φ D P b i ≪≫
    ((ModuleCat.extendScalars φ).mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) i).app P ≪≫
    (ModuleCat.extendScalars φ).mapIso
      (homologyIsoOfIsoQ eM i)⟩

/-- **Derived base change from a field commutes with cohomology**: for a perfect object `M` over
a field `k` and a ring map `φ : k → B`, `H^i(M ⊗ᴸ_k B) ≅ B ⊗_k H^i(M)`. Every module over a field
is projective, so this is
`StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_projective`. -/
theorem nonempty_homology_totalDerivedExtensionScalars_iso_of_field {k : Type u} [Field k]
    {B : Type u} [CommRing B] (φ : k →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} k)] [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} k)) (hM : IsPerfect M) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M) ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj M)) :=
  nonempty_homology_totalDerivedExtensionScalars_iso_of_projective φ D M hM
    (fun _ => inferInstance) i

/-- **Derived base change from a field has finite free cohomology**: for a perfect object `M` over
a field `k` and any ring map `φ : k → B`, every `H^i(M ⊗ᴸ_k B)` is a finite free `B`-module. -/
theorem free_homology_totalDerivedExtensionScalars_of_field {k : Type u} [Field k]
    {B : Type u} [CommRing B] (φ : k →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} k)] [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} φ)
    (M : DerivedCategory (ModuleCat.{u} k)) (hM : IsPerfect M) (i : ℤ) :
    Module.Free B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) ∧
      Module.Finite B
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj M)) :=
  free_homology_totalDerivedExtensionScalars_of_projective φ D M hM (fun _ => inferInstance) i

end BaseChange

section Noetherian

variable [IsNoetherianRing A] [IsLocalRing A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [∀ k : ℕ, HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ IsLocalRing.maximalIdeal A ^ k))]

/-- **The Artinian quotients detect free cohomology over a Noetherian local ring.** Let `A` be a
Noetherian local ring with maximal ideal `𝔪` and `M` a perfect object of `D(A)`. If for every
`k ≥ 1` every cohomology module of `M ⊗ᴸ_A A/𝔪^k` is a projective `A/𝔪^k`-module, then every
cohomology module of `M` is free of finite type.

Let `F` be the minimal model of `M`. Each `F ⊗_A A/𝔪^k` is a minimal complex over the local ring
`A/𝔪^k` computing `M ⊗ᴸ_A A/𝔪^k`, so its differentials vanish
(`CochainComplex.moduleCat_d_eq_zero_of_projective_homology`); by Krull's intersection theorem
(`LinearMap.eq_zero_of_forall_extendScalars_map_eq_zero`) so do those of `F`, and
`H^i(M) ≅ F^i`. -/
theorem free_homology_of_forall_quotient_pow
    (D : ∀ k : ℕ, TotalDerivedExtensionScalars.{u, u, u, w, w'}
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ k)))
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPerfect M)
    (h : ∀ k : ℕ, 0 < k → ∀ i, Module.Projective (A ⧸ IsLocalRing.maximalIdeal A ^ k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ IsLocalRing.maximalIdeal A ^ k)) i).obj
        ((D k).functor.obj M)))
    (i : ℤ) :
    Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) ∧
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) := by
  obtain ⟨F, b, r, hF, hX, hmin, ⟨eM⟩⟩ := exists_minimal_free_complex_iso M hM
  have : ∀ i, Projective (F.X i) := fun i =>
    Projective.of_iso (hX i).some.symm (projective_ulift_fin_fun (r i))
  have : ∀ i, Module.Finite A (F.X i) := fun i => (free_and_finite_of_iso (hX i).some).2
  have hd : ∀ i j, F.d i j = 0 := fun i j => by
    refine LinearMap.eq_zero_of_forall_extendScalars_map_eq_zero (F.d i j) fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (A ⧸ IsLocalRing.maximalIdeal A ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        exact Ideal.Quotient.subsingleton_iff.2 rfl
      have : Subsingleton ((ModuleCat.extendScalars
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 0))).obj (F.X j)) :=
        Module.subsingleton (A ⧸ IsLocalRing.maximalIdeal A ^ 0) _
      ext x
      exact Subsingleton.elim _ _
    · let m := IsLocalRing.maximalIdeal A
      have hne : m ^ k ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        (top_le_iff.1 (h ▸ Ideal.pow_le_self hk.ne'))
      have : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
      have : IsLocalRing (A ⧸ m ^ k) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective
      let Fk := FibreCycleLift.fibreComplex (Ideal.Quotient.mk (m ^ k)) F
      have : Fk.IsStrictlyLE b := (Fk.isStrictlyLE_iff b).2 fun i hi =>
        (ModuleCat.extendScalars _).map_isZero (F.isZero_of_isStrictlyLE b i hi)
      have : ∀ i, Module.Finite (A ⧸ m ^ k) (Fk.X i) := fun i =>
        Module.Finite.equiv ((ModuleCat.extendScalars (Ideal.Quotient.mk (m ^ k))).mapIso
          (hX i).some ≪≫ (extendScalars_standard_free_iso.{u, u} _ (r i)).some).toLinearEquiv.symm
      have hminK : ∀ i j, LinearMap.range (Fk.d i j).hom ≤
          (IsLocalRing.maximalIdeal (A ⧸ m ^ k)) • (⊤ : Submodule _ (Fk.X j)) := fun i j =>
        (ModuleCat.range_extendScalars_map_le_smul _ (F.d i j) m (hmin i j)).trans
          (Submodule.smul_mono_left (Ideal.map_le_iff_le_comap.2
            (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _
              Ideal.Quotient.mk_surjective)).ge))
      have : ∀ i, Projective (Fk.homology i) := fun i => by
        have := h k hk i
        exact Projective.of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso ((D k).functor.mapIso eM) ≪≫
            homologyTotalDerivedExtensionScalarsQIso _ (D k) F b i) inferInstance
      exact Fk.moduleCat_d_eq_zero_of_projective_homology b hminK i j
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M ≅
      ModuleCat.of A (ULift.{u} (Fin (r i) → A)) :=
    (homologyIsoOfIsoQ eM i).symm ≪≫ F.moduleCatHomologyIsoXOfDEqZero hd i ≪≫ (hX i).some
  exact free_and_finite_of_iso e

end Noetherian

end StacksDraft.Perfect

end
