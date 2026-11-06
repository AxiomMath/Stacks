module

public import StacksFrontier.AlgebraicGeometry.Algebraization.AnnihilatorTruncationReduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete
public import StacksFrontier.Homology.PseudoCoherent.Characterization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived completion unit is injective on cohomology

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and let `X` be an object of `D(A)`
whose cohomology modules are finite. Derived `𝔪`-adic completion is the reflection of `D(A)`
onto the derived `𝔪`-complete objects, with unit `η : X ⟶ X^∧`. This file proves that `η` is
injective on cohomology in every degree:

`Hⁿ(X) ⟶ Hⁿ(X^∧)` is injective for every `n`.

## Main results

* `AdicCompletionCohomology.injective_homology_adicCompletionUnit` — the statement for the named
  derived completion endofunctor `Stacks.Algebraization.adicCompletionFunctor`, for any ideal
  contained in the Jacobson radical of a Noetherian ring.
* `AdicCompletionCohomology.injective_homology_derivedCompletionUnit` — the same statement for
  the Čech model `DerivedCompletion.derivedCompletionUnit` of derived completion along the
  maximal ideal of a Noetherian local ring.

## Implementation notes

The proof produces, for every `k`, an explicit derived `I`-complete test object together with a
map from `X` into it whose effect on `Hⁿ` is computable, and then uses the universal property of
the unit to factor that map through `η`. Concretely:

* The statement is first reduced, by the uniqueness of a reflection, from the Čech model to the
  unit of the adjunction `Stacks.Algebraization.adicCompletionAdjunction`, the two units being
  identified by `Stacks.Algebraization.exists_iso_derivedCompletionFunctor_completionFunctor`.
* For a complex `F` whose `n`-th term is a finite module, the test object in degree `n` is the
  single complex at `F ^ n / (im d ^ {n-1} + Iᵏ F ^ n)`. It is annihilated by `Iᵏ`, hence derived
  `I`-complete, and the quotient map `F ^ n ⟶ F ^ n / (…)` is a map of complexes into it because
  it kills the image of the differential. Its effect on `Hⁿ` is the map induced by the inclusion
  of the cycles, so a cycle killed by all of them lies in `⋂ₖ (im d ^ {n-1} + Iᵏ F ^ n)`, which
  is `im d ^ {n-1}` by Krull's intersection theorem applied to the finite module
  `F ^ n / im d ^ {n-1}`. Such a cycle is a boundary, so the class vanishes.
* A general `X` is compared with the truncation `τ^{≤ -1}`, which is pseudo-coherent and
  therefore represented by a bounded-above complex of finite free modules. Completion has
  cohomological amplitude contained in `[-r, 0]` for an ideal with `r` generators, by
  [Stacks, Tag 0AAJ], so below degree `-r - 1` the completion of that comparison is invertible
  and the two injectivity statements agree. An arbitrary degree is brought into that range by
  shifting, the unit being compatible with the shift because the completion adjunction is.

## References

* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0AAJ](https://stacks.math.columbia.edu/tag/0AAJ)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace AdicCompletionCohomology

section Completion

variable {A : Type u} [CommRing A]

/-- The annihilator of a module depends only on its isomorphism class. -/
private theorem annihilator_le_of_iso {M N : ModuleCat.{u} A} (e : M ≅ N) :
    Module.annihilator A M ≤ Module.annihilator A N := by
  intro a ha
  rw [← Stacks.Algebraization.smul_id_eq_zero_iff_mem_annihilator] at ha ⊢
  exact Stacks.Algebraization.smul_id_eq_zero_of_iso a e.symm ha

/-- A module annihilated by a power of `I` is derived `I`-complete. -/
private theorem isDerivedCompleteModule_of_pow_annihilates (I : Ideal A) (m : ℕ)
    (N : ModuleCat.{u} A) (h : (I ^ m : Ideal A) ≤ Module.annihilator A N) :
    IsDerivedCompleteModule I N := by
  intro a ha
  rw [isDerivedCompleteAt_single_iff_isIso_oneSubSmulShift, ← isDerivedCompleteAt_iff_isIso]
  refine isDerivedCompleteAt_of_isNilpotent ⟨m, ?_⟩
  apply End.ext
  rw [smul_id_pow, End.zero_asHom]
  exact (Stacks.Algebraization.smul_id_eq_zero_iff_mem_annihilator N (a ^ m)).2
    (h (Ideal.pow_mem_pow ha m))

/-- Krull's intersection theorem, relative to a submodule: over a Noetherian ring and for an
ideal inside the Jacobson radical, the submodules `B + IᵏM` of a finite module meet in `B`. -/
@[ega "0 7.3.5" "a⇒c, a⇒d", ega "0 7.4.2" "more general", ega "IV 19.5.5" "more general"]
private theorem iInf_sup_pow_smul_top_eq [IsNoetherianRing A] (I : Ideal A)
    (hjac : I ≤ Ideal.jacobson (⊥ : Ideal A)) (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (B : Submodule A M) :
    ⨅ k : ℕ, (B ⊔ I ^ k • (⊤ : Submodule A M)) = B := by
  refine le_antisymm (fun x hx ↦ ?_) (le_iInf fun _ ↦ le_sup_left)
  rw [Submodule.mem_iInf] at hx
  have hfin : Module.Finite A (M ⧸ B) :=
    Module.Finite.of_surjective B.mkQ B.mkQ_surjective
  have hmem : B.mkQ x ∈ ⨅ k : ℕ, I ^ k • (⊤ : Submodule A (M ⧸ B)) := by
    refine Submodule.mem_iInf _ |>.mpr fun k ↦ ?_
    have h1 : Submodule.map B.mkQ (B ⊔ I ^ k • (⊤ : Submodule A M)) =
        I ^ k • (⊤ : Submodule A (M ⧸ B)) := by
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, B.range_mkQ,
        B.mkQ_map_self, bot_sup_eq]
    rw [← h1]
    exact Submodule.mem_map_of_mem (hx k)
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hjac] at hmem
  simpa using (Submodule.Quotient.mk_eq_zero B).mp hmem

/-! ### The homology of a map to a single complex -/

/-- The homology map of `HomologicalComplex.mkHomToSingle q`, read through the canonical
identification of the homology of a single complex with its value, is induced by `q` on
cycles. -/
private theorem homologyπ_homologyMap_mkHomToSingle
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (N : ModuleCat.{u} A) (q : F.X n ⟶ N)
    (hq : ∀ i, (ComplexShape.up ℤ).Rel i n → F.d i n ≫ q = 0) :
    F.homologyπ n ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.mkHomToSingle q hq) n ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n N).hom =
      F.iCycles n ≫ q := by
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.mkHomToSingle_f]
  simp

/-! ### Derived completeness of a single complex killed by a power of the ideal -/

/-- A complex concentrated in one degree whose value is annihilated by `Iᵏ` is derived
`I`-complete. -/
private theorem isDerivedComplete_single (I : Ideal A) (m : ℕ) (n : ℤ) (N : ModuleCat.{u} A)
    (hN : (I ^ m : Ideal A) ≤ Module.annihilator A N) :
    IsDerivedComplete I (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) n).obj N)) := by
  set S := (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) n).obj N with hS
  rw [isDerivedComplete_iff_forall_isDerivedCompleteModule_homology]
  intro i
  refine isDerivedCompleteModule_of_pow_annihilates I m _ ?_
  refine le_trans ?_ (annihilator_le_of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app S).symm)
  by_cases hi : i = n
  · subst hi
    exact hN.trans (annihilator_le_of_iso
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i N).symm)
  · have hz : IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
        (ComplexShape.up ℤ) i).obj S) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n N i hi
    intro a _
    exact Module.mem_annihilator.mpr fun x ↦
      (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _

/-! ### The pseudo-coherent case -/

open Stacks.Algebraization in
/-- **Injectivity on `Hⁿ` of the derived completion unit, for a complex whose `n`-th term is a
finite module.** -/
private theorem injective_homology_adicCompletionUnit_of_finite_X
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (hFn : Module.Finite A (F.X n)) :
    Function.Injective
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((adicCompletionUnit A I hI).app (DerivedCategory.Q.obj F))).hom) := by
  let := hFn
  set B : Submodule A (F.X n) := LinearMap.range (F.d (n - 1) n).hom with hBdef
  set u : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (DerivedCategory.Q.obj F) ⟶
      F.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.app F with hudef
  have hu : IsIso u := by
    rw [hudef]
    exact NatIso.isIso_app_of_isIso
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom F
  refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
  set x := u.hom y with hxdef
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (F.homologyπ n)).mp inferInstance x
  have key : ∀ k : ℕ, (F.iCycles n).hom z ∈ B ⊔ I ^ k • (⊤ : Submodule A (F.X n)) := by
    intro k
    set U : Submodule A (F.X n) := B ⊔ I ^ k • (⊤ : Submodule A (F.X n)) with hUdef
    set N : ModuleCat.{u} A := ModuleCat.of A ((F.X n) ⧸ U) with hNdef
    set q : F.X n ⟶ N := ModuleCat.ofHom U.mkQ with hqdef
    have hqd : ∀ i, (ComplexShape.up ℤ).Rel i n → F.d i n ≫ q = 0 := by
      intro i hi
      obtain rfl : i = n - 1 := by
        simp only [ComplexShape.up_Rel] at hi; omega
      refine ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_)
      show U.mkQ ((F.d (n - 1) n).hom w) = 0
      exact (Submodule.Quotient.mk_eq_zero U).mpr
        (Submodule.mem_sup_left (LinearMap.mem_range_self _ w))
    set θ : F ⟶ (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) n).obj N :=
      HomologicalComplex.mkHomToSingle q hqd with hθdef
    have hann : (I ^ k : Ideal A) ≤ Module.annihilator A N := by
      intro a ha
      refine Module.mem_annihilator.mpr fun w ↦ ?_
      refine Submodule.Quotient.induction_on _ w fun v ↦ ?_
      exact (Submodule.Quotient.mk_eq_zero U).mpr
        (Submodule.mem_sup_right (Submodule.smul_mem_smul ha Submodule.mem_top))
    obtain ⟨g, hg⟩ := (completionUnit_comp_bijective I hI (DerivedCategory.Q.obj F) _
      (isDerivedComplete_single I k n N hann)).2 (DerivedCategory.Q.map θ)
    have hg' : (adicCompletionUnit A I hI).app (DerivedCategory.Q.obj F) ≫ g =
      DerivedCategory.Q.map θ := hg
    have hθy : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (DerivedCategory.Q.map θ)).hom y = 0 := by
      have hsplit : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            (DerivedCategory.Q.map θ) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            ((adicCompletionUnit A I hI).app (DerivedCategory.Q.obj F)) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map g := by
        rw [← Functor.map_comp, hg']
      rw [hsplit, ModuleCat.comp_apply, hy, map_zero]
    have hx0 : (HomologicalComplex.homologyMap θ n).hom x = 0 := by
      have h1 := ConcreteCategory.congr_hom
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.naturality θ) y
      simp only [Functor.comp_map] at h1
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h1
      rw [hθy, map_zero] at h1
      exact h1.symm
    have hid := ConcreteCategory.congr_hom
      (homologyπ_homologyMap_mkHomToSingle F n N q hqd) z
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply, hz, hx0,
      map_zero] at hid
    exact (Submodule.Quotient.mk_eq_zero U).mp hid.symm
  have hmem : (F.iCycles n).hom z ∈ B := by
    rw [← iInf_sup_pow_smul_top_eq I hjac (F.X n) B, Submodule.mem_iInf]
    exact key
  obtain ⟨w, hw⟩ := hmem
  have hzw : F.toCycles (n - 1) n w = z := by
    refine (ModuleCat.mono_iff_injective (F.iCycles n)).mp inferInstance ?_
    have ht := ConcreteCategory.congr_hom (F.toCycles_i (n - 1) n) w
    rw [ModuleCat.comp_apply] at ht
    rw [ht, hw]
  have hx : x = 0 := by
    rw [← hz, ← hzw]
    have ht := ConcreteCategory.congr_hom (F.toCycles_comp_homologyπ (n - 1) n) w
    rw [ModuleCat.comp_apply] at ht
    simpa using ht
  exact (ModuleCat.mono_iff_injective u).mp inferInstance (by rw [← hxdef, hx]; simp)

/-! ### Transfer along a morphism -/

/-- Injectivity transfers across a commuting square whose left side is an epimorphism and whose
right side is a monomorphism. -/
private theorem injective_of_square {M₁ M₂ N₁ N₂ : ModuleCat.{u} A}
    (α : M₁ ⟶ M₂) (β : N₁ ⟶ N₂) (ρ : M₁ ⟶ N₁) (σ : M₂ ⟶ N₂)
    (hcomm : α ≫ σ = ρ ≫ β) (hρ : Epi ρ) (hσ : Mono σ)
    (hα : Function.Injective α.hom) : Function.Injective β.hom := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective ρ).mp hρ v
  have h3 := ConcreteCategory.congr_hom hcomm w
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hw, hv] at h3
  have h4 : α.hom w = 0 := by
    refine (ModuleCat.mono_iff_injective σ).mp hσ ?_
    rw [h3]
    simp
  rw [← hw, (injective_iff_map_eq_zero _).mp hα w h4]
  simp

open Stacks.Algebraization in
/-- Injectivity of the completion unit on `Hⁿ` passes along a morphism `φ` which is invertible
on `Hⁿ` and whose completion is a monomorphism on `Hⁿ`. -/
private theorem injective_homology_adicCompletionUnit_of_hom
    (I : Ideal A) (hI : I.FG) (n : ℤ) {X Y : DerivedCategory (ModuleCat.{u} A)} (φ : X ⟶ Y)
    (hφ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map φ))
    (hφ' : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((adicCompletionFunctor A I hI).map φ)))
    (hX : Function.Injective (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((adicCompletionUnit A I hI).app X)).hom)) :
    Function.Injective (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((adicCompletionUnit A I hI).app Y)).hom) := by
  have := hφ
  refine injective_of_square _ _ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map φ) _
    ?_ inferInstance hφ' hX
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map)
    ((adicCompletionUnit A I hI).naturality φ).symm

/-! ### The case of a degree below the negative of the number of generators -/

open Stacks.Algebraization CompletionAdjunction in
/-- **Injectivity on `Hʲ` of the derived completion unit for `j ≤ -r - 1`.** Here `r` is the
number of generators of `I`; below that degree the completion of the inclusion of the truncation
`τ^{≤ -1}` is invertible on `Hʲ`, which reduces the statement to a pseudo-coherent complex. -/
private theorem injective_homology_adicCompletionUnit_of_le
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ Ideal.jacobson (⊥ : Ideal A))
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X))
    (j : ℤ) (hj : j ≤ -(r : ℤ) - 1) :
    Function.Injective (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((adicCompletionUnit A I hI).app X)).hom) := by
  subst hf
  set P₀ := DerivedCategory.Q.objPreimage X with hP₀
  set eX : DerivedCategory.Q.obj P₀ ≅ X := DerivedCategory.Q.objObjPreimageIso X with heX
  set W := DerivedCategory.Q.obj (P₀.truncLE (-1)) with hWdef
  set φ : W ⟶ X := DerivedCategory.Q.map (P₀.ιTruncLE (-1)) ≫ eX.hom with hφdef
  have hι : ∀ i : ℤ, i ≤ -1 → IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (DerivedCategory.Q.map (P₀.ιTruncLE (-1)))) := fun i hi ↦
    have := P₀.quasiIsoAt_ιTruncLE (-1) i hi
    (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i) (P₀.ιTruncLE (-1))).mpr
        (inferInstanceAs (IsIso (HomologicalComplex.homologyMap (P₀.ιTruncLE (-1)) i)))
  have hiso : ∀ i : ℤ, i ≤ -1 →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ) := by
    intro i hi
    have := hι i hi
    rw [hφdef, Functor.map_comp]
    infer_instance
  have hzW : ∀ i : ℤ, (-1 : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj W) :=
    (DerivedCategory.isLE_iff _ (-1)).mp inferInstance
  have hmono0 : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map φ) :=
    (hzW 0 (by omega)).mono _
  have hamp := ((derivedCompletion_finiteCohomologicalDimension A f
    (Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI)
    (adicCompletionAdjunction A (Ideal.span (Set.range f)) hI) φ).2 ⟨hiso, hmono0⟩).1 j hj
  have hXP : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (DerivedCategory.Q.obj P₀)) := by
    intro i
    have := hX i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eX).toLinearEquiv.symm
  have hWpc : StacksDraft.PseudoCoherence.IsPseudoCoherent W := by
    refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      W 0 A).2.1.mpr ⟨⟨-1, hzW⟩, fun i ↦ ?_⟩
    by_cases hi : i ≤ -1
    · have := hι i hi
      have := hXP i
      exact Module.Finite.equiv (asIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          (DerivedCategory.Q.map (P₀.ιTruncLE (-1))))).toLinearEquiv.symm
    · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj W) :=
        ModuleCat.isZero_iff_subsingleton.mp (hzW i (by omega))
      infer_instance
  obtain ⟨G, hG, ⟨eG⟩⟩ := hWpc
  have hGfin : Module.Finite A (G.X j) := (hG.finiteFree j).1
  refine injective_homology_adicCompletionUnit_of_hom _ hI j φ (hiso j (by omega)) ?_ ?_
  · have hamp' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((adicCompletionFunctor A (Ideal.span (Set.range f)) hI).map φ)) := hamp
    infer_instance
  · exact injective_homology_adicCompletionUnit_of_hom _ hI j eG.hom inferInstance inferInstance
      (injective_homology_adicCompletionUnit_of_finite_X _ hI hjac G j hGfin)

/-! ### The general degree, and the Čech unit -/

open Stacks.Algebraization in
/-- **Injectivity on `Hⁿ` of the derived `I`-adic completion unit**, for every degree `n` and
every object of `D(A)` with finite cohomology modules over a Noetherian ring whose ideal lies in
the Jacobson radical. -/
theorem injective_homology_adicCompletionUnit
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X))
    (n : ℤ) :
    Function.Injective (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((adicCompletionUnit A I hI).app X)).hom) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  let := (adicCompletionAdjunction A I hI).leftAdjointCommShift ℤ
  have := (adicCompletionAdjunction A I hI).commShift_of_rightAdjoint ℤ
  have haj : (n + (r : ℤ) + 1) + (-(r : ℤ) - 1) = n := by omega
  have hY : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (X⟦n + (r : ℤ) + 1⟧)) := by
    intro i
    have := hX (n + (r : ℤ) + 1 + i)
    have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (X⟦n + (r : ℤ) + 1⟧) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + (r : ℤ) + 1 + i)).obj X :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
        (n + (r : ℤ) + 1) i (n + (r : ℤ) + 1 + i) rfl).app X
    exact Module.Finite.equiv e.toLinearEquiv.symm
  have h1 := injective_homology_adicCompletionUnit_of_le I hI hjac f hf
    (X⟦n + (r : ℤ) + 1⟧) hY (-(r : ℤ) - 1) le_rfl
  have hcs : (adicCompletionUnit A I hI).app (X⟦n + (r : ℤ) + 1⟧) ≫
      ((adicCompletionFunctor A I hI).commShiftIso (n + (r : ℤ) + 1)).hom.app X =
      ((adicCompletionUnit A I hI).app X)⟦n + (r : ℤ) + 1⟧' :=
    Adjunction.unit_app_commShiftIso_hom_app (adicCompletionAdjunction A I hI) ℤ
      (n + (r : ℤ) + 1) X
  have h2 : Function.Injective
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ) - 1)).map
        (((adicCompletionUnit A I hI).app X)⟦n + (r : ℤ) + 1⟧')).hom) := by
    refine injective_of_square
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ) - 1)).map
        ((adicCompletionUnit A I hI).app (X⟦n + (r : ℤ) + 1⟧)))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ) - 1)).map
        (((adicCompletionUnit A I hI).app X)⟦n + (r : ℤ) + 1⟧'))
      (𝟙 _)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ) - 1)).map
        (((adicCompletionFunctor A I hI).commShiftIso (n + (r : ℤ) + 1)).hom.app X))
      ?_ inferInstance inferInstance h1
    rw [← Functor.map_comp, hcs, Category.id_comp]
  have hnat := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso_hom_naturality
    (n + (r : ℤ) + 1) (-(r : ℤ) - 1) n haj ((adicCompletionUnit A I hI).app X)
  refine injective_of_square _ _
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
      (n + (r : ℤ) + 1) (-(r : ℤ) - 1) n haj).hom.app X)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
      (n + (r : ℤ) + 1) (-(r : ℤ) - 1) n haj).hom.app
        ((adicCompletionFunctor A I hI).obj X))
    hnat (@IsIso.epi_of_iso _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _))
    (@IsIso.mono_of_iso _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _)) h2

end Completion

open Stacks.Algebraization in
/-- **Stacks 0A06, the injectivity of the comparison.** Let `A` be a Noetherian local ring and
let `f` generate its maximal ideal. For an object `X` of `D(A)` whose cohomology modules are
finite, the unit `X ⟶ X^∧` of derived completion along the maximal ideal is injective on
cohomology in every degree. -/
theorem injective_homology_derivedCompletionUnit
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ n : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X))
    (n : ℤ) :
    Function.Injective
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((DerivedCompletion.derivedCompletionUnit A f).app X)).hom) := by
  have hI : (IsLocalRing.maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨e, he⟩ := exists_iso_derivedCompletionFunctor_completionFunctor
    (IsLocalRing.maximalIdeal A) hI f hf X
  have hadic := injective_homology_adicCompletionUnit (IsLocalRing.maximalIdeal A) hI
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) X hX n
  have hcomp : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((DerivedCompletion.derivedCompletionUnit A f).app X) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map e.hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((adicCompletionUnit A (IsLocalRing.maximalIdeal A) hI).app X) := by
    rw [← Functor.map_comp, he]
  intro y₁ y₂ hy
  refine hadic ?_
  have k1 := ConcreteCategory.congr_hom hcomp y₁
  have k2 := ConcreteCategory.congr_hom hcomp y₂
  rw [ModuleCat.comp_apply] at k1 k2
  rw [← k1, ← k2, hy]

end AdicCompletionCohomology
