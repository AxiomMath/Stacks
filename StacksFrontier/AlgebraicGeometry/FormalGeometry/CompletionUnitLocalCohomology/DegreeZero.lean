module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.InductiveSteps

/-!
# The completion unit on local cohomology in degree zero

For a sufficiently small support ideal the completion unit `RΓ_J(M) ⟶ RΓ_J(M)^∧` is invertible
on `H⁰`, from Stacks 0EEX: the map `H⁰(RΓ_J(M)^∧) ⟶ M` obtained from the completion of the
counit lands in `⨆ Γ_{J'}(M)` and is injective.

## Main results

* `Stacks.Algebraization.isIso_homology_completionUnit_localCohomology_zero`

## References

* [Stacks Project, Tag 0EEX](https://stacks.math.columbia.edu/tag/0EEX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### Degree zero -/

section DegreeZero

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a finite module `M` over an `I`-adically complete Noetherian ring, the completion unit
`M ⟶ M^∧` of `M` placed in degree `0` induces isomorphisms on every cohomology module. -/
instance isIso_homology_completionUnit_single (I : Ideal A) (hI : I.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) := by
  have := isIso_completionUnit_single I hI M
  infer_instance

/-- The canonical map `H⁰(RΓ_{V(J)}(M)^∧) ⟶ M`: the completion of the counit
`RΓ_{V(J)}(M) ⟶ M`, read through the identification of `M` with `H⁰(M^∧)` coming from the
`I`-adic completeness of `M`. -/
def completedLocalCohomologyZeroToModule (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    [IsAdicComplete I A] (M : ModuleCat.{u} A) [Module.Finite A M] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((adicCompletionFunctor A I hI).obj
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) ⟶ M :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionFunctor A I hI).map
        ((Dualizing.localCohomologyAdjunction A J hJ).counit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) ≫
    inv ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I hI).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom.app M

/-- A functor turns an equality of two-step composites into one. -/
private theorem map_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, ← G.map_comp, h]

/-- The rearrangement identity behind the compatibility of the degree-zero comparison with
reduction modulo a power of `I`. -/
private theorem normalized_comp_of_squares {C : Type*} [Category C]
    {HFX HFK HFXn HFKn HK HKn Mo No : C}
    (f : HFX ⟶ HFK) (b : HK ⟶ HFK) [IsIso b] (σM : HK ⟶ Mo) (qn : Mo ⟶ No)
    (bn : HKn ⟶ HFKn) [IsIso bn] (p : HK ⟶ HKn) (pf : HFK ⟶ HFKn) (σN : HKn ⟶ No)
    (g : HFX ⟶ HFXn) (fn : HFXn ⟶ HFKn)
    (h1 : f ≫ pf = g ≫ fn) (h2 : p ≫ bn = b ≫ pf) (h3 : p ≫ σN = σM ≫ qn) :
    (f ≫ inv b ≫ σM) ≫ qn = g ≫ fn ≫ inv bn ≫ σN := by
  have h4 : inv b ≫ p = pf ≫ inv bn := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← h2]
    simp
  have e : f ≫ pf ≫ inv bn ≫ σN = g ≫ fn ≫ inv bn ≫ σN := by
    rw [← Category.assoc, h1, Category.assoc]
  simp only [Category.assoc]
  rw [← h3, ← Category.assoc (inv b) p σN, h4, Category.assoc]
  exact e

/-- A normalization identity: from `a ≫ c = d ≫ b` with `b` invertible one gets
`a ≫ c ≫ b⁻¹ ≫ s = d ≫ s`. -/
private theorem comp_assoc_inv_cancel {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (c : X ⟶ Y) (b : Z ⟶ Y) [IsIso b] (d : W ⟶ Z) (s : Z ⟶ T)
    (h : a ≫ c = d ≫ b) : a ≫ c ≫ inv b ≫ s = d ≫ s := by
  rw [← Category.assoc, h]
  simp

/-- Composing the completion unit with the canonical map to `M` recovers the degree-zero
local-cohomology inclusion `H⁰_{V(J)}(M) ⟶ M`. -/
theorem completionUnit_comp_completedLocalCohomologyZeroToModule
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) ≫
      completedLocalCohomologyZeroToModule I J hI hJ M =
    Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M := by
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH
  set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 with hS
  set F := adicCompletionFunctor A I hI with hF
  set η := adicCompletionUnit A I hI with hη
  set K := S.obj M with hK
  set X := ((Dualizing.localCohomologyFunctor A J hJ).obj K).obj with hX
  set ε := (Dualizing.localCohomologyAdjunction A J hJ).counit.app K with hε
  have hnat : ε ≫ η.app K = η.app X ≫ F.map ε := η.naturality ε
  have hnat₂ : H.map ε ≫ H.map (η.app K) = H.map (η.app X) ≫ H.map (F.map ε) :=
    (H.map_comp ε (η.app K)).symm.trans
      ((congrArg H.map hnat).trans (H.map_comp (η.app X) (F.map ε)))
  exact comp_assoc_inv_cancel _ _ _ _ _ hnat₂.symm

/-- **The degree-zero comparison is compatible with reduction modulo `Iⁿ`.** -/
theorem completedLocalCohomologyZeroToModule_comp_mkQ
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (n : ℕ) :
    completedLocalCohomologyZeroToModule I J hI hJ M ≫
        ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((adicCompletionFunctor A I hI).map
            (((Dualizing.localCohomologyFunctor A J hJ).map
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
                (ModuleCat.ofHom
                  (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ))).hom)) ≫
        completedLocalCohomologyZeroToModule I J hI hJ
          (ModuleCat.of A ((M : Type u) ⧸ (I ^ n • (⊤ : Submodule A (M : Type u))))) := by
  have h1 := map_comp_eq_of_eq (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
    (map_comp_eq_of_eq (adicCompletionFunctor A I hI)
      (((Dualizing.localCohomologyAdjunction A J hJ).counit.naturality
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ))).symm))
  have h2 := map_comp_eq_of_eq (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
    ((adicCompletionUnit A I hI).naturality
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)))
  have h3 := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} A) 0).hom.naturality
      (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)
  exact normalized_comp_of_squares _ _ _ _ _ _ _ _ _ _ h1 h2 h3

/-- When `RΓ_{V(J)}(M)` is already derived `I`-complete, the degree-zero comparison lands in the
`J`-power-torsion submodule of `M`. -/
theorem completedLocalCohomologyZeroToModule_mem_primaryComponent
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hc : IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) :
    (completedLocalCohomologyZeroToModule I J hI hJ M).hom z ∈
      Ideal.primaryComponent (M : Type u) J := by
  have hu := isIso_completionUnit_of_derivedComplete I hI _ hc
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) := by
    infer_instance
  have hkey : completedLocalCohomologyZeroToModule I J hI hJ M =
      inv ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) ≫
      Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M := by
    rw [← completionUnit_comp_completedLocalCohomologyZeroToModule I J hI hJ M]
    simp
  have hz := ConcreteCategory.congr_hom hkey z
  rw [hz]
  exact Stacks.Duality.supportLocalCohomologyToModule_mem_primaryComponent.{u, u} A J hJ M _

/-- **The image of the degree-zero comparison.** The map `H⁰(RΓ_{V(J)}(M)^∧) ⟶ M` lands in the
submodule of elements whose cyclic support meets `V(I)` only inside `V(J)`, that is, in the
colimit of Stacks 0EEX: stagewise, its reduction modulo `Iⁿ` factors through `H⁰_{V(J)}(M/IⁿM)`,
because `RΓ_{V(J)}(M/IⁿM)` is derived `I`-complete. -/
theorem completedLocalCohomologyZeroToModule_mem_supportTraceSubmodule
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) :
    (completedLocalCohomologyZeroToModule I J hI hJ M).hom y ∈
      Dualizing.supportTraceSubmodule A I J (M : Type u) := by
  rw [Dualizing.mem_supportTraceSubmodule_iff_forall_mkQ_mem_primaryComponent]
  intro n
  have hann : (I ^ n : Ideal A) ≤ Module.annihilator A
      (ModuleCat.of A ((M : Type u) ⧸ (I ^ n • (⊤ : Submodule A (M : Type u))))) := by
    intro c hc
    refine Module.mem_annihilator.mpr fun x => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective
      (I ^ n • (⊤ : Submodule A (M : Type u))) x
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_smul hc Submodule.mem_top)
  have hc := isDerivedComplete_localCohomology_of_pow_le_annihilator I J hJ n _ hann
  have hcomp := completedLocalCohomologyZeroToModule_comp_mkQ I J hI hJ M n
  have key : ((completedLocalCohomologyZeroToModule I J hI hJ M) ≫
      ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ).hom y ∈
      Ideal.primaryComponent ((M : Type u) ⧸ (I ^ n • (⊤ : Submodule A (M : Type u)))) J := by
    rw [hcomp]
    exact completedLocalCohomologyZeroToModule_mem_primaryComponent I J hI hJ _ hc _
  exact key

omit [IsNoetherianRing A] in
/-- The image of the degree-zero local-cohomology inclusion is the torsion submodule. -/
private theorem mem_primaryComponent_iff_exists_supportLocalCohomologyToModule
    (J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) (x : (M : Type u)) :
    x ∈ Ideal.primaryComponent (M : Type u) J ↔
      ∃ z, (Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M).hom z = x := by
  obtain ⟨e, he⟩ := Stacks.Duality.supportLocalCohomology_zero_iso_torsion.{u, u} A J hJ M
  refine ⟨fun hx => ⟨e.inv.hom ⟨x, hx⟩, ?_⟩, ?_⟩
  · rw [← he]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_assoc
      (ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent (M : Type u) J)))) ⟨x, hx⟩
  · rintro ⟨z, rfl⟩
    exact Stacks.Duality.supportLocalCohomologyToModule_mem_primaryComponent.{u, u} A J hJ M z

/-- **The degree-zero case of Stacks 0EFL.** Let `A` be Noetherian and `I`-adically complete,
let `M` be a finite `A`-module and let `J` be an ideal for which the colimit of Stacks 0EEX is
already attained at `J`, that is, every element of `M` whose cyclic support meets `V(I)` only
inside `V(J)` is already `J`-power torsion. Then the completion unit

`H⁰_{V(J)}(M) ⟶ H⁰(RΓ_{V(J)}(M)^∧)`

is an isomorphism.

Both sides are identified with submodules of `M`: the source by the degree-zero local-cohomology
inclusion, the target by `Stacks.Algebraization.completedLocalCohomologyZeroToModule`, whose
image lies in the colimit by
`Stacks.Algebraization.completedLocalCohomologyZeroToModule_mem_supportTraceSubmodule` and which
is therefore a split surjection onto `Γ_J(M)`. Stacks 0EEX makes the target abstractly isomorphic
to `Γ_J(M)`, so Orzech's theorem turns that surjection into a bijection. -/
theorem isIso_homology_zero_completionUnit_localCohomology
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hstab : Dualizing.supportTraceSubmodule A I J (M : Type u) =
      Ideal.primaryComponent (M : Type u) J) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) := by
  classical
  have hA := completionUnit_comp_completedLocalCohomologyZeroToModule I J hI hJ M
  choose s hs using fun x : Ideal.primaryComponent (M : Type u) J =>
    (mem_primaryComponent_iff_exists_supportLocalCohomologyToModule J hJ M x).1 x.2
  have hP : Ideal.primaryComponent (M : Type u) J =
      ⨆ (J' : Ideal A) (_ : J' ≤ J)
        (_ : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)),
        Ideal.primaryComponent (M : Type u) J' :=
    ((Dualizing.iSup_primaryComponent_eq_supportTraceSubmodule A I J (M : Type u)).trans
      hstab).symm
  obtain ⟨e₂, -⟩ := Dualizing.exists_iso_homology_zero_completedLocalCohomology A I J M
    (Ideal.primaryComponent (M : Type u) J) hP
  have hrange : ∀ y, (completedLocalCohomologyZeroToModule I J hI hJ M).hom y ∈
      Ideal.primaryComponent (M : Type u) J := fun y =>
    hstab ▸ completedLocalCohomologyZeroToModule_mem_supportTraceSubmodule I J hI hJ M y
  set a := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((adicCompletionUnit A I hI).app
      ((Dualizing.localCohomologyFunctor A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) with ha
  have hcomp : ∀ z, (completedLocalCohomologyZeroToModule I J hI hJ M).hom (a.hom z) =
      (Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M).hom z := fun z =>
    ConcreteCategory.congr_hom hA z
  have hsplit : ∀ x : Ideal.primaryComponent (M : Type u) J,
      (completedLocalCohomologyZeroToModule I J hI hJ M).hom (a.hom (s x)) = x.val :=
    fun x => (hcomp (s x)).trans (hs x)
  let u' : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) : Type u) →ₗ[A]
      Ideal.primaryComponent (M : Type u) J :=
    LinearMap.codRestrict _ (completedLocalCohomologyZeroToModule I J hI hJ M).hom hrange
  have hu'surj : Function.Surjective u' := fun x =>
    ⟨a.hom (s x), Subtype.ext (hsplit x)⟩
  have hi : Function.Injective
      (e₂.hom.hom : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((adicCompletionFunctor A I hI).obj
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) : Type u) →ₗ[A]
        Ideal.primaryComponent (M : Type u) J) :=
    (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
  have hu'inj : Function.Injective u' :=
    IsNoetherian.injective_of_surjective_of_injective _ u' hi hu'surj
  have huinj : Function.Injective (completedLocalCohomologyZeroToModule I J hI hJ M).hom :=
    fun y y' h => hu'inj (Subtype.ext h)
  have hainj : Function.Injective a.hom := by
    intro z z' h
    have h1 : (Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M).hom z =
        (Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M).hom z' := by
      rw [← hcomp z, ← hcomp z', h]
    exact Stacks.LocalCohomology.localCohomologyZeroToModule_injective.{u, u} A J hJ M h1
  have hasurj : Function.Surjective a.hom := by
    intro y
    refine ⟨s ⟨(completedLocalCohomologyZeroToModule I J hI hJ M).hom y, hrange y⟩, ?_⟩
    exact huinj (hsplit ⟨_, hrange y⟩)
  exact (ConcreteCategory.isIso_iff_bijective a).2 ⟨hainj, hasurj⟩

/-- A functor turns a factorization of a composite into one. -/
private theorem map_comp_eq_of_comp_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    G.map f ≫ G.map g = G.map h := by
  rw [← G.map_comp, e]

/-- Composing a two-step composite with a further morphism. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ Y) (h : f ≫ g = f') (s : Y ⟶ Z) :
    f ≫ g ≫ s = f' ≫ s := by
  rw [← Category.assoc, h]

omit [IsNoetherianRing A] in
/-- If the comparison `RΓ_{V(J)}(M) ⟶ RΓ_{V(J')}(M)` is invertible on `H⁰`, the two torsion
submodules of `M` agree. -/
theorem primaryComponent_eq_of_isIso_homology_zero_localCohomologyComparison
    (J J' : Ideal A) (hJ : J.FG) (hJ' : J'.FG) (hle : J' ≤ J) (M : ModuleCat.{u} A)
    (hg : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (localCohomologyComparison A J J' hJ hJ' hle
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) :
    Ideal.primaryComponent (M : Type u) J = Ideal.primaryComponent (M : Type u) J' := by
  have hcounit := localCohomologyComparison_comp_counit J J' hJ hJ' hle
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  have h1' := map_comp_eq_of_comp_eq (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
    hcounit
  have hkey : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (localCohomologyComparison A J J' hJ hJ' hle
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≫
      Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J' hJ' M =
      Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M :=
    comp_comp_eq_of_comp_eq _ _ _ h1' _
  have hbij := (ConcreteCategory.isIso_iff_bijective
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (localCohomologyComparison A J J' hJ hJ' hle
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))).1 hg
  refine Submodule.ext fun x => ?_
  rw [mem_primaryComponent_iff_exists_supportLocalCohomologyToModule J hJ M x,
    mem_primaryComponent_iff_exists_supportLocalCohomologyToModule J' hJ' M x]
  refine ⟨fun ⟨z, hz⟩ => ⟨_, (ConcreteCategory.congr_hom hkey z).trans hz⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨z, rfl⟩ := hbij.2 w
  exact ⟨z, (ConcreteCategory.congr_hom hkey z).symm.trans hw⟩

/-- **The degree-zero case, in the form used by the induction.** If shrinking `J` inside the
admissible range does not change `H⁰` of local cohomology, the completion unit is invertible on
`H⁰`. -/
theorem isIso_homology_zero_completionUnit_localCohomology_of_stable
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hiso : ∀ L : Ideal A, ∀ hL : L ≤ J,
      PrimeSpectrum.zeroLocus (L : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (localCohomologyComparison A J L hJ L.fg_of_isNoetherianRing hL
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) := by
  refine isIso_homology_zero_completionUnit_localCohomology I J hI hJ M ?_
  rw [← Dualizing.iSup_primaryComponent_eq_supportTraceSubmodule A I J (M : Type u)]
  refine le_antisymm (iSup_le fun L => iSup_le fun hL => iSup_le fun hV => ?_) ?_
  · exact (primaryComponent_eq_of_isIso_homology_zero_localCohomologyComparison J L hJ
      L.fg_of_isNoetherianRing hL M (hiso L hL hV)).symm.le
  · exact le_iSup_of_le J (le_iSup_of_le le_rfl (le_iSup_of_le rfl le_rfl))

end DegreeZero

end Stacks.Algebraization

end
