module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex.MatlisPowerQuotients
import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# Local cohomology as a colimit of Hom complexes

Local cohomology with support in `V(I)` of a complex represented by a K-injective complex `J` is the
termwise `I`-power-torsion subcomplex of `J`, which is the colimit of the Hom complexes
`Hom^•(A/I^(n+1)[0], J)`. This file sets up these models, together with the systems of quotients
`A/𝔪^(n+1)` and of the modules `Hom_A(A/𝔪^(n+1), E)` used to compute local cohomology of a
normalized dualizing complex.

This file was split from
`StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing.LocalDuality

open CochainComplex.HomComplex StacksDraft.DerivedHom

universe u v w

/-- The termwise `I`-power-torsion subcomplex of a complex `J`, read in the derived category.
For a K-injective `J` representing `K` this computes local cohomology of `K`. -/
noncomputable def highUniverseLocalCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    DerivedCategory (ModuleCat.{max v u} A) :=
  let F := powerTorsionFunctor.{u, max u v} A I
  let P := powerTorsionModuleProperty.{u, max u v} A I
    (Ideal.fg_of_isNoetherianRing (I := I))
  letI : F.Additive := powerTorsionFunctor_additive A I
  letI : P.IsSerreClass := powerTorsionModuleProperty_isSerreClass A I
    (Ideal.fg_of_isNoetherianRing (I := I))
  letI : P.ι.Additive := {
    map_add := by intro X Y f g; ext x; rfl }
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj J
  DerivedCategory.Q.obj
    ((P.ι.mapHomologicalComplex (.up ℤ)).obj FC)

/-- Derived `I`-power torsion of `K` is the termwise torsion subcomplex of a K-injective complex
representing `K`. -/
noncomputable def derivedPowerTorsion_modelIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max v u} A))
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [hJ : J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) :
    (derivedPowerTorsionProperty.{u, max u v} A I
      (Ideal.fg_of_isNoetherianRing I)).ι.obj
        ((powerTorsionComparison.{u, max u v} A I
          (Ideal.fg_of_isNoetherianRing I)).obj
          ((derivedPowerTorsion.{u, v} A I
            (Ideal.fg_of_isNoetherianRing I)).obj K)) ≅
      highUniverseLocalCohomology A I J := by
  let hI : I.FG := Ideal.fg_of_isNoetherianRing I
  let P := derivedPowerTorsionProperty.{u, max u v} A I hI
  let PM := powerTorsionModuleProperty.{u, max u v} A I hI
  let PT : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let F := powerTorsionFunctor.{u, max u v} A I
  let hcat := (HomotopyCategory.quotient (ModuleCat.{max u v} A) (.up ℤ)).obj J
  letI : PT.IsSerreClass := powerTorsionModuleProperty_isSerreClass A I hI
  letI : F.Additive := powerTorsionFunctor_additive A I
  letI : PM.ι.Additive := {
    map_add := by intro X Y f g; ext x; rfl }
  let QhT : HomotopyCategory (PT.FullSubcategory) (.up ℤ) ⥤
      DerivedCategory (PT.FullSubcategory) := DerivedCategory.Qh
  have hA : ∀ C : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∃ (J' : CochainComplex (ModuleCat.{max u v} A) ℤ) (f : C ⟶ J'),
        J'.IsKInjective ∧ QuasiIso f := by
    intro C
    obtain ⟨J', f, hf, hJ'⟩ := CochainComplex.exists_quasiIso_isKInjective C
    exact ⟨J', f, hJ', hf⟩
  let hpt := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (.up ℤ) ⋙ QhT) hA
  letI : (F.mapHomotopyCategory (.up ℤ) ⋙ QhT).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) := hpt.1
  let D := (F.mapHomotopyCategory (.up ℤ) ⋙ QhT).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  let unit := (F.mapHomotopyCategory (.up ℤ) ⋙ QhT).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  let src := QhT.obj ((F.mapHomotopyCategory (.up ℤ)).obj hcat)
  have hu : IsIso (unit.app hcat) := hpt.2 (L := DerivedCategory.Qh) (RF := D) (α := unit) J hJ
  let eK : DerivedCategory.Q.obj J ≅ K := eJ
  let eQ : DerivedCategory.Qh.obj hcat ≅ DerivedCategory.Q.obj J :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app J
  let G := powerTorsionComparison.{u, max u v} A I hI ⋙ P.ι
  let PMι := PM.ι
  let eD : G.obj (D.obj K) ≅ G.obj (D.obj (DerivedCategory.Qh.obj hcat)) :=
    G.mapIso (D.mapIso (eQ ≪≫ eK)).symm
  let eUnit : G.obj (D.obj (DerivedCategory.Qh.obj hcat)) ≅ G.obj src :=
    G.mapIso (asIso (unit.app hcat)).symm
  let eComp : G.obj src ≅ (PMι.mapDerivedCategory).obj src :=
    (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).app src
  letI : (PMι).Additive := inferInstance
  let fH := (F.mapHomotopyCategory (.up ℤ)).obj hcat
  let eFact₁ := PMι.mapDerivedCategoryFactorsh.app fH
  let eF := (F.mapHomotopyCategoryFactors (.up ℤ)).app J
  let eFact₂ := DerivedCategory.Qh.mapIso
    ((PMι.mapHomotopyCategory (.up ℤ)).mapIso eF)
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj J
  let eFact₃ := DerivedCategory.Qh.mapIso
    ((PMι.mapHomotopyCategoryFactors (.up ℤ)).app FC)
  let eFact₄ := (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app
    ((PMι.mapHomologicalComplex (.up ℤ)).obj FC)
  change G.obj (D.obj K) ≅ DerivedCategory.Q.obj
    ((PMι.mapHomologicalComplex (.up ℤ)).obj FC)
  exact eD ≪≫ eUnit ≪≫ eComp ≪≫ eFact₁ ≪≫ eFact₂ ≪≫ eFact₃ ≪≫ eFact₄

/-- Local cohomology with support in `V(I)` is the termwise `I`-power-torsion subcomplex of a
K-injective complex representing the object. -/
noncomputable def localCohomology_modelIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max v u} A))
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) :
    (derivedPowerTorsionProperty.{u, max u v} A I
      (Ideal.fg_of_isNoetherianRing I)).ι.obj
        ((localCohomologyFunctor A I
          (Ideal.fg_of_isNoetherianRing I)).obj K) ≅
      highUniverseLocalCohomology A I J := by
  let hI : I.FG := Ideal.fg_of_isNoetherianRing I
  let P := derivedPowerTorsionProperty.{u, max u v} A I hI
  haveI := TorsionCounit.isIso_compareTorsionFunctors_app.{u, v} A I hI K
  let e := asIso ((compareTorsionFunctors.{u, v} A I hI).app K)
  exact (P.ι.mapIso e).symm ≪≫ derivedPowerTorsion_modelIso A I K J eJ

/-- The single complex on the universe-lifted quotient `A/I`, in degree zero. -/
noncomputable abbrev highUniverseQuotientSingle
    (A : Type u) [CommRing A] (I : Ideal A) :
    CochainComplex (ModuleCat.{max v u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj
    ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I)))

/-- The universe-lifted quotient map `A/I^(n+1) → A/I^n`. -/
noncomputable def highUniverseQuotientPowerSucc
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ⟶
      (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I ^ n)) :=
  (ModuleCat.uliftFunctor.{v} A).map (quotientPowerSucc A I n)

/-- The universe-lifted quotient map `A/I^(n+1) → A/I^n` sends `1` to `1`. -/
private lemma highUniverseQuotientPowerSucc_apply_one
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    highUniverseQuotientPowerSucc.{u, v} A I n (ULift.up 1) = ULift.up 1 := by
  change ULift.up (Ideal.Quotient.factorPowSucc I n 1) = ULift.up 1
  rw [map_one]

/-- The sequence of universe-lifted quotients `A/𝔪^(n+1)`, as finite-length modules. -/
noncomputable def quotientPowerFiniteLengthFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    ℕ ⥤ (FiniteLengthModules.{u, v} A)ᵒᵖ :=
  Functor.ofSequence
    (X := fun n ↦ Opposite.op
      (⟨maximalIdealPowerQuotientModule A n,
        maximalIdealPowerQuotientModule_isFiniteLength A n⟩ :
          FiniteLengthModules.{u, v} A))
    (fun n ↦ (show
      (⟨maximalIdealPowerQuotientModule A (n + 1),
        maximalIdealPowerQuotientModule_isFiniteLength A (n + 1)⟩ :
          FiniteLengthModules.{u, v} A) ⟶
      (⟨maximalIdealPowerQuotientModule A n,
        maximalIdealPowerQuotientModule_isFiniteLength A n⟩ :
          FiniteLengthModules.{u, v} A) from
      ⟨highUniverseQuotientPowerSucc A (IsLocalRing.maximalIdeal A) (n + 1)⟩).op)

/-- Precomposition with `A/𝔪^(n+2) → A/𝔪^(n+1)` is the inclusion of torsion submodules of `E`. -/
theorem matlisPowerModuleIso_naturality
    (A : Type u) [CommRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) (n : ℕ) :
    let t := highUniverseQuotientPowerSucc A (IsLocalRing.maximalIdeal A) (n + 1)
    let d : ModuleCat.of A (maximalIdealPowerQuotientModule A n ⟶ E) ⟶
        ModuleCat.of A (maximalIdealPowerQuotientModule A (n + 1) ⟶ E) :=
      ModuleCat.ofHom {
        toFun := fun f => t ≫ f
        map_add' := by intro f g; exact Preadditive.comp_add _ _ _ _ f g
        map_smul' := by intro r f; exact Linear.comp_smul _ _ _ _ r f }
    d ≫ (matlisPowerModuleIso A E (n + 1)).hom =
      (matlisPowerModuleIso A E n).hom ≫
        ModuleCat.ofHom (Submodule.inclusion ((maximalIdealPowTorsionOrderHom A E).monotone
          (Nat.le_succ n))) := by
  intro t d
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change (t ≫ f) (ULift.up (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 2))) =
    f (ULift.up (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)))
  exact congrArg (fun x ↦ (show maximalIdealPowerQuotientModule A n ⟶ E from f) x)
    (highUniverseQuotientPowerSucc_apply_one A _ (n + 1))

/-- The sequence `n ↦ Hom_A(A/𝔪^(n+1), E)`, with the transition maps given by precomposition. -/
noncomputable def matlisPowerModuleFunctor
    (A : Type u) [CommRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) : ℕ ⥤ ModuleCat.{max v u} A :=
  Functor.ofSequence
    (X := fun n ↦ ModuleCat.of A (maximalIdealPowerQuotientModule A n ⟶ E))
    (fun n ↦ ModuleCat.ofHom {
      toFun := fun f ↦ highUniverseQuotientPowerSucc A
        (IsLocalRing.maximalIdeal A) (n + 1) ≫ f
      map_add' := by intro f g; exact Preadditive.comp_add _ _ _ _ f g
      map_smul' := by intro r f; exact Linear.comp_smul _ _ _ _ r f })

/-- The system `n ↦ Hom_A(A/𝔪^(n+1), E)` is the system of `𝔪^(n+1)`-torsion submodules of `E`. -/
noncomputable def matlisPowerModuleNatIso
    (A : Type u) [CommRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) :
    matlisPowerModuleFunctor A E ≅
      submoduleSequenceDiagram E (maximalIdealPowTorsionOrderHom A E) := by
  let t : matlisPowerModuleFunctor A E ⟶
      submoduleSequenceDiagram E (maximalIdealPowTorsionOrderHom A E) :=
    NatTrans.ofSequence (fun n ↦ (matlisPowerModuleIso A E n).hom)
    (fun n ↦ by
      change (matlisPowerModuleFunctor A E).map (homOfLE (Nat.le_succ n)) ≫
          (matlisPowerModuleIso A E (n + 1)).hom =
        (matlisPowerModuleIso A E n).hom ≫
          (submoduleSequenceDiagram E
            (maximalIdealPowTorsionOrderHom A E)).map (homOfLE (Nat.le_succ n))
      simp only [matlisPowerModuleFunctor, Functor.ofSequence_map_homOfLE_succ]
      exact matlisPowerModuleIso_naturality A E n)
  exact NatIso.ofComponents (matlisPowerModuleIso A E) (fun f ↦ t.naturality f)

/-- For an injective hull `E` of the residue field, `colim Hom_A(A/𝔪^(n+1), E) = E`. -/
noncomputable def matlisPowerModuleColimitIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    colimit (matlisPowerModuleFunctor A E) ≅ E := by
  let k := IsLocalRing.ResidueField A
  let e : k ≃ₗ[A] (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A k) :=
    (ULift.moduleEquiv : ULift.{v} k ≃ₗ[A] k).symm
  exact HasColimit.isoOfNatIso (matlisPowerModuleNatIso A E) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (maximalIdealPowTorsion_isColimit A _ E e i hi)

/-- The sequence `n ↦ Hom^•(A/I^(n+1)[0], J)` of Hom complexes out of the single complexes. -/
noncomputable def highUniverseHomPowersComplex
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{max v u} A) ℤ :=
  Functor.ofSequence
    (X := fun n ↦ CochainComplex.HomComplexR A
      (highUniverseQuotientSingle A (I ^ (n + 1))) J)
    (fun n ↦ Stacks.HomComplex.TensorHomMap.precomp A _ _ J
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).map
        (highUniverseQuotientPowerSucc A I (n + 1))))

/-- A homomorphism out of the universe-lifted quotient `A/I` is determined by its value at `1`. -/
private lemma highUniverseQuotientHom_ext
    (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{max v u} A)
    {f g : (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I)) ⟶ M}
    (h : f (ULift.up (1 : A ⧸ I)) = g (ULift.up 1)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := ULift.up_surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hq : (ULift.up (Ideal.Quotient.mk I a) : ULift.{v} (A ⧸ I)) =
      a • ULift.up (1 : A ⧸ I) := by
    apply ULift.ext
    simp [Algebra.smul_def]
  rw [hq]
  change f.hom (a • ULift.up (1 : A ⧸ I)) =
    g.hom (a • ULift.up (1 : A ⧸ I))
  exact (f.hom.map_smul a _).trans
    ((congrArg (fun y ↦ a • y) h).trans (g.hom.map_smul a _).symm)

/-- Evaluation of a cochain out of a single complex is linear in the cochain. -/
lemma fromSingleEquiv_smul {R : Type w} [Ring R]
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [CategoryTheory.Linear R C] {X : C} {K : CochainComplex C ℤ} {p q n : ℤ}
    (h : p + n = q) (r : R)
    (z : Cochain ((CochainComplex.singleFunctor C p).obj X) K n) :
    Cochain.fromSingleEquiv h (r • z) = r • Cochain.fromSingleEquiv h z := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p X).inv ≫
      (r • z).v p q h = _
  rw [Cochain.smul_v, Linear.comp_smul]
  rfl

/-- Evaluation at `1` of a cochain of degree `q` from the single complex on `A/I` to `J`. -/
noncomputable def highUniverseSingleEval
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q : ℤ) :
    Cochain (highUniverseQuotientSingle A I) J q →ₗ[A] J.X q where
  toFun z := (Cochain.fromSingleEquiv (zero_add q) z) (ULift.up 1)
  map_add' _ _ := by
    simp only [map_add]
    rfl
  map_smul' r z :=
    congrArg
      (fun g : (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I)) ⟶ J.X q ↦
        g (ULift.up 1))
      (fromSingleEquiv_smul (zero_add q) r z)

/-- Evaluation at `1` is injective on cochains out of the single complex on `A/I`. -/
lemma highUniverseSingleEval_injective
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q : ℤ) :
    Function.Injective (highUniverseSingleEval A I J q) := by
  intro x y h
  exact (Cochain.fromSingleEquiv (zero_add q)).injective (highUniverseQuotientHom_ext A I (J.X q) h)

/-- Evaluation at `1` of a cochain out of the single complex on `A/I` is `I`-torsion. -/
lemma highUniverseSingleEval_mem
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q : ℤ) (z) :
    highUniverseSingleEval A I J q z ∈
      Submodule.torsionBySet A (J.X q) (I : Set A) := by
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  change a.val • (Cochain.fromSingleEquiv (zero_add q) z) (ULift.up 1) = 0
  change a.val • ((Cochain.fromSingleEquiv (zero_add q) z).hom
    (ULift.up (1 : A ⧸ I))) = 0
  have h : a.val • (ULift.up (1 : A ⧸ I) : ULift.{v} (A ⧸ I)) = 0 := by
    apply ULift.ext
    simpa [Algebra.smul_def] using Ideal.Quotient.eq_zero_iff_mem.mpr a.property
  exact ((((Cochain.fromSingleEquiv (zero_add q) z).hom.map_smul a.val
        (ULift.up (1 : A ⧸ I))).symm.trans
      (congrArg (Cochain.fromSingleEquiv (zero_add q) z).hom h)).trans
    (Cochain.fromSingleEquiv (zero_add q) z).hom.map_zero)

/-- Every `I`-torsion element of `J^q` is the value at `1` of a cochain of degree `q`. -/
lemma highUniverseSingleEval_surjective
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q : ℤ) (x : J.X q)
    (hx : x ∈ Submodule.torsionBySet A (J.X q) (I : Set A)) :
    ∃ z, highUniverseSingleEval A I J q z = x := by
  let f : (A ⧸ I) →ₗ[A] J.X q := I.liftQ
    (LinearMap.toSpanSingleton A (J.X q) x)
    (fun r hr ↦ (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩)
  let g : (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (A ⧸ I)) ⟶ J.X q :=
    ModuleCat.ofHom (f.comp
      (ULift.moduleEquiv : ULift.{v} (A ⧸ I) ≃ₗ[A] A ⧸ I).toLinearMap)
  refine ⟨Cochain.fromSingleMk g (zero_add q), ?_⟩
  change (Cochain.fromSingleEquiv (zero_add q)
    (Cochain.fromSingleMk g (zero_add q))) (ULift.up 1) = x
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  change f (Submodule.Quotient.mk (1 : A)) = x
  exact one_smul A x

/-- Evaluation at `1` commutes with the differential of the Hom complex. -/
lemma highUniverseSingleEval_d
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q q' : ℤ) (z) :
    highUniverseSingleEval A I J q' (δ q q' z) =
      (J.d q q') (highUniverseSingleEval A I J q z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  rw [Cochain.δ_fromSingleMk _ _ _ q' (zero_add q')]
  change (Cochain.fromSingleEquiv (zero_add q')
    (Cochain.fromSingleMk (f ≫ J.d q q') (zero_add q'))) (ULift.up 1) =
    (J.d q q') ((Cochain.fromSingleEquiv (zero_add q)
      (Cochain.fromSingleMk f (zero_add q))) (ULift.up 1))
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  rfl

/-- Evaluation at `1` maps `Hom^•(A/I^(n+1)[0], J)` into the `I`-power-torsion subcomplex
of `J`. -/
noncomputable def highUniverseHomPowersToTorsion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℕ) :
    (highUniverseHomPowersComplex A I J).obj n ⟶
      ((powerTorsionModuleProperty A I
        (Ideal.fg_of_isNoetherianRing I)).ι.mapHomologicalComplex (.up ℤ)).obj
        (((powerTorsionFunctor A I).mapHomologicalComplex (.up ℤ)).obj J) where
  f q := ModuleCat.ofHom ((highUniverseSingleEval A (I ^ (n + 1)) J q).codRestrict _
    (fun z ↦ Submodule.mem_iSup_of_mem (n + 1)
      (highUniverseSingleEval_mem A (I ^ (n + 1)) J q z)))
  comm' q q' _ := ModuleCat.hom_ext (LinearMap.ext fun z ↦
    Subtype.ext (highUniverseSingleEval_d A (I ^ (n + 1)) J q q' z).symm)

/-- The evaluation maps are compatible with the transition maps of the system of Hom complexes. -/
lemma highUniverseHomPowersToTorsion_naturality
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℕ) :
    (highUniverseHomPowersComplex A I J).map (homOfLE (Nat.le_succ n)) ≫
      highUniverseHomPowersToTorsion A I J (n + 1) =
      highUniverseHomPowersToTorsion A I J n := by
  simp only [highUniverseHomPowersComplex, Functor.ofSequence_map_homOfLE_succ]
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  change highUniverseSingleEval A (I ^ (n + 2)) J q
      ((Cochain.ofHom ((CochainComplex.singleFunctor _ 0).map
        (highUniverseQuotientPowerSucc A I (n + 1)))).comp
        (Cochain.fromSingleMk f (zero_add q)) (zero_add q)) =
    highUniverseSingleEval A (I ^ (n + 1)) J q
      (Cochain.fromSingleMk f (zero_add q))
  rw [← Cochain.fromSingleMk_precomp]
  change (Cochain.fromSingleEquiv (zero_add q)
    (Cochain.fromSingleMk
      (highUniverseQuotientPowerSucc A I (n + 1) ≫ f) (zero_add q)))
      (ULift.up 1) =
    (Cochain.fromSingleEquiv (zero_add q)
      (Cochain.fromSingleMk f (zero_add q))) (ULift.up 1)
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact congrArg (fun x ↦ f x) (highUniverseQuotientPowerSucc_apply_one A I (n + 1))

/-- The cocone on `n ↦ Hom^•(A/I^(n+1)[0], J)` with vertex the `I`-power-torsion subcomplex
of `J`. -/
noncomputable def highUniverseHomPowersCocone
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    Cocone (highUniverseHomPowersComplex A I J) where
  pt := ((powerTorsionModuleProperty A I
    (Ideal.fg_of_isNoetherianRing I)).ι.mapHomologicalComplex (.up ℤ)).obj
      (((powerTorsionFunctor A I).mapHomologicalComplex (.up ℤ)).obj J)
  ι := NatTrans.ofSequence (highUniverseHomPowersToTorsion A I J)
    (fun n ↦ by
      change (highUniverseHomPowersComplex A I J).map
          (homOfLE (Nat.le_succ n)) ≫
          highUniverseHomPowersToTorsion A I J (n + 1) =
        highUniverseHomPowersToTorsion A I J n ≫ 𝟙 _
      simpa only [Category.comp_id] using
        highUniverseHomPowersToTorsion_naturality A I J n)

/-- The `I`-power-torsion subcomplex of `J` is the colimit of the Hom complexes out of the
single complexes on `A/I^(n+1)`. -/
noncomputable def highUniverseHomPowersCocone_isColimit
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    IsColimit (highUniverseHomPowersCocone A I J) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  letI : PreservesColimitsOfShape ℕ (forget (ModuleCat.{max v u} A)) :=
    highUniverse_forget_preservesSequentialColimits A
  letI := reflectsColimit_of_reflectsIsomorphisms
    (highUniverseHomPowersComplex A I J ⋙ HomologicalComplex.eval _ _ q)
    (forget (ModuleCat.{max v u} A))
  apply isColimitOfReflects (forget (ModuleCat.{max v u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (J.X q) I x.val).mp x.property
    have hn' : x.val ∈ Submodule.torsionBySet A (J.X q)
        ((I ^ (n + 1) : Ideal A) : Set A) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_succ n) I hn
    obtain ⟨z, hz⟩ := highUniverseSingleEval_surjective A (I ^ (n + 1)) J q x.val hn'
    exact ⟨n, z, Subtype.ext hz.symm⟩
  · intro n x y h
    have hxy : x = y := highUniverseSingleEval_injective A (I ^ (n + 1)) J q
      (congrArg Subtype.val h)
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

/-- The canonical comparison of the colimit with the `I`-power-torsion subcomplex of `J`. -/
noncomputable def highUniverseHomPowers_colimitIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    colimit (highUniverseHomPowersComplex A I J) ≅
      (highUniverseHomPowersCocone A I J).pt :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (highUniverseHomPowersCocone_isColimit A I J)

/-- Each cohomology module of local cohomology is the colimit of the cohomology modules of the
Hom complexes out of the single complexes on `A/I^(n+1)`. -/
noncomputable def highUniverseLocalCohomology_homologyIsoColimit
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj
        (highUniverseLocalCohomology A I J) ≅
      colimit (highUniverseHomPowersComplex A I J ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{max v u} A) (.up ℤ) q) := by
  let F := highUniverseHomPowersComplex A I J
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max v u} A) (.up ℤ) q
  letI : HasExactColimitsOfShape ℕ (ModuleCat.{max v u} A) :=
    highUniverse_hasExactSequentialColimits A
  letI : PreservesColimitsOfShape ℕ H :=
    Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) q
  exact (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    H.mapIso (highUniverseHomPowers_colimitIso A I J).symm ≪≫
      preservesColimitIso H F

end Dualizing.LocalDuality

end
