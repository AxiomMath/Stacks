module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The derived Spec–Γ counit on an affine scheme

Let `R` be a commutative ring. The counit of the canonical derived sheafification–sections
adjunction `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is invertible at every object
of `D_QCoh(𝒪_{Spec R})`: a complex of `𝒪_{Spec R}`-modules with quasi-coherent cohomology is
recovered from its derived global sections by derived sheafification.

The proof is a dévissage in cohomological degree, and it needs no essential surjectivity
statement. Three ingredients combine.

* **The pure case.** For a bounded below cochain complex `K` of *quasi-coherent*
  `𝒪_{Spec R}`-modules the comparison `Q(Γ(Spec R, K)) ⟶ RΓ(Spec R, Q(K))` is invertible
  (bounded below affine vanishing,
  `AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent`), and the
  degreewise sheafification–sections counit `Γ(Spec R, K)^∼ ⟶ K` is invertible because each term of
  `K` is quasi-coherent (Stacks 01I8, available as
  `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`). The normalization
  equation that defines the derived adjunction turns the two into invertibility of the derived
  counit at `Q(K)`. Taking `K` concentrated in one degree gives the case of a quasi-coherent
  module placed in a single degree.
* **The two truncation comparisons of Stacks 08D4.** For `E` with quasi-coherent cohomology,
  `Hⁱ(RΓ(τ_{≤ i}E)) ⟶ Hⁱ(RΓ(E))` and `Hⁱ(RΓ(τ_{≤ i}E)) ⟶ Hⁱ(RΓ(τ_{≥ i}τ_{≤ i}E))` are
  invertible, the second by Serre vanishing at `N = 1`. Derived sheafification is exact, so it
  carries these to isomorphisms on degree-`i` cohomology.
* **Naturality of the counit** along `τ_{≤ i}E ⟶ E` and `τ_{≤ i}E ⟶ τ_{≥ i}τ_{≤ i}E`. The
  degree-`i` cohomology of the counit at `E` is therefore invertible as soon as it is at the pure
  piece `τ_{≥ i}τ_{≤ i}E`, which is the first ingredient. A morphism of the derived category
  invertible on all cohomology is invertible.

## Main results

* `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso` — **Stacks 06Z0**, the
  counit clause.

## Implementation notes

The statement is taken at `CategoryTheory.HasDerivedCategory.standard` for the
`𝒪_{Spec R}`-modules, supplied explicitly to the free binder of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction`, and at a *free*
`[HasDerivedCategory.{w₂} (ModuleCat.{u} R)]` binder for the modules. The standard model is forced
on the sheaf side and only there: the upper half of Stacks 08D4
(`AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero`) rests on
the convergence statement Stacks 08D3, which is available at that model alone, while that result
leaves the model of its target category free. Since the preferred locally small model is a
*global* instance here, the standard one is unreachable by an instance attribute and is written
into the statement by a `let`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`.

`AlgebraicGeometry.tilde.adjunction` has `AlgebraicGeometry.moduleSpecΓFunctor` as its right
adjoint, and `AlgebraicGeometry.globalSectionsOver (𝟙 (Spec R))` is a different spelling of the
same functor — they are definitionally equal, which is what
`AlgebraicGeometry.moduleSpecΓIsoGlobalSectionsOver` records. The adjunction is restated at the
second spelling as `AlgebraicGeometry.tildeGlobalSectionsAdjunction` so that the functor recorded
in its type is the one the derived adjunction's normalization equation uses; without that, the
two sides of the equation differ by a reassociation that `rw` cannot see.

Serre vanishing enters as the hypothesis of Stacks 08D4 at `N = 1`, in the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` shape. It is obtained from the `ℕ`-indexed
`AlgebraicGeometry.isZero_rightDerived_globalSectionsOver_of_isQuasicoherent` through the
comparison `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` of the two indexings.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace AlgebraicGeometry

section Generic

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)

/-- Transporting invertibility of a counit along an isomorphism. -/
private lemma isIso_counit_app_of_iso {A B : D} (e : A ≅ B)
    (h : IsIso (adj.counit.app B)) : IsIso (adj.counit.app A) :=
  IsIso.of_isIso_fac_right (adj.counit.naturality e.hom).symm

/-- The naturality square of a counit, read through a functor. -/
private lemma map_counit_naturality {E : Type*} [Category E] (H : D ⥤ E) {A B : D} (f : A ⟶ B) :
    H.map (adj.counit.app A) ≫ H.map f =
      H.map ((G ⋙ L).map f) ≫ H.map (adj.counit.app B) := by
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (adj.counit.naturality f).symm

end Generic

private lemma counit_compatibility_of_unit
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    {G : A ⥤ B} {F : B ⥤ A} (adj : G ⊣ F)
    {LG : DA ⥤ DB} {RF : DB ⥤ DA} (adjD : LG ⊣ RF)
    (QA : A ⥤ DA) (QB : B ⥤ DB)
    (e : QA ⋙ LG ≅ G ⋙ QB) (β : F ⋙ QA ⟶ QB ⋙ RF)
    (h : ∀ M, adjD.unit.app (QA.obj M) ≫ RF.map (e.hom.app M) =
      QA.map (adj.unit.app M) ≫ β.app (G.obj M)) (K : B) :
    LG.map (β.app K) ≫ adjD.counit.app (QB.obj K) =
      e.hom.app (F.obj K) ≫ QB.map (adj.counit.app K) := by
  apply (adjD.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  calc
    _ = β.app K := by
      simp only [Functor.map_comp, ← Category.assoc, adjD.unit_naturality]
      simp [Category.assoc]
    _ = (QA.map (adj.unit.app (F.obj K)) ≫ β.app (G.obj (F.obj K))) ≫
        RF.map (QB.map (adj.counit.app K)) := by
      have hn := β.naturality (adj.counit.app K)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [Category.assoc, ← hn]
      simp [← QA.map_comp, ← Category.assoc]
    _ = _ := by
      rw [← h]
      simp [Functor.map_comp, Category.assoc]

section Affine

variable (R : CommRingCat.{u})

/-- Sheafification is left adjoint to `R`-linear global sections over `Spec R`. -/
private def tildeGlobalSectionsAdjunction :
    tilde.functor R ⊣ globalSectionsOver (𝟙 (Spec R)) :=
  tilde.adjunction

private lemma tildeGlobalSectionsComplexUnit_eq :
    tildeGlobalSectionsComplexUnit R =
      ((tildeGlobalSectionsAdjunction R).mapHomologicalComplex (ComplexShape.up ℤ)).unit := by
  apply NatTrans.ext
  funext M
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp [tildeGlobalSectionsComplexUnit, Adjunction.mapHomologicalComplex,
    tildeGlobalSectionsAdjunction, moduleSpecΓIsoGlobalSectionsOver]
  exact Category.comp_id ((tilde.adjunction (R := R)).unit.app (M.X n))

private lemma counit_degreewise_isIso (K : CochainComplex (Spec R).Modules ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso (((tildeGlobalSectionsAdjunction R).mapHomologicalComplex
      (ComplexShape.up ℤ)).counit.app K) := by
  have (n : ℤ) : IsIso ((((tildeGlobalSectionsAdjunction R).mapHomologicalComplex
      (ComplexShape.up ℤ)).counit.app K).f n) := by
    have := hqc n
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

variable [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- The counit of the derived adjunction at `Q(K)` is invertible as soon as the comparison from
termwise to derived global sections is invertible at `K` and the degreewise counit is. -/
private lemma isIso_counit_app_Q
    (K : CochainComplex (Spec R).Modules ℤ)
    (hβ : IsIso ((globalSectionsComplexComparisonNatTrans (𝟙 (Spec R))).app K))
    (hc : IsIso (((tildeGlobalSectionsAdjunction R).mapHomologicalComplex
      (ComplexShape.up ℤ)).counit.app K)) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
      (DerivedCategory.Q.obj K)) :=
  IsIso.of_isIso_fac_left (counit_compatibility_of_unit
    ((tildeGlobalSectionsAdjunction R).mapHomologicalComplex (ComplexShape.up ℤ))
    (derivedTildeGlobalSectionsAdjunction R).val DerivedCategory.Q DerivedCategory.Q
    (derivedTildeFactors R) (globalSectionsComplexComparisonNatTrans (𝟙 (Spec R)))
    (fun M ↦ by
      rw [globalSectionsComplexComparisonNatTrans_app, ← tildeGlobalSectionsComplexUnit_eq]
      exact (derivedTildeGlobalSectionsAdjunction R).property M) K)

/-- **The derived Spec–Γ counit is invertible on a quasi-coherent module placed in a single
degree.** -/
private lemma isIso_counit_app_singleFunctor (M : (Spec R).Modules)
    (hM : M.IsQuasicoherent) (n : ℤ) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
      ((DerivedCategory.singleFunctor (Spec R).Modules n).obj M)) := by
  refine isIso_counit_app_of_iso _
    ((DerivedCategory.singleFunctorIsoCompQ (Spec R).Modules n).app M) ?_
  have hqc : ∀ i : ℤ,
      (((CochainComplex.singleFunctor (Spec R).Modules n).obj M).X i).IsQuasicoherent := by
    intro i
    by_cases hi : i = n
    · subst hi
      exact isQuasicoherent_of_iso (Spec R) M _
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).symm) hM
    · exact isQuasicoherent_of_isZero (Spec R) _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M i hi)
  refine isIso_counit_app_Q R _ ?_ (counit_degreewise_isIso R _ hqc)
  rw [globalSectionsComplexComparisonNatTrans_app]
  exact isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent (𝟙 (Spec R)) _
    ⟨n, inferInstance⟩ hqc

/-- Derived sheafification turns a morphism of `D(R)` invertible on degree-`i` cohomology into
one invertible on degree-`i` cohomology: `~` is exact, so it commutes with cohomology. -/
private lemma isIso_homologyFunctor_map_derivedTilde_map
    {M N : DerivedCategory (ModuleCat.{u} R)} (g : M ⟶ N) (i : ℤ)
    (hg : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map g)) :
    IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map
      ((derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).map g)) := by
  have hmid : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map
      ((tilde.functor R).mapDerivedCategory.map g)) := by
    have hnat := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (tilde.functor R) i).hom.naturality g
    dsimp only [Functor.comp_map] at hnat
    exact IsIso.of_isIso_fac_right hnat
  have hcompι := (derivedTildeCompι R).hom.naturality g
  dsimp only [Functor.comp_map] at hcompι
  have heq : (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).map g =
    (derivedTildeCompι R).hom.app M ≫ (tilde.functor R).mapDerivedCategory.map g ≫
      (derivedTildeCompι R).inv.app N := by
    rw [← Category.assoc, ← hcompι]
    simp [Functor.comp_map]
  rw [heq, Functor.map_comp, Functor.map_comp]
  infer_instance


/-- Along a morphism `f` of `D(𝒪_{Spec R})` that is invertible on degree-`i` cohomology and whose
derived global sections are too, the degree-`i` cohomology of the derived counit is invertible at
the source if and only if it is at the target. -/
private lemma isIso_homologyFunctor_map_counit_iff
    {A B : DerivedCategory (Spec R).Modules} (f : A ⟶ B) (i : ℤ)
    (hRG : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).map f)))
    (hf : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map f)) :
    IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map
        ((derivedTildeGlobalSectionsAdjunction R).val.counit.app A)) ↔
      IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map
        ((derivedTildeGlobalSectionsAdjunction R).val.counit.app B)) := by
  have : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules i).map
      ((derivedGlobalSectionsOver (𝟙 (Spec R)) ⋙ (derivedTilde R ⋙
        (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι)).map f)) :=
    isIso_homologyFunctor_map_derivedTilde_map R _ i hRG
  have hsq := map_counit_naturality (derivedTildeGlobalSectionsAdjunction R).val
    (DerivedCategory.homologyFunctor (Spec R).Modules i) f
  dsimp only [Functor.id_obj] at hsq
  exact ⟨fun h ↦ IsIso.of_isIso_fac_left hsq.symm, fun h ↦ IsIso.of_isIso_fac_right hsq⟩


/-- Serre vanishing in the form Stacks 08D4's upper half asks for: the higher right derived
functors of `R`-linear global sections vanish on a quasi-coherent `𝒪_{Spec R}`-module. -/
private lemma isZero_rightDerivedPlus_globalSectionsOver (M : (Spec R).Modules)
    (hM : M.IsQuasicoherent) (p : ℤ) (hp : (1 : ℤ) ≤ p) :
    IsZero (((globalSectionsOver (𝟙 (Spec R))).rightDerivedPlus p).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl _).2 ?_
  exact isZero_rightDerived_globalSectionsOver_of_isQuasicoherent (𝟙 (Spec R)) M n (by omega)

/-- The derived Spec–Γ counit is invertible at the pure piece `τ_{≥ i} τ_{≤ i} F` whenever its
degree-`i` cohomology is quasi-coherent. -/
private lemma isIso_counit_app_truncGE_truncLE (F : DerivedCategory (Spec R).Modules) (i : ℤ)
    (hF : ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE i).obj
        ((DerivedCategory.TStructure.t.truncLE i).obj F))).IsQuasicoherent) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
      ((DerivedCategory.TStructure.t.truncGE i).obj
        ((DerivedCategory.TStructure.t.truncLE i).obj F))) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((DerivedCategory.TStructure.t.truncGE i).obj
      ((DerivedCategory.TStructure.t.truncLE i).obj F)) i
  refine isIso_counit_app_of_iso _ e (isIso_counit_app_singleFunctor R M ?_ i)
  exact isQuasicoherent_of_iso (Spec R) _ M
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (Spec R).Modules i).app M)
    hF

end Affine

/-- **Stacks 06Z0, the counit clause.** On an affine scheme the counit of the canonical derived
sheafification–sections adjunction is invertible at every object of `D_QCoh(𝒪_{Spec R})`: derived
sheafification recovers a complex with quasi-coherent cohomology from its derived global
sections. -/
@[stacks 06Z0 "canonical counit isomorphism"]
theorem derivedTildeGlobalSectionsAdjunction_counit_isIso (R : CommRingCat.{u})
    [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory,
      IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj E)) := by
  intro inst E
  have hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules j).obj
      E.obj).IsQuasicoherent := E.property
  rw [DerivedCategory.isIso_iff]
  intro i
  have hE' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules j).obj
      ((DerivedCategory.TStructure.t.truncLE i).obj E.obj)).IsQuasicoherent :=
    fun j ↦ isQuasicoherent_homology_truncLE (Spec R) E.obj hE i j
  have hRG_ι : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).map
        ((DerivedCategory.TStructure.t.truncLEι i).app E.obj))) :=
    -- The derived category of the `𝒪_{Spec R}`-modules is named by `inst`, at the spelling
    -- `AlgebraicGeometry.Scheme.Modules`; [Stacks, Tag 08D4] asks for it at the spelling
    -- `SheafOfModules …`, which instance search will not cross, so `inst` is handed over by
    -- name and the crossing is left to unification.
    @isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι (Spec R) _ _ _ inst _
      (globalSectionsOver (𝟙 (Spec R)))
      (inferInstanceAs (globalSectionsOver (𝟙 (Spec R))).Additive)
      (derivedGlobalSectionsOver (𝟙 (Spec R)))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec R)))
      (derivedGlobalSectionsOver_isRightDerivedFunctor (𝟙 (Spec R))) E.obj hE i i le_rfl
  have hι := isIso_homology_truncLE E.obj i i le_rfl
  refine (isIso_homologyFunctor_map_counit_iff R _ i hRG_ι hι).1 ?_
  have := isIso_counit_app_truncGE_truncLE R E.obj i
    (isQuasicoherent_homology_truncGE (Spec R) _ hE' i i)
  have hRG : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).map
        ((DerivedCategory.TStructure.t.truncGEπ i).app
          ((DerivedCategory.TStructure.t.truncLE i).obj E.obj)))) := by
    have h := isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero (Spec R)
      (globalSectionsOver (𝟙 (Spec R))) (derivedGlobalSectionsOver (𝟙 (Spec R)))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec R))) 1
      (fun M hM p hp ↦
        isZero_rightDerivedPlus_globalSectionsOver R M hM p (by exact_mod_cast hp))
      ((DerivedCategory.TStructure.t.truncLE i).obj E.obj) hE' i i le_rfl
    rwa [show i - ((1 : ℕ) : ℤ) + 1 = i by omega] at h
  have := isIso_homology_truncGE ((DerivedCategory.TStructure.t.truncLE i).obj E.obj) i i le_rfl
  exact (isIso_homologyFunctor_map_counit_iff R _ i hRG this).2 inferInstance

end AlgebraicGeometry

end
