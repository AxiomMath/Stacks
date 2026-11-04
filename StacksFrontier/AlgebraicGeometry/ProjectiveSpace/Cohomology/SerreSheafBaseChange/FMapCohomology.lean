module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.CechRefinement

/-!
# Homology representatives and the cohomology map of an `f`-map

Representatives of homology classes by cochains, and `Stacks.Cohomology.CechIso.fMapCohomology`,
the map `Hᵖ(Y, 𝒢) → Hᵖ(X, ℱ)` attached to a morphism of schemes and an `f`-map, on Čech cochains.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 5000] IsGrothendieckAbelian.enoughInjectives
attribute [local instance 5000]
  instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover

namespace Stacks.Homology.HomologyRep

/-- A homology class `h` is represented by the cochain `v`: some cycle with class `h` has
underlying cochain `v`. -/
def Rep {A : Type u} [Ring A] {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (ModuleCat.{u} A) c) (q : κ) (h : K.homology q) (v : K.X q) : Prop :=
  ∃ z : K.cycles q, ConcreteCategory.hom (K.homologyπ q) z = h ∧
    ConcreteCategory.hom (K.iCycles q) z = v

variable {A : Type u} [Ring A] {κ : Type*} {c : ComplexShape κ}
  {K L : HomologicalComplex (ModuleCat.{u} A) c} {q : κ}

/-- Every homology class is represented. -/
theorem exists_rep (h : K.homology q) : ∃ v, Rep K q h v := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).1 inferInstance h
  exact ⟨_, z, rfl, rfl⟩

/-- A cochain represents at most one class. -/
theorem rep_unique {h h' : K.homology q} {v : K.X q} (H : Rep K q h v) (H' : Rep K q h' v) :
    h = h' := by
  obtain ⟨z, rfl, hz⟩ := H
  obtain ⟨z', rfl, hz'⟩ := H'
  rw [(ModuleCat.mono_iff_injective (K.iCycles q)).1 inferInstance (hz.trans hz'.symm)]

/-- Representatives are transported along a morphism of complexes. -/
theorem rep_map (M : K ⟶ L) {h : K.homology q} {v : K.X q} (H : Rep K q h v) :
    Rep L q (ConcreteCategory.hom (HomologicalComplex.homologyMap M q) h)
      (ConcreteCategory.hom (M.f q) v) := by
  obtain ⟨z, rfl, rfl⟩ := H
  exact ⟨ConcreteCategory.hom (HomologicalComplex.cyclesMap M q) z,
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality M q) z).symm,
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i M q) z⟩

/-- A cocycle represents a class. -/
theorem exists_rep_of_d_eq_zero (v : K.X q) (hv : ConcreteCategory.hom (K.d q (c.next q)) v = 0) :
    ∃ h, Rep K q h v := by
  refine ⟨ConcreteCategory.hom (K.homologyπ q)
    (ConcreteCategory.hom (K.sc q).moduleCatCyclesIso.inv ⟨v, hv⟩), _, rfl, ?_⟩
  exact ConcreteCategory.congr_hom (K.sc q).moduleCatCyclesIso_inv_iCycles ⟨v, hv⟩

/-- A representing cochain is a cocycle. -/
theorem rep_d_eq_zero {h : K.homology q} {v : K.X q} (H : Rep K q h v) (j : κ) :
    ConcreteCategory.hom (K.d q j) v = 0 := by
  obtain ⟨z, -, rfl⟩ := H
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
  rfl

/-- A cochain whose image under a morphism of complexes, injective in the next degree, is a
cocycle is itself a cocycle. -/
theorem d_eq_zero_of_map (M : K ⟶ L) (j : κ)
    (hM : Function.Injective (ConcreteCategory.hom (M.f j)))
    (v : K.X q) (hv : ConcreteCategory.hom (L.d q j) (ConcreteCategory.hom (M.f q) v) = 0) :
    ConcreteCategory.hom (K.d q j) v = 0 := by
  refine hM ?_
  rw [map_zero, ← ConcreteCategory.comp_apply, ← M.comm, ConcreteCategory.comp_apply, hv]

variable {B : Type u} [Ring B] (φ : B →+* A)

/-- Representatives are transported along the identification of homology with restriction of
scalars. -/
theorem rep_restrictScalarsHomologyIso_hom {K : CochainComplex (ModuleCat.{u} A) ℕ} {q : ℕ}
    {h : (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).homology q} {v : K.X q}
    (H : Rep (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
      q h v) :
    Rep K q (ConcreteCategory.hom
      (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso φ K q).hom h) v := by
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars.{u} φ
  obtain ⟨z, rfl, rfl⟩ := H
  exact ⟨ConcreteCategory.hom ((K.sc q).mapCyclesIso (ModuleCat.restrictScalars.{u} φ)).hom z,
    (ConcreteCategory.congr_hom (Stacks.Homology.mapHomologyIso_homologyπ (K.sc q)
      (ModuleCat.restrictScalars.{u} φ)) z).symm,
    ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (K.sc q)
      (ModuleCat.restrictScalars.{u} φ)) z⟩

/-- Representatives are transported along the inverse identification of homology with restriction
of scalars. -/
theorem rep_restrictScalarsHomologyIso_inv {K : CochainComplex (ModuleCat.{u} A) ℕ} {q : ℕ}
    {h : K.homology q} {v : K.X q} (H : Rep K q h v) :
    Rep (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) q
      (ConcreteCategory.hom
        (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso φ K q).inv h) v := by
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars.{u} φ
  obtain ⟨z, rfl, rfl⟩ := H
  set e := (K.sc q).mapCyclesIso (ModuleCat.restrictScalars.{u} φ)
  have hπ := ConcreteCategory.congr_hom (Stacks.Homology.mapHomologyIso_homologyπ (K.sc q)
      (ModuleCat.restrictScalars.{u} φ)) (ConcreteCategory.hom e.inv z)
  have hi := ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (K.sc q)
      (ModuleCat.restrictScalars.{u} φ)) (ConcreteCategory.hom e.inv z)
  have hez := e.inv_hom_id_apply z
  refine ⟨ConcreteCategory.hom e.inv z, ?_,
    ((ConcreteCategory.comp_apply _ _ _).symm.trans hi).symm.trans ?_⟩
  · refine ((Iso.hom_inv_id_apply
      (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso φ K q) _).symm.trans ?_)
    exact congrArg (ConcreteCategory.hom
      (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso φ K q).inv)
      (((ConcreteCategory.comp_apply _ _ _).symm.trans hπ).trans
        ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hez)))
  · exact (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hez)

end Stacks.Homology.HomologyRep

namespace Stacks.Cohomology.CechIso

open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The map on cohomology attached to an `f`-map**, `H^q(Y, G) ⟶ H^q(X, F)` for a morphism of
schemes `g : X ⟶ Y` and `φ : g^* G ⟶ F`, the target read over `Γ(Y, 𝒪_Y)`: the map of
[Stacks, Tag 01FA], read on the cohomology groups as right derived functors of global
sections. -/
def fMapCohomology (F : X.Modules) (G : Y.Modules)
    (φ : (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj G ⟶ F) (q : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor Y ⊤).rightDerived q).obj G ⟶
      (Stacks.Cohomology.restrictGlobalScalars g.toLRSHom.toShHom).obj
        (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived q).obj F) :=
  (Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor Y ⊤) q).hom.app G ≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      (Stacks.Cohomology.derivedModuleGlobalSectionsMap g.toLRSHom.toShHom φ) ≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Stacks.Cohomology.derivedSectionsScalarComparison g.toLRSHom.toShHom).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (Stacks.Cohomology.restrictGlobalScalars g.toLRSHom.toShHom) (q : ℤ)).hom.app _ ≫
    (Stacks.Cohomology.restrictGlobalScalars g.toLRSHom.toShHom).map
      ((Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor X ⊤) q).inv.app F)

variable {Ix Jy : Type u} (U : Ix → X.Opens) (V : Jy → Y.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hV : (⊤ : Y.Opens) = ⨆ j, V j)
  (haffU : ∀ (r : ℕ) (s : Fin (r + 1) → Ix), IsAffineOpen (⨅ k, U (s k)))
  (haffV : ∀ (r : ℕ) (s : Fin (r + 1) → Jy), IsAffineOpen (⨅ k, V (s k)))
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
  (φ : (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj G ⟶ F)
  (c : Ix → Jy) (hc : ∀ i, U i ≤ (Opens.map g.toLRSHom.toShHom.hom.base).obj (V (c i)))

/-- **The map on cohomology attached to an `f`-map is the map induced by the Čech refinement
map**, through the identifications of [Stacks, Tag 01XD] of sheaf cohomology with the homology of
the Čech complexes of coverings with affine finite intersections. -/
theorem fMapCohomology_comp_cechHomologyIsoRightDerived (q : ℕ) :
    fMapCohomology g F G φ q ≫
        (Stacks.Cohomology.restrictGlobalScalars g.toLRSHom.toShHom).map
          (cechHomologyIsoRightDerived X ⊤ U hU haffU F q).hom =
      (cechHomologyIsoRightDerived Y ⊤ V hV haffV G q).hom ≫
        HomologicalComplex.homologyMap
          (Stacks.Cohomology.CechRefinement.cechComplexRefinementMap g.toLRSHom.toShHom F G φ
            U V hU hV c hc) q ≫
        (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso
          (Stacks.Cohomology.globalSectionsRingHom g.toLRSHom.toShHom).hom
          (cechComplex.{u, u, u, u} (⊤ : X.Opens) U hU F) q).hom := by
  have hY := Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen Y ⊤ V hV
    haffV G q
  have hX := Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen X ⊤ U hU
    haffU F q
  exact Stacks.DerivedFunctor.final_paste _ _ _ (@asIso _ _ _ _ _ hY).inv _ _ _ _ _ _
    (@asIso _ _ _ _ _ hX).inv _ _ _ _
    (Stacks.Cohomology.CechRefinement.cechCohomologyToCohomology_comp_derivedModuleGlobalSectionsMap
      g.toLRSHom.toShHom U V hU hV F G φ c hc q)
    (@asIso _ _ _ _ _ hY).inv_hom_id (@asIso _ _ _ _ _ hX).hom_inv_id
    ((Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor X ⊤)
        q).inv_hom_id_app F)

section Ordered

open Stacks.Homology.HomologyRep

variable {I : Type u} [LinearOrder I] (U' : I → X.Opens) (V' : I → Y.Opens)
  (hU' : (⊤ : X.Opens) = ⨆ i, U' i) (hV' : (⊤ : Y.Opens) = ⨆ j, V' j)
  (haffU' : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U' (s k)))
  (haffV' : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, V' (s k)))
  (hc' : ∀ i, U' i ≤ (Opens.map g.toLRSHom.toShHom.hom.base).obj (V' i))

/-- **The map on cohomology attached to an `f`-map, on ordered Čech representatives.** If the
ordered Čech class of a cohomology class on `Y` is represented by `v`, the ordered Čech class of
its image on `X` is represented by the ordered Čech refinement of `v`. -/
theorem rep_fMapCohomology (q : ℕ)
    (x : ((Stacks.Cohomology.sectionsFunctor Y ⊤).rightDerived q).obj G)
    (v : (orderedModuleComplex (⊤ : Y.Opens) V' hV' G).X q)
    (H : Rep (orderedModuleComplex (⊤ : Y.Opens) V' hV' G) q
      (ConcreteCategory.hom (orderedCechHomologyModuleIso (⊤ : Y.Opens) V' hV' G q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerived Y ⊤ V' hV' haffV' G q).hom x)) v) :
    Rep (orderedModuleComplex (⊤ : X.Opens) U' hU' F) q
      (ConcreteCategory.hom (orderedCechHomologyModuleIso (⊤ : X.Opens) U' hU' F q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerived X ⊤ U' hU' haffU' F q).hom
          (ConcreteCategory.hom (fMapCohomology g F G φ q) x)))
      (Stacks.Cohomology.CechRefinement.refineOrd g.toLRSHom.toShHom F G φ U' V' hc' v) := by
  have e1 : ConcreteCategory.hom (HomologicalComplex.homologyMap
      (orderedToCechComplex (⊤ : Y.Opens) V' hV' G) q)
      (ConcreteCategory.hom (orderedCechHomologyModuleIso (⊤ : Y.Opens) V' hV' G q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerived Y ⊤ V' hV' haffV' G q).hom x)) =
      ConcreteCategory.hom (cechHomologyIsoRightDerived Y ⊤ V' hV' haffV' G q).hom x :=
    (ConcreteCategory.congr_hom
      (orderedCechHomologyModuleIso_hom (⊤ : Y.Opens) V' hV' G q).symm _).trans
      (Iso.inv_hom_id_apply _ _)
  have H1 := e1 ▸ rep_map (orderedToCechComplex (⊤ : Y.Opens) V' hV' G) H
  have H2 := (Stacks.Cohomology.CechRefinement.refinementMap_orderedToCechComplex
    g.toLRSHom.toShHom F G φ U' V' hU' hV' hc' v) ▸
    rep_map (Stacks.Cohomology.CechRefinement.cechComplexRefinementMap g.toLRSHom.toShHom
      F G φ U' V' hU' hV' id hc') H1
  have H3 := rep_restrictScalarsHomologyIso_hom _ H2
  have h5 := ConcreteCategory.congr_hom
    (fMapCohomology_comp_cechHomologyIsoRightDerived g U' V' hU' hV' haffU' haffV' F G φ id hc' q) x
  have hd : ConcreteCategory.hom ((orderedModuleComplex (⊤ : X.Opens) U' hU' F).d q
      ((ComplexShape.up ℕ).next q))
      (Stacks.Cohomology.CechRefinement.refineOrd g.toLRSHom.toShHom F G φ U' V' hc' v) = 0 :=
    d_eq_zero_of_map (orderedToCechComplex (⊤ : X.Opens) U' hU' F) _
      (orderedToCechComplex_f_injective _ _ _ _ _) _ (rep_d_eq_zero H3 _)
  obtain ⟨o', Ho'⟩ := exists_rep_of_d_eq_zero _ hd
  have H4 := rep_map (orderedToCechComplex (⊤ : X.Opens) U' hU' F) Ho'
  have he := (orderedCechHomologyModuleIso_hom (⊤ : X.Opens) U' hU' F q).symm ▸ rep_unique H4 H3
  have ho : o' = ConcreteCategory.hom (orderedCechHomologyModuleIso (⊤ : X.Opens) U' hU' F q).inv
      (ConcreteCategory.hom (cechHomologyIsoRightDerived X ⊤ U' hU' haffU' F q).hom
        (ConcreteCategory.hom (fMapCohomology g F G φ q) x)) := by
    refine (Iso.hom_inv_id_apply (orderedCechHomologyModuleIso (⊤ : X.Opens) U' hU' F q)
      o').symm.trans ?_
    exact congrArg (ConcreteCategory.hom (orderedCechHomologyModuleIso (⊤ : X.Opens) U' hU' F
      q).inv) (he.trans h5.symm)
  exact ho ▸ Ho'

end Ordered

end Stacks.Cohomology.CechIso

end
