module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoClass
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TopDegreePairingCount

/-!
# The base case of the derived Poincaré duality of Tag 03VM

For a member `i = (M, I)` of the Poincaré family and an injective resolution `K₀` of `j_! μ_n`,
`n = #Λ`, the top-degree pairing `H²(Γ^Gal(I)) × H⁰(Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))) → ℚ/ℤ` of the
Poincaré pairing is perfect, so that `H²` of its chain map is an isomorphism (the base case `hbase`
of `AlgebraicGeometry.quasiIso_poincarePairing`).

On classes of cocycles `x` of `Γ(X̄_k̄, I|)` and `β` of `Γ^Gal(ℋom^•(I, K))`, the pairing is
`tr(H²_c(θ_β)(x))`: the cocycle `⟨x, β⟩` is the image of `x` under the morphism of complexes of
`β` (`Stacks.EtaleCohomology.galoisHomOpCocycleAct_ΓRes`), which computes `H²_c` of the map `θ_β`
it lies over
(`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso_homologyπ_eq_restrictScalarsMapOfBar`),
and `tr ∘ H²_c(θ)` is the degree-zero pairing with the restriction of `θ` to `X_k̄`
(`AlgebraicGeometry.compactSupportCyclotomicTrace_restrictScalarsMapOfBar`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius Opposite

universe u

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

/-- `#Λ ≠ 0` for a finite ring. -/
local instance neZero_fintypeCard_poincareBase (Λ : Type) [Ring Λ] [Fintype Λ] :
    NeZero (Fintype.card Λ) :=
  ⟨Fintype.card_ne_zero⟩

private lemma ΓRes_globalSections_map_apply {Y : Scheme.{u}} {R : Type} [Ring R]
    {F G : EtaleModules.{u, 0} R Y} (φ : F ⟶ G) (U : Y.Etaleᵒᵖ)
    (t : (etaleModuleGlobalSections.{u, 0} R Y).obj F) :
    (G.ΓRes U).hom (((etaleModuleGlobalSections.{u, 0} R Y).map φ).hom t) =
      (φ.hom.app U).hom ((F.ΓRes U).hom t) :=
  ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality φ U) t

private lemma ΓRes_globalSectionsRestrictScalars_apply {Y : Scheme.{u}} {R : Type} [Ring R]
    (M : EtaleModules.{u, 0} R Y) (U : Y.Etaleᵒᵖ)
    (t : (etaleModuleGlobalSections.{u, 0} R Y).obj M) :
    (((etaleModuleRestrictScalars (Int.castRingHom R) Y).obj M).ΓRes U).hom
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom R) Y).hom.app M).hom t) =
      (M.ΓRes U).hom t :=
  congrArg (fun φ => φ.hom t)
    (etaleModuleGlobalSectionsRestrictScalars_hom_app_ΓRes (Int.castRingHom R) M U)

/-- `a ≫ b = s ≫ c ≫ e⁻¹` gives `a ≫ b ≫ e = s ≫ c`. -/
private lemma augmentation_iso_chase {C : Type*} [Category* C] {A B D E F : C} (a : A ⟶ B)
    (b : B ⟶ D) (e : E ≅ D) (s : A ⟶ F) (c : F ⟶ E) (h : a ≫ b = s ≫ c ≫ e.hom) :
    a ≫ b ≫ e.inv = s ≫ c := by
  rw [← Category.assoc, h]
  simp

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))))
  [K₀.cocomplex.IsStrictlyGE 0]

omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Algebra (ZMod (Fintype.card Λ)) Λ]
  [K₀.cocomplex.IsStrictlyGE 0] in
/-- **On sections, the morphism of complexes of a cocycle `β` is the pairing with `β`**, read
in `res_ℤ(K₀|_{X̄_k̄})` through `(res_ℤ K₀)| ≅ res_ℤ(K₀|)`. -/
theorem globalSections_map_galoisHomOpCocycleAct_glue (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (β : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).X 0).obj.obj.V)
    (hβ : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).d 0 1).hom.hom.hom.hom β = 0)
    (a : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex).X 2).obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    ((etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)).map
        ((galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) β hβ ≫
          (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).hom).f 2)).hom
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ)
          (fieldBaseChange (Over.mk j.toBase) kbar)).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj (i.I.cocomplex.X 2))).hom a) =
      ((etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)).map
        (inverseImageRestrictScalarsApp (Int.castRingHom (ZMod (Fintype.card Λ)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar) (K₀.cocomplex.X 2))).hom
        (galoisHomOpPair (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) 2 0 2 (zero_add 2) a β) := by
  let := connectedSpace_of_isCurve B X f
  refine ΓRes_etaleMkId_injective ℤ _ (((ΓRes_globalSections_map_apply _ _ _).trans ?_).trans
    (ΓRes_globalSections_map_apply _ _ _).symm)
  refine (congrArg (fun w => (((galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) β hβ ≫
      (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).hom).f 2).hom.app
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk j.toBase) kbar))))).hom w)
    (ΓRes_globalSectionsRestrictScalars_apply _ _ a)).trans ?_
  rw [HomologicalComplex.comp_f]
  have h := galoisHomOpCocycleAct_ΓRes (Over.mk j.toBase) kbar i.I.cocomplex
    (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) β hβ 2 a
  exact congrArg (fun w => ((galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar
    K₀.cocomplex).hom.f 2).hom.app
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk j.toBase) kbar)))) w) h

/-- **The cocycle action lies over `θ_β`**, as morphisms of bounded below complexes: the restricted
augmentation of `I` followed by the action of `β` is `θ_β[0]` followed by that of `K₀`. -/
theorem compactSupportResolutionIntAugmentation_comp_poincareAct
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (z : letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportResolutionIntAugmentation kbar ((representationSheaf B X _ Λ).obj i.M) i.I ≫
        ObjectProperty.homMk (galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) _
            (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z) ≫
          (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).hom) =
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
          (poincareCocycleH0 B X f kbar Λ y j K₀ i _
            (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)) ≫
        compactSupportResolutionIntAugmentation kbar _ K₀ := by
  let := connectedSpace_of_isCurve B X f
  have := quasiIso_poincareAugmentationL B X f kbar Λ y j i
  have := quasiIso_poincareAugmentationK B X f kbar Λ y j K₀
  have := isStrictlyGE_galoisBaseChangeComplex_poincare B X f kbar Λ y j i
  have := isStrictlyGE_galoisBaseChangeComplex_cyclotomic B X f kbar Λ y j K₀
  have h := augmentation_comp_galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
    (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)
    (poincareAugmentationL B X f kbar Λ y j i) (poincareAugmentationK B X f kbar Λ y j K₀) _
    (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)
  exact ObjectProperty.hom_ext _ (augmentation_iso_chase _ _
    (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).symm _ _ h)

/-- **The class of the pairing with a cocycle, in `H²_c(X_k̄, ℱ_μ)`**: for a degree-two cycle `x`
of `Γ^Gal(I)` and a degree-zero cycle `z` of `Γ^Gal(ℋom^•(I, K))`, the class of the cocycle
`⟨x, z⟩` of `Γ(X̄_k̄, K₀|)` is the image of the class of `x` under the map induced by `θ_z`. -/
theorem galoisCompactSupportResolutionIso_homologyπ_pair_eq_restrictScalarsMapOfBar
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (x : letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2)
    (xΛ : letI := connectedSpace_of_isCurve B X f
      (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hx : letI := connectedSpace_of_isCurve B X f
      (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom xΛ =
        ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
          (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2).hom x)
    (z : letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0)
    (zμ : letI := connectedSpace_of_isCurve B X f
      (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hzμ : letI := connectedSpace_of_isCurve B X f
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom (ZMod (Fintype.card Λ)))
        (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom.hom
          (galoisHomOpPair (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) 2 0 2 (zero_add 2)
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2 x)
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 0 z)) =
        (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom zμ) :
    letI := connectedSpace_of_isCurve B X f
    (galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom.hom
        ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom zμ) =
      galoisCompactSupportRestrictScalarsMapOfBar f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ)
        ((representationSheaf B X _ Λ).obj i.M)
        ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
          (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))
        (restrictScalarsIntLift (algebraMap (ZMod (Fintype.card Λ)) Λ) _ ZMod.intCast_surjective
          (poincareCocycleH0 B X f kbar Λ y j K₀ i _
            (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z)))
        ((galoisCompactSupportResolutionIso (f := f) kbar _ i.I ((2 : ℕ) : ℤ)).hom.hom
          ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom xΛ)) := by
  letI := connectedSpace_of_isCurve B X f
  have hx' := hx
  have he : (fieldBaseChangeGlobalSectionsRestrictScalarsIso
        (Int.castRingHom (ZMod (Fintype.card Λ)))
        (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom ≫
      (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom (ZMod (Fintype.card Λ)))
        (fieldBaseChange (Over.mk j.toBase) kbar)).hom.app _ =
      (etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)).map
        (inverseImageRestrictScalarsApp (Int.castRingHom (ZMod (Fintype.card Λ)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar) (K₀.cocomplex.X 2)) := by
    rw [fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  convert galoisCompactSupportResolutionIso_homologyπ_eq_restrictScalarsMapOfBar kbar
    (algebraMap (ZMod (Fintype.card Λ)) Λ) ZMod.intCast_surjective
    ((representationSheaf B X _ Λ).obj i.M)
    ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
      (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))) i.I K₀
    (poincareCocycleH0 B X f kbar Λ y j K₀ i _
      (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z))
    (ObjectProperty.homMk (galoisHomOpCocycleAct (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) _
        (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z) ≫
      (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).hom))
    (compactSupportResolutionIntAugmentation_comp_poincareAct B X f kbar Λ y j K₀ i z)
    xΛ zμ (by
      rw [← hzμ]
      refine (ConcreteCategory.congr_hom he _).trans
        ((globalSections_map_galoisHomOpCocycleAct_glue B X f kbar Λ y j K₀ i _
          (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z) _).symm.trans ?_)
      rw [hx']
      rfl) using 2

end AlgebraicGeometry

end
