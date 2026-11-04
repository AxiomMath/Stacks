module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTraceClass
public import StacksFrontier.Homology.DerivedCategory.MapCyclesHomologyPi

/-!
# The base case of the derived Poincaré duality of Tag 03VM: `H²` of the pairing is invertible

For a member `i = (M, I)` of the Poincaré family, an injective resolution `K₀` of `j_! μ_n` in
degrees `≥ 0` (`n = #Λ`, invertible in `k̄`) and a lift `t : Γ^Gal(res_ℤ K₀) ⟶ T` of the trace
`H²_c(X_k̄, μ_n) → ℚ/ℤ`, the chain map `Γ^Gal(I) ⟶ Hom^•(Γ^Gal(ℋom^•(I, res_ℤ K₀)), T)` of the
Poincaré pairing is an isomorphism on `H²`
(`AlgebraicGeometry.isIso_homologyMap_poincarePairing_two_of_fintypeCard`): this is the base case
`hbase` of `AlgebraicGeometry.quasiIso_poincarePairing`.

The top-degree pairing `H²(Γ^Gal(I)) × H⁰(Γ^Gal(ℋom^•(I, K))) → ℚ/ℤ` is, on classes of cocycles
`x`, `β`, the degree-zero duality pairing `T₀(M) × Hom_N(M, μ_n) → ℚ/ℤ`
(`AlgebraicGeometry.compactSupportDegreeZeroPairing`, perfect by Tag 03VK) of the class of `x`
with the restriction to `X_k̄` of the map `θ_β` under `β`. The map `β ↦ θ_β|` is injective on
`H⁰` (BC2-inj) between groups of the same order (BC2-count), so the pairing is perfect
(`Stacks.ContinuousCohomology.bijective_of_pairing_transport_of_natCard_eq`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius Opposite

universe u

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

universe v w in
/-- Reading a degree-two class at the index `2` or `((2 : ℕ) : ℤ)` gives the same element, here
after a linear map, an additive map and `ULift.down ∘ ULift.up`. -/
theorem ulift_down_up_hom_homologyπ_two_natCast {R : Type} [Ring R]
    {C : CochainComplex (ModuleCat.{v} R) ℤ} {Y : ModuleCat.{v} R}
    (e : C.homology ((2 : ℕ) : ℤ) ⟶ Y) {A : Type*} [AddCommGroup A] (g : Y →+ A) (z : C.cycles 2) :
    (ULift.up.{w} (g (e.hom ((C.homologyπ 2).hom z)))).down =
      g (e.hom ((C.homologyπ ((2 : ℕ) : ℤ)).hom z)) :=
  rfl

section TraceLiftSpelling

variable {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The trace of the class of a cycle, read through `Stacks.Injectives.ContinuousModule` (as in
`Stacks.ContinuousCohomology.postcomp_topDegreePairing_homologyπ_of_traceLift`), is the same read
through `Stacks.EtaleCohomology.GaloisModules` (as in
`AlgebraicGeometry.trace_mapHomologyIso_homologyπ`). -/
theorem forgetAb_map_traceLift_galoisModules
    (G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) ℤ)
    (tr : (DerivedCategory.homologyFunctor
        (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) 2).obj
          (DerivedCategory.Q.obj G) ⟶ Stacks.ContinuousCohomology.ratCircle.{u, u + 1}
              (kbar ≃ₐ[k] kbar))
    (c : (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ G).cycles 2) :
    (Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        ((DerivedCategory.homologyFunctorFactors _ 2).inv.app G ≫ tr)
      (((G.sc 2).mapHomologyIso
          (Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))).hom
        ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ G).homologyπ 2 c)) =
    ((Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        ((DerivedCategory.homologyFunctorFactors (GaloisModules ℤ k kbar) 2).inv.app
          (show CochainComplex (GaloisModules ℤ k kbar) ℤ from G) ≫ tr)).hom
      ((((show CochainComplex
          (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) ℤ from
          (show CochainComplex (GaloisModules ℤ k kbar) ℤ from G)).sc 2).mapHomologyIso
            (Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))).hom
        (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
          (show CochainComplex (GaloisModules ℤ k kbar) ℤ from G)).homologyπ 2).hom c)) :=
  rfl

end TraceLiftSpelling

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} (ZMod (Fintype.card Λ)) _) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf.{u, 0} B X _ (ZMod (Fintype.card Λ))).obj
              (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))))
  [K₀.cocomplex.IsStrictlyGE 0]

/-! The objects below are spelled with the `NeZero (#Λ)` instance `⟨Fintype.card_ne_zero⟩` and the
universe `u + 2` of the declarations they are compared with, so that the kernel meets syntactically
equal terms. -/

/-- The class in `H²_c(X_k̄, ℱ_μ)` of a degree-two cycle of `Γ(X̄_k̄, K₀|)`. -/
abbrev poincareCompactSupportClassK (zμ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    galoisCompactSupportCohomologyGroup.{u, 0} (ZMod (Fintype.card Λ)) f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf.{u, 0} B X _ (ZMod (Fintype.card Λ))).obj
          (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))) ((2 : ℕ) : ℤ) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom.hom
    ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom zμ)

/-- The class in `H²_c(X_k̄, ℱ_M)` of a degree-two cycle of `Γ(X̄_k̄, I|)`. -/
abbrev poincareCompactSupportClassI (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (xΛ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)).cycles ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf.{u, 0} B X _ Λ).obj i.M)) ((2 : ℕ) : ℤ) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (galoisCompactSupportResolutionIso (f := f) kbar _ i.I ((2 : ℕ) : ℤ)).hom.hom
    ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom xΛ)

/-- The `ℤ/n`-linear lift of `θ_z` (`AlgebraicGeometry.poincareCocycleH0`), for a degree-zero cycle
`z` of `Γ^Gal(ℋom^•(I, res_ℤ K₀))`. -/
abbrev poincareTheta (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (z : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    (etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
        (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf.{u, 0} B X _ Λ).obj i.M))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
            ((representationSheaf.{u, 0} B X _ (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  restrictScalarsIntLift (algebraMap (ZMod (Fintype.card Λ)) Λ) _ ZMod.intCast_surjective
    (poincareCocycleH0 B X f kbar Λ y j K₀ i _
        (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z))

/-- The trace of the class of the pairing, by BC3. -/
theorem trace_poincareCompactSupportClassK_eq (hn : IsUnit (((Fintype.card Λ) : ℕ) : kbar))
    (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (x : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2)
    (xΛ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hx : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom xΛ =
        ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2).hom x)
    (z : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0)
    (zμ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hzμ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
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
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn
        (poincareCompactSupportClassK B X f kbar Λ y j K₀ zμ) =
      compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar
            (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
          (poincareTheta B X f kbar Λ y j K₀ i z)
              (poincareCompactSupportClassI B X f kbar Λ y j i xΛ)) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  with_reducible
    exact congrArg (compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn)
      (galoisCompactSupportResolutionIso_homologyπ_pair_eq_restrictScalarsMapOfBar B X f kbar
        Λ y j K₀ i x xΛ hx z zμ hzμ)

/-- The trace of the map induced by `θ_z`, by the S6a bridge. -/
theorem trace_restrictScalarsMapOfBar_poincareTheta (hn : IsUnit (((Fintype.card Λ) : ℕ) : kbar))
    (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (xΛ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (z : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar
            (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
          (poincareTheta B X f kbar Λ y j K₀ i z)
              (poincareCompactSupportClassI B X f kbar Λ y j i xΛ)) =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M
        ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar i.M).inv.hom
            (poincareCompactSupportClassI B X f kbar Λ y j i xΛ))
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            (poincareTheta B X f kbar Λ y j K₀ i z))) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  with_reducible
    exact compactSupportCyclotomicTrace_restrictScalarsMapOfBar B X f kbar Λ y j hn i.M
      (poincareTheta B X f kbar Λ y j K₀ i z) (poincareCompactSupportClassI B X f kbar Λ y j i xΛ)

/-- **The trace of the class of the pairing is the degree-zero duality pairing** (BC3 and the
trace formula of the S6a bridge): for a degree-two cycle `x` of `Γ^Gal(I)`, a degree-zero cycle `z`
of `Γ^Gal(ℋom^•(I, K))` and the cocycle `zμ` of `Γ(X̄_k̄, K₀|)` with underlying element `⟨x, z⟩`,
`tr` of the class of `zμ` is the pairing of the class of `x` in `T₀(M)` with the class of `θ_z`. -/
theorem trace_poincareCompactSupportClassK_eq_compactSupportDegreeZeroPairing
    (hn : IsUnit (((Fintype.card Λ) : ℕ) : kbar)) (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (x : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2)
    (xΛ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hx : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom xΛ =
        ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2).hom x)
    (z : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0)
    (zμ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hzμ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
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
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn
        (poincareCompactSupportClassK B X f kbar Λ y j K₀ zμ) =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M
        ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar i.M).inv.hom
            (poincareCompactSupportClassI B X f kbar Λ y j i xΛ))
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            (poincareTheta B X f kbar Λ y j K₀ i z))) :=
  (trace_poincareCompactSupportClassK_eq B X f kbar Λ y j K₀ hn i x xΛ hx z zμ hzμ).trans
    (trace_restrictScalarsMapOfBar_poincareTheta B X f kbar Λ y j K₀ hn i xΛ z)

omit [IsAlgClosed kbar] [CompactSpace (kbar ≃ₐ[k] kbar)] [Algebra (ZMod (Fintype.card Λ)) Λ] in
/-- The class in `H²(Γ^Gal(I))` of a cycle `a`, read in `H²_c(X_k̄, ℱ_M)`, is the class of the
same sections in `Γ(X̄_k̄, I|)`. -/
theorem poincareAHomologyIso_hom_homologyπ (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (a : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    (poincareAHomologyIso kbar i 2).hom ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).homologyπ 2 a) =
      poincareCompactSupportClassI B X f kbar Λ y j i
          (((HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) 2).mapCyclesIso (forget₂ (ModuleCat Λ) AddCommGrpCat)).hom a) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have h := ConcreteCategory.congr_hom
    (StacksDraft.DerivedCategoryHomology.mapCyclesIso_hom_map_homologyπ
      (HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) 2) (forget₂ (ModuleCat Λ) AddCommGrpCat)) a
  exact (congrArg (fun w => (forget₂ (ModuleCat Λ) AddCommGrpCat).map
    (galoisCompactSupportResolutionIso (f := f) kbar _ i.I 2).hom w) h).symm

omit [IsAlgClosed kbar] [CompactSpace (kbar ≃ₐ[k] kbar)] [Algebra (ZMod (Fintype.card Λ)) Λ] in
/-- The cycle of `Γ(X̄_k̄, I|)` underlying a cycle `a` of `Γ^Gal(I)` has the same sections. -/
theorem iCycles_mapCyclesIso_hom_poincare (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (a : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) ((2 : ℕ) : ℤ)).hom
                  (((HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) 2).mapCyclesIso (forget₂ (ModuleCat Λ) AddCommGrpCat)).hom a) =
      ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2).hom a := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  exact ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles
    (HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) 2) (forget₂ (ModuleCat Λ) AddCommGrpCat)) a


/-- **The top-degree pairing of the Poincaré pairing is the degree-zero duality pairing**: for a
degree-two cycle `a` of `Γ^Gal(I)` and a degree-zero cycle `z` of `Γ^Gal(ℋom^•(I, K))`, the pairing
of their classes, read in `ℚ/ℤ` through a trace lift `t`, is the pairing
`AlgebraicGeometry.compactSupportDegreeZeroPairing` of the class of `a` in `T₀(M)` with the class
of `θ_z` in `Hom_N(M, μ_n)`. -/
theorem poincarePairing_topDegreePairing_homologyπ (hn : IsUnit (((Fintype.card Λ) : ℕ) : kbar))
    (t : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (show CochainComplex
          (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar)) ℤ from
        galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) ⟶
        Stacks.ContinuousCohomology.traceTarget.{u, u + 1} (kbar ≃ₐ[k] kbar) 2)
    (ht : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      DerivedCategory.Q.map t =
        @Stacks.ContinuousCohomology.derivedTraceOfIsLE.{u, u + 1} (kbar ≃ₐ[k] kbar) _ _ _
          (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar)) ℤ from
        galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) 2
          (isLE_galoisHomOpG_cyclotomic B X f kbar y (Fintype.card Λ) j K₀)
          (galoisHomOpCyclotomicTrace B X f kbar y (Fintype.card Λ) j K₀ hn) ≫
        (@DerivedCategory.Q
            (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar))
          _ _ (HasDerivedCategory.standard _)).map
            (Stacks.ContinuousCohomology.traceTargetι.{u, u + 1} (kbar ≃ₐ[k] kbar) 2))
    (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (a : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).cycles 2)
    (z : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    ((Stacks.ContinuousCohomology.traceTargetShiftHomologyIso.{u, u + 1}
      (kbar ≃ₐ[k] kbar) 2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)
        (((poincarePairing kbar (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) t
            i).topDegreePairing 2 ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).homologyπ 2 a)).hom
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).homologyπ 0 z)) =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M
          (((poincareAHomologyIso kbar i 2).addCommGroupIsoToAddEquiv.toEquiv.trans
          (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar
              i.M).symm.toLinearEquiv.toEquiv)
              ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).homologyπ 2 a))
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            (poincareTheta B X f kbar Λ y j K₀ i z))) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨cG, hcG⟩ := CochainComplex.exists_iCycles_eq
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))) 2
    ((galoisHomOpComplexPairing (Over.mk j.toBase) kbar i.I.cocomplex
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).pair 2 0 2
      (zero_add 2) ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).iCycles 2 a)
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 0 z))
    (Stacks.ContinuousCohomology.ComplexPairing.d_pair_iCycles.{u, u + 1}
      (galoisHomOpComplexPairing (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) 2 a z)
  have hdμ : ((((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).d 2 (2 + 1)).hom
      ((fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom (ZMod (Fintype.card Λ)))
        (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom.hom
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 2 cG)) = 0 := by
    have e := congrArg
        (fun φ => ModuleCat.Hom.hom φ ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 2 cG))
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom_naturality
        (Int.castRingHom (ZMod (Fintype.card Λ))) (Over.mk j.toBase) kbar
            (K₀.cocomplex.d 2 (2 + 1)))
    have hw : (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).d 2 (2 + 1)
            ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 2 cG) = 0 :=
      congrArg (fun φ => AddCommGrpCat.Hom.hom φ cG)
          ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles_d 2 (2 + 1))
    exact e.symm.trans ((congrArg (fieldBaseChangeGlobalSectionsRestrictScalarsIso
      (Int.castRingHom (ZMod (Fintype.card Λ))) (Over.mk j.toBase) kbar
        (K₀.cocomplex.X (2 + 1))).hom.hom hw).trans (map_zero _))
  obtain ⟨zμ, hzμ⟩ := CochainComplex.exists_iCycles_eq_moduleCat
      (((etaleModuleGlobalSections.{u, 0} (ZMod (Fintype.card Λ))
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) 2 _ hdμ
  have hx := iCycles_mapCyclesIso_hom_poincare B X f kbar Λ y j i a
  have s1 :=
      @Stacks.ContinuousCohomology.postcomp_topDegreePairing_homologyπ_of_traceLift.{u, u + 1}
    (kbar ≃ₐ[k] kbar) _ _ _ _ _ _ _ _ _ _ _ _ _
    (galoisHomOpComplexPairing (Over.mk j.toBase) kbar i.I.cocomplex
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) 2
    (isLE_galoisHomOpG_cyclotomic B X f kbar y (Fintype.card Λ) j K₀)
    (galoisHomOpCyclotomicTrace B X f kbar y (Fintype.card Λ) j K₀ hn) t ht a z cG hcG
  have sT := trace_mapHomologyIso_homologyπ B X f kbar y (Fintype.card Λ) j K₀ hn cG zμ hzμ.symm
  have s3 := trace_poincareCompactSupportClassK_eq_compactSupportDegreeZeroPairing B X f
      kbar Λ y j K₀ hn i a
    (((HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              i.I.cocomplex)) 2).mapCyclesIso (forget₂ (ModuleCat Λ) AddCommGrpCat)).hom a) hx z zμ
                  ((congrArg (fieldBaseChangeGlobalSectionsRestrictScalarsIso
      (Int.castRingHom (ZMod (Fintype.card Λ))) (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom.hom
        hcG).symm.trans hzμ.symm)
  have s5 := congrArg (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar i.M).inv.hom
    (poincareAHomologyIso_hom_homologyπ B X f kbar Λ y j i a)
  have sB := forgetAb_map_traceLift_galoisModules kbar
    (galoisHomOpG (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))
    (galoisHomOpCyclotomicTrace B X f kbar y (Fintype.card Λ) j K₀ hn) cG
  refine ((congrArg ULift.down ((s1.trans sB).trans sT)).trans ?_).trans (s3.trans
    (congrArg
        (fun α => compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M α
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            (poincareTheta B X f kbar Λ y j K₀ i z)))) s5.symm))
  with_reducible exact ulift_down_up_hom_homologyπ_two_natCast _ _ zμ

/-- **The base case of the Poincaré duality of Tag 03VM, for `n = Fintype.card Λ`**: for a lift
`t` of the trace, the map of the Poincaré pairing of a member `i` of the family is an isomorphism
on `H²`. The top-degree pairing is the perfect degree-zero duality pairing
(`AlgebraicGeometry.poincarePairing_topDegreePairing_homologyπ`), read through the injective map
`β ↦ θ_β|` between groups of the same order. -/
theorem isIso_homologyMap_poincarePairing_two_of_fintypeCard
    (hn : IsUnit (((Fintype.card Λ) : ℕ) : kbar)) (t : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (show CochainComplex
          (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar)) ℤ from
        galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) ⟶
        Stacks.ContinuousCohomology.traceTarget.{u, u + 1} (kbar ≃ₐ[k] kbar) 2)
    (ht : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      DerivedCategory.Q.map t =
        @Stacks.ContinuousCohomology.derivedTraceOfIsLE.{u, u + 1} (kbar ≃ₐ[k] kbar) _ _ _
          (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar)) ℤ from
        galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)) 2
          (isLE_galoisHomOpG_cyclotomic B X f kbar y (Fintype.card Λ) j K₀)
          (galoisHomOpCyclotomicTrace B X f kbar y (Fintype.card Λ) j K₀ hn) ≫
        (@DerivedCategory.Q
            (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (kbar ≃ₐ[k] kbar))
          _ _ (HasDerivedCategory.standard _)).map
            (Stacks.ContinuousCohomology.traceTargetι.{u, u + 1} (kbar ≃ₐ[k] kbar) 2))
    (i : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    IsIso (HomologicalComplex.homologyMap
      (Stacks.ContinuousCohomology.internalHomComplexOfPairing
          (poincarePairing kbar
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) t i)) 2) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  refine
    Stacks.ContinuousCohomology.isIso_homologyMap_internalHomComplexOfPairing_of_bijective 2 _ ?_
  have hcard := natCard_homology_zero_galoisHomOpE_poincare B X f kbar Λ y j K₀ hn i
  have := finite_homology_zero_galoisHomOpE_poincare B X f kbar Λ y j K₀ hn i
  have : Finite ((geometricCyclotomicDualInvariants B X f kbar Λ y).obj (op i.M)) :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
  refine Stacks.ContinuousCohomology.bijective_of_pairing_transport_of_natCard_eq
    (fun x => (poincarePairing kbar
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) t i).topDegreePairing 2 x)
    (fun α => compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M α)
    ((poincareAHomologyIso kbar i 2).addCommGroupIsoToAddEquiv.toEquiv.trans
          (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar
              i.M).symm.toLinearEquiv.toEquiv)
    ((Stacks.ContinuousCohomology.traceTargetShiftHomologyIso.{u, u + 1}
      (kbar ≃ₐ[k] kbar) 2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)
    ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).homologyπ 0).hom
    ((AddCommGrpCat.epi_iff_surjective _).1 inferInstance)
    (fun z => geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            (poincareTheta B X f kbar Λ y j K₀ i z)))
    ?_ (bijective_compactSupportDegreeZeroPairing B X f kbar Λ y j hn i.M)
    (fun b hb => CharacterModule.exists_character_apply_ne_zero_of_ne_zero hb) ?_ hcard
  · intro x z
    obtain ⟨a, rfl⟩ :=
        (AddCommGrpCat.epi_iff_surjective ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).homologyπ 2)).1 inferInstance x
    exact poincarePairing_topDegreePairing_homologyπ B X f kbar Λ y j K₀ hn t ht i a z
  · intro z hz
    apply homologyπ_eq_zero_of_poincareCocycleH0_eq_zero B X f kbar Λ y j K₀ i z
    have h0 : compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ)
        ((representationSheaf B X _ Λ).obj i.M)
        ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
          (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))) 0 = 0 := by
      simp [compactSupportOpenRestriction, geometricSmoothModelCoefficientMap]
    have h1 := (geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M).injective
      (hz.trans (map_zero _).symm)
    have h2 := (bijective_compactSupportOpenRestriction f j kbar
      (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _).1 (h1.trans h0.symm)
    have h3 := restrictScalarsIntLift_spec (algebraMap (ZMod (Fintype.card Λ)) Λ) _
      ZMod.intCast_surjective (poincareCocycleH0 B X f kbar Λ y j K₀ i _
        (galoisHomOpE_d_iCycles_zero B X f kbar Λ y j K₀ i z))
    unfold poincareTheta at h2
    rw [h2, Functor.map_zero, Limits.comp_zero] at h3
    exact h3.symm

end AlgebraicGeometry

end
