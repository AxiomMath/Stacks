module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTrace
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomComplex

/-!
# The Galois-equivariant trace on the class of a cocycle

Let `K₀` be an injective resolution of `j_! ℱ_μ` on `X̄` and `Γ^Gal_ℤ(res_ℤ K₀)` the complex of
discrete Galois modules of its sections over `X̄_k̄`. The Galois-equivariant trace
`AlgebraicGeometry.galoisHomOpCyclotomicTrace : H²(Γ^Gal_ℤ(res_ℤ K₀)) ⟶ ℚ/ℤ` is computed on the
class of a cocycle (`AlgebraicGeometry.trace_mapHomologyIso_homologyπ`): it is `tr_{X_k̄}` of the
class in `H²_c(X_k̄, ℱ_μ)` of the same sections, read as a cocycle of `Γ(X̄_k̄, K₀|)`. This is the
form in which the trace enters the top-degree pairing of Tag 03VM.

The input is that the comparison `Stacks.EtaleCohomology.exactFunctorPlusHomologyIso` of an exact
functor with cohomology, built through the derived categories, is the comparison on complexes
(`Stacks.EtaleCohomology.exactFunctorPlusHomologyIso_hom`), hence compatible with classes of
cocycles (`Stacks.EtaleCohomology.map_homologyπ_exactFunctorPlusHomologyIso_hom`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology

section ExactHomology

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] (T : A ⥤ B)
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- Cancelling three inverse pairs in a composite. -/
private theorem comp_cancel_three {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ : C}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₁) (d : P₁ ⟶ P₀) (e : P₀ ⟶ P₃) (f : P₃ ⟶ P₄)
    (g : P₄ ⟶ P₃) (hbc : b ≫ c = 𝟙 _) (had : a ≫ d = 𝟙 _) (hfg : f ≫ g = 𝟙 _) :
    ((a ≫ b) ≫ (c ≫ d ≫ e ≫ f)) ≫ g = e := by
  simp only [Category.assoc, hfg, Category.comp_id, reassoc_of% hbc, reassoc_of% had]

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- Flipping a commutative square with two sides isomorphisms. -/
private theorem comp_iso_hom_of_comp_iso_inv {C : Type*} [Category* C] {W X Y Z : C}
    (π' : X ⟶ Z) (e : Y ≅ Z) (mi : X ≅ W) (p : W ⟶ Y) (h : π' ≫ e.inv = mi.hom ≫ p) :
    p ≫ e.hom = mi.inv ≫ π' := by
  rw [← cancel_epi mi.hom, Iso.hom_inv_id_assoc, ← reassoc_of% h, Iso.inv_hom_id, Category.comp_id]

/-- **The comparison `T(Hᵐ(K)) ≅ Hᵐ(T K)` of an exact functor through the derived categories is the
comparison on complexes** `Stacks.DerivedFunctor.complexHomologyIso` (inverse direction). -/
theorem exactFunctorPlusHomologyIso_inv (K : CochainComplex.Plus A) (m : ℤ) :
    (exactFunctorPlusHomologyIso T K m).inv =
      (Stacks.DerivedFunctor.complexHomologyIso T (ComplexShape.up ℤ) m).hom.app K.obj := by
  have h1 := Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q T m K.obj
  have e : DerivedCategory.Plus.ι.mapIso ((T.mapDerivedCategoryPlusQIso).app K) =
      T.mapDerivedCategoryFactors.app K.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusQIso_hom_app T K)
  have h2 := congrArg Iso.inv e
  have h4 : (DerivedCategory.Plus.homologyFunctor B m).map
      ((T.mapDerivedCategoryPlusQIso).inv.app K) =
      (DerivedCategory.homologyFunctor B m).map (T.mapDerivedCategoryFactors.inv.app K.obj) :=
    congrArg (DerivedCategory.homologyFunctor B m).map h2
  have hE : (exactFunctorPlusHomologyIso T K m).inv =
      (((DerivedCategory.homologyFunctorFactors B m).inv.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) ≫
        (DerivedCategory.Plus.homologyFunctor B m).map ((T.mapDerivedCategoryPlusQIso).inv.app K)) ≫
        (Stacks.DerivedFunctor.derivedHomologyIso T m).hom.app (DerivedCategory.Q.obj K.obj)) ≫
        T.map ((DerivedCategory.homologyFunctorFactors A m).hom.app K.obj) := rfl
  rw [hE, h4, h1]
  exact comp_cancel_three _ _ _ _ _ _ _
    ((DerivedCategory.homologyFunctor B m).mapIso
      (T.mapDerivedCategoryFactors.app K.obj)).inv_hom_id
    ((DerivedCategory.homologyFunctorFactors B m).app _).inv_hom_id
    (T.mapIso ((DerivedCategory.homologyFunctorFactors A m).app K.obj)).inv_hom_id

/-- **The comparison `T(Hᵐ(K)) ≅ Hᵐ(T K)` of an exact functor through the derived categories is the
comparison on complexes** `Stacks.DerivedFunctor.complexHomologyIso`. -/
theorem exactFunctorPlusHomologyIso_hom (K : CochainComplex.Plus A) (m : ℤ) :
    (exactFunctorPlusHomologyIso T K m).hom =
      ((Stacks.DerivedFunctor.complexHomologyIso T (ComplexShape.up ℤ) m).app K.obj).inv :=
  Iso.inv_ext' ((congrArg (· ≫ (exactFunctorPlusHomologyIso T K m).hom)
    (exactFunctorPlusHomologyIso_inv T K m).symm).trans
        (exactFunctorPlusHomologyIso T K m).inv_hom_id)

/-- **The comparison `T(Hᵐ(K)) ≅ Hᵐ(T K)` on the class of a cocycle** (inverse direction): the
class of a cocycle of `T K` is `T` of the class of the corresponding cocycle of `K`. -/
theorem homologyπ_exactFunctorPlusHomologyIso_inv (K : CochainComplex.Plus A) (m : ℤ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).homologyπ m ≫
        (exactFunctorPlusHomologyIso T K m).inv =
      ((K.obj.sc m).mapCyclesIso T).hom ≫ T.map (K.obj.homologyπ m) := by
  rw [exactFunctorPlusHomologyIso_inv, Stacks.DerivedFunctor.complexHomologyIso_hom_app]
  exact Stacks.Homology.mapHomologyIso_homologyπ (K.obj.sc m) T

/-- **The comparison `T(Hᵐ(K)) ≅ Hᵐ(T K)` on the class of a cocycle**: `T` of the class of a
cocycle of `K` goes to the class of the corresponding cocycle of `T K`. -/
theorem map_homologyπ_exactFunctorPlusHomologyIso_hom (K : CochainComplex.Plus A) (m : ℤ) :
    T.map (K.obj.homologyπ m) ≫ (exactFunctorPlusHomologyIso T K m).hom =
      ((K.obj.sc m).mapCyclesIso T).inv ≫
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).homologyπ m :=
  comp_iso_hom_of_comp_iso_inv _ _ _ _ (homologyπ_exactFunctorPlusHomologyIso_inv T K m)

end ExactHomology

end Stacks.EtaleCohomology

namespace Stacks.ContinuousCohomology

universe v w

/-- The underlying map of abelian groups of a map of discrete `R`-`Q`-modules is the underlying
map of modules. -/
theorem forgetAb_map_hom_apply {R : Type} [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q]
    {M N : Stacks.Injectives.ContinuousModule.{0, v, w} R Q} (φ : M ⟶ N) (a : M.obj.obj.V) :
    ((forgetAb.{0, v, w} R Q).map φ).hom a = φ.hom.hom.hom.hom a :=
  rfl

end Stacks.ContinuousCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

section GaloisTraceClass

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))

/-- Pasting three commutative squares, one of them an inverse pair. -/
private theorem comp_chase_of_three_squares {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : C}
    (π : P₀ ⟶ P₁) (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₁) (hm : P₁ ⟶ P₃) (e : P₃ ⟶ P₄) (cm : P₀ ⟶ P₅)
    (π' : P₅ ⟶ P₃) (mc : P₅ ⟶ P₆) (fp : P₆ ⟶ P₄) (hc : a ≫ b = 𝟙 _) (hn : π ≫ hm = cm ≫ π')
    (hE : π' ≫ e = mc ≫ fp) : π ≫ a ≫ b ≫ hm ≫ e = cm ≫ mc ≫ fp := by
  rw [reassoc_of% hc, reassoc_of% hn, hE]

/-- Pasting a square through a functor. -/
private theorem map_comp_chase_of_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P₀ P₁ P₂ P₃ P₄ P₅ : C} {Y : D} (p₁ : P₀ ⟶ P₁) (p₂ : P₁ ⟶ P₂) (h : P₂ ⟶ P₃)
    (cm : P₀ ⟶ P₄) (mc : P₄ ⟶ P₅) (s : P₅ ⟶ P₃) (R : F.obj P₃ ⟶ Y) (X : F.obj P₂ ⟶ Y)
    (T : F.obj P₅ ⟶ Y) (hU : X = F.map h ≫ R) (hM : p₁ ≫ p₂ ≫ h = cm ≫ mc ≫ s)
    (hs : F.map s ≫ R = T) : F.map (p₁ ≫ p₂) ≫ X = F.map (cm ≫ mc) ≫ T := by
  have h' := congrArg F.map hM
  simp only [Functor.map_comp, Category.assoc] at h' ⊢
  rw [hU, reassoc_of% h', hs]

/-- Pasting the inclusions of cycles through a functor. -/
private theorem map_comp_chase_of_cycles {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P₀ P₁ P₂ P₃ P₄ : C} (cm : P₀ ⟶ P₁) (mc : P₁ ⟶ P₂) (fi : P₂ ⟶ P₃) (i₁ : P₁ ⟶ P₃)
    (iG : P₀ ⟶ P₄) (gf : P₄ ⟶ P₃) (V : F.obj P₂ ⟶ F.obj P₃) (hV : V = F.map fi)
    (h₁ : mc ≫ fi = i₁) (h₂ : cm ≫ i₁ = iG ≫ gf) : F.map (cm ≫ mc) ≫ V = F.map (iG ≫ gf) := by
  rw [hV, ← F.map_comp, Category.assoc, h₁, h₂]

/-- The inverse of `ShortComplex.mapCyclesIso` against the inclusion of cycles. -/
private theorem mapCyclesIso_inv_comp_iCycles {C D : Type*} [Category* C] [Category* D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, ShortComplex.mapCyclesIso_hom_iCycles]

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- **The class of a cocycle of `Γ^Gal_ℤ(res_ℤ K₀)` in `res_ℤ H²(Γ^Gal_{ℤ/n}(K₀))`**: through
`H²(Q(-)) = H²(-)` and `AlgebraicGeometry.galoisHomOpGCyclotomicHomologyIso`, it is the class of
the corresponding cocycle of `Γ^Gal_{ℤ/n}(K₀)` (the degreewise identification
`AlgebraicGeometry.galoisHomOpGCyclotomicIso`). -/
theorem homologyπ_comp_galoisHomOpGCyclotomicHomologyIso_hom :
    letI := connectedSpace_of_isCurve B X f
    HomologicalComplex.homologyπ
        (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))
        ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) 2 ≫
      (DerivedCategory.homologyFunctorFactors _ 2).inv.app
          (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
          (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) ≫
      (galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)).hom =
    HomologicalComplex.cyclesMap
        (show (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
        (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) ⟶
            (((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (kbar ≃ₐ[k] kbar))).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj from (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom) 2 ≫
      ((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus).obj.sc ((2 : ℕ) : ℤ)).mapCyclesIso
          (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar))).hom ≫
      (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).map
          (((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus).obj.homologyπ ((2 : ℕ) : ℤ)) := by
  let := connectedSpace_of_isCurve B X f
  let G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) ℤ :=
    Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
      (cyclotomicIntResolution B X f kbar y n j K₀)
  let Fc := Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)
  let S := (galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
    K₀.cocomplexPlus
  let φ : G ⟶ (Fc.mapHomologicalComplex _).obj S.obj :=
    (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom
  have hh : (galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)).hom =
      (DerivedCategory.homologyFunctorFactors _ ((2 : ℕ) : ℤ)).hom.app G ≫
        HomologicalComplex.homologyMap φ ((2 : ℕ) : ℤ) ≫
        (exactFunctorPlusHomologyIso Fc S ((2 : ℕ) : ℤ)).inv := rfl
  rw [hh]
  exact comp_chase_of_three_squares _ _ _ _ _ _ _ _ _ (Iso.inv_hom_id_app _ _)
    (HomologicalComplex.homologyπ_naturality _ _) (homologyπ_exactFunctorPlusHomologyIso_inv _ _ _)

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- **The class of a cocycle of `Γ^Gal_ℤ(res_ℤ K₀)` in `H²(Γ(X̄_k̄, K₀|))`**, on underlying groups:
through `AlgebraicGeometry.galoisHomOpCyclotomicUnderlyingIso`, it is the class of the
corresponding cocycle of `Γ(X̄_k̄, K₀|)`. -/
theorem map_homologyπ_comp_galoisHomOpCyclotomicUnderlyingIso_hom :
    letI := connectedSpace_of_isCurve B X f
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        (HomologicalComplex.homologyπ
        (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))
        ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) 2 ≫
        (DerivedCategory.homologyFunctorFactors _ 2).inv.app
            (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
            (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀))) ≫
      (galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom =
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        (HomologicalComplex.cyclesMap
        (show (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
        (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) ⟶
            (((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (kbar ≃ₐ[k] kbar))).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj from (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom) 2 ≫
        ((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj.sc ((2 : ℕ) : ℤ)).mapCyclesIso
            (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar))).hom) ≫
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))).map
          (((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus).obj.sc ((2 : ℕ) : ℤ)).mapCyclesIso
          (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n)
          (kbar ≃ₐ[k] kbar))).inv ≫
        (((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n)
            (kbar ≃ₐ[k] kbar)).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj).homologyπ ((2 : ℕ) : ℤ)) := by
  let := connectedSpace_of_isCurve B X f
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))
  let Un := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar)
  let S := (galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
    K₀.cocomplexPlus
  have hU : (galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom =
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
          (galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)).hom ≫
        R.map (exactFunctorPlusHomologyIso Un S ((2 : ℕ) : ℤ)).hom := rfl
  exact map_comp_chase_of_square _ _ _ _ _ _ _ _ _ _ hU
    (homologyπ_comp_galoisHomOpGCyclotomicHomologyIso_hom B X f kbar y n j K₀)
    ((R.map_comp _ _).symm.trans
      (congrArg R.map (map_homologyπ_exactFunctorPlusHomologyIso_hom Un S ((2 : ℕ) : ℤ))))

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- The cocycle of `Γ(X̄_k̄, K₀|)` attached to a cocycle of `Γ^Gal_ℤ(res_ℤ K₀)` has the same
sections: its inclusion into the cochains is the degreewise identification
`AlgebraicGeometry.galoisHomOpGCyclotomicIso` of the inclusion of the original cocycle. -/
theorem map_cyclesMap_galoisHomOpGCyclotomicIso_iCycles :
    letI := connectedSpace_of_isCurve B X f
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        (HomologicalComplex.cyclesMap
        (show (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
        (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) ⟶
            (((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (kbar ≃ₐ[k] kbar))).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj from (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom) 2 ≫
        ((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj.sc ((2 : ℕ) : ℤ)).mapCyclesIso
            (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar))).hom) ≫
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))).map
          (((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus).obj.sc ((2 : ℕ) : ℤ)).mapCyclesIso
          (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n)
          (kbar ≃ₐ[k] kbar))).inv ≫
        (((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n)
            (kbar ≃ₐ[k] kbar)).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj).iCycles ((2 : ℕ) : ℤ)) =
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        (HomologicalComplex.iCycles
        (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))
        ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) 2 ≫
            (show (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
            (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)) ⟶
            (((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (kbar ≃ₐ[k] kbar))).mapHomologicalComplex _).obj
            ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
            K₀.cocomplexPlus).obj from (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom).f 2) :=
            by
  let := connectedSpace_of_isCurve B X f
  exact map_comp_chase_of_cycles
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) _ _ _ _ _ _ _
    (congrArg (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))).map
      (mapCyclesIso_inv_comp_iCycles _ _))
    (ShortComplex.mapCyclesIso_hom_iCycles _ _) (HomologicalComplex.cyclesMap_i _ _)

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- **The class of a cocycle, from `H²(Q(Γ^Gal_ℤ(res_ℤ K₀)))` to `H²(Γ(X̄_k̄, K₀|))`**: if `c` is a
degree-two cocycle of the underlying complex of `Γ^Gal_ℤ(res_ℤ K₀)` and `z` the cocycle of
`Γ(X̄_k̄, K₀|)` with the same sections (`hcz`), then
`AlgebraicGeometry.galoisHomOpCyclotomicUnderlyingIso` carries the class of `c` to the class of
`z`. -/
theorem galoisHomOpCyclotomicUnderlyingIso_hom_homologyπ
    (c : (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y n j K₀))).cycles 2)
    (z : (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles 2)
    (hcz : (fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom (ZMod n))
        (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom.hom
          (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
              (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
              (cyclotomicIntResolution B X f kbar y n j K₀))).iCycles 2).hom c) =
      (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) 2).hom z) :
    letI := connectedSpace_of_isCurve B X f
    (galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom
      (((Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
          ((DerivedCategory.homologyFunctorFactors _ 2).inv.app (Stacks.EtaleCohomology.galoisHomOpG
          (Over.mk j.toBase) kbar (cyclotomicIntResolution B X f kbar y n j K₀)))).hom
        ((((show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ
            (kbar ≃ₐ[k] kbar)) ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)).sc 2).mapHomologyIso
            (Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))).hom
          (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
              (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
              (cyclotomicIntResolution B X f kbar y n j K₀))).homologyπ 2).hom c))) =
      (HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) 2).hom z := by
  let := connectedSpace_of_isCurve B X f
  let G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)) ℤ :=
    Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
      (cyclotomicIntResolution B X f kbar y n j K₀)
  let S := ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
    K₀.cocomplexPlus).obj
  let Fa := Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)
  let Fc := Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)
  let Un := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar)
  let UZ := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)
  let φ : G ⟶ (Fc.mapHomologicalComplex _).obj S :=
    (galoisHomOpGCyclotomicIso B X f kbar y n j K₀).hom
  let y₀ := ((G.sc 2).mapCyclesIso Fa).hom c
  let ι := (DerivedCategory.homologyFunctorFactors _ 2).inv.app G
  let U := (galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom
  -- the cycle `z'` of `Γ(X̄_k̄, K₀|)` reached from `c`, and `z' = z`
  have hz : ((S.sc ((2 : ℕ) : ℤ)).mapCyclesIso Un).inv
      (UZ.map (HomologicalComplex.cyclesMap φ 2 ≫
        ((S.sc ((2 : ℕ) : ℤ)).mapCyclesIso Fc).hom) y₀) = z := by
    apply (ModuleCat.mono_iff_injective
      (((Un.mapHomologicalComplex _).obj S).iCycles ((2 : ℕ) : ℤ))).1 inferInstance
    have e3 := ConcreteCategory.congr_hom
      (map_cyclesMap_galoisHomOpGCyclotomicIso_iCycles B X f kbar y n j K₀) y₀
    have e4 := ConcreteCategory.congr_hom
      (UZ.map_comp (HomologicalComplex.iCycles G 2) (φ.f 2)) y₀
    have e5 := congrArg (UZ.map (φ.f 2)).hom (ConcreteCategory.congr_hom
        (ShortComplex.mapCyclesIso_hom_iCycles (G.sc 2) Fa) c)
    exact e3.trans (e4.trans (e5.trans hcz))
  have f1 := ConcreteCategory.congr_hom
    (Stacks.Homology.mapHomologyIso_homologyπ (G.sc 2) Fa) c
  have f2 := ConcreteCategory.congr_hom (UZ.map_comp (G.homologyπ 2) ι) y₀
  have f3 := ConcreteCategory.congr_hom
    (map_homologyπ_comp_galoisHomOpCyclotomicUnderlyingIso_hom B X f kbar y n j K₀) y₀
  have f4 := congrArg (ConcreteCategory.hom (((Un.mapHomologicalComplex _).obj S).homologyπ 2)) hz
  have g := ((congrArg (fun a => U (Fa.map ι a)) f1).trans (congrArg U f2.symm)).trans f3
  exact g.trans f4


end GaloisTraceClass

section GaloisTraceClassFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n)))))

/-- **The trace on the class of a cocycle**: for a degree-two cocycle `c` of the underlying complex
of `Γ^Gal_ℤ(res_ℤ K₀)`, read as the cocycle `z` of `Γ(X̄_k̄, K₀|)` with the same sections, the
Galois-equivariant trace `AlgebraicGeometry.galoisHomOpCyclotomicTrace` of its class is
`tr_{X_k̄}` (`AlgebraicGeometry.compactSupportCyclotomicTrace`) of the class of `z` in
`H²_c(X_k̄, ℱ_μ)` (`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`).

The resolution `K₀` is written with `representationSheaf.{u, 0}` in this section so that the
statements used in the proof, once instantiated, are spelled as the goal; a consumer whose `K₀` is
written without the annotation applies it with `rw`. -/
theorem trace_mapHomologyIso_homologyπ (hn : IsUnit ((n : ℕ) : kbar))
    (c : (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
        (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y n j K₀))).cycles 2)
    (z : (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles 2)
    (hcz : (fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom (ZMod n))
        (Over.mk j.toBase) kbar (K₀.cocomplex.X 2)).hom.hom
          (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
              (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
              (cyclotomicIntResolution B X f kbar y n j K₀))).iCycles 2).hom c) =
      (HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) 2).hom z) :
    letI := connectedSpace_of_isCurve B X f
    ((Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).map
        (((DerivedCategory.homologyFunctorFactors _ 2).inv.app (Stacks.EtaleCohomology.galoisHomOpG
        (Over.mk j.toBase) kbar (cyclotomicIntResolution B X f kbar y n j K₀))) ≫
        (galoisHomOpCyclotomicTrace B X f kbar y n j K₀ hn))).hom
      ((((show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))
          ℤ from
        Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)).sc 2).mapHomologyIso
            (Stacks.ContinuousCohomology.forgetAb.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar))).hom
          (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} ℤ
              (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
              (cyclotomicIntResolution B X f kbar y n j K₀))).homologyπ 2).hom c)) =
      ULift.up (compactSupportCyclotomicTrace B X f kbar y n j hn
        ((galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom.hom
            ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} (ZMod n)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} (ZMod n)
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) 2).hom z))) := by
  refine (ConcreteCategory.congr_hom (Functor.map_comp _ _ _) _).trans
    ((ConcreteCategory.comp_apply _ _ _).trans
    ((Stacks.ContinuousCohomology.forgetAb_map_hom_apply _ _).trans
    ((ULift.up_down _).symm.trans (congrArg ULift.up
    ((galoisHomOpCyclotomicTrace_apply B X f kbar y n j K₀ hn _).trans ?_)))))
  exact congrArg (compactSupportCyclotomicTrace B X f kbar y n j hn)
    (congrArg (ConcreteCategory.hom (galoisCompactSupportResolutionIso (f := f) kbar _ K₀
      ((2 : ℕ) : ℤ)).hom) (galoisHomOpCyclotomicUnderlyingIso_hom_homologyπ B X f kbar y n
      j K₀ c z hcz))

end GaloisTraceClassFormula


end AlgebraicGeometry
