module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCech
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechComplex
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleQuasiIso
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionAffine
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# The top differential on Čech complexes: homology

Let `f : X ⟶ Spec A` be separated and `U` a family of affine opens covering `X`, indexed by a
linearly ordered type. This file reads the cohomology of `X` and of the de Rham differential on
the alternating Čech complexes of `U`, as complexes of `A`-modules:

* a morphism of complexes of modules induces zero on `H^{n+1}` exactly when it carries every
  `(n+1)`-cocycle to a coboundary (`CochainComplex.moduleCat_homologyMap_succ_eq_zero_iff`);
* the de Rham differential `Ω^e_{X/A} ⟶ Ω^{e+1}_{X/A}` induces zero on `H^{q+1}(X, -)` of the
  underlying abelian sheaves exactly when it induces zero on `H^{q+1}` of the alternating Čech
  complexes (`Stacks.Cech.rightDerived_map_deRham_d_eq_zero_iff_homologyMap`);
* the alternating Čech complex computes `Hᵐ(X, F)` as an `A`-module
  (`Stacks.Cech.alternatingCechModuleHomologyIsoCohomology`); hence over a Noetherian ring and
  for `f` proper its homology is finite for `F` coherent ([Stacks, Tag 02O6]) and vanishes above
  the fibre dimension ([Stacks, Tag 02V7]).

## References

* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u v

/-- If two isomorphisms conjugate `a` to `b`, then `a` is zero exactly when `b` is. -/
private theorem eq_zero_iff_of_comp_eq_comp {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {X Y X' Y' : C} {a : X ⟶ Y} {b : X' ⟶ Y'} {d : X ⟶ X'} {e : Y ⟶ Y'} [IsIso d] [IsIso e]
    (h : a ≫ e = d ≫ b) : a = 0 ↔ b = 0 := by
  constructor
  · rintro rfl
    rw [zero_comp] at h
    exact (cancel_epi d).1 (h.symm.trans comp_zero.symm)
  · rintro rfl
    rw [comp_zero] at h
    exact (cancel_mono e).1 (h.trans zero_comp.symm)

namespace CategoryTheory.ShortComplex

/-- **A morphism of short complexes of modules is zero on homology exactly when it carries every
cycle to a boundary.** -/
theorem moduleCat_homologyMap_eq_zero_iff {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    homologyMap φ = 0 ↔ ∀ x : S.X₂, S.g x = 0 → ∃ y : T.X₁, T.f y = φ.τ₂ x := by
  have heq := ShortComplex.π_homologyMap_ι φ
  constructor
  · intro h x hx
    rw [h, zero_comp, comp_zero] at heq
    let y := S.moduleCatCyclesIso.inv ⟨x, hx⟩
    have hy : S.iCycles y = x :=
      ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩
    have h0 : T.pOpcycles (φ.τ₂ x) = 0 := by
      simpa [ConcreteCategory.comp_apply, hy] using (ConcreteCategory.congr_hom heq y).symm
    exact (T.moduleCat_pOpcycles_eq_zero_iff _).1 h0
  · intro h
    apply (cancel_epi S.homologyπ).1
    apply (cancel_mono T.homologyι).1
    rw [Category.assoc, heq]
    simp only [comp_zero, zero_comp]
    apply ModuleCat.hom_ext
    ext y
    exact (T.moduleCat_pOpcycles_eq_zero_iff _).2 (h _ (ConcreteCategory.congr_hom S.iCycles_g y))

end CategoryTheory.ShortComplex

namespace CochainComplex

/-- **A morphism of cochain complexes of modules is zero on `H^{n+1}` exactly when it carries
every `(n+1)`-cocycle to a coboundary.** -/
theorem moduleCat_homologyMap_succ_eq_zero_iff {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap φ (n + 1) = 0 ↔
      ∀ x : K.X (n + 1), K.d (n + 1) (n + 1 + 1) x = 0 →
        ∃ y : L.X n, L.d n (n + 1) y = φ.f (n + 1) x := by
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := CochainComplex.prev_nat_succ n
  have hk : (ComplexShape.up ℕ).next (n + 1) = n + 1 + 1 := CochainComplex.next ℕ (n + 1)
  let e := HomologicalComplex.natIsoSc' (ModuleCat.{v} R) (ComplexShape.up ℕ) n (n + 1)
    (n + 1 + 1) hi hk
  let φ' := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) n (n + 1) (n + 1 + 1)).map φ
  have hnat := congrArg (fun v ↦ ShortComplex.homologyMap v) (e.hom.naturality φ)
  simp only [ShortComplex.homologyMap_comp] at hnat
  change HomologicalComplex.homologyMap φ (n + 1) ≫ (L.homologyIsoSc' n (n + 1) (n + 1 + 1)
      hi hk).hom = (K.homologyIsoSc' n (n + 1) (n + 1 + 1) hi hk).hom ≫
        ShortComplex.homologyMap φ' at hnat
  exact (eq_zero_iff_of_comp_eq_comp hnat).trans
    (ShortComplex.moduleCat_homologyMap_eq_zero_iff φ')

end CochainComplex

namespace Stacks.Cech

section Push

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  (U : I → X.Opens) {F G : X.Modules} (ψ : F.presheaf ⟶ G.presheaf)
  (hψ : ∀ (W : X.Opens) (a : A) (x : Γ(F, W)),
    ψ.app (op W) ((baseRingHom f W).hom a • x) = (baseRingHom f W).hom a • ψ.app (op W) x)

/-- **[Stacks, Tag 01FM] for the induced maps on cohomology.** For a linearly ordered index type,
the morphism of alternating Čech complexes induced by `ψ` is zero on `Hⁿ` exactly when the
morphism of full Čech complexes is: the inclusion of the alternating complex commutes with both
and is a quasi-isomorphism. -/
theorem homologyMap_alternatingCechModulePush_eq_zero_iff [LinearOrder I] (n : ℕ) :
    HomologicalComplex.homologyMap (alternatingCechModulePush f U ψ hψ) n = 0 ↔
      HomologicalComplex.homologyMap (cechModulePush f U ψ hψ) n = 0 := by
  have sq := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (alternatingCechModulePush_inclusion f U ψ hψ)
  simp only [HomologicalComplex.homologyMap_comp] at sq
  have hF : IsIso
      (HomologicalComplex.homologyMap (alternatingCechModuleComplex_inclusion f U F) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  have hG : IsIso
      (HomologicalComplex.homologyMap (alternatingCechModuleComplex_inclusion f U G) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact eq_zero_iff_of_comp_eq_comp sq

end Push

section DeRham

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f]
  {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

include hU hUaff in
/-- **The de Rham differential on cohomology, read on the alternating Čech complexes of an affine
covering.** For `f : X ⟶ Spec A` separated and `U` a covering of `X` by affine opens, the de Rham
differential `Ω^e_{X/A} ⟶ Ω^{e+1}_{X/A}` induces zero on `H^{q+1}(X, -)` of the underlying abelian
sheaves exactly when the morphism it induces on the alternating Čech complexes of `U` is zero on
`H^{q+1}`. -/
theorem rightDerived_map_deRham_d_eq_zero_iff_homologyMap (e q : ℕ) :
    ((sectionsFunctor X.carrier ⊤).rightDerived (q + 1)).map
        ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0 ↔
      HomologicalComplex.homologyMap
        (alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f e)
          (Scheme.Hom.deRhamPresheafD_app_smul f e)) (q + 1) = 0 := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f e
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f (e + 1)
  refine (Stacks.Cech.Hypercohomology.rightDerived_toSheaf_map_eq_zero_iff_cech _ _
    (f.relativeDifferentialForms (e : ℤ)) (f.relativeDifferentialForms ((e + 1 : ℕ) : ℤ))
    (f.deRhamComplex.d e (e + 1)) U hU (fun _ s => inter_isAffineOpen f U hUaff s) q).trans ?_
  rw [homologyMap_alternatingCechModulePush_eq_zero_iff,
    CochainComplex.moduleCat_homologyMap_succ_eq_zero_iff, cechModuleComplex_d,
    cechModuleComplex_d]
  rfl

end DeRham

section Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)
  [F.IsQuasicoherent] [IsSeparated f] (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The alternating Čech complex of an affine covering computes cohomology, `A`-linearly**
([Stacks, Tags 01FM, 01XD]). -/
def alternatingCechModuleHomologyIsoCohomology (m : ℕ) :
    (alternatingCechModuleComplex f U F).homology m ≅
      (ModuleCat.restrictScalars.{u} (globalRingHom f).hom).obj
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived m).obj F) :=
  ((alternatingCechModuleComplex f U F).extendHomologyIso
      ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (m : ℤ)).mapIso
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexIsoExtend
        f U hU F).symm ≪≫
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.homologyBaseAlternatingCechComplexIso
      f U hU F (fun _ s => inter_isAffineOpen f U hUaff s) m

include hU hUaff in
/-- **The homology of the alternating Čech complex is finite over a Noetherian base** for `f`
proper and `F` coherent ([Stacks, Tag 02O6]). -/
theorem moduleFinite_homology_alternatingCechModuleComplex [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] (m : ℕ) :
    Module.Finite A ((alternatingCechModuleComplex f U F).homology m) := by
  have hA := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology f F m
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have hfin : Module.Finite A ((ModuleCat.restrictScalars.{u} (globalRingHom f).hom).obj
      (((AlgebraicGeometry.moduleGlobalSections X).rightDerived m).obj F)) :=
    Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((AlgebraicGeometry.moduleGlobalSections X).rightDerived m).obj F))
  exact Module.Finite.equiv
    (alternatingCechModuleHomologyIsoCohomology f U hU F hUaff m).symm.toLinearEquiv

open Stacks.AlgebraicGeometry.FibreDimension in
include hU hUaff in
/-- **The homology of the alternating Čech complex vanishes above the fibre dimension** for `f`
proper over a Noetherian ring and `F` coherent ([Stacks, Tag 02V7]). -/
theorem isZero_homology_alternatingCechModuleComplex [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] {d : ℕ}
    (hfib : ∀ s : Spec (.of A), topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞))
    {m : ℕ} (hm : d < m) :
    IsZero ((alternatingCechModuleComplex f U F).homology m) :=
  (Functor.map_isZero _
    (isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le f hfib F hm)).of_iso
    (alternatingCechModuleHomologyIsoCohomology f U hU F hUaff m)

end Cohomology

end Stacks.Cech
