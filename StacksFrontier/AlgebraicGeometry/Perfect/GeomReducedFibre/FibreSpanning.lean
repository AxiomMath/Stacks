module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.CycleBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsKernelModel
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UnitSpreading
public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# Fibre functions coming from the total space, read on the Čech model

Let `f : X ⟶ Spec B` be separated, `U` a finite affine open cover of `X` with affine finite
intersections, `ψ : B → T` a ring map and `X' = X ×_{Spec B} Spec T`. If every global function on
`X'` is a `T`-linear combination of pullbacks of global functions on `X`, then every degree-zero
cocycle of the base change `Č(U, 𝒪_X) ⊗_B T` of the Čech model comes from a degree-zero cocycle of
`Č(U, 𝒪_X)`: this is `DegreeZeroCyclesSurjective ψ`.

The hypothesis holds at the closed fibre over a local ring with algebraically closed residue
field, for a proper morphism with reduced closed fibre: the global functions on the fibre are a
finite reduced algebra over an algebraically closed field, hence spanned by idempotents
(`mem_span_isIdempotentElem`), and every idempotent comes from a global function on `X` by
[Stacks, Tag 0G7X], the only open neighbourhood of the closed point of a local scheme being the
whole scheme.

## Main results

* `StacksDraft.Perfect.GeomReducedFibre.mem_span_isIdempotentElem`
* `StacksDraft.Perfect.GeomReducedFibre.degreeZeroCyclesSurjective_of_mem_span`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **A finite reduced algebra over an algebraically closed field is spanned by its
idempotents.** It is a finite product of finite field extensions of `k`, each of which is `k`. -/
theorem mem_span_isIdempotentElem {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Module.Finite k A] [IsReduced A] (z : A) :
    z ∈ Submodule.span k {e : A | IsIdempotentElem e} := by
  classical
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let E := IsArtinianRing.equivPi A
  have hc : ∀ I : MaximalSpectrum A, ∃ c : k,
      algebraMap k (A ⧸ I.asIdeal) c = Ideal.Quotient.mk I.asIdeal z := by
    intro I
    have : Module.Finite k (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.IsIntegral k (A ⧸ I.asIdeal) := inferInstance
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 _
  choose c hc using hc
  have he : ∀ I, IsIdempotentElem (E.symm (Pi.single I 1)) := fun I => by
    change E.symm (Pi.single I 1) * E.symm (Pi.single I 1) = E.symm (Pi.single I 1)
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hz : z = ∑ I, c I • E.symm (Pi.single I 1) := by
    apply E.injective
    funext J
    rw [map_sum, Finset.sum_apply]
    have hterm : ∀ I, E (c I • E.symm (Pi.single I 1)) J =
        if I = J then algebraMap k (A ⧸ J.asIdeal) (c J) else 0 := by
      intro I
      rw [Algebra.smul_def, map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply,
        IsArtinianRing.equivPi_apply]
      by_cases hIJ : I = J
      · obtain rfl := hIJ
        rw [Pi.single_eq_same, mul_one, ite_eq_left rfl]
        rfl
      · rw [Pi.single_eq_of_ne' hIJ, mul_zero, ite_eq_right hIJ]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc J, IsArtinianRing.equivPi_apply]
  rw [hz]
  exact Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span (he I))

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
/-- The pullback of a global function, as a section of the pulled back structure sheaf, is the
pulled back function. -/
theorem pullbackUnitIso_hom_app_pullbackSectionHom {X Y : Scheme.{u}} (g : Y ⟶ X)
    (a : Γ(Scheme.unitModule X, ⊤)) (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    (Scheme.Modules.pullbackUnitIso g).hom.app ⊤
        (AlgebraicGeometry.pullbackSectionHom g (Scheme.unitModule X) ⊤ ⊤ h a) =
      g.appTop a := by
  refine Eq.trans ?_ (SectionsEqualizer.pullbackUnitIso_unit g a)
  congr 1

/-- On a local scheme the only open neighbourhood of the closed point is the whole scheme. -/
theorem eq_top_of_closedPoint_mem {B : Type u} [CommRing B] [IsLocalRing B]
    (U : (Spec (.of B)).Opens) (hU : (IsLocalRing.closedPoint B : Spec (.of B)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  exact ((PrimeSpectrum.le_iff_specializes _ _).1
    (IsLocalRing.le_maximalIdeal x.2.ne_top)).mem_open U.isOpen hU

/-- The fibre of a morphism to `Spec B` over a point, as a scheme over the spectrum of the residue
field `κ(x)` of `B` at `x` in the sense of `Ideal.ResidueField`. -/
def fiberToSpec {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (x : PrimeSpectrum B) : f.fiber x ⟶ Spec (.of x.asIdeal.ResidueField) :=
  f.fiberToSpecResidueField x ≫ Spec.map (Scheme.Spec.residueFieldIso (.of B) x).inv

/-- The fibre is the base change along `Spec κ(x) ⟶ Spec B`. -/
theorem isPullback_fiberι_fiberToSpec {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : PrimeSpectrum B) :
    IsPullback (f.fiberι x) (fiberToSpec f x) f
      (Spec.map (CommRingCat.ofHom (algebraMap B x.asIdeal.ResidueField))) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback f ((Spec (.of B)).fromSpecResidueField x))
    (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (Scheme.Spec.residueFieldIso (.of B) x).inv)) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · simp
  · simpa using (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of B) x).symm

/-- The fibre of a proper morphism to `Spec B` is proper over the residue field `κ(x)`. -/
instance {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f]
    (x : PrimeSpectrum B) : IsProper (fiberToSpec f x) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_fiberι_fiberToSpec f x)
    ‹IsProper f›

/-- **Over a local ring with algebraically closed residue field, global functions on a reduced
closed fibre come from the total space, up to linear combinations.** The global functions on the
fibre are a finite reduced algebra over the residue field, hence spanned by idempotents, and every
idempotent extends to a global function by [Stacks, Tag 0G7X]. -/
theorem mem_span_range_appTop_closedFibre {B : Type u} [CommRing B] [IsLocalRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f]
    [IsAlgClosed (IsLocalRing.closedPoint B).asIdeal.ResidueField]
    [IsReduced (f.fiber (IsLocalRing.closedPoint B))]
    (z : Γ(f.fiber (IsLocalRing.closedPoint B), ⊤)) :
    letI := (Stacks.Cech.globalRingHom (fiberToSpec f (IsLocalRing.closedPoint B))).hom.toAlgebra
    z ∈ Submodule.span (IsLocalRing.closedPoint B).asIdeal.ResidueField
      (Set.range (fun a : Γ(X, ⊤) =>
        ((f.fiberι (IsLocalRing.closedPoint B)).appTop a :
          Γ(f.fiber (IsLocalRing.closedPoint B), ⊤)))) := by
  let T := (IsLocalRing.closedPoint B).asIdeal.ResidueField
  let : Algebra T Γ(f.fiber (IsLocalRing.closedPoint B), ⊤) :=
    ((Scheme.ΓSpecIso (.of T)).inv ≫
      (fiberToSpec f (IsLocalRing.closedPoint B)).appTop).hom.toAlgebra
  have hfin : Module.Finite T Γ(f.fiber (IsLocalRing.closedPoint B), ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper T
      (fiberToSpec f (IsLocalRing.closedPoint B))
  have : IsAlgClosed T := ‹_›
  change z ∈ Submodule.span T _
  refine Submodule.span_mono ?_ (mem_span_isIdempotentElem (k := T) z)
  rintro e (he : IsIdempotentElem e)
  obtain ⟨U, hmU, a, ha⟩ :=
    Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper f
      (IsLocalRing.closedPoint B) e he
  obtain rfl := eq_top_of_closedPoint_mem U hmU
  refine ⟨a, Eq.trans ?_ ha⟩
  exact (congrArg (fun φ => (ConcreteCategory.hom φ) a)
    (Scheme.Hom.appLE_eq_app (f.fiberι (IsLocalRing.closedPoint B)) (U := ⊤))).symm

section Span

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {B T : Type u} [CommRing B] [CommRing T] (ψ : B →+* T)
  {X X' : Scheme.{u}} {f : X ⟶ Spec (.of B)} [IsSeparated f] {f' : X' ⟶ Spec (.of T)}
  {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom ψ)))
  {I : Type u} [Finite I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- An isomorphism of complexes of modules, followed by its inverse, is the identity on an element
of a degree. -/
private theorem iso_inv_f_hom_f_apply {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (θ : K ≅ L) (i : ι) (x : K.X i) :
    θ.inv.f i (θ.hom.f i x) = x := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, θ.hom_inv_id]
  rfl

/-- **The Čech cochain of a function on the base change.** A global function `z` on `X'` gives a
degree-zero cochain of the base change `Č(U, 𝒪_X) ⊗_B T` of the Čech model: the cochain of `z`
in the Čech model of `X'` for the inverse-image cover, read back through the base-change
isomorphism of [Stacks, Tag 07VK] (2). -/
def fibreCochain (z : Γ(X', ⊤)) :
    (extendScalarsCx ψ (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).X 0 :=
  (baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U hU hUaff).inv.f 0
    (sectionsToModel f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj (Scheme.unitModule X))
      ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z))

/-- The cochain of the zero function is zero. -/
theorem fibreCochain_zero : fibreCochain ψ hsq U hU hUaff 0 = 0 := by
  have h1 : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (0 : Γ(X', ⊤)) = 0 :=
    map_zero ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤).hom
  simp only [fibreCochain, h1, map_zero]

/-- The cochain of a sum of functions is the sum of their cochains. -/
theorem fibreCochain_add (z₁ z₂ : Γ(X', ⊤)) :
    fibreCochain ψ hsq U hU hUaff (z₁ + z₂) =
      fibreCochain ψ hsq U hU hUaff z₁ + fibreCochain ψ hsq U hU hUaff z₂ := by
  have h1 : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (z₁ + z₂ : Γ(X', ⊤)) =
      (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z₁ +
        (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z₂ :=
    map_add ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤).hom z₁ z₂
  simp only [fibreCochain, h1, map_add]

/-- The cochain is `T`-linear in the function. -/
theorem fibreCochain_smul (t : T) (z : Γ(X', ⊤)) :
    letI := (Stacks.Cech.globalRingHom f').hom.toAlgebra
    fibreCochain ψ hsq U hU hUaff (t • z) = t • fibreCochain ψ hsq U hU hUaff z := by
  let := (Stacks.Cech.globalRingHom f').hom.toAlgebra
  let := Stacks.Cech.sectionsModule f'
    ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)) ⊤
  have h1 : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (t • z) =
      t • (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z := by
    change (Scheme.Modules.pullbackUnitIso g).inv.app ⊤
        ((Stacks.Cech.globalRingHom f').hom t * z) =
      (Stacks.Cech.baseRingHom f' ⊤).hom t • (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z
    rw [baseRingHom_top_apply]
    exact Scheme.Modules.Hom.app_smul (Scheme.Modules.pullbackUnitIso g).inv _ z
  simp only [fibreCochain, h1, map_smul]

/-- On the pullback of a function on `X`, the cochain is `1 ⊗` the cochain of that function. -/
theorem fibreCochain_appTop (a : Γ(X, ⊤)) :
    fibreCochain ψ hsq U hU hUaff (g.appTop a) =
      (1 : T) ⊗ₜ[B, ψ] (letI := Stacks.Cech.sectionsModule f (Scheme.unitModule X) ⊤
        sectionsToModel f U hU (Scheme.unitModule X) (a : Γ(Scheme.unitModule X, ⊤))) := by
  let := Stacks.Cech.sectionsModule f (Scheme.unitModule X) ⊤
  let a' : Γ(Scheme.unitModule X, ⊤) := a
  have hpb : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (g.appTop a) =
      AlgebraicGeometry.pullbackSectionHom g (Scheme.unitModule X) ⊤ ⊤ (by simp) a' := by
    rw [← pullbackUnitIso_hom_app_pullbackSectionHom g a' (by simp)]
    exact SectionsEqualizer.moduleIso_hom_inv_app (Scheme.Modules.pullbackUnitIso g).symm _
  change (baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U hU hUaff).inv.f 0
    (sectionsToModel f' _ _ _ ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (g.appTop a))) = _
  rw [hpb, ← baseChangeIso_sectionsToModel ψ hsq (Scheme.unitModule X) U hU hUaff a']
  exact iso_inv_f_hom_f_apply _ 0 _

/-- Distinct functions on `X'` have distinct cochains. -/
theorem fibreCochain_injective : Function.Injective (fibreCochain ψ hsq U hU hUaff) := by
  intro z₁ z₂ h
  have h1 := congrArg ((baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U hU
    hUaff).hom.f 0) h
  simp only [fibreCochain] at h1
  erw [iso_inv_f_hom_f_apply (baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U
    hU hUaff).symm, iso_inv_f_hom_f_apply (baseAlternatingCechComplexBaseChangeIso ψ hsq
    (Scheme.unitModule X) U hU hUaff).symm] at h1
  have h2 := sectionsToModel_injective _ _ _ _ h1
  have h3 := congrArg ((Scheme.Modules.pullbackUnitIso g).hom.app ⊤) h2
  exact (SectionsEqualizer.moduleIso_hom_inv_app (Scheme.Modules.pullbackUnitIso g) z₁).symm.trans
    (h3.trans (SectionsEqualizer.moduleIso_hom_inv_app (Scheme.Modules.pullbackUnitIso g) z₂))

/-- The cochain of a function is a cocycle. -/
theorem d_fibreCochain (z : Γ(X', ⊤)) :
    (extendScalarsCx ψ (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).d 0 1
      (fibreCochain ψ hsq U hU hUaff z) = 0 := by
  let := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)) ⊤
  let θ := baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U hU hUaff
  have hc := congrArg (fun m => m (sectionsToModel f' (fun i => g ⁻¹ᵁ U i)
    (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj (Scheme.unitModule X))
    ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z))) (θ.inv.comm 0 1)
  simp only [ModuleCat.comp_apply] at hc
  change _ = 0
  refine hc.trans ?_
  have hd := (range_sectionsToModel f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
    ((Scheme.Modules.pullback g).obj (Scheme.unitModule X))).le
    (LinearMap.mem_range_self _ ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤ z))
  rw [LinearMap.mem_ker] at hd
  change θ.inv.f 1 _ = 0
  rw [hd, map_zero]

/-- Every degree-zero cocycle of the base changed Čech model is the cochain of a function. -/
theorem exists_fibreCochain_eq
    (x : (extendScalarsCx ψ (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).X 0)
    (hx : (extendScalarsCx ψ (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).d 0 1 x =
      0) :
    ∃ z : Γ(X', ⊤), fibreCochain ψ hsq U hU hUaff z = x := by
  let := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)) ⊤
  let θ := baseAlternatingCechComplexBaseChangeIso ψ hsq (Scheme.unitModule X) U hU hUaff
  have hθd : (baseAlternatingCechComplex f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj (Scheme.unitModule X))).d 0 1 (θ.hom.f 0 x) = 0 := by
    have hc := congrArg (fun m => m x) (θ.hom.comm 0 1)
    simp only [ModuleCat.comp_apply] at hc
    refine hc.trans ?_
    change θ.hom.f 1 ((extendScalarsCx ψ (baseAlternatingCechComplex f U hU
      (Scheme.unitModule X))).d 0 1 x) = 0
    rw [hx, map_zero]
  obtain ⟨s, hs⟩ : θ.hom.f 0 x ∈ LinearMap.range (sectionsToModel f' (fun i => g ⁻¹ᵁ U i)
      (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj (Scheme.unitModule X))) :=
    (range_sectionsToModel _ _ _ _).ge hθd
  refine ⟨(Scheme.Modules.pullbackUnitIso g).hom.app ⊤ s, ?_⟩
  change θ.inv.f 0 (sectionsToModel f' _ _ _ ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤
    ((Scheme.Modules.pullbackUnitIso g).hom.app ⊤ s))) = x
  have hinv : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤
      ((Scheme.Modules.pullbackUnitIso g).hom.app ⊤ s) = s :=
    SectionsEqualizer.moduleIso_hom_inv_app (Scheme.Modules.pullbackUnitIso g).symm s
  rw [hinv, hs]
  exact iso_inv_f_hom_f_apply θ 0 x

include hsq hUaff in
/-- **Fibre functions spanned by pullbacks give `DegreeZeroCyclesSurjective`.** If every global
function on the base change `X'` is a `T`-linear combination of pullbacks of global functions on
`X`, every degree-zero cocycle of the Čech model of `𝒪_X` base changed to `T` comes from a
cocycle of the Čech model. -/
theorem degreeZeroCyclesSurjective_of_mem_span
    (hspan : ∀ z : Γ(X', ⊤),
      letI := (Stacks.Cech.globalRingHom f').hom.toAlgebra
      z ∈ Submodule.span T (Set.range (fun a : Γ(X, ⊤) => (g.appTop a : Γ(X', ⊤))))) :
    DegreeZeroCyclesSurjective ψ (baseAlternatingCechComplex f U hU (Scheme.unitModule X)) := by
  classical
  intro x hx
  let := (Stacks.Cech.globalRingHom f').hom.toAlgebra
  let := Stacks.Cech.sectionsModule f (Scheme.unitModule X) ⊤
  let W := LinearMap.range
    (ModuleCat.extendScalars.{u, u, u} ψ |>.map
      ((baseAlternatingCechComplex f U hU (Scheme.unitModule X)).iCycles 0)).hom
  have hP : ∀ z, fibreCochain ψ hsq U hU hUaff z ∈ W := by
    intro z
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan z)
    · rintro _ ⟨a, rfl⟩
      have hσ : (baseAlternatingCechComplex f U hU (Scheme.unitModule X)).d 0 1
          (sectionsToModel f U hU (Scheme.unitModule X) (a : Γ(Scheme.unitModule X, ⊤))) =
            0 :=
        (range_sectionsToModel f U hU (Scheme.unitModule X)).le (LinearMap.mem_range_self _ _)
      rw [fibreCochain_appTop]
      refine ⟨(1 : T) ⊗ₜ[B, ψ] (baseAlternatingCechComplex f U hU (Scheme.unitModule X)).cyclesMk
        _ 1 (by simp) hσ, ?_⟩
      change (ModuleCat.extendScalars.{u, u, u} ψ).map
        ((baseAlternatingCechComplex f U hU (Scheme.unitModule X)).iCycles 0)
        ((1 : T) ⊗ₜ[B, ψ] _) = _
      rw [ModuleCat.ExtendScalars.map_tmul]
      congr 1
      exact HomologicalComplex.i_cyclesMk (baseAlternatingCechComplex f U hU (Scheme.unitModule X))
        _ _ _ _
    · rw [fibreCochain_zero]
      exact W.zero_mem
    · intro z₁ z₂ _ _ h₁ h₂
      rw [fibreCochain_add]
      exact W.add_mem h₁ h₂
    · intro t z _ hz
      rw [fibreCochain_smul]
      exact W.smul_mem t hz
  obtain ⟨z, rfl⟩ := exists_fibreCochain_eq ψ hsq U hU hUaff x hx
  exact hP z

end Span

end StacksDraft.Perfect.GeomReducedFibre

end
