module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.CycleBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.AffineLocalSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsChainModel
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Splitting a flat model off its degree-zero cohomology

Let `R` be a ring, `p` a prime of `R`, and `D` a bounded complex of flat `R`-modules concentrated
in degrees `≥ 0` which is perfect in `D(R)` — the Čech model of `RΓ(X, 𝒪_X)` for a proper flat
morphism `X → Spec R` of finite presentation. Assume that every degree-zero cocycle of
`D ⊗_R κ(p)` comes from a cocycle of `D` (`DegreeZeroCyclesSurjective`). Then after inverting a
single element `g ∉ p`:

* `K = D` splits in `D(R_g)` as `K_g ≅ H⁰(K)_g[0] ⊕ τ_{≥ 1} K_g`, with `H⁰(K)_g` finite free and
  `τ_{≥ 1} K_g` perfect of Tor amplitude in `[1, ∞)` ([Stacks, Tag 0A1U] and [Stacks, Tag 0A1V],
  through the affine-local form of [Stacks, Tag 0E62] (b));
* the base change `Z⁰(D) ⊗_R κ(p) → D⁰ ⊗_R κ(p)` of the inclusion of the degree-zero cocycles is
  injective, so that `H⁰(D) ⊗_R κ(p) → H⁰(D ⊗_R κ(p))` is bijective.

This is the algebraic part of the proof of [Stacks, Tag 0G7Y].

## Main results

* `StacksDraft.Perfect.GeomReducedFibre.fibreCohomologyVanishes_neg_one`
* `StacksDraft.Perfect.GeomReducedFibre.cohomologyBaseChangeSurjective_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]

/-- A complex concentrated in degrees `≥ 0` has no differential into degree `0`. -/
theorem d_neg_one_zero_eq_zero (D : CochainComplex (ModuleCat.{u} R) ℤ) [D.IsStrictlyGE 0] :
    D.d (-1) 0 = 0 :=
  (D.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _

/-- A bounded above complex of finite free modules is termwise flat. -/
theorem flat_of_isBoundedAboveFiniteFree {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : PseudoCoherence.IsBoundedAboveFiniteFree P) (i : ℤ) : Module.Flat R (P.X i) := by
  have := (hP.finiteFree i).2
  infer_instance

/-- **The derived fibre of a flat model in degrees `≥ 0` has no cohomology in degree `-1`.**

Statements about `D(R)` in this file are read at the standard model `HasDerivedCategory.standard`,
which is the model of `StacksDraft.Perfect.FibreCohomologyVanishes` and of the splitting criteria
of [Stacks, Tag 0A1U] and [Stacks, Tag 0A1V] that consume them. -/
theorem fibreCohomologyVanishes_neg_one (D : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [D.IsStrictlyGE 0] [D.IsStrictlyLE n] [∀ i, Module.Flat R (D.X i)] :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    IsPerfect (DerivedCategory.Q.obj D) →
      FibreCohomologyVanishes.{u, u} p (DerivedCategory.Q.obj D) (-1) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
  intro hD
  obtain ⟨P, hP, ⟨eP⟩⟩ := isPseudoCoherent_of_isPerfect.{u, u} _ hD
  refine ⟨P, hP, ⟨eP⟩, ?_⟩
  obtain ⟨b, hb⟩ := hP.upperBound
  have := flat_of_isBoundedAboveFiniteFree hP
  let Dt := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R p.ResidueField)
  obtain ⟨e₁⟩ := nonempty_homology_totalDerived_iso_of_flat (algebraMap R p.ResidueField) P b (-1)
  obtain ⟨e₂⟩ := nonempty_homology_totalDerived_iso_of_flat (algebraMap R p.ResidueField) D n (-1)
  have hz : IsZero ((extendScalarsCx (algebraMap R p.ResidueField) D).homology (-1)) :=
    (extendScalarsCx (algebraMap R p.ResidueField) D).isZero_of_isGE 0 (-1) (by omega)
  exact hz.of_iso (e₁.symm ≪≫ (DerivedCategory.homologyFunctor _ (-1)).mapIso
    (Dt.functor.mapIso eP) ≪≫ e₂)

/-- The differential vanishes on the cycles of a complex of modules. -/
private theorem d_iCycles_apply_eq_zero {S : Type u} [CommRing S]
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (i j : ℤ) (c : K.cycles i) :
    K.d i j (K.iCycles i c) = 0 := by
  have := congrArg (fun m => m c) (K.iCycles_d i j)
  simp only [ModuleCat.comp_apply] at this
  exact this.trans (by simp)

/-- The cycle inclusion of a complex of modules is injective. -/
private theorem injective_iCycles {S : Type u} [CommRing S]
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) : Function.Injective (K.iCycles i) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- Elementwise form of `cyclesBaseChange_iCycles`. -/
private theorem iCycles_cyclesBaseChange_apply {T : Type u} [CommRing T] (φ : R →+* T)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) (y : (ModuleCat.extendScalars.{u, u, u} φ).obj
      (D.cycles 0)) : (extendScalarsCx φ D).iCycles 0 (cyclesBaseChange φ D y) =
    (ModuleCat.extendScalars.{u, u, u} φ).map (D.iCycles 0) y := by
  have := congrArg (fun m => m y) (cyclesBaseChange_iCycles φ D)
  simpa only [ModuleCat.comp_apply] using this

/-- A complex in degrees `≥ 0` has no differential into degree `0` after extending scalars. -/
private theorem extendScalarsCx_d_neg_one_zero {T : Type u} [CommRing T] (φ : R →+* T)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) [D.IsStrictlyGE 0] :
    (extendScalarsCx φ D).d (-1) 0 = 0 := by
  change (ModuleCat.extendScalars.{u, u, u} φ).map (D.d (-1) 0) = 0
  rw [d_neg_one_zero_eq_zero D, Functor.map_zero]

/-- Under `DegreeZeroCyclesSurjective`, the comparison of degree-zero cocycles is surjective. -/
theorem epi_cyclesBaseChange_of_degreeZeroCyclesSurjective {T : Type u} [CommRing T]
    (φ : R →+* T) (D : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : DegreeZeroCyclesSurjective φ D) : Epi (cyclesBaseChange φ D) := by
  rw [ModuleCat.epi_iff_surjective]
  intro c
  obtain ⟨y, hy⟩ := h _ (d_iCycles_apply_eq_zero _ 0 1 c)
  exact ⟨y, injective_iCycles _ 0 ((iCycles_cyclesBaseChange_apply φ D y).trans hy)⟩

/-- **The degree-zero base-change map of a flat model is surjective at `p`.** For a bounded complex
`D` of flat modules in degrees `≥ 0`, perfect in `D(R)`, `DegreeZeroCyclesSurjective` at the
residue field of `p` is the surjectivity condition of [Stacks, Tag 0A1U] in degree `0`, read on a
bounded above finite free representative of `D`. -/
theorem cohomologyBaseChangeSurjective_zero (D : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [D.IsStrictlyGE 0] [D.IsStrictlyLE n] [∀ i, Module.Flat R (D.X i)]
    (hS : DegreeZeroCyclesSurjective (algebraMap R p.ResidueField) D) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    IsPerfect (DerivedCategory.Q.obj D) →
      CohomologyBaseChangeSurjective.{u, u} p (DerivedCategory.Q.obj D) 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  intro hD
  obtain ⟨P, hP, ⟨eP⟩⟩ := isPseudoCoherent_of_isPerfect.{u, u} _ hD
  refine ⟨P, hP, ⟨eP⟩, ?_⟩
  obtain ⟨b, hb⟩ := hP.upperBound
  have := flat_of_isBoundedAboveFiniteFree hP
  have hproj : ∀ i, Projective (P.X i) := fun i => by
    have := (hP.finiteFree i).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X i))
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨u, hu⟩ := PseudoCoherence.exists_chainMap_of_isKProjective P D eP.hom
  have hqu : QuasiIso u := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hu]
    infer_instance
  let φ := algebraMap R p.ResidueField
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let Fu := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u
  have hFu : QuasiIso Fu := PseudoCoherence.quasiIso_extendScalars_map_of_flat φ b n u
  -- the cocycles of `D` and of its fibre are the cohomology, there being nothing in degree `-1`
  have hπD : IsIso (D.homologyπ 0) := D.isIso_homologyπ (-1) 0 (by simp)
    (d_neg_one_zero_eq_zero D)
  have hπDκ : IsIso ((extendScalarsCx φ D).homologyπ 0) :=
    (extendScalarsCx φ D).isIso_homologyπ (-1) 0 (by simp) (extendScalarsCx_d_neg_one_zero φ D)
  -- the map on degree-zero cocycles induced by `u` is surjective
  have hZu : Epi (HomologicalComplex.cyclesMap u 0) := by
    have h : HomologicalComplex.cyclesMap u 0 =
        (P.homologyπ 0 ≫ HomologicalComplex.homologyMap u 0) ≫ inv (D.homologyπ 0) := by
      rw [IsIso.eq_comp_inv]
      exact (HomologicalComplex.homologyπ_naturality u 0).symm
    rw [h]
    infer_instance
  have : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj φ).isLeftAdjoint
  have hFZu : Epi (F.map (HomologicalComplex.cyclesMap u 0)) := inferInstance
  have hmD : Epi (cyclesBaseChange φ D) :=
    epi_cyclesBaseChange_of_degreeZeroCyclesSurjective φ D hS
  have hnat : F.map (HomologicalComplex.cyclesMap u 0) ≫ cyclesBaseChange φ D =
      cyclesBaseChange φ P ≫ HomologicalComplex.cyclesMap Fu 0 := by
    rw [← cancel_mono ((extendScalarsCx φ D).iCycles 0), Category.assoc, Category.assoc,
      cyclesBaseChange_iCycles, HomologicalComplex.cyclesMap_i, cyclesBaseChange_iCycles_assoc,
      ← F.map_comp, HomologicalComplex.cyclesMap_i, F.map_comp]
    rfl
  have hkey : Epi (cyclesBaseChange φ P ≫ (extendScalarsCx φ P).homologyπ 0) := by
    have h : cyclesBaseChange φ P ≫ (extendScalarsCx φ P).homologyπ 0 =
        (F.map (HomologicalComplex.cyclesMap u 0) ≫ cyclesBaseChange φ D ≫
          (extendScalarsCx φ D).homologyπ 0) ≫ inv (HomologicalComplex.homologyMap Fu 0) := by
      rw [IsIso.eq_comp_inv, ← Category.assoc, hnat, Category.assoc, Category.assoc,
        HomologicalComplex.homologyπ_naturality]
    rw [h]
    infer_instance
  intro _ _ x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 hkey ((extendScalarsCx φ P).homologyπ 0 x)
  have hyc := iCycles_cyclesBaseChange_apply φ P y
  have hd : (extendScalarsCx φ P).d 0 (0 + 1) (F.map (P.iCycles 0) y) = 0 := by
    rw [← hyc]
    exact d_iCycles_apply_eq_zero _ 0 _ _
  refine ⟨y, hd, ?_⟩
  have hmk : (extendScalarsCx φ P).cyclesMk (F.map (P.iCycles 0) y) (0 + 1) (by simp) hd =
      cyclesBaseChange φ P y := by
    apply injective_iCycles _ 0
    exact (HomologicalComplex.i_cyclesMk (extendScalarsCx φ P) _ _ _ _).trans hyc.symm
  change (extendScalarsCx φ P).homologyπ 0
    ((extendScalarsCx φ P).cyclesMk (F.map (P.iCycles 0) y) (0 + 1) (by simp) hd) = _
  rw [hmk]
  simp only [ModuleCat.comp_apply] at hy
  exact hy

/-- **The degree-zero base change of a split flat model is injective.** Let `D` be as in
`cohomologyBaseChangeSurjective_zero`, and assume that after inverting `g ∉ p` the object `D`
splits as `H⁰(D)_g[0] ⊕ P` with `H⁰(D)_g` finite free and `P` a bounded complex of projective
modules concentrated in degrees `≥ 1`. Then `Z⁰(D) ⊗_R κ(p) → D⁰ ⊗_R κ(p)` is injective.

The comparison `Z⁰(D) ⊗_R κ(p) → Z⁰(D ⊗_R κ(p))` is surjective, and both sides are isomorphic
to `H⁰(D)_g ⊗ κ(p)`: the source because `Z⁰(D) = H⁰(D)`, the target because the derived base
change of the splitting to `κ(p)` has `H⁰` equal to that of its first summand. A surjective
endomorphism of a finite module is injective. -/
theorem injective_extendScalars_iCycles_of_splitting (D : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) [D.IsStrictlyGE 0] [D.IsStrictlyLE n] [∀ i, Module.Flat R (D.X i)]
    (hS : DegreeZeroCyclesSurjective (algebraMap R p.ResidueField) D) (g : R) (hg : g ∉ p)
    (P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ) (b : ℤ)
    [P.IsStrictlyGE 1] [P.IsStrictlyLE b]
    (hPproj : ∀ j, Module.Projective (Localization.Away g) (P.X j)) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away g))
    let H0g := (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away g))).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (DerivedCategory.Q.obj D))
    Module.Finite (Localization.Away g) H0g → Module.Free (Localization.Away g) H0g →
    Nonempty ((PseudoCoherence.localizationAwayFunctorAux.{u, u} g).obj
        (DerivedCategory.Q.obj D) ≅
      (DerivedCategory.singleFunctor _ 0).obj H0g ⊞ DerivedCategory.Q.obj P) →
    Function.Injective
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R p.ResidueField)).map (D.iCycles 0)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away g))
  let := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
  intro H0g hfin hfree ⟨e⟩
  let φ := algebraMap R p.ResidueField
  have hunit : IsUnit (φ g) :=
    isUnit_iff_ne_zero.2 fun h => hg (Ideal.algebraMap_residueField_eq_zero.1 h)
  let ψ : Localization.Away g →+* p.ResidueField := IsLocalization.Away.lift g hunit
  have hψ : ψ.comp (algebraMap R (Localization.Away g)) = φ := IsLocalization.Away.lift_comp g hunit
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let Fg := ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away g))
  let Fψ := ModuleCat.extendScalars.{u, u, u} ψ
  let c : F ≅ Fg ⋙ Fψ :=
    eqToIso (congrArg (fun f => ModuleCat.extendScalars.{u, u, u} f) hψ.symm) ≪≫
      ModuleCat.extendScalarsComp (algebraMap R (Localization.Away g)) ψ
  -- the source: `Z⁰(D) ⊗ κ(p) ≅ H⁰(D)_g ⊗ κ(p)`
  obtain ⟨eS⟩ : Nonempty (F.obj (D.cycles 0) ≅ Fψ.obj H0g) :=
    ⟨F.mapIso (D.isoHomologyπ (-1) 0 (by simp) (d_neg_one_zero_eq_zero D) ≪≫
      ((DerivedCategory.homologyFunctorFactors _ 0).app D).symm) ≪≫ c.app _⟩
  -- the target: `Z⁰(D ⊗ κ(p)) ≅ H⁰(D)_g ⊗ κ(p)`
  let Dg := extendScalarsCx (algebraMap R (Localization.Away g)) D
  have hDgflat : ∀ i, Module.Flat (Localization.Away g) (Dg.X i) := fun i =>
    Module.Flat.of_linearEquiv
      (PseudoCoherence.extendScalarsTensorIso (S := Localization.Away g) (D.X i)).toLinearEquiv
  obtain ⟨t₂⟩ : Nonempty (extendScalarsCx φ D ≅ extendScalarsCx ψ Dg) :=
    ⟨(NatIso.mapHomologicalComplex c (ComplexShape.up ℤ)).app D⟩
  obtain ⟨t₄⟩ := nonempty_homology_totalDerived_iso_of_flat ψ Dg n 0
  let Dt := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} ψ
  have t₅ : Nonempty (DerivedCategory.Q.obj Dg ≅
      (PseudoCoherence.localizationAwayFunctorAux.{u, u} g).obj (DerivedCategory.Q.obj D)) := by
    let : Fg.Additive := extendScalars_additive.{u, u, u} _
    let : PreservesFiniteLimits Fg :=
      extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))
    let : PreservesColimitsOfSize.{0, 0} Fg :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
    let : PreservesFiniteColimits Fg := PreservesColimitsOfSize.preservesFiniteColimits Fg
    exact ⟨(Fg.mapDerivedCategoryFactors.app D).symm⟩
  obtain ⟨t₅⟩ := t₅
  have : Projective H0g := by
    have := hfree
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis _ H0g)
  obtain ⟨t₈⟩ : Nonempty (Dt.functor.obj ((DerivedCategory.singleFunctor _ 0).obj H0g) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Fψ.obj H0g)) := by
    let S := (CochainComplex.singleFunctor (ModuleCat.{u} (Localization.Away g)) 0).obj H0g
    have hproj : ∀ i : ℤ, Projective (S.X i) := by
      intro i
      rcases eq_or_ne i 0 with rfl | hi
      · exact Projective.of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H0g).symm inferInstance
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 H0g i hi).projective
    have hcomp : IsIso (Dt.comparison.app S) := Dt.comparison_isIso_of_projective S 0
    exact ⟨Dt.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app H0g) ≪≫
      @asIso _ _ _ _ _ hcomp ≪≫ DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex Fψ (ComplexShape.up ℤ) 0).app H0g) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (Fψ.obj H0g)).symm⟩
  have t₉ : IsZero ((DerivedCategory.homologyFunctor _ 0).obj
      (Dt.functor.obj (DerivedCategory.Q.obj P))) := by
    have hproj : ∀ i : ℤ, Projective (P.X i) := fun i => by
      have := hPproj i
      exact ModuleCat.projective_of_categoryTheory_projective _
    have hcomp : IsIso (Dt.comparison.app P) := Dt.comparison_isIso_of_projective P b
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ 0).mapIso
      (@asIso _ _ _ _ _ hcomp) ≪≫
        (DerivedCategory.homologyFunctorFactors _ 0).app (extendScalarsCx ψ P))
    exact (extendScalarsCx ψ P).isZero_of_isGE 1 0 (by omega)
  have : PreservesBinaryBiproducts Dt.functor :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts
      (DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) 0) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  obtain ⟨eT⟩ : Nonempty ((extendScalarsCx φ D).cycles 0 ≅ Fψ.obj H0g) := ⟨
    (extendScalarsCx φ D).isoHomologyπ (-1) 0 (by simp)
      (extendScalarsCx_d_neg_one_zero φ D) ≪≫
      (HomologicalComplex.homologyFunctor _ _ 0).mapIso t₂ ≪≫ t₄.symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso (Dt.functor.mapIso (t₅ ≪≫ e) ≪≫
        Dt.functor.mapBiprod _ _) ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapBiprod _ _ ≪≫ (isoBiprodZero t₉).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso t₈ ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (Fψ.obj H0g)⟩
  -- a surjective endomorphism of a finite module is injective
  have hfinψ : Module.Finite p.ResidueField (Fψ.obj H0g) := by
    let := ψ.toAlgebra
    change Module.Finite p.ResidueField (p.ResidueField ⊗[Localization.Away g] H0g)
    infer_instance
  have hmD : Function.Surjective (cyclesBaseChange φ D) :=
    (ModuleCat.epi_iff_surjective _).1
      (epi_cyclesBaseChange_of_degreeZeroCyclesSurjective φ D hS)
  let f := (eS.inv ≫ cyclesBaseChange φ D ≫ eT.hom).hom
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := hmD (eT.inv z)
    refine ⟨eS.hom w, ?_⟩
    change eT.hom (cyclesBaseChange φ D (eS.inv (eS.hom w))) = z
    rw [eS.hom_inv_id_apply, hw, eT.inv_hom_id_apply]
  have hfi : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hf
  have hmDi : Function.Injective (cyclesBaseChange φ D) := by
    intro x y hxy
    apply eS.toLinearEquiv.injective
    apply hfi
    change eT.hom (cyclesBaseChange φ D (eS.inv (eS.hom x))) =
      eT.hom (cyclesBaseChange φ D (eS.inv (eS.hom y)))
    rw [eS.hom_inv_id_apply, eS.hom_inv_id_apply, hxy]
  rw [← cyclesBaseChange_iCycles φ D]
  exact (injective_iCycles _ 0).comp hmDi

/-- **Splitting a flat model off its degree-zero cohomology.** Let `D` be a bounded complex of
flat `R`-modules in degrees `≥ 0`, perfect in `D(R)`, all of whose degree-zero cocycles over
`κ(p)` come from cocycles of `D`. Then there are `g ∉ p` and a bounded complex `P` of finite
projective `R_g`-modules concentrated in degrees `[1, b]` such that `H⁰(D)_g` is finite free
and `D ⊗_R R_g ≅ H⁰(D)_g[0] ⊕ P` in `D(R_g)`; moreover `Z⁰(D) ⊗_R κ(p) → D⁰ ⊗_R κ(p)` is
injective. -/
theorem exists_away_splitting (D : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [D.IsStrictlyGE 0] [D.IsStrictlyLE n] [∀ i, Module.Flat R (D.X i)]
    (hS : DegreeZeroCyclesSurjective (algebraMap R p.ResidueField) D) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    IsPerfect (DerivedCategory.Q.obj D) →
    ∃ g : R, g ∉ p ∧ ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ) (b : ℤ),
      P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
      (∀ j, Module.Finite (Localization.Away g) (P.X j)) ∧
      (∀ j, Module.Projective (Localization.Away g) (P.X j)) ∧
      (letI := HasDerivedCategory.standard (ModuleCat.{u} R)
       letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away g))
       let H0g := (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away g))).obj
         ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (DerivedCategory.Q.obj D))
       Module.Finite (Localization.Away g) H0g ∧ Module.Free (Localization.Away g) H0g ∧
         Nonempty ((PseudoCoherence.localizationAwayFunctorAux.{u, u} g).obj
            (DerivedCategory.Q.obj D) ≅
          (DerivedCategory.singleFunctor _ 0).obj H0g ⊞ DerivedCategory.Q.obj P)) ∧
      Function.Injective
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R p.ResidueField)).map (D.iCycles 0)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  intro hD
  have hK : PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj D) :=
    isPseudoCoherent_of_isPerfect.{u, u} _ hD
  have hneg : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (DerivedCategory.Q.obj D)) := fun i hi =>
    (D.isZero_of_isGE 0 i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app D)
  obtain ⟨g, hg, hmain⟩ :=
    UnitSplitting.exists_localization_iso_single_homology_biprod_truncGE.{u, u}
      p (DerivedCategory.Q.obj D) hK hneg (fibreCohomologyVanishes_neg_one p D n hD)
      (cohomologyBaseChangeSurjective_zero p D n hS hD)
  dsimp only at hmain
  obtain ⟨hfin, hfree, -, ⟨P, b, hPge, hPle, hPfin, hPproj, ⟨eP⟩, -⟩, ⟨e⟩⟩ := hmain
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away g))
  have e' := e ≪≫ biprod.mapIso (Iso.refl _) eP
  refine ⟨g, hg, P, b, hPge, hPle, hPfin, hPproj, ⟨hfin, hfree, ⟨e'⟩⟩, ?_⟩
  exact injective_extendScalars_iCycles_of_splitting p D n hS g hg P b hPproj hfin hfree ⟨e'⟩

end StacksDraft.Perfect.GeomReducedFibre

end
