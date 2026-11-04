module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleShift
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafDegreeZeroMap

/-!
# The canonical map `π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` on a relative projective spectrum

Let `s` be a relative `Proj` situation (Situation 01NN) with structure morphism
`π : Proj_S(𝒜) ⟶ S`, and let `ℳ` be a graded `𝒜`-module with quasi-coherent homogeneous pieces.
Property (7) of Tag 01O7 is a canonical map

`π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~`

generalizing the map `M ⟶ ⨁_{n ∈ ℤ} Γ(Proj S, M(n)~)` of Tag 01MR. Here `ℳ` on the left is the
`𝒪_S`-module `⨁_{n ∈ ℤ} ℳ_n` underlying the graded module, `ℳ(n)` is the shift
`SheafOfModules.LeftGradedModule.shift`, with `ℳ(n)_k = ℳ_{k + n}`, and `(ℳ(n))~` is the sheaf
`Stacks.RelativeProj.Situation.moduleSheaf` of the shift.

The degree-zero piece of `ℳ(n)` is `ℳ_n`, so the canonical map `π^*ℳ(n)_0 ⟶ (ℳ(n))~` of property
(3) is a map `π^*ℳ_n ⟶ (ℳ(n))~`. The pullback preserves direct sums, being a left adjoint, so
these assemble into the map of the statement.

That this generalizes Tag 01MR is `Stacks.RelativeProj.Situation.shiftedDegreeSheafMap_chart`: over
an affine open `W` of the base, on the chart `Proj 𝒜(W)`, the degree-`n` component carries a
section `m` of `ℳ_n` over `W` to the global section `m / 1` of `Γ(W, ℳ)(n)~`, which is the value
in degree `n` of the map of Tag 01MR for the graded `𝒜(W)`-module `Γ(W, ℳ)`. The identification of
the graded module of sections of `ℳ(n)` with the shift of that of `ℳ` used there is
`Stacks.RelativeProj.Situation.sectionModuleShiftLinearMap`.

## Main definitions

* `Stacks.RelativeProj.Situation.shiftedDegreeSheafMap`: the degree-`n` component
  `π^*ℳ_n ⟶ (ℳ(n))~`.
* `Stacks.RelativeProj.Situation.shiftedSumSheafMap`: **the canonical map
  `π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` of property (7) of Tag 01O7.**

## Main results

* `Stacks.RelativeProj.Situation.pullback_map_ι_shiftedSumSheafMap` and
  `Stacks.RelativeProj.Situation.shiftedSumSheafMap_ext`: on the summand `π^*ℳ_n` the map is the
  degree-`n` component followed by the inclusion of the `n`-th summand, and that determines it.
* `Stacks.RelativeProj.Situation.homEquiv_shiftedDegreeSheafMap`: the transpose of the degree-`n`
  component across `π^* ⊣ π_*` is `m ↦ m / 1` on the sections over the affine opens of the base.
* `Stacks.RelativeProj.Situation.shiftedDegreeSheafMap_chart`: **the chart description, which is
  the map of Tag 01MR.**

## Implementation notes

The direct sums are the categorical coproducts `∐` of sheaves of modules, indexed by `ℤ`. The
shift is the unsigned reindexing: Situation 01NN's algebras are commutative and no Koszul sign
enters.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Equation 27.10.0.6, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- The homogeneous pieces of a shift of a graded module with quasi-coherent homogeneous pieces
are quasi-coherent: they are the homogeneous pieces of the module itself. -/
public instance isQuasicoherent_shift_piece (k n : ℤ) : ((ℳ.shift k).piece n).IsQuasicoherent :=
  inferInstanceAs ((ℳ.piece (n + k)).IsQuasicoherent)

/-- The degree-zero piece of the shift `ℳ(n)` is the degree-`n` piece of `ℳ`, up to the
identification `0 + n = n` of degrees. -/
public def shiftPieceZeroIso (n : ℤ) : ℳ.piece n ≅ (ℳ.shift n).piece 0 :=
  eqToIso (congrArg ℳ.piece (zero_add n).symm)

/-- **The degree-`n` component `π^*ℳ_n ⟶ (ℳ(n))~`**: the canonical map of property (3) of Tag
01O7 for the shift `ℳ(n)`, whose degree-zero piece is `ℳ_n`. -/
public def shiftedDegreeSheafMap (n : ℤ) :
    (Scheme.Modules.pullback (relativeProjToBase s)).obj (ℳ.piece n) ⟶
      moduleSheaf (ℳ.shift n) :=
  (Scheme.Modules.pullback (relativeProjToBase s)).map (shiftPieceZeroIso ℳ n).hom ≫
    degreeZeroSheafMap (ℳ.shift n)

/-- **The degree-`n` component read on the base**: its transpose across `π^* ⊣ π_*` is the
identification `ℳ_n = ℳ(n)_0` followed by the morphism `ℳ(n)_0 ⟶ π_* (ℳ(n))~` which on the
sections over an affine open `W` of the base is `m ↦ m / 1`. This is the formula of the map
`M ⟶ ⨁_{n ∈ ℤ} Γ(Proj S, M(n)~)` of Tag 01MR on the chart over `W`. -/
public theorem homEquiv_shiftedDegreeSheafMap (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _
        (shiftedDegreeSheafMap ℳ n) =
      (shiftPieceZeroIso ℳ n).hom ≫ degreeZeroPushforwardHom (ℳ.shift n) :=
  (Adjunction.homEquiv_naturality_left _ _ _).trans
    (congrArg (_ ≫ ·) (homEquiv_degreeZeroSheafMap (ℳ.shift n)))

/-- **Stacks Project, Tag 01O7, property (7).** The canonical map

`π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~`

on the relative projective spectrum `π : Proj_S(𝒜) ⟶ S`, out of the pullback of the
`𝒪_S`-module `ℳ = ⨁_{n ∈ ℤ} ℳ_n` underlying a graded `𝒜`-module with quasi-coherent homogeneous
pieces. On the summand `π^*ℳ_n` it is the degree-`n` component
`Stacks.RelativeProj.Situation.shiftedDegreeSheafMap`, the canonical map of property (3) for the
shift `ℳ(n)`, followed by the inclusion of the `n`-th summand; on the sections over an affine
open of the base it is the map of Tag 01MR, `m ↦ m / 1` in degree `n`. -/
@[stacks 01O7 "property (7): the canonical map from the pullback of a graded module to the direct
sum of the sheaves associated to its shifts on the relative projective spectrum"]
public def shiftedSumSheafMap :
    (Scheme.Modules.pullback (relativeProjToBase s)).obj (∐ fun n : ℤ => ℳ.piece n) ⟶
      ∐ fun n : ℤ => moduleSheaf (ℳ.shift n) :=
  (PreservesCoproduct.iso (Scheme.Modules.pullback (relativeProjToBase s))
      (fun n : ℤ => ℳ.piece n)).hom ≫
    Sigma.desc fun n => shiftedDegreeSheafMap ℳ n ≫
      Sigma.ι (fun k : ℤ => moduleSheaf (ℳ.shift k)) n

/-- **The canonical map `π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` on the summand `π^*ℳ_n`** is the degree-`n`
component followed by the inclusion of the `n`-th summand. The summands generate `π^*ℳ`, so this
determines the map. -/
public theorem pullback_map_ι_shiftedSumSheafMap (n : ℤ) :
    (Scheme.Modules.pullback (relativeProjToBase s)).map
        (Sigma.ι (fun k : ℤ => ℳ.piece k) n) ≫ shiftedSumSheafMap ℳ =
      shiftedDegreeSheafMap ℳ n ≫ Sigma.ι (fun k : ℤ => moduleSheaf (ℳ.shift k)) n := by
  have h := ι_comp_sigmaComparison (Scheme.Modules.pullback (relativeProjToBase s))
    (fun k : ℤ => ℳ.piece k) n
  change _ ≫ (PreservesCoproduct.iso _ _).inv = _ at h
  erw [shiftedSumSheafMap, ← h, Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_desc]

/-- **The canonical map `π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` is the only morphism with these components.** -/
public theorem shiftedSumSheafMap_ext
    {φ : (Scheme.Modules.pullback (relativeProjToBase s)).obj (∐ fun n : ℤ => ℳ.piece n) ⟶
      ∐ fun n : ℤ => moduleSheaf (ℳ.shift n)}
    (hφ : ∀ n : ℤ, (Scheme.Modules.pullback (relativeProjToBase s)).map
        (Sigma.ι (fun k : ℤ => ℳ.piece k) n) ≫ φ =
      shiftedDegreeSheafMap ℳ n ≫ Sigma.ι (fun k : ℤ => moduleSheaf (ℳ.shift k)) n) :
    φ = shiftedSumSheafMap ℳ := by
  refine (cancel_epi (PreservesCoproduct.iso (Scheme.Modules.pullback (relativeProjToBase s))
    (fun n : ℤ => ℳ.piece n)).inv).mp (Sigma.hom_ext _ _ fun n => ?_)
  have h := ι_comp_sigmaComparison (Scheme.Modules.pullback (relativeProjToBase s))
    (fun k : ℤ => ℳ.piece k) n
  change _ ≫ (PreservesCoproduct.iso _ _).inv = _ at h
  erw [← Category.assoc, ← Category.assoc, h, hφ, pullback_map_ι_shiftedSumSheafMap]

/-! ### The chart reading, and Tag 01MR

On the chart over an affine open `W` of the base, the degree-`n` component reads a section `m` of
`ℳ_n` over `W` as the global section `m / 1` of the sheaf attached to the graded module of
sections `Γ(W, ℳ(n))`. That graded module is `Γ(W, ℳ)(n)`, by the reindexing
`Stacks.RelativeProj.Situation.sectionModuleShiftLinearMap`, and through it the section is the
degree-`n` value `m / 1 ∈ Γ(Proj 𝒜(W), Γ(W, ℳ)(n)~)` of the map of Tag 01MR,
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`. -/

section Chart

open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjShiftedSections Stacks.GradedModule

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The reindexing `Γ(U, ℳ(n)) ⟶ Γ(U, ℳ)`: the degree-`k` section `x` of `ℳ(n)`, which is a
section of `ℳ_{k + n}`, goes to `x` in degree `k + n`. -/
public def sectionModuleShiftAddHom (U : s.base.Opens) (n : ℤ) :
    sectionModule (ℳ.shift n) U →+ sectionModule ℳ U :=
  DirectSum.toAddMonoid fun k => DirectSum.of (sectionModulePieces ℳ U) (k + n)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
public theorem sectionModuleShiftAddHom_of (U : s.base.Opens) (n k : ℤ)
    (x : sectionModulePieces (ℳ.shift n) U k) :
    sectionModuleShiftAddHom ℳ U n (DirectSum.of (sectionModulePieces (ℳ.shift n) U) k x) =
      DirectSum.of (sectionModulePieces ℳ U) (k + n) x :=
  DirectSum.toAddMonoid_of _ k x

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The reindexing is linear over the graded ring of sections. -/
public theorem sectionModuleShiftAddHom_smul (U : s.base.Opens) (n : ℤ) (w : s.sectionRing U)
    (z : sectionModule (ℳ.shift n) U) :
    sectionModuleShiftAddHom ℳ U n (w • z) = w • sectionModuleShiftAddHom ℳ U n z := by
  induction w using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, zero_smul]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of k x =>
      rw [sectionModule_of_smul_of (ℳ.shift n) U a x, sectionModuleShiftAddHom_of,
        sectionModuleShiftAddHom_of, sectionModule_of_smul_of ℳ U a x]
      exact DirectSum.of_eq_of_gradedMonoid_eq
        (Sigma.ext (show (i : ℤ) + k + n = i + (k + n) by omega)
          (SheafOfModules.heq_castHom _ _ _ _))
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', add_smul]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The identification `Γ(U, ℳ(n)) = Γ(U, ℳ)(n)`** of graded modules over the graded ring of
sections over `U`, as a linear map: the reindexing of the homogeneous summands. -/
public def sectionModuleShiftLinearMap (U : s.base.Opens) (n : ℤ) :
    sectionModule (ℳ.shift n) U →ₗ[s.sectionRing U] sectionModule ℳ U where
  toFun := sectionModuleShiftAddHom ℳ U n
  map_add' := map_add _
  map_smul' := sectionModuleShiftAddHom_smul ℳ U n

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The reindexing carries the degree-`k` part of `Γ(U, ℳ(n))` into the degree-`k` part of
`Γ(U, ℳ)(n)`, which is the degree-`k + n` part of `Γ(U, ℳ)`. -/
public theorem sectionModuleShiftLinearMap_mem (U : s.base.Opens) (n : ℤ) (k : ℤ)
    (z : sectionModule (ℳ.shift n) U) (hz : z ∈ sectionModuleGrading (ℳ.shift n) U k) :
    sectionModuleShiftLinearMap ℳ U n z ∈ shiftedGrading (sectionModuleGrading ℳ U) n k := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, (sectionModuleShiftAddHom_of ℳ U n k x).symm⟩

/-- **The comparison `Γ(W, ℳ(n))~ ⟶ Γ(W, ℳ)(n)~` of the sheaves on the chart over `W`** induced by
the identification `Γ(W, ℳ(n)) = Γ(W, ℳ)(n)`. -/
public def moduleChartShiftComparison (W : s.base.affineOpens) (n : ℤ) :
    moduleChart (ℳ.shift n) W ⟶
      associatedModuleSheaf (s.sectionRingGrading W.1)
        (shiftedGrading (sectionModuleGrading ℳ W.1) n) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
    (s.sectionRingGrading W.1) (sectionModuleGrading (ℳ.shift n) W.1)
    (shiftedGrading (sectionModuleGrading ℳ W.1) n) (sectionModuleShiftLinearMap ℳ W.1 n)
    (sectionModuleShiftLinearMap_mem ℳ W.1 n)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The identification of the degree-zero piece of `ℳ(n)` with `ℳ_n` does not change the
underlying section. -/
private theorem heq_shiftPieceZeroIso (n : ℤ) (U : (Opens s.base)ᵒᵖ)
    (m : (ℳ.piece n).val.obj U) :
    HEq (((shiftPieceZeroIso ℳ n).hom.val.app U).hom m) m := by
  have key : ∀ (a : ℤ) (h : a = n), HEq
      (((eqToHom (congrArg ℳ.piece h.symm) : ℳ.piece n ⟶ ℳ.piece a).val.app U).hom m) m := by
    rintro a rfl
    rfl
  exact key (0 + n) (zero_add n)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The global section `m / 1` of `Γ(W, ℳ(n))~` is the degree-`n` value of the map of Tag 01MR**
through the comparison with `Γ(W, ℳ)(n)~`: for a section `m` of `ℳ_n` over `W`, the global section
attached to `m`, read as a degree-zero section of `ℳ(n)`, goes to
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections` of `m` in degree `n`. -/
public theorem moduleChartShiftComparison_degreeZeroToGlobalSections (W : s.base.affineOpens)
    (n : ℤ) (m : (ℳ.piece n).val.obj (op W.1)) :
    ((moduleChartShiftComparison ℳ W n).val.app (op ⊤)).hom
        (degreeZeroToGlobalSections (s.sectionRingGrading W.1)
          (sectionModuleGrading (ℳ.shift n) W.1)
          (degreeZeroSectionElem (ℳ.shift n) W.1
            (((shiftPieceZeroIso ℳ n).hom.val.app (op W.1)).hom m))) =
      degreeNToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1) n
        ⟨DirectSum.of (sectionModulePieces ℳ W.1) n m, mem_sectionModuleGrading_of ℳ W.1 m⟩ := by
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans ?_ (degreeNToGlobalSections_apply (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) n
    ⟨DirectSum.of (sectionModulePieces ℳ W.1) n m, mem_sectionModuleGrading_of ℳ W.1 m⟩ x.1).symm
  refine (LocalizedModule.map_mk _ _ _ _).trans ?_
  refine congrArg (fun z => LocalizedModule.mk z
    (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)) ?_
  refine (sectionModuleShiftAddHom_of ℳ W.1 n 0 _).trans ?_
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (zero_add n)
    (heq_shiftPieceZeroIso ℳ n (op W.1) m))

/-- An isomorphism of modules cancels its inverse on elements. -/
private alias iso_hom_inv_apply' := iso_hom_inv_apply

/-- **The degree-`n` component of property (7) of Tag 01O7 generalizes the map of Tag 01MR.** Over
an affine open `W` of the base, transpose the component `π^*ℳ_n ⟶ (ℳ(n))~` across
`π^* ⊣ π_*`, apply it to a section `m` of `ℳ_n` over `W`, read the resulting section of `(ℳ(n))~`
over `π⁻¹(W)` on the chart `Proj 𝒜(W)` and move it along the identification
`Γ(W, ℳ(n)) = Γ(W, ℳ)(n)`: the result is the degree-`n` value `m / 1` of the map
`Γ(W, ℳ) ⟶ ⨁_{n ∈ ℤ} Γ(Proj 𝒜(W), Γ(W, ℳ)(n)~)` of Tag 01MR, restricted to the part of the chart
lying over `W` (which is all of it). -/
public theorem shiftedDegreeSheafMap_chart (W : s.base.affineOpens) (n : ℤ)
    (m : (ℳ.piece n).val.obj (op W.1)) :
    ((moduleChartShiftComparison ℳ W n).val.app
        (op (relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1)))).hom
      (((modulesDirectedGlueData (ℳ.shift n)).chartSectionsIso W
          (preimage_le_opensRange_relativeProjChart W)).hom.hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _
          (shiftedDegreeSheafMap ℳ n)).val.app (op W.1)).hom m)) =
      (associatedModuleSheaf (s.sectionRingGrading W.1)
          (shiftedGrading (sectionModuleGrading ℳ W.1) n)).val.map (homOfLE le_top).op
        (degreeNToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1) n
          ⟨DirectSum.of (sectionModulePieces ℳ W.1) n m, mem_sectionModuleGrading_of ℳ W.1 m⟩) := by
  have h₁ : (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _
      (shiftedDegreeSheafMap ℳ n)).val.app (op W.1)).hom m =
      degreeZeroSection (ℳ.shift n) W (((shiftPieceZeroIso ℳ n).hom.val.app (op W.1)).hom m) :=
    (congrArg (fun k => (k.val.app (op W.1)).hom m) (homEquiv_shiftedDegreeSheafMap ℳ n)).trans
      (degreeZeroPushforwardHom_app_apply (ℳ.shift n) W _)
  refine (congrArg (fun y => ((moduleChartShiftComparison ℳ W n).val.app
      (op (relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1)))).hom
    (((modulesDirectedGlueData (ℳ.shift n)).chartSectionsIso W
      (preimage_le_opensRange_relativeProjChart W)).hom.hom y)) h₁).trans ?_
  refine (congrArg (fun y => ((moduleChartShiftComparison ℳ W n).val.app
      (op (relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1)))).hom y)
    (chartSectionsIso_hom_degreeZeroSection (ℳ.shift n) W _)).trans ?_
  have hle : relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1) ≤ ⊤ := le_top
  exact (PresheafOfModules.naturality_apply (moduleChartShiftComparison ℳ W n).val
    (homOfLE hle).op (degreeZeroToGlobalSections (s.sectionRingGrading W.1)
      (sectionModuleGrading (ℳ.shift n) W.1) (degreeZeroSectionElem (ℳ.shift n) W.1
        (((shiftPieceZeroIso ℳ n).hom.val.app (op W.1)).hom m)))).trans
    (congrArg (fun z => (associatedModuleSheaf (s.sectionRingGrading W.1)
      (shiftedGrading (sectionModuleGrading ℳ W.1) n)).val.map (homOfLE hle).op z)
      (moduleChartShiftComparison_degreeZeroToGlobalSections ℳ W n m))

end Chart

end Stacks.RelativeProj.Situation

end
