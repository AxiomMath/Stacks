module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleExistence0BVG
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeTraceSection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.AnnihilatorCoherent

/-!
# The different of a flat locally quasi-finite morphism

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes, let
`ω_{Y/X}` be its relative dualizing module and let `τ_{Y/X} ∈ Γ(Y, ω_{Y/X})` be its trace
element.  The *different* `𝔇_f ⊆ 𝒪_Y` is the annihilator of the cokernel of the map
`𝒪_Y → ω_{Y/X}` sending `1` to `τ_{Y/X}`, and it is a coherent ideal.

## Main definitions

* `Stacks.Discriminant.sectionHom`: the map `𝒪_Y → ω_{Y/X}` determined by a global section of
  `ω_{Y/X}`, and `Stacks.Discriminant.annihilatorSectionCokernel` the annihilator of its
  cokernel.  Neither needs `f` flat.
* `Stacks.Discriminant.RelativeTraceSection`: a global section of the sheaf of a relative
  dualizing chart datum whose image on every affine chart is the algebraic trace element.
* `Stacks.Discriminant.traceMorphism`: the map `𝒪_Y → ω_{Y/X}` determined by such a section.
* `AlgebraicGeometry.Scheme.Hom.different`: **the different `𝔇_f` of Tag 0BW4**, as a submodule
  sheaf of `𝒪_Y`, built from the relative dualizing module
  `Stacks.Discriminant.relativeDualizingModuleData f` of Tag 0BVG and its trace element
  `Stacks.Discriminant.relativeTraceSection` of Tag 0BVJ.
* `Stacks.Discriminant.different`: the same annihilator, formed from an arbitrary relative
  dualizing module datum and trace element.  Every choice gives `f.different`
  (`AlgebraicGeometry.Scheme.Hom.different_eq`).

## Main results

* `Stacks.Discriminant.range_eval_eq_annihilator_quotient_span`: for an invertible module `ω`
  over a commutative ring `B` and `τ : ω`, the image of evaluation at `τ` on the dual of `ω`
  is the annihilator of `ω / Bτ`.
* `AlgebraicGeometry.Scheme.Hom.isCoherent_different`: the different is a coherent ideal.
  `Stacks.Discriminant.isCoherent_different` is the same for an arbitrary datum.
* `Stacks.Discriminant.mem_different_iff`: a section of `𝒪_Y` lies in the different exactly
  when all of its restrictions annihilate the cokernel of the trace map.
* `Stacks.Discriminant.RelativeTraceSection.canonical` and
  `Stacks.Discriminant.RelativeTraceSection.sect_eq`: every relative dualizing module datum has a
  trace element, the relative trace section `τ_{Y/X}` of Tag 0BVJ, and only that one.

## Implementation notes

The relative dualizing module `ω_{Y/X}` of Tag 0BVG and its trace element `τ_{Y/X}` of
Tag 0BVJ enter as *data*: `Stacks.Discriminant.RelativeDualizingModuleData`, a sheaf on `Y`
with its identifications over the affine charts, and `Stacks.Discriminant.RelativeTraceSection`,
a global section whose image in every affine chart is a trace element in the sense of Tag 0BT6
(`Stacks.Discriminant.IsTraceElement`).  The canonical datum is
`Stacks.Discriminant.relativeDualizingModuleData`, any two data are related by the unique
comparison of Tag 0BVG, and by Tag 0BT7 the trace element of a datum is pinned down chart by
chart.  The statements below hold for every such datum, the canonical one in particular.

The annihilator is `Stacks.SheafOfModules.annihilatorSheaf` of Tag 0H2H, and coherence comes
from Tag 0H2L together with coherence of the structure sheaf of a locally Noetherian scheme
(Tag 01XZ) and of a cokernel of coherent modules (Tag 01BY).

The structure sheaf is spelled `AlgebraicGeometry.Scheme.ringCatSheaf` wherever a sheaf of
modules on `Y` is meant, and `structureSheafRing Y.toRingedSpace` wherever
the annihilator interface is used; the two have the same body but are not interchangeable for
typeclass resolution, so the ambient category is fixed as `SheafOfModules Y.ringCatSheaf`
throughout.

## References

* [Stacks Project, Tag 0BW4](https://stacks.math.columbia.edu/tag/0BW4)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
* [Stacks Project, Tag 0BVJ](https://stacks.math.columbia.edu/tag/0BVJ)
* [Stacks Project, Tag 0H2H](https://stacks.math.columbia.edu/tag/0H2H)
* [Stacks Project, Tag 0H2L](https://stacks.math.columbia.edu/tag/0H2L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u v w

namespace Stacks.Discriminant

/-! ### The elementary fact about invertible modules -/

section Invertible

variable {B : Type u} [CommRing B] {ω : Type v} [AddCommGroup ω] [Module B ω]

/-- For an invertible module `ω` over a commutative ring `B` and an element `τ : ω`, the image
of the evaluation map `Hom_B(ω, B) → B`, `φ ↦ φ τ`, is the annihilator of `ω / Bτ`, that is,
of the cokernel of `B → ω`, `b ↦ b τ`. -/
theorem range_eval_eq_annihilator_quotient_span [Module.Invertible B ω] (τ : ω) :
    (Set.range fun φ : ω →ₗ[B] B ↦ φ τ) =
      (Module.annihilator B (ω ⧸ Submodule.span B {τ}) : Set B) := by
  classical
  have hbij : Function.Bijective (contractLeft B ω) := Module.Invertible.bijective
  obtain ⟨w, hw⟩ := hbij.surjective 1
  -- Every tensor in `ωᵛ ⊗ ω` is a multiple of the distinguished one.
  have hcol : ∀ t : Module.Dual B ω ⊗[B] ω, t = contractLeft B ω t • w := fun t ↦
    hbij.injective (by rw [map_smul, hw, smul_eq_mul, mul_one])
  -- An element killed by every value of every functional is zero.
  have hzero : ∀ y : ω, (∀ (ψ : Module.Dual B ω) (z : ω), ψ z • y = 0) → y = 0 := by
    intro y hy
    have hL : (LinearMap.toSpanSingleton B ω y) ∘ₗ contractLeft B ω = 0 :=
      TensorProduct.ext' fun ψ z ↦ by
        simpa [LinearMap.toSpanSingleton_apply] using hy ψ z
    have hwy := congrArg (fun g : Module.Dual B ω ⊗[B] ω →ₗ[B] ω ↦ g w) hL
    simpa [LinearMap.toSpanSingleton_apply, hw] using hwy
  let h : ω →ₗ[B] ω := dualTensorHom B ω ω w
  have hh : h = dualTensorHom B ω ω w := rfl
  -- The defining identity of an invertible module: `ψ x • z = ψ z • h x`.
  have key : ∀ (ψ : Module.Dual B ω) (z x : ω), ψ x • z = ψ z • h x := by
    intro ψ z x
    have hd := congrArg (dualTensorHom B ω ω) (hcol (ψ ⊗ₜ[B] z))
    rw [map_smul, contractLeft_apply] at hd
    simpa [hh] using congrArg (fun g : ω →ₗ[B] ω ↦ g x) hd
  -- Hence `h` is an involution, in particular surjective.
  have hinvol : ∀ x : ω, h (h x) = x := by
    intro x
    refine sub_eq_zero.mp (hzero (h (h x) - x) fun ψ z ↦ ?_)
    have e₁ : ψ x • h z = ψ z • h (h x) := by
      simpa only [map_smul] using congrArg (fun y : ω ↦ h y) (key ψ z x)
    rw [smul_sub, ← e₁, ← key ψ x z, sub_self]
  let ev : (ω →ₗ[B] B) →ₗ[B] B :=
    { toFun := fun φ ↦ φ τ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  ext b
  simp only [Set.mem_range, SetLike.mem_coe, Module.mem_annihilator]
  constructor
  · rintro ⟨φ, rfl⟩ q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hx : φ τ • x = φ (h x) • τ := by simpa only [hinvol x] using (key φ τ (h x)).symm
    rw [hx]
    exact Submodule.mem_span_singleton.mpr ⟨φ (h x), rfl⟩
  · intro hb
    have hspan : ∀ x : ω, b • x ∈ Submodule.span B {τ} := by
      intro x
      have hbx := hb (Submodule.Quotient.mk x)
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hbx
    have hmem : ∀ t : Module.Dual B ω ⊗[B] ω,
        b * contractLeft B ω t ∈ LinearMap.range ev := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul ψ z =>
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan z)
        refine ⟨a • ψ, ?_⟩
        have hψ := congrArg (fun y : ω ↦ ψ y) ha
        simp only [map_smul, smul_eq_mul] at hψ
        change a * ψ τ = b * contractLeft B ω (ψ ⊗ₜ[B] z)
        simpa using hψ
      | add s t hs ht =>
        simpa [mul_add] using Submodule.add_mem (LinearMap.range ev) hs ht
    obtain ⟨φ, hφ⟩ := hmem w
    exact ⟨φ, by rwa [hw, mul_one] at hφ⟩

end Invertible

/-! ### The trace section and the different -/

section Section

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-- The morphism `𝒪_Y → ω_{Y/X}` determined by a global section of `ω_{Y/X}`: it sends the
unit section over an open to the restriction of that section to the open. -/
def sectionHom (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ ω.sheaf :=
  ω.sheaf.unitHomEquiv.symm
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf ω.sheaf s)

/-- The value of `Stacks.Discriminant.sectionHom` on the unit section over an open is the
restriction of the section to that open. -/
theorem sectionHom_app_one (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤))
    (U : Y.Opens) :
    ((sectionHom ω s).val.app (op U)).hom (1 : Γ(Y, U)) =
      (ω.sheaf.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s :=
  congrArg (fun t : ω.sheaf.sections ↦ t.val (op U))
    (ω.sheaf.unitHomEquiv.apply_symm_apply
      (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf ω.sheaf s))

/-- The cokernel of `Stacks.Discriminant.sectionHom`, read as a module over the structure
sheaf in its ringed-space spelling. -/
def sectionCokernel (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) :
    SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  cokernel (sectionHom ω s)

/-- The annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}` given by a global section of
`ω_{Y/X}`. -/
def annihilatorSectionCokernel (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) :
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).Submodule :=
  Stacks.SheafOfModules.annihilatorSheaf Y.toRingedSpace (sectionCokernel ω s)

/-- A section of `𝒪_Y` over `U` lies in the annihilator of the cokernel of
`Stacks.Discriminant.sectionHom` exactly when each of its restrictions annihilates every local
section of that cokernel. -/
theorem mem_annihilatorSectionCokernel_iff (ω : RelativeDualizingModuleData f)
    (s : Γ(ω.sheaf, ⊤)) (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureSheafRing Y.toRingedSpace).obj.obj U) :
    r ∈ (annihilatorSectionCokernel ω s).toSubmodule.obj U ↔
      ∀ (V : (Opens Y.carrier)ᵒᵖ) (i : U ⟶ V) (m : (sectionCokernel ω s).val.obj V),
        ((structureSheafRing Y.toRingedSpace).obj.map i r) • m = 0 :=
  Iff.rfl

/-- The annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}` given by a global section is a
coherent ideal of `𝒪_Y`. -/
theorem isCoherent_annihilatorSectionCokernel (ω : RelativeDualizingModuleData f)
    (s : Γ(ω.sheaf, ⊤)) :
    Stacks.SheafOfModules.IsCoherent (annihilatorSectionCokernel ω s).toSheafOfModules := by
  have hunit : Stacks.SheafOfModules.IsCoherent
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y)
  have hunit' : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Y.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hω : _root_.SheafOfModules.IsCoherent ω.sheaf := ω.isCoherent
  have hcok : Stacks.SheafOfModules.IsCoherent (sectionCokernel ω s) :=
    (_root_.SheafOfModules.isCoherent_iff _).mp
      (@_root_.SheafOfModules.cokernel_isCoherent _ _ _ _ _ hunit' hω (sectionHom ω s))
  exact @Stacks.SheafOfModules.isCoherent_annihilatorSheaf Y.toRingedSpace
    (sectionCokernel ω s) hunit hcok

end Section

section Different

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

/-- The trace element `τ_{Y/X} ∈ Γ(Y, ω_{Y/X})` of [Stacks, Tag 0BVJ], as data: a global
section of the sheaf of a relative dualizing chart datum whose image under the affine
identification of every chart is a trace element in the sense of [Stacks, Tag 0BT6].  By
[Stacks, Tag 0BT7] such an image is unique, so this condition pins the section chart by
chart. -/
structure RelativeTraceSection (ω : RelativeDualizingModuleData f) where
  /-- The global section of the relative dualizing module. -/
  sect : Γ(ω.sheaf, ⊤)
  /-- On every affine chart the section becomes the algebraic trace element. -/
  isTraceElement_localEquiv :
    ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
      letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
        RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
      letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
      letI := moduleOfLE ω.sheaf (show V.1 ≤ ⊤ from le_top)
      ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
        IsTraceElement.{u, u, u, u, u, u} F
          (ω.localEquiv U V hVU F (restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) sect))

/-- **The trace element of a relative dualizing module datum**, [Stacks, Tag 0BVJ]: the global
section `Stacks.Discriminant.relativeTraceSection ω`, which restricts on every affine chart to
the trace element of the chart's coordinate-ring map. -/
def RelativeTraceSection.canonical (ω : RelativeDualizingModuleData f) :
    RelativeTraceSection ω where
  sect := relativeTraceSection ω
  isTraceElement_localEquiv U V hVU F := by
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    exact (isTraceElement_iff_eq_traceCandidate F _).mpr
      (localEquiv_relativeTraceSection ω U V hVU F)

/-- The section of a trace element of a relative dualizing module datum is the relative trace
section. -/
theorem RelativeTraceSection.sect_eq (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) : τ.sect = relativeTraceSection ω := by
  obtain ⟨σ, -, hσ⟩ := existsUnique_relativeTraceSection ω
  refine (hσ τ.sect fun U V hVU F => ?_).trans (hσ _ (localEquiv_relativeTraceSection ω)).symm
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  exact (isTraceElement_iff_eq_traceCandidate F _).mp (τ.isTraceElement_localEquiv U V hVU F)

/-- A relative dualizing module datum has exactly one trace element. -/
instance (ω : RelativeDualizingModuleData f) : Subsingleton (RelativeTraceSection ω) := by
  refine ⟨fun τ₁ τ₂ => ?_⟩
  have h := (RelativeTraceSection.sect_eq ω τ₁).trans (RelativeTraceSection.sect_eq ω τ₂).symm
  cases τ₁
  cases τ₂
  cases h
  rfl

/-- The morphism `𝒪_Y → ω_{Y/X}` determined by the trace element: it sends the unit section
over an open to the restriction of `τ_{Y/X}` to that open. -/
def traceMorphism (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ ω.sheaf :=
  sectionHom ω τ.sect

/-- The value of the trace morphism on the unit section over an open is the restriction of the
trace element to that open. -/
theorem traceMorphism_app_one (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (U : Y.Opens) :
    ((traceMorphism ω τ).val.app (op U)).hom (1 : Γ(Y, U)) =
      (ω.sheaf.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom τ.sect :=
  sectionHom_app_one ω τ.sect U

/-- The cokernel of the trace morphism, `Coker(τ_{Y/X} : 𝒪_Y → ω_{Y/X})`, read as a module
over the structure sheaf in its ringed-space spelling. -/
def traceCokernel (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  sectionCokernel ω τ.sect

/-- The annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}` given by the trace element of a
relative dualizing module datum `ω`.  For the canonical datum this is the different
`AlgebraicGeometry.Scheme.Hom.different` of [Stacks, Tag 0BW4], and by
`AlgebraicGeometry.Scheme.Hom.different_eq` every datum gives that same ideal. -/
def different (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).Submodule :=
  annihilatorSectionCokernel ω τ.sect

/-- A section of `𝒪_Y` over `U` lies in the different exactly when each of its restrictions
annihilates every local section of the cokernel of the trace morphism. -/
theorem mem_different_iff (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
    (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureSheafRing Y.toRingedSpace).obj.obj U) :
    r ∈ (different ω τ).toSubmodule.obj U ↔
      ∀ (V : (Opens Y.carrier)ᵒᵖ) (i : U ⟶ V) (m : (traceCokernel ω τ).val.obj V),
        ((structureSheafRing Y.toRingedSpace).obj.map i r) • m = 0 :=
  Iff.rfl

/-- The annihilator of the cokernel of the trace morphism of a relative dualizing module datum
is a coherent ideal of `𝒪_Y`. -/
theorem isCoherent_different (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) :
    Stacks.SheafOfModules.IsCoherent (different ω τ).toSheafOfModules :=
  isCoherent_annihilatorSectionCokernel ω τ.sect

end Different

/-! ### The different of a flat locally quasi-finite morphism -/

section Intrinsic

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyOfFiniteType f]
  [LocallyQuasiFinite f]

/-- The *different* `𝔇_f ⊆ 𝒪_Y` of a flat locally quasi-finite morphism `f : Y ⟶ X` of locally
Noetherian schemes: the annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}`, `1 ↦ τ_{Y/X}`,
where `ω_{Y/X}` is the relative dualizing module
`Stacks.Discriminant.relativeDualizingModuleData f` and `τ_{Y/X}` is its trace element
`Stacks.Discriminant.relativeTraceSection`.

The hypothesis `LocallyOfFiniteType f` is part of the source's "locally quasi-finite", which
includes being locally of finite type; Mathlib's `LocallyQuasiFinite` does not.  The ideal does
not depend on the relative dualizing module chosen: `Scheme.Hom.different_eq`. -/
@[stacks 0BW4 "the different"]
def _root_.AlgebraicGeometry.Scheme.Hom.different :
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).Submodule :=
  annihilatorSectionCokernel (relativeDualizingModuleData f)
    (relativeTraceSection (relativeDualizingModuleData f))

/-- The different of `f` is the annihilator of the cokernel of the trace morphism of the
canonical relative dualizing module with its trace element. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.different_eq_canonical :
    f.different = Stacks.Discriminant.different (relativeDualizingModuleData f)
      (RelativeTraceSection.canonical (relativeDualizingModuleData f)) :=
  rfl

/-- A section of `𝒪_Y` over `U` lies in the different of `f` exactly when each of its
restrictions annihilates every local section of `Coker(τ_{Y/X} : 𝒪_Y → ω_{Y/X})`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.mem_different_iff (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureSheafRing Y.toRingedSpace).obj.obj U) :
    r ∈ f.different.toSubmodule.obj U ↔
      ∀ (V : (Opens Y.carrier)ᵒᵖ) (i : U ⟶ V)
        (m : (sectionCokernel (relativeDualizingModuleData f)
          (relativeTraceSection (relativeDualizingModuleData f))).val.obj V),
        ((structureSheafRing Y.toRingedSpace).obj.map i r) • m = 0 :=
  Iff.rfl

/-- The different `𝔇_f` of a flat locally quasi-finite morphism of locally Noetherian schemes is
a coherent ideal of `𝒪_Y`. -/
@[stacks 0BW4 "coherence"]
theorem _root_.AlgebraicGeometry.Scheme.Hom.isCoherent_different :
    Stacks.SheafOfModules.IsCoherent f.different.toSheafOfModules :=
  isCoherent_annihilatorSectionCokernel (relativeDualizingModuleData f)
    (relativeTraceSection (relativeDualizingModuleData f))

end Intrinsic

end Stacks.Discriminant

end
