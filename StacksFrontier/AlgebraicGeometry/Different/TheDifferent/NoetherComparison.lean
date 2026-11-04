module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.TraceElement
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections

/-!
# The different and the Noether different on a chart with invertible dualizing module

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes, with
relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`.  On an affine chart
`V = Spec B ⊆ Y` lying over an affine open `U = Spec A ⊆ X` for which `ω_{B/A}` is an invertible
`B`-module, the different `𝔇_f` of [Stacks, Tag 0BW4] is the Noether different of `B` over `A`.

## Main results

* `Stacks.Discriminant.different_sections_eq_noetherDifferent`: the ideal of sections of the
  different over such a chart is the Noether different of the chart algebra.

## Implementation notes

[Stacks, Tag 0BW6] states the conclusion as an equality `𝔇_f|_V = 𝔇~` of coherent ideal
sheaves on `V`.  The different is coherent (`Stacks.Discriminant.isCoherent_different`), and on
an affine open a coherent ideal sheaf is the tilde of its ideal of sections, so that equality of
sheaves holds exactly when the two ideals of sections over `V` agree.  The ideal equality is
what is proved here; it is the affine-local reading of the source statement.

The ambient category is `AlgebraicGeometry.Scheme.Modules`, written `Y.Modules`, throughout, and
the trace morphism `Stacks.Discriminant.traceMorphism` is read there.  The two spellings
`Y.Modules` and `SheafOfModules Y.ringCatSheaf` have the same underlying type but carry different
`CategoryTheory.Category` instances, so a cokernel formed at one of them is not found by instance
search at the other; the two are bridged in one place (`Stacks.Discriminant.traceCoker_eq`) by a
definitional equality rather than being mixed.

## References

* [Stacks Project, Tag 0BW6](https://stacks.math.columbia.edu/tag/0BW6)
* [Stacks Project, Tag 0BW4](https://stacks.math.columbia.edu/tag/0BW4)
* [Stacks Project, Tag 0BVT](https://stacks.math.columbia.edu/tag/0BVT)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing Scheme.Modules

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

/-- The structure sheaf of `Y`, read as an object of the category `Y.Modules`. -/
def unitModule (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

/-- The trace morphism `𝒪_Y → ω_{Y/X}`, read in the category `Y.Modules` of `𝒪_Y`-modules. -/
def traceHom (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    unitModule Y ⟶ ω.sheaf :=
  traceMorphism ω τ

/-- The cokernel of the trace morphism, formed in `Y.Modules`. -/
def traceCoker (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    Y.Modules :=
  cokernel (traceHom ω τ)

/-- The cokernel of the trace morphism formed in `Y.Modules` is `traceCokernel ω τ`. -/
theorem traceCoker_eq (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) :
    traceCoker ω τ = traceCokernel ω τ := rfl

/-- The cokernel of the trace morphism is coherent. -/
theorem isCoherent_traceCoker (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) : (traceCoker ω τ).IsCoherent :=
  have : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have : _root_.SheafOfModules.IsCoherent ω.sheaf := ω.isCoherent
  _root_.SheafOfModules.cokernel_isCoherent (traceHom ω τ)

/-- The sections of the different over an affine chart are the annihilator of the sections of
the cokernel of the trace morphism there.  This is [Stacks, Tag 02OM] applied to the coherent
module `Coker(τ_{Y/X})`. -/
theorem different_sections_eq_annihilator (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (V : Y.affineOpens) :
    (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
      Module.annihilator Γ(Y, V.1) Γ(traceCoker ω τ, V.1) := by
  have := isCoherent_traceCoker ω τ
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (traceCoker ω τ)
  obtain ⟨I, -, hIeq, hI⟩ :=
    AlgebraicGeometry.exists_isCoherent_submodule_eq_annihilatorIdeal (traceCoker ω τ)
  rw [← AlgebraicGeometry.annihilatorIdeal_ideal (traceCoker ω τ) V, hI V, hIeq]
  rfl

/-- The structure sheaf of a locally Noetherian scheme is quasi-coherent. -/
theorem isQuasicoherent_unitModule (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (unitModule Y).IsQuasicoherent :=
  have : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (unitModule Y)).1

/-- Over an affine chart, the sections of the cokernel of the trace morphism are the sections of
the relative dualizing module modulo the line through the chart image of the trace section. -/
def cokernelSectionsEquiv (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (V : Y.affineOpens) :
    (Γ(ω.sheaf, V.1) ⧸
        Submodule.span Γ(Y, V.1) {(traceHom ω τ).app V.1 (1 : Γ(Y, V.1))}) ≃ₗ[Γ(Y, V.1)]
      Γ(traceCoker ω τ, V.1) := by
  have : (unitModule Y).IsQuasicoherent := isQuasicoherent_unitModule Y
  have : ω.sheaf.IsQuasicoherent := ω.isQuasicoherent
  have hsurj : Function.Surjective
      (Scheme.Modules.sectionsLinearMap (cokernel.π (traceHom ω τ)) V.1) :=
    AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen (cokernel.π (traceHom ω τ)) V.2
  have hker : LinearMap.ker
        (Scheme.Modules.sectionsLinearMap (cokernel.π (traceHom ω τ)) V.1) =
      LinearMap.range (Scheme.Modules.sectionsLinearMap (traceHom ω τ) V.1) :=
    LinearMap.exact_iff.mp
      (Stacks.Algebraization.affine_sections_cokernel_exact (traceHom ω τ) V)
  have hrange : LinearMap.range (Scheme.Modules.sectionsLinearMap (traceHom ω τ) V.1) =
      Submodule.span Γ(Y, V.1) {(traceHom ω τ).app V.1 (1 : Γ(Y, V.1))} := by
    have hgen : ∀ b : Γ(unitModule Y, V.1),
        Scheme.Modules.sectionsLinearMap (traceHom ω τ) V.1 b =
          (show Γ(Y, V.1) from b) • (traceHom ω τ).app V.1 (1 : Γ(Y, V.1)) := by
      intro b
      have hb : (show Γ(Y, V.1) from b) •
          (show Γ(unitModule Y, V.1) from (1 : Γ(Y, V.1))) = b :=
        mul_one (show Γ(Y, V.1) from b)
      have hsm := Scheme.Modules.Hom.app_smul (traceHom ω τ) (show Γ(Y, V.1) from b)
        (show Γ(unitModule Y, V.1) from (1 : Γ(Y, V.1)))
      rwa [hb] at hsm
    refine le_antisymm ?_ ?_
    · rintro x ⟨b, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨b, (hgen b).symm⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨(1 : Γ(Y, V.1)), rfl⟩
  exact (Submodule.quotEquivOfEq _ _ (hker.trans hrange).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)

/-- **[Stacks, Tag 0BW6].** Let `f : Y ⟶ X` be flat and locally quasi-finite between locally
Noetherian schemes, with relative dualizing module `ω` and trace section `τ`.  On affine opens
`V = Spec B ⊆ Y` and `U = Spec A ⊆ X` with `f(V) ⊆ U`, if the algebraic relative dualizing
module `ω_{B/A}` is an invertible `B`-module, then the ideal of sections of the different over
`V` is the Noether different of `B` over `A`.

The source states this as `𝔇_f|_V = 𝔇~` as coherent ideal sheaves on `V`; the different is a
coherent ideal sheaf, so on the affine `V` it is the tilde of its ideal of sections and the two
readings agree. -/
@[stacks 0BW6]
theorem different_sections_eq_noetherDifferent (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)),
      Module.Invertible Γ(Y, V.1) (dualizingModule F) →
        (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
          noetherDifferent Γ(X, U.1) Γ(Y, V.1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  intro F _
  let := moduleOfLE ω.sheaf (show V.1 ≤ ⊤ from le_top)
  have hsect : ω.localEquiv U V hVU F ((traceHom ω τ).app V.1 (1 : Γ(Y, V.1))) =
      dualizingModule.traceElement F := by
    have happ : (traceHom ω τ).app V.1 (1 : Γ(Y, V.1)) =
        restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) τ.sect :=
      traceMorphism_app_one ω τ V.1
    rw [happ]
    exact eq_traceElement_of_isTraceElement F (τ.isTraceElement_localEquiv U V hVU F)
  have hmap : Submodule.map
      (ω.localEquiv U V hVU F : Γ(ω.sheaf, V.1) →ₗ[Γ(Y, V.1)] dualizingModule F)
      (Submodule.span Γ(Y, V.1) {(traceHom ω τ).app V.1 (1 : Γ(Y, V.1))}) =
      Submodule.span Γ(Y, V.1) {dualizingModule.traceElement F} := by
    rw [Submodule.map_span, Set.image_singleton]
    exact congrArg (Submodule.span Γ(Y, V.1) {·}) hsect
  have e : Γ(traceCoker ω τ, V.1) ≃ₗ[Γ(Y, V.1)]
      (dualizingModule F ⧸ Submodule.span Γ(Y, V.1) {dualizingModule.traceElement F}) :=
    (cokernelSectionsEquiv ω τ V).symm.trans
      (Submodule.Quotient.equiv _ _ (ω.localEquiv U V hVU F) hmap)
  rw [different_sections_eq_annihilator ω τ V, e.annihilator_eq]
  refine SetLike.coe_injective ?_
  rw [← range_eval_eq_annihilator_quotient_span (dualizingModule.traceElement F)]
  exact (noetherDifferent_eq_range_traceElement F).symm

end Stacks.Discriminant

end
