module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Noetherian.AdicKernelStabilization

/-!
# The tower of sections of a coherent adic system over an affine chart

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and `E` a coherent
`𝓘`-adic system on the small étale site of `F`, indexed by `ℕᵒᵖ`. Over an affine étale chart `V`
the sections `n ↦ E_n(V)` form a tower of modules over the ring `A = 𝒪_F(V)` whose transition
maps are surjective with kernel `𝓘(V) ^ (n + 1)` times the term above. Over a Noetherian affine
chart the inverse limit of the tower is an adically complete module whose completion is finite
over the completion of `A`.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsSystem`: the tower `n ↦ E_n(V)` of sections over a
  chart.
* `AlgebraicGeometry.Space.chartSectionsLimit`: its inverse limit, and
  `AlgebraicGeometry.Space.chartSectionsLevel` the projection of the limit onto level `n`.
* `AlgebraicGeometry.Space.chartCompletedSections`: the `𝓘(V)`-adic completion of that limit.

## Main results

* `AlgebraicGeometry.Space.surjective_chartSectionsSystem_map`: the transition maps of the tower
  of sections over an affine chart are surjective.
* `AlgebraicGeometry.Space.ker_chartSectionsSystem_map` and
  `AlgebraicGeometry.Space.ker_chartSectionsSystem_map_eq_pow_smul`: the kernel of a transition
  map on the sections over a chart is the sections of `𝓘 ^ (n + 1) E_{n + 1}`, and over an affine
  chart those sections are `𝓘(V) ^ (n + 1) · E_{n + 1}(V)`.
* `AlgebraicGeometry.Space.moduleFinite_chartSectionsSystem_obj`: each term of the tower over an
  affine chart is a finite module over the ring of the chart.
* `AlgebraicGeometry.Space.surjective_chartSectionsLevel`,
  `AlgebraicGeometry.Space.ker_chartSectionsLevel` and
  `AlgebraicGeometry.Space.isAdicComplete_chartSectionsLimit`: the limit of the tower has
  surjective projections with kernel the ideal-power multiple, and is adically complete.
* `AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`: the completed module is finite
  over the completion of the ring of a Noetherian affine chart.
* `AlgebraicGeometry.Space.chartSectionsLimitMap_chartSectionsLevel`: the projections of the
  limit are natural in the system.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### The tower of sections over a chart -/

/-- The tower of sections of an inverse system of `𝒪_F`-modules over an étale chart `V`: the
inverse system `n ↦ E_n(V)` of modules over the ring `𝒪_F(V)` of the chart. -/
def chartSectionsSystem (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    ℕᵒᵖ ⥤ ModuleCat.{u} (chartRing B S hS F hF V) :=
  E ⋙ SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op V)

/-- The term at level `n` of the tower of sections is the sections at that level. -/
theorem chartSectionsSystem_obj (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (n : ℕᵒᵖ) :
    (chartSectionsSystem B S hS F hF E V).obj n =
      ModuleCat.of _ ((E.obj n).val.obj (op V)) :=
  rfl

/-- The transition maps of the tower of sections are the maps on sections of the transition maps
of the system. -/
theorem chartSectionsSystem_map (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (chartSectionsSystem B S hS F hF E V).map g = (E.map g).val.app (op V) :=
  rfl

/-! ### Surjectivity of the transition maps over an affine chart -/

/-- Every term of a coherent adic system is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_of_isCoherentAdicSystem
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (n : ℕ) : IsCartesianOnAffineCharts (E.obj (op n)) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _
    (hE.1 n).toIsQuasicoherentOnSite

/-- The transition maps of the tower of sections of a coherent adic system over an affine chart
are surjective. -/
theorem surjective_chartSectionsSystem_map
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (n : ℕ) :
    Function.Surjective
      (((chartSectionsSystem B S hS F hF E V).map (homOfLE (Nat.le_succ n)).op).hom) := by
  have hepi : Epi (E.map (homOfLE (Nat.le_succ n)).op) :=
    epi_map_le_succ B S hS F hF 𝓘 hE n
  have hsrc := isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 hE (n + 1)
  exact surjective_val_app_of_epi_of_cartesian
    (E.map (homOfLE (Nat.le_succ n)).op) hsrc
    (isCartesianOnAffineCharts_kernel _ hsrc
      (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 hE n)) V hV

/-! ### The kernel of a transition map on sections -/

/-- The kernel of a transition map of a coherent adic system on the sections over a chart is
the sections of `𝓘 ^ (n + 1) E_{n + 1}`. -/
theorem ker_chartSectionsSystem_map
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (V : SmallEtale B S hS F) (n : ℕ) :
    LinearMap.ker
        (((chartSectionsSystem B S hS F hF E V).map (homOfLE (Nat.le_succ n)).op).hom) =
      chartSubmodule B S hS F hF
        (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1)))) V := by
  obtain ⟨e, he⟩ := hE.2.2 n
  ext s
  have hval : ((chartSectionsSystem B S hS F hF E V).map (homOfLE (Nat.le_succ n)).op).hom s =
      e.hom.val.app (op V)
        ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (E.obj (op (n + 1)))).ι).val.app (op V) s) := by
    rw [chartSectionsSystem_map, ← he]
    rfl
  have hmono : Function.Injective (e.hom.val.app (op V)) :=
    Function.LeftInverse.injective (g := e.inv.val.app (op V)) fun z =>
      congrArg
        (fun k : idealPowerQuotient B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1))) ⟶
            idealPowerQuotient B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1))) =>
          k.val.app (op V) z) e.hom_inv_id
  have hiff := cokernel_π_app_eq_zero_iff B S hS F hF
    (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1)))) (op V) s
  exact ⟨fun hs => hiff.mp
      (hmono ((hval.symm.trans (LinearMap.mem_ker.mp hs)).trans (map_zero _).symm)),
    fun hs => LinearMap.mem_ker.mpr (hval.trans
      ((congrArg (fun z => e.hom.val.app (op V) z) (hiff.mpr hs)).trans (map_zero _)))⟩

/-- Over an affine chart the kernel of a transition map on sections is `𝓘(V) ^ (n + 1)` times
the sections above. -/
theorem ker_chartSectionsSystem_map_eq_pow_smul
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (n : ℕ) :
    LinearMap.ker
        (((chartSectionsSystem B S hS F hF E V).map (homOfLE (Nat.le_succ n)).op).hom) =
      chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V)
          ((E.obj (op (n + 1))).val.obj (op V))) := by
  rw [ker_chartSectionsSystem_map B S hS F hF 𝓘 hE V n,
    idealPowerMultiple_eq_idealPowSubmodule B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1))),
    chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS F hF 𝓘 (E.obj (op (n + 1)))
      (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 hE (n + 1))
      hIcart (n + 1) hV]

/-! ### Finiteness of the terms over a Noetherian affine chart -/

/-- Each term of the tower of sections of a coherent adic system over an affine chart is a finite
module over the ring of the chart. -/
theorem moduleFinite_chartSectionsSystem_obj
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (n : ℕ) :
    Module.Finite (chartRing B S hS F hF V)
      ((chartSectionsSystem B S hS F hF E V).obj (op n)) :=
  moduleFinite_sections_of_isCoherent B S hS F hF (E.obj (op n)) (hE.1 n) hV

/-! ### The limit of the tower, and its completion -/

/-- The map on the towers of sections over a chart induced by a morphism of inverse systems of
`𝒪_F`-modules. -/
def chartSectionsSystemMap {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (τ : E ⟶ E')
    (V : SmallEtale B S hS F) :
    chartSectionsSystem B S hS F hF E V ⟶ chartSectionsSystem B S hS F hF E' V :=
  Functor.whiskerRight τ (SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op V))

/-- The inverse limit of the tower of sections of an inverse system of `𝒪_F`-modules over an
étale chart. -/
def chartSectionsLimit (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    ModuleCat.{u} (chartRing B S hS F hF V) :=
  limit (chartSectionsSystem B S hS F hF E V)

/-- The projection of the limit of the tower of sections over a chart onto its term at a
level. -/
def chartSectionsLevel (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (n : ℕ) :
    chartSectionsLimit B S hS F hF E V ⟶ (chartSectionsSystem B S hS F hF E V).obj (op n) :=
  limit.π (chartSectionsSystem B S hS F hF E V) (op n)

/-- The map between the limits of the towers of sections induced by a morphism of inverse
systems. -/
def chartSectionsLimitMap {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (τ : E ⟶ E')
    (V : SmallEtale B S hS F) :
    chartSectionsLimit B S hS F hF E V ⟶ chartSectionsLimit B S hS F hF E' V :=
  limMap (chartSectionsSystemMap B S hS F hF τ V)

/-- The projections of the limit of the tower of sections commute with a morphism of inverse
systems. -/
theorem chartSectionsLimitMap_chartSectionsLevel
    {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (τ : E ⟶ E') (V : SmallEtale B S hS F) (n : ℕ) :
    chartSectionsLimitMap B S hS F hF τ V ≫ chartSectionsLevel B S hS F hF E' V n =
      chartSectionsLevel B S hS F hF E V n ≫ (chartSectionsSystemMap B S hS F hF τ V).app (op n) :=
  limMap_π _ _

/-- The projections of the limit of the tower of sections over an affine chart are
surjective. -/
theorem surjective_chartSectionsLevel
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (n : ℕ) :
    Function.Surjective ((chartSectionsLevel B S hS F hF E V n).hom) :=
  Stacks.Coherent.moduleLimit_projection_surjective _
    (surjective_chartSectionsSystem_map B S hS F hF 𝓘 hE hV) n

/-- Over a Noetherian affine chart, the kernel of the projection of the limit onto level `n` is
`𝓘(V) ^ (n + 1)` times the limit. -/
theorem ker_chartSectionsLevel
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) (n : ℕ) :
    LinearMap.ker ((chartSectionsLevel B S hS F hF E V n).hom) =
      chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V)
          (chartSectionsLimit B S hS F hF E V)) :=
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  Stacks.Coherent.moduleLimit_projection_ker _
    (surjective_chartSectionsSystem_map B S hS F hF 𝓘 hE hV.1)
    (ker_chartSectionsSystem_map_eq_pow_smul B S hS F hF 𝓘 hE hIcart hV.1)
    (Ideal.fg_of_isNoetherianRing _) n

/-- The limit of the tower of sections over a Noetherian affine chart is adically
complete. -/
theorem isAdicComplete_chartSectionsLimit
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) :
    IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  Stacks.Coherent.moduleLimit_isAdicComplete _
    (surjective_chartSectionsSystem_map B S hS F hF 𝓘 hE hV.1)
    (ker_chartSectionsSystem_map_eq_pow_smul B S hS F hF 𝓘 hE hIcart hV.1)
    (Ideal.fg_of_isNoetherianRing _)

/-- The reduction of the limit modulo `𝓘(V)` is a finite module over the ring of a Noetherian
affine chart. -/
theorem moduleFinite_chartSectionsLimit_quotient
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) :
    Module.Finite (chartRing B S hS F hF V)
      ((chartSectionsLimit B S hS F hF E V) ⧸
        (chartSectionIdeal B S hS F hF 𝓘 V •
          (⊤ : Submodule (chartRing B S hS F hF V)
            (chartSectionsLimit B S hS F hF E V)))) :=
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  Stacks.Coherent.moduleLimit_zeroQuotient_finite _
    (surjective_chartSectionsSystem_map B S hS F hF 𝓘 hE hV.1)
    (ker_chartSectionsSystem_map_eq_pow_smul B S hS F hF 𝓘 hE hIcart hV.1)
    (Ideal.fg_of_isNoetherianRing _)
    (moduleFinite_chartSectionsSystem_obj B S hS F hF 𝓘 hE hV.1 0)

/-- The `𝓘(V)`-adic completion of the limit of the tower of sections over a chart, a module
over the completed ring `𝒪_F(V)^∧`. -/
abbrev chartCompletedSections (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) : Type u :=
  AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
    (chartSectionsLimit B S hS F hF E V)

/-- The completed module of a coherent adic system over a Noetherian affine chart is finite over
the completion of the ring of the chart. -/
theorem moduleFinite_chartCompletedSections
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) :
    Module.Finite (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
        (chartRing B S hS F hF V))
      (chartCompletedSections B S hS F hF 𝓘 E V) :=
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  Stacks.Coherent.finite_adicCompletion_of_finite_reduction
    (Ideal.fg_of_isNoetherianRing _) _
    (moduleFinite_chartSectionsLimit_quotient B S hS F hF 𝓘 hE hIcart hV)

end AlgebraicGeometry.Space

end
