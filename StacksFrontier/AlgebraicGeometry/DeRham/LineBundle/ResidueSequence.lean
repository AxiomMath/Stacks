module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroChart
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basis
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequence
import StacksCore.Tactic.StacksAttribute
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The residue sequence of the complement of the zero section of a line bundle

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. This file glues the residues over the base
charts of `Stacks.LineBundle.Situation.BaseChart` into a morphism of sheaves and assembles the
short exact sequence of complexes of Stacks 0FUF,

`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`.

The complexes are complexes of sheaves of abelian groups on `X`, as for the residue sequence of
log poles (Stacks 0FMW): the differentials of de Rham complexes are not `𝒪_X`-linear. Each map
is defined on all opens by gluing from the base charts, where the local computation of
`Stacks.LineBundle.Situation.BaseChart.model` applies, and the identities between them are
checked on the base charts, which form a basis of `X`.

## Main definitions

* `Stacks.LineBundle.Situation.weightZeroComplex`: the complex `Ω^•_{L^⋆/S,0}`.
* `AlgebraicGeometry.Scheme.Hom.deRhamShiftAbComplex`: the complex `Ω^•_{X/S}[-1]`.
* `Stacks.LineBundle.Situation.pullbackHom`, `Stacks.LineBundle.Situation.inclusionMap`: the
  inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}`, the pullback of forms along `π`.
* `Stacks.LineBundle.Situation.residueHom`, `Stacks.LineBundle.Situation.residueMap`: the
  residue `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]`, `π^*α + d log s ∧ π^*β ↦ β`.

## Main results

* `Stacks.LineBundle.Situation.BaseChart.res_restrict`: the residue does not depend on the
  trivialization.
* `Stacks.LineBundle.Situation.residueHom_decomposition`: the defining formula of the residue.
* `Stacks.LineBundle.Situation.residueShortComplex_shortExact`: **Stacks 0FUF**, the sequence
  `0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0` is short exact.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open KaehlerDifferential
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open scoped ZeroObject

universe u

/-! ### Morphisms of abelian sheaves agreeing on a basis -/

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u} {B : ι → X.Opens}

/-- **Two morphisms between the abelian sheaves underlying sheaves of modules agreeing on the
sections over a basis are equal.** -/
theorem abelianSheaf_hom_ext_of_isBasis (hB : Opens.IsBasis (Set.range B))
    {φ ψ : (abelianSheaf X).obj M ⟶ (abelianSheaf X).obj N}
    (h : ∀ i (s : Γ(M, B i)), φ.hom.app (op (B i)) s = ψ.hom.app (op (B i)) s) : φ = ψ := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)))
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq N W.unop _ _ fun x hx => ?_
  obtain ⟨_, ⟨i, rfl⟩, hxi, hiU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hiU, hxi, ?_⟩
  have h1 := congrArg (fun k => AddCommGrpCat.Hom.hom k s) (φ.hom.naturality (homOfLE hiU).op)
  have h2 := congrArg (fun k => AddCommGrpCat.Hom.hom k s) (ψ.hom.naturality (homOfLE hiU).op)
  exact h1.symm.trans ((h i _).trans h2)

end Stacks.AlgebraicGeometry.ModuleHomGlue

/-! ### The shifted de Rham complex -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `d ∘ d = 0` for the relative de Rham differential, read in abelian sheaves. -/
theorem deRhamDifferentialAbHom_comp (p : ℕ) :
    deRhamDifferentialAbHom f p ≫ deRhamDifferentialAbHom f (p + 1) = 0 :=
  (deRhamAbComplex f).d_comp_d p (p + 1) (p + 1 + 1)

/-- The terms of `Ω^•_{X/S}[-1]`: `0` in degree `0`, `Ω^p_{X/S}` in degree `p + 1`. -/
def deRhamShiftAbX : ℕ → Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}
  | 0 => 0
  | p + 1 => (abelianSheaf X).obj (relativeDifferentialForms f (p : ℤ))

/-- The differential of `Ω^•_{X/S}[-1]`: `-d`, the sign of the shift. -/
def deRhamShiftAbD : ∀ n : ℕ, deRhamShiftAbX f n ⟶ deRhamShiftAbX f (n + 1)
  | 0 => 0
  | p + 1 => -deRhamDifferentialAbHom f p

/-- The differential of `Ω^•_{X/S}[-1]` squares to zero. -/
theorem deRhamShiftAbD_comp (n : ℕ) : deRhamShiftAbD f n ≫ deRhamShiftAbD f (n + 1) = 0 := by
  cases n with
  | zero => exact zero_comp
  | succ p =>
    show (-deRhamDifferentialAbHom f p) ≫ (-deRhamDifferentialAbHom f (p + 1)) = 0
    rw [Preadditive.neg_comp_neg]
    exact deRhamDifferentialAbHom_comp f p

/-- **The shifted relative de Rham complex `Ω^•_{X/S}[-1]`** of sheaves of abelian groups on `X`:
`Ω^{n-1}_{X/S}` in degree `n`, with the differential negated. -/
def deRhamShiftAbComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (deRhamShiftAbX f) (deRhamShiftAbD f) (deRhamShiftAbD_comp f)

/-- The differential of `Ω^•_{X/S}[-1]` from degree `n` to `n + 1` is
`AlgebraicGeometry.Scheme.Hom.deRhamShiftAbD`. -/
theorem deRhamShiftAbComplex_d (n : ℕ) :
    (deRhamShiftAbComplex f).d n (n + 1) = deRhamShiftAbD f n := by
  unfold deRhamShiftAbComplex
  exact CochainComplex.of_d (deRhamShiftAbX f) (deRhamShiftAbD f) n

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Restriction -/

/-- **The pullback of forms along `π` commutes with restriction.** -/
theorem Situation.pullbackG_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    (D.gradedAmbient p).presheaf.map (homOfLE hWU).op (D.pullbackG p U α) =
      D.pullbackG p W
        ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hWU).op α) :=
  (PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamFormsPushforwardHom
    D.laurentSpectrumToBase D.f (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S)
    ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm)).app (p : ℤ)).val
    (homOfLE hWU).op α).symm

/-- **The restriction of a decomposed form is decomposed**, with the restricted unit. -/
theorem Situation.map_decomposition (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (w : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    (D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op
        (D.pullbackG (p + 1) U α + D.gradedWedge p U (D.pullbackG p U β) (D.laurentDlog U w)) =
      D.pullbackG (p + 1) W
          ((Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ)).presheaf.map
            (homOfLE hWU).op α) +
        D.gradedWedge p W (D.pullbackG p W
          ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hWU).op β))
          (D.laurentDlog W (Units.map
            (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom.toMonoidHom
              w)) := by
  rw [map_add, D.pullbackG_map, D.gradedWedge_map, D.pullbackG_map, D.laurentDlog_map]

namespace Situation.BaseChart

variable {D}

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB isScalarTower

/-- **The coordinate of a base chart, restricted to a smaller base chart, has degree one
there.** -/
theorem restrict_unit_mem (c c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) :
    (((Units.map (D.secR (D.laurentSpectrumToBase ⁻¹ᵁ c'.U.1)).toMonoidHom
      (Units.map (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom.toMonoidHom
        c.unit)) : c'.Bˣ) : c'.B) ∈
      LaurentDeRham.transportGrading (R := c'.R) c'.model.equiv 1 := by
  show (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom
    (D.secR _ (c.unit : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))))
      ∈ c'.grading 1
  rw [c.unit_val]
  exact (congrArg (· ∈ c'.grading 1) (D.laurentFunction_map 1 h c.chart.gen)).mpr
    (c'.laurentFunction_mem_grading 1 _)

/-- **The residues over two base charts agree on their overlap**: the residue over a smaller
base chart of the restriction of a weight-zero form is the restriction of its residue. -/
theorem res_restrict (c c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (p : ℕ)
    {ω : Γ(D.gradedAmbient (p + 1), c.U.1)}
    (hω : ω ∈ (D.gradedLaurentForms (p + 1) 0).obj (op c.U.1)) :
    c'.model.res p ((D.gradedAmbient (p + 1)).presheaf.map (homOfLE h).op ω) =
      (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
        (c.model.res p ω) := by
  obtain ⟨α, hα⟩ := c.model.exists_decomposition (x := ω) hω (c.isDlog_laurentDlog c.unit)
    c.unit_mem
  have hα' : ω = D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (c.model.res p ω))
        (D.laurentDlog c.U.1 c.unit) := hα
  have key := congrArg ((D.gradedAmbient (p + 1)).presheaf.map (homOfLE h).op) hα'
  rw [D.map_decomposition p h α (c.model.res p ω) c.unit] at key
  rw [key]
  exact c'.model.res_decomposition p _ _ (c'.isDlog_laurentDlog _) (restrict_unit_mem c c' h)

end Situation.BaseChart

/-! ### The base charts form a basis -/

/-- **Every point of an open `W` of `X` lies in a base chart contained in `W`.** -/
theorem Situation.exists_baseChart {W : D.X.Opens} {x : D.X} (hx : x ∈ W) :
    ∃ c : D.BaseChart, x ∈ c.U.1 ∧ c.U.1 ≤ W := by
  obtain ⟨I, Ui, hUi, e⟩ :=
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial.exists_trivializing_cover (M := D.L)
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff (↥D.X) Ui).mp hUi).exists_mem x
  obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp D.S.isBasis_affineOpens
    (show D.f.base x ∈ (⊤ : D.S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUle⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens
    (show x ∈ W ⊓ (Ui i ⊓ D.f ⁻¹ᵁ V) from ⟨hx, hxi, hxV⟩)
  refine ⟨⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hUle.trans (inf_le_right.trans inf_le_right)⟩,
    Situation.LaurentChart.ofTrivialization (Stacks.SheafOfModules.isoUnitOverOfHom
      D.L (homOfLE (hUle.trans (inf_le_right.trans inf_le_left))) (e i).some)⟩, hxU, ?_⟩
  exact hUle.trans inf_le_left

/-- **The opens of the base charts form a basis of the topology of `X`.** -/
theorem Situation.isBasis_baseChart :
    Opens.IsBasis (Set.range fun c : D.BaseChart => c.U.1) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W x} hx => ?_
  obtain ⟨c, hxc, hcW⟩ := D.exists_baseChart hx
  exact ⟨c.U.1, ⟨c, rfl⟩, hxc, hcW⟩

/-! ### The weight-zero module -/

/-- **The weight-zero part `Ω^p_{L^⋆/S,0}` of the pushed-forward forms of `L^⋆`**, as an
`𝒪_X`-module. -/
def Situation.weightZero (p : ℕ) : D.X.Modules := (D.gradedLaurentForms p 0).toSheafOfModules

/-- A section of `Ω^p_{L^⋆/S,0}`, read as a section of the pushed-forward forms. -/
def Situation.weightZeroVal (p : ℕ) {U : D.X.Opens} (x : Γ(D.weightZero p, U)) :
    Γ(D.gradedAmbient p, U) :=
  (x : (D.gradedLaurentForms p 0).obj (op U)).1

/-- A section of `Ω^p_{L^⋆/S,0}` is a pushed-forward form of weight zero. -/
theorem Situation.weightZeroVal_mem (p : ℕ) {U : D.X.Opens} (x : Γ(D.weightZero p, U)) :
    D.weightZeroVal p x ∈ (D.gradedLaurentForms p 0).obj (op U) :=
  (x : (D.gradedLaurentForms p 0).obj (op U)).2

/-- Reading a section of `Ω^p_{L^⋆/S,0}` as a pushed-forward form commutes with restriction. -/
theorem Situation.weightZeroVal_map (p : ℕ) {U W : D.X.Opens} (h : W ≤ U)
    (x : Γ(D.weightZero p, U)) :
    D.weightZeroVal p ((D.weightZero p).presheaf.map (homOfLE h).op x) =
      (D.gradedAmbient p).presheaf.map (homOfLE h).op (D.weightZeroVal p x) :=
  rfl

/-- Reading a section of `Ω^p_{L^⋆/S,0}` as a pushed-forward form is additive. -/
theorem Situation.weightZeroVal_add (p : ℕ) {U : D.X.Opens} (x y : Γ(D.weightZero p, U)) :
    D.weightZeroVal p (x + y) = D.weightZeroVal p x + D.weightZeroVal p y :=
  rfl

/-- Reading a section of `Ω^p_{L^⋆/S,0}` as a pushed-forward form is `𝒪_X`-linear. -/
theorem Situation.weightZeroVal_smul (p : ℕ) {U : D.X.Opens} (r : Γ(D.X, U))
    (x : Γ(D.weightZero p, U)) :
    D.weightZeroVal p (r • x) = r • D.weightZeroVal p x :=
  rfl

/-- The zero section of `Ω^p_{L^⋆/S,0}` is the zero pushed-forward form. -/
theorem Situation.weightZeroVal_zero (p : ℕ) {U : D.X.Opens} :
    D.weightZeroVal p (0 : Γ(D.weightZero p, U)) = 0 :=
  rfl

/-- The section of `Ω^p_{L^⋆/S,0}` attached to a section of the pushed-forward forms of weight
zero. -/
def Situation.weightZeroMk (p : ℕ) {U : D.X.Opens} (y : Γ(D.gradedAmbient p, U))
    (hy : y ∈ (D.gradedLaurentForms p 0).obj (op U)) : Γ(D.weightZero p, U) :=
  (⟨y, hy⟩ : (D.gradedLaurentForms p 0).obj (op U))

/-- The section of `Ω^p_{L^⋆/S,0}` attached to a form `y` of weight zero is read back as `y`. -/
theorem Situation.weightZeroVal_mk (p : ℕ) {U : D.X.Opens} (y : Γ(D.gradedAmbient p, U))
    (hy : y ∈ (D.gradedLaurentForms p 0).obj (op U)) :
    D.weightZeroVal p (D.weightZeroMk p y hy) = y :=
  rfl

/-- A section of `Ω^p_{L^⋆/S,0}` is determined by its underlying pushed-forward form. -/
theorem Situation.weightZeroVal_injective (p : ℕ) {U : D.X.Opens} :
    Function.Injective (D.weightZeroVal p (U := U)) :=
  fun _ _ h => Subtype.ext h

/-! ### The weight-zero de Rham complex -/

/-- `d ∘ d = 0` for the relative de Rham differential of `L^⋆`, on sections over an open of `X`. -/
theorem Situation.gradedDiff_gradedDiff (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedDiff (p + 1) U (D.gradedDiff p U ω) = 0 :=
  congrArg (fun g : (Scheme.Hom.deRhamComplex D.laurentToBase).X p ⟶
      (Scheme.Hom.deRhamComplex D.laurentToBase).X (p + 1 + 1) =>
    g.val.app (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ω)
    ((Scheme.Hom.deRhamComplex D.laurentToBase).d_comp_d p (p + 1) (p + 1 + 1))

/-- The de Rham differential of the weight-zero forms on sections over `U`, as an additive map. -/
def Situation.weightZeroD (p : ℕ) (U : D.X.Opens) :
    Γ(D.weightZero p, U) →+ Γ(D.weightZero (p + 1), U) where
  toFun x := D.weightZeroMk (p + 1) (D.gradedDiff p U (D.weightZeroVal p x))
    (D.gradedDiff_mem_gradedLaurentForms_of_mem p 0 (D.weightZeroVal_mem p x))
  map_zero' := D.weightZeroVal_injective (p + 1) (D.gradedDiff_zero p U)
  map_add' _ _ := D.weightZeroVal_injective (p + 1) (D.gradedDiff_add p U _ _)

/-- The differential of a weight-zero form is the de Rham differential of `L^⋆` of the
underlying pushed-forward form. -/
theorem Situation.weightZeroVal_weightZeroD (p : ℕ) (U : D.X.Opens) (x : Γ(D.weightZero p, U)) :
    D.weightZeroVal (p + 1) (D.weightZeroD p U x) = D.gradedDiff p U (D.weightZeroVal p x) :=
  rfl

/-- The de Rham differential of the weight-zero forms, as a morphism of the underlying abelian
presheaves. -/
def Situation.weightZeroDPresheafHom (p : ℕ) :
    Scheme.Modules.presheaf (D.weightZero p) ⟶ Scheme.Modules.presheaf (D.weightZero (p + 1)) where
  app U := AddCommGrpCat.ofHom (D.weightZeroD p U.unop)
  naturality _ _ g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    D.weightZeroVal_injective (p + 1) ((D.gradedDiff_map p (leOfHom g.unop) _).symm))

/-- **The de Rham differential of `Ω^•_{L^⋆/S,0}`**, as a morphism of abelian sheaves on `X`. -/
def Situation.weightZeroDAbHom (p : ℕ) :
    (abelianSheaf D.X).obj (D.weightZero p) ⟶ (abelianSheaf D.X).obj (D.weightZero (p + 1)) :=
  abHom (D.weightZeroDPresheafHom p)

/-- The differential of `Ω^•_{L^⋆/S,0}` squares to zero. -/
theorem Situation.weightZeroDAbHom_comp (p : ℕ) :
    D.weightZeroDAbHom p ≫ D.weightZeroDAbHom (p + 1) = 0 := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)))
  exact D.weightZeroVal_injective (p + 2) (D.gradedDiff_gradedDiff p U.unop _)

/-- **The weight-zero de Rham complex `Ω^•_{L^⋆/S,0}`** of the complement of the zero section, as
a complex of abelian sheaves on `X`: the weight-zero part of `π_*Ω^•_{L^⋆/S}` for the grading by
the action of `𝔾_m`, with the relative de Rham differential of `L^⋆` over `S`. -/
def Situation.weightZeroComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology D.X.carrier) AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (fun p => (abelianSheaf D.X).obj (D.weightZero p)) D.weightZeroDAbHom
    D.weightZeroDAbHom_comp

/-- The differential of `Ω^•_{L^⋆/S,0}` from degree `p` to `p + 1` is
`Stacks.LineBundle.Situation.weightZeroDAbHom`. -/
theorem Situation.weightZeroComplex_d (p : ℕ) :
    D.weightZeroComplex.d p (p + 1) = D.weightZeroDAbHom p := by
  unfold Situation.weightZeroComplex
  exact CochainComplex.of_d (fun p => (abelianSheaf D.X).obj (D.weightZero p))
    D.weightZeroDAbHom p

/-! ### The glued residue -/

attribute [local instance] Situation.AffineChart.algebraRA Situation.BaseChart.algebraRB
  Situation.BaseChart.algebraAB Situation.BaseChart.isScalarTower

/-- The residue over a base chart, on sections of `Ω^{p+1}_{L^⋆/S,0}`, as an additive map:
`(-1)^p` times the residue against a right wedge of the model of the chart. -/
def Situation.BaseChart.residueAdd {D : Situation.{u}} (c : D.BaseChart) (p : ℕ) :
    Γ(D.weightZero (p + 1), c.U.1) →+
      Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) where
  toFun x := ((-1 : ℤ) ^ p) • c.model.res p (D.weightZeroVal (p + 1) x)
  map_zero' := (congrArg (((-1 : ℤ) ^ p) • ·) (c.model.res_zero p)).trans (smul_zero _)
  map_add' x y := (congrArg (((-1 : ℤ) ^ p) • ·)
    (c.model.res_add p (D.weightZeroVal (p + 1) x) (D.weightZeroVal (p + 1) y))).trans
      (smul_add _ _ _)

/-- There is a morphism of `𝒪_X`-modules `Ω^{p+1}_{L^⋆/S,0} ⟶ Ω^p_{X/S}` which over every base
chart is `(-1)^p` times the residue against a right wedge of the model of the chart. -/
theorem Situation.exists_residueHom (p : ℕ) :
    ∃ φ : D.weightZero (p + 1) ⟶ Scheme.Hom.relativeDifferentialForms D.f (p : ℤ),
      ∀ (c : D.BaseChart) (x : Γ(D.weightZero (p + 1), c.U.1)),
        φ.app c.U.1 x = ((-1 : ℤ) ^ p) • c.model.res p (D.weightZeroVal (p + 1) x) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis (fun c : D.BaseChart => c.U.1)
    D.isBasis_baseChart (fun c => c.residueAdd p)
    (fun c c' h x => by
      show ((-1 : ℤ) ^ p) • c'.model.res p (D.weightZeroVal (p + 1)
          ((D.weightZero (p + 1)).presheaf.map (homOfLE h).op x)) =
        (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
          (((-1 : ℤ) ^ p) • c.model.res p (D.weightZeroVal (p + 1) x))
      rw [D.weightZeroVal_map (p + 1) h x,
        Situation.BaseChart.res_restrict c c' h p (D.weightZeroVal_mem (p + 1) x), map_zsmul])
    (fun c r x => (congrArg (((-1 : ℤ) ^ p) • ·)
      ((congrArg (c.model.res p) (D.weightZeroVal_smul (p + 1) r x)).trans
        (c.model.res_smul p r (D.weightZeroVal_mem (p + 1) x)))).trans (smul_comm _ _ _))

/-- **The residue `Ω^{p+1}_{L^⋆/S,0} ⟶ Ω^p_{X/S}`** of Stacks 0FUF, as a morphism of
`𝒪_X`-modules: over an open where `L` is trivialized by a generator `s`, so that `s` is a unit of
degree one on `L^⋆`, it sends `π^*α + d log s ∧ π^*β` to `β`. This does not depend on the
trivialization (`Stacks.LineBundle.Situation.BaseChart.res_restrict`). -/
def Situation.residueHom (p : ℕ) :
    D.weightZero (p + 1) ⟶ Scheme.Hom.relativeDifferentialForms D.f (p : ℤ) :=
  (D.exists_residueHom p).choose

/-- Over a base chart the residue is `(-1)^p` times the residue against a right wedge,
`π^*α + π^*β ∧ d log s ↦ β`, of the model of the chart. -/
theorem Situation.residueHom_app (p : ℕ) (c : D.BaseChart) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    (D.residueHom p).app c.U.1 x = ((-1 : ℤ) ^ p) • c.model.res p (D.weightZeroVal (p + 1) x) :=
  (D.exists_residueHom p).choose_spec c x

/-- The residue of a section over a base chart vanishes iff the residue of the model does. -/
private theorem Situation.residueHom_app_eq_zero_iff (p : ℕ) (c : D.BaseChart)
    (x : Γ(D.weightZero (p + 1), c.U.1)) :
    (D.residueHom p).app c.U.1 x = 0 ↔ c.model.res p (D.weightZeroVal (p + 1) x) = 0 := by
  rw [D.residueHom_app]
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  have h3 := congrArg (((-1 : ℤ) ^ p) • ·) h
  simp only at h3
  rwa [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h3

/-- **The residue in Stacks's normalization**: over a base chart with coordinate `s`, the residue
of `π^*α + d log s ∧ π^*β` is `β`. -/
theorem Situation.residueHom_decomposition (p : ℕ) (c : D.BaseChart)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1))
    (h : D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) • β))
        (D.laurentDlog c.U.1 c.unit) ∈ (D.gradedLaurentForms (p + 1) 0).obj (op c.U.1)) :
    (D.residueHom p).app c.U.1 (D.weightZeroMk (p + 1) _ h) = β := by
  rw [D.residueHom_app, D.weightZeroVal_mk]
  refine (congrArg (((-1 : ℤ) ^ p) • ·) (c.model.res_decomposition p α (((-1 : ℤ) ^ p) • β)
    (c.isDlog_laurentDlog c.unit) c.unit_mem)).trans ?_
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-! ### The inclusion -/

/-- The pullback of forms along `π` over a base chart, with values in `Ω^p_{L^⋆/S,0}`. -/
def Situation.BaseChart.pullbackAdd {D : Situation.{u}} (c : D.BaseChart) (p : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) →+ Γ(D.weightZero p, c.U.1) where
  toFun α := D.weightZeroMk p (c.model.pull p α) (c.model.pull_mem p α)
  map_zero' := D.weightZeroVal_injective p (map_zero (c.model.pull p))
  map_add' α β := D.weightZeroVal_injective p (map_add (c.model.pull p) α β)

/-- There is a morphism of `𝒪_X`-modules `Ω^p_{X/S} ⟶ Ω^p_{L^⋆/S,0}` which over every base
chart is the pullback of forms along `π`. -/
theorem Situation.exists_pullbackHom (p : ℕ) :
    ∃ φ : Scheme.Hom.relativeDifferentialForms D.f (p : ℤ) ⟶ D.weightZero p,
      ∀ (c : D.BaseChart) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)),
        φ.app c.U.1 α = c.pullbackAdd p α :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis (fun c : D.BaseChart => c.U.1)
    D.isBasis_baseChart (fun c => c.pullbackAdd p)
    (fun _ _ h α => D.weightZeroVal_injective p (D.pullbackG_map p h α).symm)
    (fun c r α => D.weightZeroVal_injective p (c.model.pull_smul p r α))

/-- **The inclusion `Ω^p_{X/S} ⟶ Ω^p_{L^⋆/S,0}`**, the pullback of forms along `π`, as a
morphism of `𝒪_X`-modules. -/
def Situation.pullbackHom (p : ℕ) :
    Scheme.Hom.relativeDifferentialForms D.f (p : ℤ) ⟶ D.weightZero p :=
  (D.exists_pullbackHom p).choose

/-- Over a base chart the inclusion is the pullback of forms along `π`. -/
theorem Situation.pullbackHom_app (p : ℕ) (c : D.BaseChart)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    D.weightZeroVal p ((D.pullbackHom p).app c.U.1 α) = D.pullbackG p c.U.1 α :=
  congrArg (D.weightZeroVal p) ((D.exists_pullbackHom p).choose_spec c α)

/-! ### The maps of complexes -/

/-- Two morphisms between the abelian sheaves underlying `𝒪_X`-modules agreeing on the sections
over the base charts are equal. -/
theorem Situation.abelianSheaf_hom_ext {M N : D.X.Modules}
    {φ ψ : (abelianSheaf D.X).obj M ⟶ (abelianSheaf D.X).obj N}
    (h : ∀ (c : D.BaseChart) (s : Γ(M, c.U.1)), φ.hom.app (op c.U.1) s = ψ.hom.app (op c.U.1) s) :
    φ = ψ :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.abelianSheaf_hom_ext_of_isBasis D.isBasis_baseChart h

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}`** of complexes: in degree `p` the pullback of
forms along `π`, `Stacks.LineBundle.Situation.pullbackHom`. -/
def Situation.inclusionMap : Scheme.Hom.deRhamAbComplex D.f ⟶ D.weightZeroComplex where
  f p := (abelianSheaf D.X).map (D.pullbackHom p)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Scheme.Hom.deRhamAbComplex_d, D.weightZeroComplex_d]
    refine D.abelianSheaf_hom_ext fun c α => D.weightZeroVal_injective (i + 1) ?_
    change D.gradedDiff i c.U.1 (D.weightZeroVal i ((D.pullbackHom i).app c.U.1 α)) =
      D.weightZeroVal (i + 1) ((D.pullbackHom (i + 1)).app c.U.1 (D.dX i c.U.1 α))
    exact (congrArg (D.gradedDiff i c.U.1) (D.pullbackHom_app i c α)).trans
      ((c.model.dF_pull i α).trans (D.pullbackHom_app (i + 1) c (D.dX i c.U.1 α)).symm)

/-- The residue in each degree: `0` in degree `0`, `Stacks.LineBundle.Situation.residueHom` in
degree `p + 1`. -/
def Situation.residueF :
    ∀ n : ℕ, (abelianSheaf D.X).obj (D.weightZero n) ⟶ Scheme.Hom.deRhamShiftAbX D.f n
  | 0 => 0
  | p + 1 => (abelianSheaf D.X).map (D.residueHom p)

/-- The residue in each degree commutes with the differentials of `Ω^•_{L^⋆/S,0}` and
`Ω^•_{X/S}[-1]`. -/
theorem Situation.residueF_comm (n : ℕ) :
    D.residueF n ≫ Scheme.Hom.deRhamShiftAbD D.f n = D.weightZeroDAbHom n ≫ D.residueF (n + 1) := by
  cases n with
  | zero =>
    refine (zero_comp).trans ?_
    refine (D.abelianSheaf_hom_ext fun c s => ?_).symm
    show (D.residueHom 0).app c.U.1 (D.weightZeroD 0 c.U.1 s) = 0
    exact (D.residueHom_app_eq_zero_iff 0 c _).2 (c.model.res_dF_zero (D.weightZeroVal_mem 0 s))
  | succ p =>
    refine D.abelianSheaf_hom_ext fun c s => ?_
    show -D.dX p c.U.1 ((D.residueHom p).app c.U.1 s) =
      (D.residueHom (p + 1)).app c.U.1 (D.weightZeroD (p + 1) c.U.1 s)
    rw [D.residueHom_app, D.residueHom_app]
    exact (c.model.neg_one_pow_res_dF p (D.weightZeroVal_mem (p + 1) s)).symm

/-- **The residue `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]`** of complexes: in degree `p + 1` the residue
`Stacks.LineBundle.Situation.residueHom`. -/
def Situation.residueMap : D.weightZeroComplex ⟶ Scheme.Hom.deRhamShiftAbComplex D.f :=
  CochainComplex.ofHom D.residueF fun n => by
    rw [Scheme.Hom.deRhamShiftAbComplex_d, D.weightZeroComplex_d]
    exact D.residueF_comm n

/-- The residue of the pullback of a form along `π` vanishes. -/
theorem Situation.inclusionMap_comp_residueMap : D.inclusionMap ≫ D.residueMap = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact comp_zero
  | succ p =>
    refine D.abelianSheaf_hom_ext fun c α => ?_
    show (D.residueHom p).app c.U.1 ((D.pullbackHom (p + 1)).app c.U.1 α) = 0
    refine (D.residueHom_app_eq_zero_iff p c _).2 ?_
    exact (congrArg (c.model.res p) (D.pullbackHom_app (p + 1) c α)).trans
      (c.model.res_pull p α (c.isDlog_laurentDlog c.unit) c.unit_mem)

/-- **The residue sequence of the complement of the zero section**
`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`, as a short complex of complexes of sheaves
of abelian groups on `X`. -/
abbrev Situation.residueShortComplex :
    ShortComplex (CochainComplex (Sheaf (Opens.grothendieckTopology D.X.carrier)
      AddCommGrpCat.{u}) ℕ) :=
  ShortComplex.mk D.inclusionMap D.residueMap D.inclusionMap_comp_residueMap

/-! ### Short exactness -/

/-- **The inclusion is locally injective**: a form of `X` whose pullback to `L^⋆` vanishes
vanishes near every point. -/
theorem Situation.pullbackHom_locally_injective (p : ℕ) (U : D.X.Opens)
    (s : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (hs : (D.pullbackHom p).app U s = 0) : ∀ x ∈ U, ∃ (V : D.X.Opens) (h : V ≤ U), x ∈ V ∧
      (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op s = 0 := by
  intro x hx
  obtain ⟨c, hxc, hcU⟩ := D.exists_baseChart hx
  refine ⟨c.U.1, hcU, hxc, c.model.pull_injective p ?_⟩
  have h1 : (D.pullbackHom p).app c.U.1
      ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hcU).op s) =
        (D.weightZero p).presheaf.map (homOfLE hcU).op ((D.pullbackHom p).app U s) :=
    PresheafOfModules.naturality_apply (D.pullbackHom p).val (homOfLE hcU).op s
  rw [hs, map_zero] at h1
  exact (D.pullbackHom_app p c _).symm.trans ((congrArg (D.weightZeroVal p) h1).trans
    ((D.weightZeroVal_zero p).trans (map_zero (c.model.pull p)).symm))

/-- In degree `p + 1` the sequence `0 → Ω^{p+1}_{X/S} → Ω^{p+1}_{L^⋆/S,0} → Ω^p_{X/S} → 0` is
short exact. -/
theorem Situation.shortExact_eval_succ (p : ℕ) :
    (D.residueShortComplex.map (HomologicalComplex.eval _ _ (p + 1))).ShortExact :=
  Scheme.Hom.shortExact_abelianSheaf_of_local (D.pullbackHom (p + 1)) (D.residueHom p) _
    (fun U s hs x hx => D.pullbackHom_locally_injective (p + 1) U s hs x hx)
    (fun U s hs x hx => by
      obtain ⟨c, hxc, hcU⟩ := D.exists_baseChart hx
      refine ⟨c.U.1, hcU, hxc, ?_⟩
      have h1 : (D.residueHom p).app c.U.1
          ((D.weightZero (p + 1)).presheaf.map (homOfLE hcU).op s) =
          (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hcU).op
            ((D.residueHom p).app U s) :=
        PresheafOfModules.naturality_apply (D.residueHom p).val (homOfLE hcU).op s
      rw [hs, map_zero] at h1
      have h2 := (D.residueHom_app_eq_zero_iff p c _).1 h1
      obtain ⟨α, hα⟩ := c.model.exists_pull_of_res_eq_zero
        (D.weightZeroVal_mem (p + 1) ((D.weightZero (p + 1)).presheaf.map (homOfLE hcU).op s))
        (c.isDlog_laurentDlog c.unit) c.unit_mem h2
      exact ⟨α, D.weightZeroVal_injective (p + 1) ((D.pullbackHom_app (p + 1) c α).trans hα.symm)⟩)
    (fun U s x hx => by
      obtain ⟨c, hxc, hcU⟩ := D.exists_baseChart hx
      exact ⟨c.U.1, hcU, hxc, _, D.residueHom_decomposition p c 0 _
        (c.model.decomposition_mem p 0 _ (c.isDlog_laurentDlog c.unit) c.unit_mem)⟩)

/-- In degree `0` the sequence `0 → Ω^0_{X/S} → Ω^0_{L^⋆/S,0} → 0 → 0` is short exact. -/
theorem Situation.shortExact_eval_zero :
    (D.residueShortComplex.map (HomologicalComplex.eval _ _ 0)).ShortExact :=
  Scheme.Hom.shortExact_abelianSheaf_of_local_zero (D.pullbackHom 0) _ _
    (fun U s hs x hx => D.pullbackHom_locally_injective 0 U s hs x hx)
    (fun U s x hx => by
      obtain ⟨c, hxc, hcU⟩ := D.exists_baseChart hx
      obtain ⟨α, hα⟩ := c.model.exists_pull_zero
        (D.weightZeroVal_mem 0 ((D.weightZero 0).presheaf.map (homOfLE hcU).op s))
      exact ⟨c.U.1, hcU, hxc, α, D.weightZeroVal_injective 0
        ((D.pullbackHom_app 0 c α).trans hα.symm)⟩)

/-- Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible
`𝒪_X`-module and `π : L^⋆ ⟶ X` the complement of the zero section of the line bundle of `L`, with
`Ω^•_{L^⋆/S,0}` the weight-zero part of `π_*Ω^•_{L^⋆/S}` for the grading by the action of `𝔾_m`
(`Stacks.LineBundle.Situation.weightZeroComplex`, Tag 0FU9). Then the sequence of complexes of
sheaves of abelian groups on `X`

`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`

is short exact. The first map is the pullback of forms along `π`
(`Stacks.LineBundle.Situation.pullbackHom`); the second is the residue
(`Stacks.LineBundle.Situation.residueHom`), which over an open where `L` is trivialized by a
generator `s`, so that `s` is a unit of degree one on `L^⋆`, sends `π^*α + d log s ∧ π^*β` to `β`
(`Stacks.LineBundle.Situation.residueHom_decomposition`) independently of the trivialization. -/
@[stacks 0FUF]
theorem Situation.residueShortComplex_shortExact : D.residueShortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    cases n with
    | zero => exact D.shortExact_eval_zero
    | succ p => exact D.shortExact_eval_succ p

end Stacks.LineBundle

end
