module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueLogPolesMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.PullbackNonvanishing
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.LocalGenerator

/-!
# Restricting weight-zero forms along a base change of a line bundle

Let `L` be an invertible module on `X`, `π : L^⋆ ⟶ X` the complement of the zero section, and
`g : X' ⟶ X` an affine morphism, with `L̄ = g^*L` on `X'`. Over a base chart of `L` with
generator `s`, every weight-zero form is uniquely `π^*α + d log s ∧ π^*η`; the generator pulls back
to a generator `s̄` of `L̄` over `g⁻¹U` ([Stacks, Tag 0H78] over an open), and the rule

`π^*α + d log s ∧ π^*η ↦ π̄^*(α|) + d log s̄ ∧ π̄^*(η|)`

glues to a morphism `Ω^p_{L^⋆/S,0} ⟶ g_*Ω^p_{L̄^⋆/S,0}`, the restriction of weight-zero forms.

## Main definitions

* `Stacks.LineBundle.Situation.BaseChart.baseChange`: the base chart of `g^*L` induced by a base
  chart of `L`, with the pulled-back generator.
* `Stacks.LineBundle.Situation.BaseChart.decompose`: the weight-zero form with a prescribed
  decomposition.
* `Stacks.LineBundle.Situation.weightZeroRestrictF`: the restriction of weight-zero forms in every
  degree.

## Main results

* `Stacks.LineBundle.Situation.BaseChart.lineGen_baseChange`: the generator of the induced chart is
  the pulled-back generator.
* `Stacks.LineBundle.Situation.pullbackHom_comp_weightZeroRestrictF`,
  `Stacks.LineBundle.Situation.weightZeroRestrictHom_comp_residueHom`,
  `Stacks.LineBundle.Situation.weightZeroDAbHom_comp_weightZeroRestrictF`: the restriction extends
  the restriction of forms, is compatible with the residues and commutes with the differentials.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)

universe u

namespace Stacks.LineBundle

namespace Situation.BaseChart

variable {D : Situation.{u}} (c : D.BaseChart) {X' : Scheme.{u}} (g : X' ⟶ D.X)

/-- The generator of a base chart pulled back along `g`, a section of `g^*L` over `g⁻¹U`. -/
def pullbackLineGen : (D.baseChange g).L.val.obj (op (g ⁻¹ᵁ c.U.1)) :=
  Stacks.AmpleThickeningAscent.pullbackSection g D.L
    (show Γ(D.L, c.U.1) from c.lineGen)

/-- The nonvanishing locus of the generator of a base chart is the whole chart `U`. -/
theorem nonvanishingLocusOn_lineGen :
    Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn D.L c.U.1
      (show Γ(D.L, c.U.1) from c.lineGen) = c.U.1 := by
  have h := Stacks.AmpleThickeningAscent.nonvanishingLocusOn_basis c.lineTriv
  have hb : Stacks.NonvanishingOpen.basis c.lineTriv = c.lineGen := by
    change (c.lineCoord (𝟙 c.U.1)).symm 1 = c.lineGen
    change (1 : D.X.ringCatSheaf.obj.obj (op c.U.1)) • c.lineGenAt (𝟙 c.U.1) = c.lineGen
    rw [one_smul]
    exact c.lineGenAt_id
  rwa [hb] at h

/-- **The pulled-back generator generates `g^*L` over every open of `g⁻¹U`.** -/
theorem bijective_smul_pullbackLineGen (W : (D.baseChange g).X.Opens)
    (h : W ⟶ g ⁻¹ᵁ c.U.1) :
    Function.Bijective (fun r : (D.baseChange g).X.ringCatSheaf.obj.obj (op W) =>
      r • (D.baseChange g).L.val.map h.op (c.pullbackLineGen g)) := by
  have : Stacks.Ample.IsInvertibleModule (D.baseChange g).X (D.baseChange g).L :=
    (D.baseChange g).invertible
  refine Stacks.AmpleThickeningAscent.bijective_smul_of_nonvanishing (D.baseChange g).L
    (W := W) _ fun y hy => ?_
  have hres := Stacks.AmpleThickeningAscent.nonvanishingLocusOn_res (D.baseChange g).L
    (leOfHom h) (c.pullbackLineGen g)
  have hmem : y ∈ (W : Set (D.baseChange g).X) ∩
      Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn (D.baseChange g).L (g ⁻¹ᵁ c.U.1)
        (c.pullbackLineGen g) := by
    refine ⟨hy, ?_⟩
    change y ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
      (Stacks.AmpleLocallyClosed.pullbackModule g D.L) (g ⁻¹ᵁ c.U.1)
      (Stacks.AmpleThickeningAscent.pullbackSection g D.L (show Γ(D.L, c.U.1) from c.lineGen))
    rw [Stacks.AmpleThickeningAscent.nonvanishingLocusOn_pullbackSection,
      c.nonvanishingLocusOn_lineGen]
    exact leOfHom h hy
  rw [← hres] at hmem
  exact hmem

variable [IsAffineHom g]

/-- **The base chart of `g^*L` induced by a base chart of `L`**, for an affine morphism `g`: the
affine open `g⁻¹U` over the same affine open of `S`, with the pulled-back generator. -/
def baseChange : (D.baseChange g).BaseChart where
  U := ⟨g ⁻¹ᵁ c.U.1, c.U.2.preimage g⟩
  V := c.V
  le := g.preimage_mono c.le
  chart := Situation.LaurentChart.ofTrivialization
    (Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul (D.baseChange g).L (g ⁻¹ᵁ c.U.1)
      (c.pullbackLineGen g) fun V f => c.bijective_smul_pullbackLineGen g V f)

/-- The open of the induced base chart is `g⁻¹U`. -/
theorem baseChange_U : ((c.baseChange g).U : (D.baseChange g).X.Opens) = g ⁻¹ᵁ c.U.1 := rfl

/-- The generator of the induced chart is the pulled-back generator. -/
theorem lineGen_baseChange : (c.baseChange g).lineGen = c.pullbackLineGen g := by
  have hgen := Stacks.SheafOfModules.generator_overIsoUnitOfBijectiveSmul (D.baseChange g).L
    (g ⁻¹ᵁ c.U.1) (c.pullbackLineGen g) fun V f => c.bijective_smul_pullbackLineGen g V f
  change (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso (D.baseChange g).X.sheaf.obj
      (D.baseChange g).X.ringCatSheaf.property (D.baseChange g).L).hom.val.app
      (op (g ⁻¹ᵁ c.U.1))
      ((Stacks.SheafOfModules.TensorPower.tensorPowerOneIso (D.baseChange g).X.sheaf.obj
      (D.baseChange g).X.ringCatSheaf.property (D.baseChange g).L).inv.val.app
      (op (g ⁻¹ᵁ c.U.1)) _) = _
  refine (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op (g ⁻¹ᵁ c.U.1)) _)
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso (D.baseChange g).X.sheaf.obj
      (D.baseChange g).X.ringCatSheaf.property (D.baseChange g).L).inv_hom_id).trans ?_
  exact hgen

/-- **The generators of two nested induced charts differ by the pulled-back function.** -/
theorem lineGen_baseChange_res (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (u : (Γ(D.X, c'.U.1))ˣ)
    (hu : D.L.val.map (homOfLE h).op c.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.lineGen) :
    (D.baseChange g).L.val.map (homOfLE (g.preimage_mono h)).op (c.baseChange g).lineGen =
      (show (D.baseChange g).X.ringCatSheaf.obj.obj (op (c'.baseChange g).U.1) from
        ((g.app c'.U.1).hom (u : Γ(D.X, c'.U.1)))) • (c'.baseChange g).lineGen := by
  rw [lineGen_baseChange, lineGen_baseChange]
  refine (Stacks.AmpleThickeningAscent.pullbackSection_res g D.L h
    (show Γ(D.L, c.U.1) from c.lineGen)).trans ?_
  refine (congrArg (Stacks.AmpleThickeningAscent.pullbackSection g D.L) hu).trans ?_
  exact Stacks.AmpleThickeningAscent.pullbackSection_smul g D.L _ _

/-! ### Weight-zero forms from their decomposition -/

section Decompose

variable {D : Situation.{u}} (c : D.BaseChart)

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB isScalarTower

/-- **The weight-zero form with a prescribed decomposition** over a base chart:
`π^*α + d log s ∧ π^*η`, in the right-wedge normalization `π^*α + π^*((-1)^p η) ∧ d log s`. -/
def decompose (p : ℕ) (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    Γ(D.weightZero (p + 1), c.U.1) :=
  D.weightZeroMk (p + 1) (D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) • η)) c.dlogCoord)
    (c.model.decomposition_mem p α _ (c.isDlog_laurentDlog c.unit) c.unit_mem)

/-- The underlying form of `decompose p α η` is `π^*α + π^*((-1)^p η) ∧ d log s`. -/
theorem weightZeroVal_decompose (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    D.weightZeroVal (p + 1) (c.decompose p α η) = D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) • η)) c.dlogCoord :=
  rfl

/-- The pulled-back part of `decompose p α η` is `α` and its residue is `η`. -/
theorem pullPart_decompose (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.pullPart p (c.decompose p α η) = α ∧ (D.residueHom p).app c.U.1 (c.decompose p α η) = η :=
  c.pullPart_eq_of_eq p _ α η (c.weightZeroVal_decompose p α η)

/-- **A weight-zero form is the form with its own decomposition.** -/
theorem eq_decompose (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    x = c.decompose p (c.pullPart p x) ((D.residueHom p).app c.U.1 x) :=
  D.weightZeroVal_injective (p + 1) (c.weightZeroVal_eq_pullPart p x)

/-- Two weight-zero forms with the same decomposition are equal. -/
theorem ext_decompose (p : ℕ) {x y : Γ(D.weightZero (p + 1), c.U.1)}
    (h₁ : c.pullPart p x = c.pullPart p y)
    (h₂ : (D.residueHom p).app c.U.1 x = (D.residueHom p).app c.U.1 y) : x = y := by
  rw [c.eq_decompose p x, c.eq_decompose p y, h₁, h₂]

/-- `decompose` is additive in the pair `(α, η)`. -/
theorem decompose_add (p : ℕ)
    (α α' : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η η' : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.decompose p (α + α') (η + η') = c.decompose p α η + c.decompose p α' η' := by
  refine D.weightZeroVal_injective (p + 1) ?_
  rw [D.weightZeroVal_add, c.weightZeroVal_decompose, c.weightZeroVal_decompose,
    c.weightZeroVal_decompose, smul_add, c.pullbackG_add, c.pullbackG_add,
    D.gradedWedge_add_left]
  abel

/-- `decompose` is linear over functions on `U`:
`decompose p (r • α) (r • η) = r • decompose p α η`. -/
theorem decompose_smul (p : ℕ) (r : Γ(D.X, c.U.1))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    c.decompose p (r • α) (r • η) = r • c.decompose p α η := by
  refine D.weightZeroVal_injective (p + 1) ?_
  rw [D.weightZeroVal_smul, c.weightZeroVal_decompose, c.weightZeroVal_decompose, smul_add,
    D.pullbackG_smul, smul_comm, D.pullbackG_smul, D.gradedWedge_smul_left]

/-- **A form pulled back from `X` has no residue part.** -/
theorem pullbackHom_eq_decompose (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1)) :
    (D.pullbackHom (p + 1)).app c.U.1 α = c.decompose p α 0 := by
  obtain ⟨h1, h2⟩ := c.pullPart_pullbackHom p α
  rw [c.eq_decompose p ((D.pullbackHom (p + 1)).app c.U.1 α), h1, h2]

/-- **The decomposition of a differential**:
`d(π^*α + d log s ∧ π^*η) = π^*dα + d log s ∧ π^*(-dη)`. -/
theorem weightZeroD_decompose (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
    D.weightZeroD (p + 1) c.U.1 (c.decompose p α η) =
      c.decompose (p + 1) (D.dX (p + 1) c.U.1 α) (-D.dX p c.U.1 η) := by
  obtain ⟨h1, h2⟩ := c.pullPart_weightZeroD p (c.decompose p α η)
  obtain ⟨h3, h4⟩ := c.pullPart_decompose p α η
  rw [h3] at h1
  rw [h4] at h2
  rw [c.eq_decompose (p + 1) (D.weightZeroD (p + 1) c.U.1 (c.decompose p α η)), h1, h2]

end Decompose

/-! ### Restricting weight-zero forms over a base chart -/

section Restrict

variable {D : Situation.{u}} {X' : Scheme.{u}} (g : X' ⟶ D.X) [IsAffineHom g] (c : D.BaseChart)

omit [IsAffineHom g] in
/-- Restriction of forms along `g` commutes with restriction to smaller opens. -/
theorem formRes_map (n : ℤ) {U W : D.X.Opens} (h : W ≤ U)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f n, U)) :
    Scheme.Hom.formRes (f := D.f) g n W
        ((Scheme.Hom.relativeDifferentialForms D.f n).presheaf.map (homOfLE h).op α) =
      (Scheme.Hom.relativeDifferentialForms (g ≫ D.f) n).presheaf.map
        (homOfLE (g.preimage_mono h)).op (Scheme.Hom.formRes (f := D.f) g n U α) :=
  PresheafOfModules.naturality_apply (Scheme.Hom.formRestriction g D.f n).val (homOfLE h).op α

/-- **The restriction of weight-zero forms along `g` over a base chart**:
`π^*α + d log s ∧ π^*η ↦ π̄^*(α|) + d log s̄ ∧ π̄^*(η|)`, `s̄` the pulled-back generator. -/
def weightZeroRestrict (p : ℕ) :
    Γ(D.weightZero (p + 1), c.U.1) →+
      Γ((D.baseChange g).weightZero (p + 1), (c.baseChange g).U.1) :=
  AddMonoidHom.mk' (fun x => (c.baseChange g).decompose p
      (Scheme.Hom.formRes (f := D.f) g ((p + 1 : ℕ) : ℤ) c.U.1 (c.pullPart p x))
      (Scheme.Hom.formRes (f := D.f) g (p : ℤ) c.U.1 ((D.residueHom p).app c.U.1 x))) fun x y => by
    rw [c.pullPart_add, map_add, Scheme.Hom.formRes_add, Scheme.Hom.formRes_add]
    exact (c.baseChange g).decompose_add p _ _ _ _

/-- The restriction of a weight-zero form is the form on `g⁻¹U` whose decomposition is the
restriction of the decomposition of the given form. -/
theorem weightZeroRestrict_apply (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c.weightZeroRestrict g p x = (c.baseChange g).decompose p
      (Scheme.Hom.formRes (f := D.f) g ((p + 1 : ℕ) : ℤ) c.U.1 (c.pullPart p x))
      (Scheme.Hom.formRes (f := D.f) g (p : ℤ) c.U.1 ((D.residueHom p).app c.U.1 x)) :=
  rfl

/-- The pulled-back part and the residue of the restriction of `x` are the restrictions of the
pulled-back part and the residue of `x`. -/
theorem pullPart_weightZeroRestrict (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    (c.baseChange g).pullPart p (c.weightZeroRestrict g p x) =
        Scheme.Hom.formRes (f := D.f) g ((p + 1 : ℕ) : ℤ) c.U.1 (c.pullPart p x) ∧
      ((D.baseChange g).residueHom p).app (c.baseChange g).U.1 (c.weightZeroRestrict g p x) =
        Scheme.Hom.formRes (f := D.f) g (p : ℤ) c.U.1 ((D.residueHom p).app c.U.1 x) :=
  (c.baseChange g).pullPart_decompose p _ _

/-- The restriction of weight-zero forms is semilinear along `g^♯ : Γ(X, U) → Γ(X', g⁻¹U)`. -/
theorem weightZeroRestrict_smul (p : ℕ) (r : Γ(D.X, c.U.1)) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c.weightZeroRestrict g p (r • x) =
      (show Γ((D.baseChange g).X, (c.baseChange g).U.1) from (g.app c.U.1).hom r) •
        c.weightZeroRestrict g p x := by
  rw [weightZeroRestrict_apply, weightZeroRestrict_apply, c.pullPart_smul,
    Scheme.Modules.Hom.app_smul, Scheme.Hom.formRes_smul, Scheme.Hom.formRes_smul]
  exact (c.baseChange g).decompose_smul p _ _ _

/-- Over a base chart, the restriction of the weight-zero form `π^*α` is `π̄^*(α|)`. -/
theorem weightZeroRestrict_pullbackHom (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1)) :
    c.weightZeroRestrict g p ((D.pullbackHom (p + 1)).app c.U.1 α) =
      ((D.baseChange g).pullbackHom (p + 1)).app (c.baseChange g).U.1
        (Scheme.Hom.formRes (f := D.f) g ((p + 1 : ℕ) : ℤ) c.U.1 α) := by
  obtain ⟨h1, h2⟩ := c.pullPart_pullbackHom p α
  rw [weightZeroRestrict_apply, h1, h2, Scheme.Hom.formRes_zero]
  exact ((c.baseChange g).pullbackHom_eq_decompose p _).symm

/-- Over a base chart, the restriction of weight-zero forms commutes with the differentials. -/
theorem weightZeroRestrict_weightZeroD (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c.weightZeroRestrict g (p + 1) (D.weightZeroD (p + 1) c.U.1 x) =
      (D.baseChange g).weightZeroD (p + 1) (c.baseChange g).U.1 (c.weightZeroRestrict g p x) := by
  obtain ⟨h1, h2⟩ := c.pullPart_weightZeroD p x
  rw [weightZeroRestrict_apply, weightZeroRestrict_apply, h1, h2, Scheme.Hom.formRes_neg]
  refine Eq.trans ?_ ((c.baseChange g).weightZeroD_decompose p _ _).symm
  exact congrArg₂ ((c.baseChange g).decompose (p + 1))
    (Scheme.Hom.formRestriction_deRhamD (f := D.f) g (p + 1) c.U.1 _)
    (congrArg Neg.neg (Scheme.Hom.formRestriction_deRhamD (f := D.f) g p c.U.1 _))

/-- **The restriction of weight-zero forms over nested base charts is compatible with
restriction**: changing the generator by `u` changes `α` by `u⁻¹ du ∧ η` on `X`, and the
pulled-back generators change by `g^♯ u`, which changes `α|` by `(g^♯u)⁻¹ d(g^♯u) ∧ η|`. -/
theorem weightZeroRestrict_res (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (p : ℕ)
    (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c'.weightZeroRestrict g p ((D.weightZero (p + 1)).presheaf.map (homOfLE h).op x) =
      ((D.baseChange g).weightZero (p + 1)).presheaf.map (homOfLE (g.preimage_mono h)).op
        (c.weightZeroRestrict g p x) := by
  obtain ⟨u, hu⟩ := c.exists_units_lineGen_res c' h
  have hresX : (D.residueHom p).app c'.U.1 ((D.weightZero (p + 1)).presheaf.map (homOfLE h).op x) =
      (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
        ((D.residueHom p).app c.U.1 x) :=
    PresheafOfModules.naturality_apply (D.residueHom p).val (homOfLE h).op x
  obtain ⟨hy1, hy2⟩ := c.pullPart_weightZeroRestrict g p x
  have hresY : ((D.baseChange g).residueHom p).app (c'.baseChange g).U.1
      (((D.baseChange g).weightZero (p + 1)).presheaf.map (homOfLE (g.preimage_mono h)).op
        (c.weightZeroRestrict g p x)) =
      (Scheme.Hom.relativeDifferentialForms (D.baseChange g).f (p : ℤ)).presheaf.map
        (homOfLE (g.preimage_mono h)).op
        (((D.baseChange g).residueHom p).app (c.baseChange g).U.1 (c.weightZeroRestrict g p x)) :=
    PresheafOfModules.naturality_apply ((D.baseChange g).residueHom p).val
      (homOfLE (g.preimage_mono h)).op _
  have hpY := (c.baseChange g).pullPart_res (c'.baseChange g) (g.preimage_mono h)
    (Units.map (g.app c'.U.1).hom.toMonoidHom u) (c.lineGen_baseChange_res g c' h u hu) p
    (c.weightZeroRestrict g p x)
  refine (c'.baseChange g).ext_decompose p ?_ ?_
  · refine ((c'.pullPart_weightZeroRestrict g p _).1.trans ?_).trans hpY.symm
    rw [c.pullPart_res c' h u hu, hy1, hy2, Scheme.Hom.formRes_add, Scheme.Hom.formRes_smul,
      show Scheme.Hom.formRes (f := D.f) g ((p + 1 : ℕ) : ℤ) c'.U.1
          (Scheme.Hom.exactWedge D.f p c'.U.1 (u : Γ(D.X, c'.U.1))
            ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
              ((D.residueHom p).app c.U.1 x))) = _ from
        Scheme.Hom.formRestriction_exactWedge (f := D.f) g p c'.U.1 _ _,
      formRes_map]
    have e2 : (Scheme.Hom.formRestriction g D.f (p : ℤ)).val.app (op c'.U.1)
        ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
          ((D.residueHom p).app c.U.1 x)) =
        (Scheme.Hom.relativeDifferentialForms (g ≫ D.f) (p : ℤ)).presheaf.map
          (homOfLE (g.preimage_mono h)).op
          (Scheme.Hom.formRes (f := D.f) g (p : ℤ) c.U.1 ((D.residueHom p).app c.U.1 x)) :=
      formRes_map g (p : ℤ) h _
    rw [e2]
    rfl
  · refine ((c'.pullPart_weightZeroRestrict g p _).2.trans ?_).trans hresY.symm
    rw [hresX, hy2]
    exact formRes_map g (p : ℤ) h _

end Restrict

end Situation.BaseChart

/-! ### The restriction of weight-zero forms as a morphism of modules -/

section Glue

variable (D : Situation.{u}) {X' : Scheme.{u}} (g : X' ⟶ D.X) [IsAffineHom g]

/-- There is a morphism `Ω^{p+1}_{L^⋆/S,0} ⟶ g_*Ω^{p+1}_{(g^*L)^⋆/S,0}` agreeing with
`Stacks.LineBundle.Situation.BaseChart.weightZeroRestrict` over every base chart. -/
theorem Situation.exists_weightZeroRestrictHom (p : ℕ) :
    ∃ φ : D.weightZero (p + 1) ⟶
        (Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero (p + 1)),
      ∀ (c : D.BaseChart) (x : Γ(D.weightZero (p + 1), c.U.1)),
        φ.app c.U.1 x = c.weightZeroRestrict g p x :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis
    (fun c : D.BaseChart => c.U.1) D.isBasis_baseChart
    (N := (Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero (p + 1)))
    (fun c => (c.weightZeroRestrict g p : Γ(D.weightZero (p + 1), c.U.1) →+
      Γ((Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero (p + 1)), c.U.1)))
    (fun c c' h x => c.weightZeroRestrict_res g c' h p x)
    (fun c r x => c.weightZeroRestrict_smul g p r x)

/-- **The restriction of weight-zero forms along `g`**,
`Ω^{p+1}_{L^⋆/S,0} ⟶ g_*Ω^{p+1}_{(g^*L)^⋆/S,0}`,
sending `π^*α + d log s ∧ π^*η` to `π̄^*(α|) + d log s̄ ∧ π̄^*(η|)` over every base chart, `s̄` the
pulled-back generator. -/
def Situation.weightZeroRestrictHom (p : ℕ) :
    D.weightZero (p + 1) ⟶
      (Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero (p + 1)) :=
  (D.exists_weightZeroRestrictHom g p).choose

/-- Over a base chart, `weightZeroRestrictHom` is
`Stacks.LineBundle.Situation.BaseChart.weightZeroRestrict`. -/
theorem Situation.weightZeroRestrictHom_app (p : ℕ) (c : D.BaseChart)
    (x : Γ(D.weightZero (p + 1), c.U.1)) :
    (D.weightZeroRestrictHom g p).app c.U.1 x = c.weightZeroRestrict g p x :=
  (D.exists_weightZeroRestrictHom g p).choose_spec c x

/-- **The restriction of weight-zero forms extends the restriction of forms**:
`π^*α ↦ π̄^*(α|)`. -/
theorem Situation.pullbackHom_comp_weightZeroRestrictHom (p : ℕ) :
    D.pullbackHom (p + 1) ≫ D.weightZeroRestrictHom g p =
      Scheme.Hom.formRestriction g D.f ((p + 1 : ℕ) : ℤ) ≫
        (Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom (p + 1)) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis
    (B := fun c : D.BaseChart => c.U.1) D.isBasis_baseChart fun c α =>
      (D.weightZeroRestrictHom_app g p c _).trans (c.weightZeroRestrict_pullbackHom g p α)

/-- **The restriction of weight-zero forms is compatible with the residues**: the residue of the
restriction is the restriction of the residue. -/
theorem Situation.weightZeroRestrictHom_comp_residueHom (p : ℕ) :
    D.weightZeroRestrictHom g p ≫
        (Scheme.Modules.pushforward g).map ((D.baseChange g).residueHom p) =
      D.residueHom p ≫ Scheme.Hom.formRestriction g D.f (p : ℤ) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis
    (B := fun c : D.BaseChart => c.U.1) D.isBasis_baseChart fun c x =>
      (congrArg (((D.baseChange g).residueHom p).app (c.baseChange g).U.1)
        (D.weightZeroRestrictHom_app g p c x)).trans (c.pullPart_weightZeroRestrict g p x).2

/-- The de Rham differential of the weight-zero forms of `g^*L`, pushed forward along `g`, as a
morphism of abelian sheaves on `X`. -/
def Situation.pushforwardWeightZeroDAbHom (n : ℕ) :
    (abelianSheaf D.X).obj
        ((Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero n)) ⟶
      (abelianSheaf D.X).obj
        ((Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero (n + 1))) :=
  abHom ((TopCat.Presheaf.pushforward Ab g.base).map ((D.baseChange g).weightZeroDPresheafHom n))

/-- **The restriction of weight-zero forms along `g` commutes with the differentials** in
positive degree. -/
theorem Situation.weightZeroDAbHom_comp_weightZeroRestrictHom (p : ℕ) :
    D.weightZeroDAbHom (p + 1) ≫ (abelianSheaf D.X).map (D.weightZeroRestrictHom g (p + 1)) =
      (abelianSheaf D.X).map (D.weightZeroRestrictHom g p) ≫
        D.pushforwardWeightZeroDAbHom g (p + 1) :=
  D.abelianSheaf_hom_ext fun c x => by
    change (D.weightZeroRestrictHom g (p + 1)).app c.U.1 (D.weightZeroD (p + 1) c.U.1 x) =
      (D.baseChange g).weightZeroD (p + 1) (c.baseChange g).U.1
        ((D.weightZeroRestrictHom g p).app c.U.1 x)
    rw [D.weightZeroRestrictHom_app, D.weightZeroRestrictHom_app]
    exact c.weightZeroRestrict_weightZeroD g p x

/-- **The restriction of weight-zero forms along `g` in every degree**: in degree `0` the
restriction of functions, `Ω^0_{L^⋆/S,0} = 𝒪_X ⟶ g_*𝒪_{X'} = g_*Ω^0_{(g^*L)^⋆/S,0}`, in degree
`p + 1` `Stacks.LineBundle.Situation.weightZeroRestrictHom`. -/
def Situation.weightZeroRestrictF :
    ∀ n : ℕ, D.weightZero n ⟶ (Scheme.Modules.pushforward g).obj ((D.baseChange g).weightZero n)
  | 0 => haveI := isIso_pullbackHom_zero D
    inv (D.pullbackHom 0) ≫ Scheme.Hom.formRestriction g D.f ((0 : ℕ) : ℤ) ≫
      (Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom 0)
  | p + 1 => D.weightZeroRestrictHom g p

/-- The restriction of weight-zero forms extends the restriction of forms in every degree:
`π^*α ↦ π̄^*(α|)`. -/
theorem Situation.pullbackHom_comp_weightZeroRestrictF (n : ℕ) :
    D.pullbackHom n ≫ D.weightZeroRestrictF g n =
      Scheme.Hom.formRestriction g D.f (n : ℤ) ≫
        (Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom n) := by
  cases n with
  | zero =>
    have := isIso_pullbackHom_zero D
    exact IsIso.hom_inv_id_assoc _ _
  | succ p => exact D.pullbackHom_comp_weightZeroRestrictHom g p

omit [IsAffineHom g] in
/-- The pushforward along `g` of the inclusion `Ω^•_{X'/S} ⟶ Ω^•_{(g^*L)^⋆/S,0}` commutes with the
differentials. -/
theorem Situation.pushforward_inclusionMap_comm (n : ℕ) :
    Scheme.Hom.pushforwardDeRhamDifferentialAbHom g D.f n ≫
        (abelianSheaf D.X).map
          ((Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom (n + 1))) =
      (abelianSheaf D.X).map ((Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom n)) ≫
        D.pushforwardWeightZeroDAbHom g n := by
  have h := (D.baseChange g).inclusionMap.comm n (n + 1)
  rw [Scheme.Hom.deRhamAbComplex_d, (D.baseChange g).weightZeroComplex_d] at h
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)))
  exact congrArg (fun φ => φ.hom.app (op (g ⁻¹ᵁ W.unop)) x) h.symm

/-- The restriction of weight-zero forms along `g` commutes with the differentials in every
degree. -/
theorem Situation.weightZeroDAbHom_comp_weightZeroRestrictF (n : ℕ) :
    D.weightZeroDAbHom n ≫ (abelianSheaf D.X).map (D.weightZeroRestrictF g (n + 1)) =
      (abelianSheaf D.X).map (D.weightZeroRestrictF g n) ≫ D.pushforwardWeightZeroDAbHom g n := by
  cases n with
  | succ p => exact D.weightZeroDAbHom_comp_weightZeroRestrictHom g p
  | zero =>
    have := isIso_pullbackHom_zero D
    have : IsIso ((abelianSheaf D.X).map (D.pullbackHom 0)) := Functor.map_isIso _ _
    rw [← cancel_epi ((abelianSheaf D.X).map (D.pullbackHom 0))]
    have h1 := D.inclusionMap.comm 0 1
    rw [D.weightZeroComplex_d, Scheme.Hom.deRhamAbComplex_d] at h1
    have e : ∀ m : ℕ, D.inclusionMap.f m ≫ (abelianSheaf D.X).map (D.weightZeroRestrictF g m) =
        (abelianSheaf D.X).map (Scheme.Hom.formRestriction g D.f (m : ℤ)) ≫
          (abelianSheaf D.X).map
            ((Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom m)) := fun m =>
      (Functor.map_comp _ _ _).symm.trans ((congrArg (abelianSheaf D.X).map
        (D.pullbackHom_comp_weightZeroRestrictF g m)).trans (Functor.map_comp _ _ _))
    have h2 : (abelianSheaf D.X).map (Scheme.Hom.formRestriction g D.f ((0 : ℕ) : ℤ)) ≫
          Scheme.Hom.pushforwardDeRhamDifferentialAbHom g D.f 0 =
        Scheme.Hom.deRhamDifferentialAbHom D.f 0 ≫
          (abelianSheaf D.X).map (Scheme.Hom.formRestriction g D.f ((1 : ℕ) : ℤ)) :=
      Scheme.Hom.formRestriction_comm_deRhamDifferentialAbHom g D.f 0
    have h3 : Scheme.Hom.pushforwardDeRhamDifferentialAbHom g D.f 0 ≫
          (abelianSheaf D.X).map
            ((Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom 1)) =
        (abelianSheaf D.X).map
            ((Scheme.Modules.pushforward g).map ((D.baseChange g).pullbackHom 0)) ≫
          D.pushforwardWeightZeroDAbHom g 0 :=
      D.pushforward_inclusionMap_comm g 0
    change (D.inclusionMap.f 0 ≫ D.weightZeroDAbHom 0) ≫
        (abelianSheaf D.X).map (D.weightZeroRestrictF g 1) =
      D.inclusionMap.f 0 ≫ (abelianSheaf D.X).map (D.weightZeroRestrictF g 0) ≫
        D.pushforwardWeightZeroDAbHom g 0
    exact ((congrArg (· ≫ _) h1).trans (Category.assoc _ _ _)).trans
      (((congrArg (_ ≫ ·) (e 1)).trans (Category.assoc _ _ _).symm).trans
        (((congrArg (· ≫ _) h2.symm).trans (Category.assoc _ _ _)).trans
          (((congrArg (_ ≫ ·) h3).trans (Category.assoc _ _ _).symm).trans
            ((congrArg (· ≫ _) (e 0).symm).trans (Category.assoc _ _ _)))))

end Glue

end Stacks.LineBundle
