module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequenceBase
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogPolesChartFormCalculus
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueSequenceBase

/-!
# The upper left morphism of short exact sequences of Stacks Tag 0FUQ

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by `I`,
for which the de Rham complex of log poles is defined. Put `L = 𝒪_X(-Y)`, the ideal sheaf of `Y`
(`Stacks.LineBundle.idealSituation`). The proof of the upper left triangle of Stacks Tag 0FUQ
compares the shifted residue sequence of Tag 0FUF for `L` with the shifted log poles sequence of
Tag 0FMW through the morphism of short exact sequences

```
0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0
        ‖                  ↓                ↓
0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0
```

whose middle arrow is `ω' + d log s ∧ ω ↦ ω' + d log t ∧ ω`, `s` a local generator of `L` and `t`
the corresponding local equation of `Y`. This file constructs that arrow and checks the morphism.

## Main definitions

* `Stacks.LineBundle.Situation.BaseChart.lineTriv`: the trivialization of `L` over a base chart
  by the generator of the chart; for `L = 𝒪_X(-Y)` it is an ideal trivialization
  (`Stacks.LineBundle.Situation.BaseChart.idealTriv`), whose local equation is `t`.
* `Stacks.LineBundle.Situation.BaseChart.pullPart`: the part `α` of the decomposition
  `π^*α + d log s ∧ π^*η` of a weight-zero form over a base chart.
* `Stacks.LineBundle.toLogPolesHom`, `Stacks.LineBundle.toLogPolesF`: the middle arrow in each
  degree, glued from `Stacks.LineBundle.Situation.BaseChart.toLogPoles` over the base charts.
* `Stacks.LineBundle.residueToLogPolesMap`: the middle arrow as a map of complexes of sheaves of
  `f^{-1}𝒪_S`-modules.
* `Stacks.LineBundle.residueLogPolesMorphism`: **the morphism of short exact sequences.**

## Main results

* `Stacks.LineBundle.Situation.BaseChart.pullPart_res`: changing the chart changes the
  decomposition by `d log s = d log (π^♯ u) + d log s'`.
* `Stacks.LineBundle.Situation.BaseChart.toLogPoles_res`: the chart-wise arrows glue; the change
  of chart on the log side is `Stacks.Divisors.IdealTrivialization
  .logPolesChartForm_eq_of_equationAt_eq_mul`.
* `Stacks.LineBundle.residueShiftedSequence_boundary_eq`: **the upper left triangle of Tag 0FUQ
  at the level of boundary maps.**

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry KaehlerDifferential

universe w u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.LogPoles

/-- **`dlog v` is closed**: `d (v⁻¹ dv) = d(v⁻¹) ∧ dv = 0`, `d(v⁻¹)` being a multiple of `dv`. -/
theorem deRhamDifferential_ιMulti_dlogUnit {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (v : Bˣ) :
    deRhamDifferential (A := R) 1 (exteriorPower.ιMulti B 1 fun _ => dlogUnit R v) = 0 := by
  have hD : KaehlerDifferential.D R B (↑v⁻¹ : B) =
      (-((↑v⁻¹ : B) * (↑v⁻¹ : B))) • KaehlerDifferential.D R B (v : B) := by
    have h := (KaehlerDifferential.D R B).leibniz (↑v⁻¹ : B) (v : B)
    rw [v.inv_mul, (KaehlerDifferential.D R B).map_one_eq_zero] at h
    have h2 := congrArg (fun z : Ω[B⁄R] => (↑v⁻¹ : B) • z) h
    simp only [smul_zero, smul_add, smul_smul, v.inv_mul, one_smul] at h2
    rw [neg_smul, mul_smul, eq_neg_iff_add_eq_zero]
    rw [add_comm]
    simpa [smul_smul, mul_comm] using h2.symm
  have key : (exteriorPower.ιMulti B 1 fun _ => dlogUnit R v) =
      (![(↑v⁻¹ : B), (v : B)] 0) • exteriorPower.ιMulti B 1 fun i =>
        KaehlerDifferential.D R B (![(↑v⁻¹ : B), (v : B)] i.succ) := by
    show _ = (↑v⁻¹ : B) • exteriorPower.ιMulti B 1 fun _ => KaehlerDifferential.D R B (v : B)
    rw [KaehlerDifferential.smul_ιMulti_one]
    rfl
  rw [key, deRhamDifferential_smul_ιMulti_D]
  have h2 : (fun i : Fin 2 => KaehlerDifferential.D R B (![(↑v⁻¹ : B), (v : B)] i)) =
      Function.update (fun _ => KaehlerDifferential.D R B (v : B)) 0
        ((-((↑v⁻¹ : B) * (↑v⁻¹ : B))) • KaehlerDifferential.D R B (v : B)) := by
    funext i
    fin_cases i
    · simp [hD]
    · simp
  rw [h2, AlternatingMap.map_update_smul, Function.update_eq_self,
    AlternatingMap.map_eq_zero_of_eq _ (fun _ => KaehlerDifferential.D R B (v : B))
      (i := (0 : Fin (1 + 1))) (j := 1) rfl (by decide), smul_zero]

end Stacks.LogPoles

namespace Stacks.LineBundle

/-! ### The pullback of forms along `π` on sections -/

namespace Situation

variable (D : Situation.{u})

/-- **The pullback of forms along `π` is multiplicative**: it carries the product of a `p`-form
and a one-form on `X` to the product of their pullbacks. -/
theorem gradedWedge_pullbackG (p : ℕ) (U : D.X.Opens)
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (γ : Γ(Scheme.Hom.relativeDifferentialForms D.f (1 : ℤ), U)) :
    D.gradedWedge p U (D.pullbackG p U β) (D.pullbackG 1 U γ) =
      D.pullbackG (p + 1) U
        (((Scheme.Hom.deRhamAlgebras D.f).exterior.mul (p : ℤ) 1).app (op U) β γ) :=
  ((Scheme.Hom.deRhamFormsPushforwardHom D.laurentSpectrumToBase D.f
    (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S)
    ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm)).map_mul (p : ℤ) 1 (op U) β γ).symm

/-- **The pullback of forms along `π` carries `d b` to `d (π^♯ b)`.** -/
theorem pullbackG_exactOne (U : D.X.Opens) (b : Γ(D.X, U)) :
    D.pullbackG 1 U (AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.f)
      (op U) b) = D.gradedD U (D.laurentPullbackFunction U b) :=
  Scheme.Hom.deRhamFormsPushforwardHom_exactOne D.laurentSpectrumToBase D.f
    (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S)
    ((Category.comp_id (D.laurentSpectrumToBase ≫ D.f)).symm) (op U) b

/-- **The pullback of forms along `π` is `𝒪_X`-linear.** -/
theorem pullbackG_smul (p : ℕ) (U : D.X.Opens) (b : Γ(D.X, U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.pullbackG p U (b • β) = b • D.pullbackG p U β :=
  D.pullbackForms_smul p U b β

/-- The pullback along `π` of an invertible function on an open of `X`, as an invertible function
on `L^⋆`. -/
def laurentPullbackUnit (U : D.X.Opens) (v : (Γ(D.X, U))ˣ) :
    (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ :=
  Units.map (D.laurentSpectrumToBase.c.app (op U)).hom.toMonoidHom v

/-- **`d log` of a function pulled back from `X` is pulled back from `X`**: `d log (π^♯ v)` is the
pullback of `v⁻¹ dv`. -/
theorem laurentDlog_laurentPullbackUnit (U : D.X.Opens) (v : (Γ(D.X, U))ˣ) :
    D.laurentDlog U (D.laurentPullbackUnit U v) =
      D.pullbackG 1 U ((↑v⁻¹ : Γ(D.X, U)) •
        (show Γ(Scheme.Hom.relativeDifferentialForms D.f ((1 : ℕ) : ℤ), U) from
          AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.f) (op U)
            (v : Γ(D.X, U)))) := by
  rw [D.pullbackG_smul, D.pullbackG_exactOne]
  rfl

/-- Multiplying twice by `(-1) ^ p` is the identity. -/
private theorem neg_one_pow_smul_neg_one_pow_smul {M : Type*} [AddCommGroup M] (p : ℕ) (x : M) :
    ((-1 : ℤ) ^ p) • ((-1 : ℤ) ^ p) • x = x := by
  rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨p, rfl⟩, one_smul]

private theorem neg_one_pow_formProduct (p : ℕ) (U : D.X.Opens)
    (β : ((Scheme.Hom.deRhamAlgebras D.f).exteriorPower p).val.obj (op U))
    (γ : ((Scheme.Hom.deRhamAlgebras D.f).exteriorPower 1).val.obj (op U)) :
    AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras D.f) p 1 (op U)
        (((-1 : ℤ) ^ p) • β) γ =
      AlgebraicGeometry.SheafOfModules.reindexForm (Scheme.Hom.deRhamAlgebras D.f)
        (Nat.add_comm 1 p) (op U)
        (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras D.f) 1 p (op U)
          γ β) := by
  have h2 : AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras D.f) p 1
      (op U) (((-1 : ℤ) ^ p) • β) γ = ((-1 : ℤ) ^ p) •
        AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras D.f) p 1 (op U)
          β γ :=
    congrFun (congrArg DFunLike.coe
      (map_zsmul (((Scheme.Hom.deRhamAlgebras D.f).exterior.mul (p : ℤ) 1).app (op U))
        ((-1 : ℤ) ^ p) β)) γ
  rw [h2, AlgebraicGeometry.SheafOfModules.formProduct_comm _ p 1 (op U) β γ, mul_one,
    neg_one_pow_smul_neg_one_pow_smul]

/-- **Changing the coordinate by a function pulled back from `X`**: with the right-wedge
normalization of the weight-zero forms, `π^*((-1)^p β) ∧ d log (π^♯ v)` is the pullback of
`v⁻¹ dv ∧ β`. -/
theorem gradedWedge_pullbackG_laurentDlog_laurentPullbackUnit (p : ℕ) (U : D.X.Opens)
    (v : (Γ(D.X, U))ˣ) (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.gradedWedge p U (D.pullbackG p U (((-1 : ℤ) ^ p) • β))
        (D.laurentDlog U (D.laurentPullbackUnit U v)) =
      D.pullbackG (p + 1) U ((↑v⁻¹ : Γ(D.X, U)) •
        Scheme.Hom.exactWedge D.f p U (v : Γ(D.X, U)) β) := by
  rw [D.laurentDlog_laurentPullbackUnit, D.gradedWedge_pullbackG]
  congr 1
  exact ((((Scheme.Hom.deRhamAlgebras D.f).exterior.mul (p : ℤ) 1).map_smul_right (op U)
    (show D.X.sheaf.obj.obj (op U) from (↑v⁻¹ : Γ(D.X, U))) (((-1 : ℤ) ^ p) • β) _)).trans
    (congrArg ((show D.X.sheaf.obj.obj (op U) from (↑v⁻¹ : Γ(D.X, U))) • ·)
      (D.neg_one_pow_formProduct p U β _))

end Situation

namespace Situation.BaseChart

variable {D : Situation.{u}} (c : D.BaseChart)

/-- The generator of the line bundle over a base chart: the generator of its Laurent chart, read
in `L` along `L^{⊗ 1} ≅ L`. -/
def lineGen : D.L.val.obj (op c.U.1) :=
  (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj D.X.ringCatSheaf.property
    D.L).hom.val.app (op c.U.1) c.chart.gen

/-- **The generator of a base chart generates `L` over every smaller open.** -/
theorem bijective_smul_lineGen (W : D.X.Opens) (h : W ≤ c.U.1) :
    Function.Bijective (fun r : D.X.ringCatSheaf.obj.obj (op W) =>
      r • D.L.val.map (homOfLE h).op c.lineGen) := by
  let e := Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L
  have he : Function.Bijective (e.hom.val.app (op W)) :=
    ⟨Function.LeftInverse.injective (g := e.inv.val.app (op W)) fun x =>
        congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op W) x) e.hom_inv_id,
      Function.RightInverse.surjective (g := e.inv.val.app (op W)) fun y =>
        congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op W) y) e.inv_hom_id⟩
  have key : (fun r : D.X.ringCatSheaf.obj.obj (op W) =>
      r • D.L.val.map (homOfLE h).op c.lineGen) =
      e.hom.val.app (op W) ∘ (fun r => r • (D.tensorPower 1).val.map (homOfLE h).op
        c.chart.gen) := by
    funext r
    refine Eq.trans ?_ (((e.hom.val.app (op W)).hom.map_smul r _).symm)
    exact congrArg (r • ·) (PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op
      c.chart.gen).symm
  rw [key]
  exact he.comp (c.chart.bijective_smul_res_gen c.U.2 W (homOfLE h))

/-- The generator of a base chart restricted to an open `W` inside it. -/
def lineGenAt {W : D.X.Opens} (h : W ⟶ c.U.1) : D.L.val.obj (op W) :=
  D.L.val.map h.op c.lineGen

/-- Restricting the generator restricted to `W` further to `W' ≤ W` gives the generator restricted
to `W'`. -/
theorem lineGenAt_comp {W W' : D.X.Opens} (h : W ⟶ c.U.1) (h' : W' ⟶ W) :
    D.L.val.map h'.op (c.lineGenAt h) = c.lineGenAt (h' ≫ h) := by
  rw [lineGenAt, lineGenAt, op_comp, PresheafOfModules.map_comp_apply]

/-- The coordinate with respect to the generator, as a linear equivalence. -/
def lineCoord {W : D.X.Opens} (h : W ⟶ c.U.1) :
    (D.L.val.obj (op W) : Type u) ≃ₗ[(D.X.ringCatSheaf.obj.obj (op W) : Type u)]
      (D.X.ringCatSheaf.obj.obj (op W) : Type u) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (c.lineGenAt h))
    (c.bijective_smul_lineGen W (leOfHom h))).symm

/-- Every local section of `L` over `W ≤ U` is its coordinate times the restricted generator. -/
theorem eq_lineCoord_smul {W : D.X.Opens} (h : W ⟶ c.U.1) (m : D.L.val.obj (op W)) :
    m = c.lineCoord h m • c.lineGenAt h :=
  ((c.lineCoord h).symm_apply_apply m).symm

/-- The coordinate of `r • g|_W` is `r`. -/
theorem lineCoord_smul_lineGenAt {W : D.X.Opens} (h : W ⟶ c.U.1)
    (r : D.X.ringCatSheaf.obj.obj (op W)) :
    c.lineCoord h (r • c.lineGenAt h) = r :=
  (c.lineCoord h).apply_symm_apply r

/-- **The sectionwise trivialization of `L` over a base chart** given by its generator: the
coordinate of a local section `m` over `W ≤ U` is the unique `r` with `m = r • g|_W`. -/
def lineTriv : Stacks.SheafDescent.Trivialization D.X.presheaf D.L.val c.U.1 where
  θ W h := c.lineCoord h
  θ_naturality {W W'} h h' m := by
    have key : D.L.val.map h'.op m =
        D.X.ringCatSheaf.obj.map h'.op (c.lineCoord h m) • c.lineGenAt (h' ≫ h) := by
      refine (congrArg (D.L.val.map h'.op) (c.eq_lineCoord_smul h m)).trans ?_
      exact (PresheafOfModules.map_smul D.L.val h'.op _ _).trans
        (congrArg (_ • ·) (c.lineGenAt_comp h h'))
    exact (congrArg (c.lineCoord (h' ≫ h)) key).trans (c.lineCoord_smul_lineGenAt _ _)

/-- The generator restricted to the whole chart is the generator. -/
theorem lineGenAt_id : c.lineGenAt (𝟙 c.U.1) = c.lineGen := by
  rw [lineGenAt, op_id, PresheafOfModules.map_id]
  rfl

/-- **The generators of two nested base charts differ by an invertible function**:
`g|_{U'} = u · g'`. -/
theorem exists_units_lineGen_res (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) :
    ∃ u : (Γ(D.X, c'.U.1))ˣ,
      D.L.val.map (homOfLE h).op c.lineGen =
        (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.lineGen := by
  set v := c'.lineCoord (𝟙 c'.U.1) (D.L.val.map (homOfLE h).op c.lineGen)
  set w := c.lineCoord (homOfLE h) c'.lineGen
  have hv : D.L.val.map (homOfLE h).op c.lineGen = v • c'.lineGen := by
    have := c'.eq_lineCoord_smul (𝟙 c'.U.1) (D.L.val.map (homOfLE h).op c.lineGen)
    rwa [c'.lineGenAt_id] at this
  have hw : c'.lineGen = w • c.lineGenAt (homOfLE h) := c.eq_lineCoord_smul (homOfLE h) _
  have hvw : v * w = 1 := by
    refine (c.bijective_smul_lineGen c'.U.1 h).1 ?_
    show (v * w) • c.lineGenAt (homOfLE h) = (1 : D.X.ringCatSheaf.obj.obj (op c'.U.1)) •
      c.lineGenAt (homOfLE h)
    rw [one_smul, mul_smul, ← hw]
    exact hv.symm
  exact ⟨⟨(show Γ(D.X, c'.U.1) from v), (show Γ(D.X, c'.U.1) from w), hvw,
    (mul_comm (show Γ(D.X, c'.U.1) from w) (show Γ(D.X, c'.U.1) from v)).trans hvw⟩, hv⟩

/-- The generator of the Laurent chart is the generator of `L` read in `L^{⊗ 1}` along
`L ≅ L^{⊗ 1}`. -/
theorem gen_eq_lineGen : c.chart.gen =
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj D.X.ringCatSheaf.property
      D.L).inv.val.app (op c.U.1) c.lineGen :=
  (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op c.U.1) c.chart.gen)
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj D.X.ringCatSheaf.property
      D.L).hom_inv_id).symm

/-- The generators of the Laurent charts of two nested base charts differ by the same invertible
function as their generators of `L`. -/
theorem gen_res_eq (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (u : (Γ(D.X, c'.U.1))ˣ)
    (hu : D.L.val.map (homOfLE h).op c.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.lineGen) :
    (D.tensorPower 1).val.map (homOfLE h).op c.chart.gen =
      (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.chart.gen := by
  let e := Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L
  rw [c.gen_eq_lineGen, c'.gen_eq_lineGen]
  refine (PresheafOfModules.naturality_apply e.inv.val (homOfLE h).op c.lineGen).symm.trans ?_
  exact (congrArg (e.inv.val.app (op c'.U.1)) hu).trans
    ((e.inv.val.app (op c'.U.1)).hom.map_smul _ _)

/-- **The coordinates of two nested base charts differ by the pullback of an invertible function
on `X`**: `s|_{π⁻¹U'} = π^♯ u · s'`. -/
theorem unit_res_eq (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (u : (Γ(D.X, c'.U.1))ˣ)
    (hu : D.L.val.map (homOfLE h).op c.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.lineGen) :
    Units.map (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom.toMonoidHom
        c.unit = D.laurentPullbackUnit c'.U.1 u * c'.unit := by
  ext
  show (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom
      (D.secR _ (c.unit : D.laurentSpectrum.sheaf.obj.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)))) =
    D.laurentPullbackFunction c'.U.1 (u : Γ(D.X, c'.U.1)) *
      (D.secR _).symm (D.secR _ (c'.unit : D.laurentSpectrum.sheaf.obj.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ c'.U.1))))
  rw [c.unit_val, c'.unit_val]
  exact (D.laurentFunction_map 1 h c.chart.gen).trans
    ((congrArg (D.laurentFunction 1 c'.U) (c.gen_res_eq c' h u hu)).trans
      (D.laurentFunction_smul 1 c'.U _ _))

/-! ### The decomposition of a weight-zero form over a base chart -/

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB isScalarTower

/-- The logarithmic differential `d log s` of the coordinate of a base chart. -/
abbrev dlogCoord : Γ(D.gradedAmbient 1, c.U.1) := D.laurentDlog c.U.1 c.unit

/-- **The part pulled back from `X`** of a weight-zero form `x = π^*α + π^*β ∧ d log s` over a
base chart: the form `α`. -/
def pullPart (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1) :=
  Classical.choose (c.model.exists_decomposition (D.weightZeroVal_mem (p + 1) x)
    (c.isDlog_laurentDlog c.unit) c.unit_mem)

/-- **The decomposition of a weight-zero form**: `x = π^*α + π^*((-1)^p η) ∧ d log s`, with `α`
the pulled-back part and `η` the residue of Stacks Tag 0FUF; equivalently
`x = π^*α + d log s ∧ π^*η`. -/
theorem weightZeroVal_eq_pullPart (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    D.weightZeroVal (p + 1) x = D.pullbackG (p + 1) c.U.1 (c.pullPart p x) +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) •
        (D.residueHom p).app c.U.1 x)) c.dlogCoord := by
  have h := Classical.choose_spec (c.model.exists_decomposition (D.weightZeroVal_mem (p + 1) x)
    (c.isDlog_laurentDlog c.unit) c.unit_mem)
  refine h.trans ?_
  rw [D.residueHom_app, neg_one_pow_smul_neg_one_pow_smul]
  rfl

/-- **The decomposition is unique.** -/
theorem pullPart_eq_of_eq (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1))
    (h : D.weightZeroVal (p + 1) x = D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) • η)) c.dlogCoord) :
    c.pullPart p x = α ∧ (D.residueHom p).app c.U.1 x = η := by
  have hη : (D.residueHom p).app c.U.1 x = η := by
    rw [D.residueHom_app]
    have h2 := c.model.res_decomposition p α (((-1 : ℤ) ^ p) • η)
      (c.isDlog_laurentDlog c.unit) c.unit_mem
    change c.model.res p (D.pullbackG (p + 1) c.U.1 α +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 (((-1 : ℤ) ^ p) • η)) c.dlogCoord) = _ at h2
    rw [h, h2, neg_one_pow_smul_neg_one_pow_smul]
  refine ⟨?_, hη⟩
  have h0 := c.weightZeroVal_eq_pullPart p x
  rw [hη, h] at h0
  exact c.model.pull_injective (p + 1) (add_right_cancel h0).symm

/-- The part pulled back from `X` is additive. -/
theorem pullPart_add (p : ℕ) (x y : Γ(D.weightZero (p + 1), c.U.1)) :
    c.pullPart p (x + y) = c.pullPart p x + c.pullPart p y := by
  refine (c.pullPart_eq_of_eq p (x + y) _ ((D.residueHom p).app c.U.1 x +
    (D.residueHom p).app c.U.1 y) ?_).1
  rw [D.weightZeroVal_add, c.weightZeroVal_eq_pullPart, c.weightZeroVal_eq_pullPart,
    smul_add, c.pullbackG_add, c.pullbackG_add, D.gradedWedge_add_left]
  abel

/-- The part pulled back from `X` is `𝒪_X`-linear. -/
theorem pullPart_smul (p : ℕ) (r : Γ(D.X, c.U.1)) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c.pullPart p (r • x) = r • c.pullPart p x := by
  refine (c.pullPart_eq_of_eq p (r • x) _ (r • (D.residueHom p).app c.U.1 x) ?_).1
  rw [D.weightZeroVal_smul, c.weightZeroVal_eq_pullPart, smul_add, D.pullbackG_smul, smul_comm,
    D.pullbackG_smul, D.gradedWedge_smul_left]

/-- **Restricting the decomposition to a smaller base chart**: with `g|_{U'} = u g'`, the part
pulled back from `X` changes by `u⁻¹ du ∧ η`, i.e. `d log s = d log (π^♯ u) + d log s'`. -/
theorem pullPart_res (c' : D.BaseChart) (h : c'.U.1 ≤ c.U.1) (u : (Γ(D.X, c'.U.1))ˣ)
    (hu : D.L.val.map (homOfLE h).op c.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(D.X, c'.U.1))) • c'.lineGen)
    (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c'.pullPart p ((D.weightZero (p + 1)).presheaf.map (homOfLE h).op x) =
      (Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op
          (c.pullPart p x) +
        (↑u⁻¹ : Γ(D.X, c'.U.1)) • Scheme.Hom.exactWedge D.f p c'.U.1 (u : Γ(D.X, c'.U.1))
          ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op
            ((D.residueHom p).app c.U.1 x)) := by
  set η := (D.residueHom p).app c.U.1 x
  refine (c'.pullPart_eq_of_eq p _ _
    ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE h).op η) ?_).1
  rw [D.weightZeroVal_map (p + 1) h x, c.weightZeroVal_eq_pullPart, D.map_decomposition p h,
    c.unit_res_eq c' h u hu, D.laurentDlog_mul, D.gradedWedge_add_right, map_zsmul,
    D.gradedWedge_pullbackG_laurentDlog_laurentPullbackUnit, c'.pullbackG_add]
  abel

/-- **`d log s` is closed** over a base chart. -/
theorem gradedDiff_dlogCoord : D.gradedDiff 1 c.U.1 c.dlogCoord = 0 := by
  apply c.formsLF_injective (1 + 1)
  rw [c.formsLF_gradedDiff, c.formsLF_laurentDlog,
    Stacks.LogPoles.deRhamDifferential_ιMulti_dlogUnit, map_zero]

/-- **The decomposition of the differential of a weight-zero form**:
`d(π^*α + d log s ∧ π^*η) = π^*dα + d log s ∧ π^*(-dη)`. -/
theorem pullPart_weightZeroD (p : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1)) :
    c.pullPart (p + 1) (D.weightZeroD (p + 1) c.U.1 x) = D.dX (p + 1) c.U.1 (c.pullPart p x) ∧
      (D.residueHom (p + 1)).app c.U.1 (D.weightZeroD (p + 1) c.U.1 x) =
        -D.dX p c.U.1 ((D.residueHom p).app c.U.1 x) := by
  refine c.pullPart_eq_of_eq (p + 1) _ _ _ ?_
  rw [D.weightZeroVal_weightZeroD, c.weightZeroVal_eq_pullPart, D.gradedDiff_add]
  show c.model.dF (p + 1) (c.model.pull (p + 1) _) + D.gradedDiff (p + 1) c.U.1
    (D.gradedWedge p c.U.1 (c.model.pull p _) c.dlogCoord) = _
  rw [c.model.dF_pull, D.gradedDiff_gradedWedge_of_gradedDiff_eq_zero p c.U.1 _ _
    c.gradedDiff_dlogCoord]
  show _ + D.gradedWedge (p + 1) c.U.1 (c.model.dF p (c.model.pull p _)) c.dlogCoord = _
  rw [c.model.dF_pull]
  have hη : c.model.dG p (((-1 : ℤ) ^ p) • (D.residueHom p).app c.U.1 x) =
      ((-1 : ℤ) ^ (p + 1)) • -D.dX p c.U.1 ((D.residueHom p).app c.U.1 x) := by
    rw [c.model.dG_zsmul, pow_succ, mul_neg_one, neg_smul, smul_neg, neg_neg]
  rw [hη]
  rfl

/-- **The decomposition of a form pulled back from `X`**: `π^*α = π^*α + d log s ∧ 0`. -/
theorem pullPart_pullbackHom (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((p + 1 : ℕ) : ℤ), c.U.1)) :
    c.pullPart p ((D.pullbackHom (p + 1)).app c.U.1 α) = α ∧
      (D.residueHom p).app c.U.1 ((D.pullbackHom (p + 1)).app c.U.1 α) = 0 := by
  refine c.pullPart_eq_of_eq p _ _ _ ?_
  rw [D.pullbackHom_app, smul_zero]
  show _ = c.model.pull (p + 1) α + c.model.wedge p (c.model.pull p 0) c.dlogCoord
  rw [map_zero, c.model.wedge_zero_left, add_zero]
  rfl

end Situation.BaseChart

/-! ### The upper left morphism of Tag 0FUQ, over a base chart -/

section Ideal

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]

/-- **The line-bundle situation of `𝒪_X(-Y)`**: the morphism `f : X ⟶ S` together with the ideal
sheaf `ℐ = 𝒪_X(-Y)` of an effective Cartier divisor, which is invertible. Its residue sequence
(Stacks Tag 0FUF) is the one the upper left triangle of Stacks Tag 0FUQ is read from. -/
abbrev idealSituation : Situation.{u} where
  X := X
  S := S
  f := f
  L := Stacks.Divisors.negativeTwist I
  invertible := hI

namespace Situation.BaseChart

variable {f I} (c : (idealSituation f I).BaseChart)

/-- The trivialization of the ideal sheaf `ℐ = 𝒪_X(-Y)` over a base chart of the situation of
`𝒪_X(-Y)`, by the generator of the chart. -/
abbrev idealTriv : Stacks.Divisors.IdealTrivialization I c.U.1 := c.lineTriv

/-- The basis element of the ideal trivialization over `W ≤ U` is the restricted generator. -/
theorem idealTriv_basisLE {W : X.Opens} (h : W ≤ c.U.1) :
    c.idealTriv.basisLE h = (idealSituation f I).L.val.map (homOfLE h).op c.lineGen := by
  show (idealSituation f I).L.val.map (homOfLE h).op
    ((LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (c.lineGenAt (𝟙 c.U.1)))
      (c.bijective_smul_lineGen c.U.1 le_rfl)) 1) = _
  exact congrArg ((idealSituation f I).L.val.map (homOfLE h).op)
    ((one_smul _ (c.lineGenAt (𝟙 c.U.1))).trans c.lineGenAt_id)

/-- On nested base charts the local equations differ by the invertible function relating the
generators: `t|_{U'} = u t'`. -/
theorem idealTriv_equationAt_res (c' : (idealSituation f I).BaseChart) (h : c'.U.1 ≤ c.U.1)
    (u : (Γ(X, c'.U.1))ˣ)
    (hu : (idealSituation f I).L.val.map (homOfLE h).op c.lineGen =
      (show (idealSituation f I).X.ringCatSheaf.obj.obj (op c'.U.1) from (u : Γ(X, c'.U.1))) •
        c'.lineGen) :
    c.idealTriv.equationAt h = (u : Γ(X, c'.U.1)) * c'.idealTriv.equationAt le_rfl := by
  show Scheme.Hom.negativeTwistSection I c'.U.1 (c.idealTriv.basisLE h) =
    _ * Scheme.Hom.negativeTwistSection I c'.U.1 (c'.idealTriv.basisLE le_rfl)
  rw [c.idealTriv_basisLE h, c'.idealTriv_basisLE le_rfl]
  have hid : (idealSituation f I).L.val.map (homOfLE (le_refl c'.U.1)).op c'.lineGen =
      c'.lineGen := c'.lineGenAt_id
  exact (congrArg (Scheme.Hom.negativeTwistSection I c'.U.1) hu).trans
    ((((Stacks.Divisors.idealInclusion I).val.app (op c'.U.1)).hom.map_smul _ _).trans
      (congrArg (fun z => (u : Γ(X, c'.U.1)) *
        (show Γ(X, c'.U.1) from Scheme.Hom.negativeTwistSection I c'.U.1 z)) hid.symm))

/-- **The upper left morphism of Stacks Tag 0FUQ over a base chart**: the weight-zero form
`π^*α + d log s ∧ π^*η` goes to the form `α + d log t ∧ η` with a logarithmic pole, `t` the local
equation of `Y` corresponding to the generator `s` of `𝒪_X(-Y)`. -/
def toLogPoles (p : ℕ) :
    Γ((idealSituation f I).weightZero (p + 1), c.U.1) →+
      Γ(Scheme.Hom.logPolesForms f I (p + 1), c.U.1) :=
  AddMonoidHom.mk' (fun x => c.idealTriv.logPolesChartForm le_rfl (c.pullPart p x)
    (((idealSituation f I).residueHom p).app c.U.1 x)) fun x y => by
    rw [c.pullPart_add, map_add]
    exact c.idealTriv.logPolesChartForm_add le_rfl _ _ _ _

/-- `toLogPoles` sends `x` to the chart form built from its pulled-back part and its residue. -/
theorem toLogPoles_apply (p : ℕ) (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    c.toLogPoles p x = c.idealTriv.logPolesChartForm le_rfl (c.pullPart p x)
      (((idealSituation f I).residueHom p).app c.U.1 x) :=
  rfl

/-- The upper left morphism over a base chart is `𝒪_X`-linear. -/
theorem toLogPoles_smul (p : ℕ) (r : Γ((idealSituation f I).X, c.U.1))
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    c.toLogPoles p (r • x) = (show X.ringCatSheaf.obj.obj (op c.U.1) from r) •
      (show (Scheme.Hom.logPolesForms f I (p + 1)).val.obj (op c.U.1) from c.toLogPoles p x) := by
  rw [toLogPoles_apply, toLogPoles_apply, c.pullPart_smul, Scheme.Modules.Hom.app_smul]
  exact c.idealTriv.logPolesChartForm_smul le_rfl r _ _

/-- **The upper left morphism over nested base charts is compatible with restriction.** -/
theorem toLogPoles_res (c' : (idealSituation f I).BaseChart) (h : c'.U.1 ≤ c.U.1) (p : ℕ)
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    c'.toLogPoles p (((idealSituation f I).weightZero (p + 1)).presheaf.map (homOfLE h).op x) =
      (Scheme.Hom.logPolesForms f I (p + 1)).presheaf.map (homOfLE h).op (c.toLogPoles p x) := by
  obtain ⟨u, hu⟩ := c.exists_units_lineGen_res c' h
  have hres : ((idealSituation f I).residueHom p).app c'.U.1
      (((idealSituation f I).weightZero (p + 1)).presheaf.map (homOfLE h).op x) =
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
        (((idealSituation f I).residueHom p).app c.U.1 x) :=
    PresheafOfModules.naturality_apply ((idealSituation f I).residueHom p).val (homOfLE h).op x
  rw [toLogPoles_apply, toLogPoles_apply, c.pullPart_res c' h u hu, hres]
  show _ = (Scheme.Hom.logPolesForms f I (p + 1)).val.map (homOfLE h).op _
  refine Eq.trans ?_ (c.idealTriv.logPolesChartForm_res le_rfl h _ _).symm
  exact (c.idealTriv.logPolesChartForm_eq_of_equationAt_eq_mul c'.idealTriv (h.trans le_rfl)
    le_rfl (show Γ(X, c'.U.1) from ↑u⁻¹) (show Γ(X, c'.U.1) from ↑u)
    (c.idealTriv_equationAt_res c' h u hu)
    (Units.inv_mul u) _ _).symm

/-- **On forms with no pole the upper left morphism is the inclusion**: `π^*α ↦ α`. -/
theorem toLogPoles_pullbackHom (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), c.U.1)) :
    c.toLogPoles p (((idealSituation f I).pullbackHom (p + 1)).app c.U.1 α) =
      (Scheme.Hom.logPolesFormsInclusion f I (p + 1)).app c.U.1 α := by
  obtain ⟨h1, h2⟩ := c.pullPart_pullbackHom p α
  rw [toLogPoles_apply, h1, h2]
  exact (c.idealTriv.logPolesFormsInclusion_eq_logPolesChartForm le_rfl α).symm

/-- **The upper left morphism commutes with the differentials** over a base chart:
`d(α + d log t ∧ η) = dα + d log t ∧ (-dη)` on both sides. -/
theorem toLogPoles_weightZeroD (hlog : f.HasLogPolesDeRhamComplex I) (p : ℕ)
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    c.toLogPoles (p + 1) ((idealSituation f I).weightZeroD (p + 1) c.U.1 x) =
      Scheme.Hom.logD hI hlog (c.toLogPoles p x) := by
  obtain ⟨h1, h2⟩ := c.pullPart_weightZeroD p x
  rw [toLogPoles_apply, toLogPoles_apply, h1, h2,
    Stacks.Divisors.IdealTrivialization.logD_logPolesChartForm]
  rfl

/-- **The upper left morphism is compatible with the residues**: the residue of `α + d log t ∧ η`
is `η|_Y`, the restriction to `Y` of the residue of `π^*α + d log s ∧ π^*η`. -/
theorem logRes_toLogPoles (hlog : f.HasLogPolesDeRhamComplex I) (p : ℕ)
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    Scheme.Hom.logRes hI hlog (c.toLogPoles p x) =
      Scheme.Hom.formRes I.subschemeι (p : ℤ) c.U.1
        (((idealSituation f I).residueHom p).app c.U.1 x) := by
  rw [toLogPoles_apply]
  exact Stacks.Divisors.IdealTrivialization.logRes_logPolesChartForm _ hI hlog le_rfl _ _

end Situation.BaseChart

/-- There is a morphism `Ω^{p+1}_{L^⋆/S,0} ⟶ Ω^{p+1}_{X/S}(log Y)` agreeing with
`Stacks.LineBundle.Situation.BaseChart.toLogPoles` over every base chart. -/
theorem exists_toLogPolesHom (p : ℕ) :
    ∃ φ : (idealSituation f I).weightZero (p + 1) ⟶ Scheme.Hom.logPolesForms f I (p + 1),
      ∀ (c : (idealSituation f I).BaseChart)
        (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)),
        φ.app c.U.1 x = c.toLogPoles p x :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis
    (fun c : (idealSituation f I).BaseChart => c.U.1) (idealSituation f I).isBasis_baseChart
    (fun c => c.toLogPoles p) (fun c c' h x => c.toLogPoles_res c' h p x)
    (fun c r x => c.toLogPoles_smul p r x)

/-- **The middle arrow of the upper left morphism of short exact sequences of Stacks Tag 0FUQ**,
in degree `p + 1`: `Ω^{p+1}_{L^⋆/S,0} ⟶ Ω^{p+1}_{X/S}(log Y)` for `L = 𝒪_X(-Y)`, sending
`π^*α + d log s ∧ π^*η` to `α + d log t ∧ η` over every chart, `t` the local equation of `Y`
corresponding to the generator `s` of `𝒪_X(-Y)`. -/
def toLogPolesHom (p : ℕ) :
    (idealSituation f I).weightZero (p + 1) ⟶ Scheme.Hom.logPolesForms f I (p + 1) :=
  (exists_toLogPolesHom f I p).choose

/-- Over a base chart, `toLogPolesHom` is `Stacks.LineBundle.Situation.BaseChart.toLogPoles`. -/
theorem toLogPolesHom_app (p : ℕ) (c : (idealSituation f I).BaseChart)
    (x : Γ((idealSituation f I).weightZero (p + 1), c.U.1)) :
    (toLogPolesHom f I p).app c.U.1 x = c.toLogPoles p x :=
  (exists_toLogPolesHom f I p).choose_spec c x

/-- **The upper left morphism is the identity on forms with no pole.** -/
theorem pullbackHom_comp_toLogPolesHom (p : ℕ) :
    (idealSituation f I).pullbackHom (p + 1) ≫ toLogPolesHom f I p =
      Scheme.Hom.logPolesFormsInclusion f I (p + 1) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis
    (B := fun c : (idealSituation f I).BaseChart => c.U.1) (idealSituation f I).isBasis_baseChart
    fun c α => (toLogPolesHom_app f I p c _).trans (c.toLogPoles_pullbackHom p α)

/-- **The upper left morphism is compatible with the residues**: `Res(Φ x) = Res(x)|_Y`. -/
theorem toLogPolesHom_comp_logResHom (hlog : f.HasLogPolesDeRhamComplex I) (p : ℕ) :
    toLogPolesHom f I p ≫ Scheme.Hom.logResHom f I hI hlog p =
      (idealSituation f I).residueHom p ≫ Scheme.Hom.formRestriction I.subschemeι f (p : ℤ) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis
    (B := fun c : (idealSituation f I).BaseChart => c.U.1) (idealSituation f I).isBasis_baseChart
    fun c x => (congrArg (Scheme.Hom.logRes hI hlog) (toLogPolesHom_app f I p c x)).trans
      (c.logRes_toLogPoles hlog p x)

/-- **The upper left morphism commutes with the differentials**, read in abelian sheaves. -/
theorem weightZeroDAbHom_comp_toLogPolesHom (hlog : f.HasLogPolesDeRhamComplex I) (p : ℕ) :
    (idealSituation f I).weightZeroDAbHom (p + 1) ≫
        (Stacks.Perfect.AbelianFraction.abelianSheaf X).map (toLogPolesHom f I (p + 1)) =
      (Stacks.Perfect.AbelianFraction.abelianSheaf X).map (toLogPolesHom f I p) ≫
        Scheme.Hom.logDAbHom f I hI hlog (p + 1) :=
  (idealSituation f I).abelianSheaf_hom_ext fun c x => by
    show (toLogPolesHom f I (p + 1)).app c.U.1
        ((idealSituation f I).weightZeroD (p + 1) c.U.1 x) =
      Scheme.Hom.logD hI hlog ((toLogPolesHom f I p).app c.U.1 x)
    rw [toLogPolesHom_app, toLogPolesHom_app]
    exact c.toLogPoles_weightZeroD hlog p x

/-- In degree zero the inclusion `Ω^0_{X/S} ⟶ Ω^0_{L^⋆/S,0}` is an isomorphism. -/
instance isIso_pullbackHom_zero (D : Situation.{u}) : IsIso (D.pullbackHom 0) := by
  have hS := D.shortExact_eval_zero
  have : (Stacks.Perfect.AbelianFraction.abelianSheaf D.X).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf D.X.ringCatSheaf).Faithful
  have hmono : Mono ((Stacks.Perfect.AbelianFraction.abelianSheaf D.X).map (D.pullbackHom 0)) :=
    hS.mono_f
  have hepi : Epi ((Stacks.Perfect.AbelianFraction.abelianSheaf D.X).map (D.pullbackHom 0)) :=
    (hS.exact.epi_f_iff).mpr ((CategoryTheory.Limits.isZero_zero _).eq_of_tgt _ _)
  have : Mono (D.pullbackHom 0) :=
    (Stacks.Perfect.AbelianFraction.abelianSheaf D.X).mono_of_mono_map hmono
  have : Epi (D.pullbackHom 0) :=
    (Stacks.Perfect.AbelianFraction.abelianSheaf D.X).epi_of_epi_map hepi
  exact isIso_of_mono_of_epi _

/-- The middle arrow of the upper left morphism of Stacks Tag 0FUQ in every degree: in degree
`0` the identification `Ω^0_{L^⋆/S,0} = Ω^0_{X/S} = Ω^0_{X/S}(log Y)`, in degree `p + 1` the
morphism `Stacks.LineBundle.toLogPolesHom`. -/
def toLogPolesF : ∀ n : ℕ, (idealSituation f I).weightZero n ⟶ Scheme.Hom.logPolesForms f I n
  | 0 => haveI := isIso_pullbackHom_zero (idealSituation f I)
    inv ((idealSituation f I).pullbackHom 0) ≫ Scheme.Hom.logPolesFormsInclusion f I 0
  | p + 1 => toLogPolesHom f I p

/-- In every degree, `toLogPolesF` is the identity on forms with no pole. -/
theorem pullbackHom_comp_toLogPolesF (n : ℕ) :
    (idealSituation f I).pullbackHom n ≫ toLogPolesF f I n =
      Scheme.Hom.logPolesFormsInclusion f I n := by
  cases n with
  | zero =>
    have := isIso_pullbackHom_zero (idealSituation f I)
    exact IsIso.hom_inv_id_assoc _ _
  | succ p => exact pullbackHom_comp_toLogPolesHom f I p

variable (hlog : f.HasLogPolesDeRhamComplex I)

/-- In every degree, `toLogPolesF` commutes with the differentials, read in abelian sheaves. -/
theorem weightZeroDAbHom_comp_toLogPolesF (n : ℕ) :
    (idealSituation f I).weightZeroDAbHom n ≫
        (Stacks.Perfect.AbelianFraction.abelianSheaf X).map (toLogPolesF f I (n + 1)) =
      (Stacks.Perfect.AbelianFraction.abelianSheaf X).map (toLogPolesF f I n) ≫
        Scheme.Hom.logDAbHom f I hI hlog n := by
  cases n with
  | succ p => exact weightZeroDAbHom_comp_toLogPolesHom f I hlog p
  | zero =>
    have := isIso_pullbackHom_zero (idealSituation f I)
    have : IsIso ((Stacks.Perfect.AbelianFraction.abelianSheaf X).map
        ((idealSituation f I).pullbackHom 0)) := Functor.map_isIso _ _
    rw [← cancel_epi ((Stacks.Perfect.AbelianFraction.abelianSheaf X).map
      ((idealSituation f I).pullbackHom 0))]
    have h1 := (idealSituation f I).inclusionMap.comm 0 1
    rw [(idealSituation f I).weightZeroComplex_d, Scheme.Hom.deRhamAbComplex_d] at h1
    have h2 := (Scheme.Hom.logInclusionMap f I hI hlog).comm 0 1
    rw [Scheme.Hom.logDeRhamComplex_d, Scheme.Hom.deRhamAbComplex_d] at h2
    have h3 := congrArg (· ≫ (Stacks.Perfect.AbelianFraction.abelianSheaf X).map
      (toLogPolesF f I 1)) h1
    have e : ∀ m, (Stacks.Perfect.AbelianFraction.abelianSheaf X).map
          ((idealSituation f I).pullbackHom m) ≫
        (Stacks.Perfect.AbelianFraction.abelianSheaf X).map (toLogPolesF f I m) =
        (Scheme.Hom.logInclusionMap f I hI hlog).f m := fun m =>
      (Functor.map_comp _ _ _).symm.trans
        (congrArg (Stacks.Perfect.AbelianFraction.abelianSheaf X).map
          (pullbackHom_comp_toLogPolesF f I m))
    refine (Category.assoc _ _ _).symm.trans (h3.trans ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Scheme.Hom.deRhamDifferentialAbHom f 0 ≫ ·) (e 1)).trans ?_
    refine h2.symm.trans ?_
    refine (congrArg (· ≫ Scheme.Hom.logDAbHom f I hI hlog 0) (e 0).symm).trans ?_
    exact Category.assoc _ _ _

/-- **The middle arrow of the upper left morphism of short exact sequences of Stacks Tag 0FUQ**,
as a map of complexes of sheaves of `f^{-1}𝒪_S`-modules
`Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}(log Y)`, `L = 𝒪_X(-Y)`: the rule
`ω' + d log s ∧ ω ↦ ω' + d log t ∧ ω` of the source. -/
def residueToLogPolesMap :
    (idealSituation f I).weightZeroBaseComplex ⟶ Scheme.Hom.deRhamComplexLogPoles f I hI hlog where
  f n := (Scheme.Hom.toBaseModules f).map (toLogPolesF f I n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [(idealSituation f I).weightZeroBaseComplex_d, Scheme.Hom.deRhamComplexLogPoles_d]
    have h := weightZeroDAbHom_comp_toLogPolesF f I hlog i
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact congrArg (fun φ : (Stacks.Perfect.AbelianFraction.abelianSheaf X).obj
        ((idealSituation f I).weightZero i) ⟶ (Stacks.Perfect.AbelianFraction.abelianSheaf X).obj
          (Scheme.Hom.logPolesForms f I (i + 1)) => φ.hom.app W x) h.symm

/-- The middle arrow restricts to the identity on `Ω^•_{X/S}`: composed with the inclusion
`Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` it is the inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)`. -/
theorem inclusionBaseMap_comp_residueToLogPolesMap :
    (idealSituation f I).inclusionBaseMap ≫ residueToLogPolesMap f I hlog =
      Scheme.Hom.deRhamComplexLogPolesInclusion f I hI hlog := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact ((Scheme.Hom.toBaseModules f).map_comp _ _).symm.trans
    (congrArg (Scheme.Hom.toBaseModules f).map (pullbackHom_comp_toLogPolesF f I n))

/-- The middle arrow is compatible with the residues: the log residue of its image is the
restriction to `Y` of the residue. -/
theorem residueToLogPolesMap_comp_logResidueBaseMap :
    residueToLogPolesMap f I hlog ≫ Scheme.Hom.logResidueBaseMap f hI hlog =
      (idealSituation f I).residueBaseMap ≫
        CochainComplex.desuspendMap (Scheme.Hom.divisorRestrictionBase f I) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact (CategoryTheory.Limits.isZero_zero _).eq_of_tgt _ _
  | succ p =>
    exact ((Scheme.Hom.toBaseModules f).map_comp _ _).symm.trans
      ((congrArg (Scheme.Hom.toBaseModules f).map (toLogPolesHom_comp_logResHom f I hlog p)).trans
        ((Scheme.Hom.toBaseModules f).map_comp _ _))

/-- **The upper left morphism of short exact sequences of Stacks Tag 0FUQ**, from the shifted
residue sequence of Tag 0FUF for `L = 𝒪_X(-Y)`,
`0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0`, to the shifted log poles sequence of
Tag 0FMW, `0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`, over the identity of
`Ω^•_{X/S}` and the restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`. Its middle arrow is
`ω' + d log s ∧ ω ↦ ω' + d log t ∧ ω`. -/
def residueLogPolesMorphism :
    Stacks.ShiftedBoundary.Morphism (idealSituation f I).residueShiftedSequence
      (Scheme.Hom.logPolesShiftedSequence f hI hlog) (𝟙 _)
      (Scheme.Hom.divisorRestrictionInt f I) :=
  Stacks.ShiftedBoundary.Morphism.ofShortExact (𝟙 _)
    (HomologicalComplex.extendMap (residueToLogPolesMap f I hlog) ComplexShape.embeddingUpNat)
    (Scheme.Hom.divisorRestrictionInt f I)
    (by
      refine ((HomologicalComplex.extendMap_comp _ _ _).symm.trans ?_).trans
        (Category.id_comp _).symm
      exact congrArg (HomologicalComplex.extendMap · ComplexShape.embeddingUpNat)
        (inclusionBaseMap_comp_residueToLogPolesMap f I hlog))
    (by
      change HomologicalComplex.extendMap (residueToLogPolesMap f I hlog) _ ≫
          HomologicalComplex.extendMap (Scheme.Hom.logResidueBaseMap f hI hlog) _ ≫
            (CochainComplex.desuspendExtendIso (Scheme.Hom.divisorDeRhamBase f I)).hom =
        (HomologicalComplex.extendMap (idealSituation f I).residueBaseMap _ ≫
          (CochainComplex.desuspendExtendIso (Scheme.Hom.deRhamComplex f)).hom) ≫
            (HomologicalComplex.extendMap (Scheme.Hom.divisorRestrictionBase f I) _)⟦(-1 : ℤ)⟧'
      rw [Category.assoc, ← CochainComplex.desuspendExtendIso_naturality, ← Category.assoc,
        ← Category.assoc, ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
        residueToLogPolesMap_comp_logResidueBaseMap])

/-- **Stacks Project, Tag 0FUQ, upper left triangle, at the level of boundary maps**: the boundary
map `Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of the shifted residue sequence of Tag 0FUF for `𝒪_X(-Y)` is the
boundary map `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` of the shifted log poles sequence of Tag 0FMW composed
with the restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`. This is the functoriality of boundary
maps along `Stacks.LineBundle.residueLogPolesMorphism`, the morphism of short exact sequences of
the proof. -/
theorem residueShiftedSequence_boundary_eq
    [HasDerivedCategory.{w} (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf f))] :
    (idealSituation f I).residueShiftedSequence.boundary =
      DerivedCategory.Q.map (Scheme.Hom.divisorRestrictionInt f I) ≫
        (Scheme.Hom.logPolesShiftedSequence f hI hlog).boundary :=
  Stacks.ShiftedBoundary.Morphism.boundary_eq_comp_boundary (residueLogPolesMorphism f I hlog)

end Ideal

end Stacks.LineBundle
