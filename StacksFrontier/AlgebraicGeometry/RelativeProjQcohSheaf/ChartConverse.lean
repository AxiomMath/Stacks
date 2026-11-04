module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenCharts
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiSeparated

/-!
# The converse of the chart agreement

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `d ≥ 1` and `X`
a relative homogeneous spectrum of `𝒜` ([Stacks, Tag 01NQ]).
`...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement` says that two chart-wise
classes with the same image under `...RelativeProjQcohSheaf.Fd.chartClassInv` have the same
morphism into `X`. This file proves the converse: two chart-wise classes with the same
morphism into `X` — and, for two different opens of the base, recording the same morphism to
the base — have the same image under `Fd.chartClassInv`.

## Implementation notes

At one open, `...Fd.chartHom` is the `Equiv` `...RelativeProjQcohSheaf.Fd.chartRelativeEquiv`
followed by the inclusion of `U_d ⊓ f⁻¹(U)`, so it is injective, and `Fd.chartClassInv` is
injective by `...Fd.chartClass_chartClassInv`.  Two arbitrary affine opens are handled by
refining the overlap by affine opens `Z ≤ U ⊓ V` and concluding with
`...ZariskiSeparated.Fd.eq_of_pullback_eq_of_cover`.

The hypothesis that the two classes record the same morphism to `S` is implied by the
conclusion.  `Fd.chartHom_comp_toBase_of_chartBaseHom` reduces it to the single equation

`Fd.chartBaseHom A U hU hk ≫ U.ι = (Proj.degreeOpen (𝒜(U)) k).ι ≫ P.chart U hU ≫ P.toBase`,

which is proved as `...RelativeProjQcohSheaf.Fd.chartBaseHom_comp_ι`.

## Main results

* `...RelativeProjQcohSheaf.Fd.chartHom_injective`: the chart-wise morphism of one affine open
  of the base is injective.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_injective`: the inverse of the chart-wise class is
  injective.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq_of_le`: the converse for a nested
  pair of affine opens.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq`: the converse for two arbitrary
  affine opens of the base.
* `...RelativeProjQcohSheaf.Fd.chartHom_comp_toBase_of_chartBaseHom`: the base clause reduced to
  one equation about the chart.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### Injectivity at one open -/

/-- The chart-wise morphism of one affine open of the base is injective. -/
theorem Fd.chartHom_injective (U : S.Opens) (P : RelativeProjData A) (hU : IsAffineOpen U)
    {k : ℕ} (hk : 0 < k) (T : Scheme.{u}) :
    Function.Injective (Fd.chartHom A U P hU hk T) := by
  have hmono : Mono (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι :=
    AlgebraicGeometry.IsOpenImmersion.mono _
  intro ξ η h
  exact (Fd.chartRelativeEquiv A U P hU hk T).injective
    ((cancel_mono (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι).mp h)

/-- The inverse `...RelativeProjQcohSheaf.Fd.chartClassInv` of the chart-wise class is
injective. -/
theorem Fd.chartClassInv_injective (V : S.Opens) {k : ℤ} {T : Scheme.{u}} :
    Function.Injective (Fd.chartClassInv A V (k := k) (T := T)) := by
  intro η η' h
  obtain ⟨g, q⟩ := η
  obtain ⟨g', q'⟩ := η'
  have hfst : g = g' := (cancel_mono V.ι).mp (congrArg Sigma.fst h)
  subst hfst
  refine (Fd.chartClass_chartClassInv A V
    (⟨g, q⟩ : Fd (situationAlgebra (A.restrict V.ι)) k T)).symm.trans ?_
  refine Eq.trans (congrArg (Fd.chartClass A V g) (eq_of_heq (Fd.heq_snd h))) ?_
  exact Fd.chartClass_chartClassInv A V (⟨g, q'⟩ : Fd (situationAlgebra (A.restrict V.ι)) k T)

/-! ### The base clause, reduced to one equation about the chart -/

/-- If the morphism `...RelativeProjQcohSheaf.Fd.chartBaseHom` from the degree-`d` open of
`Proj 𝒜(U)` down to `U` agrees with the chart's own structure morphism into `X` followed by
`f : X ⟶ S`, then every chart-wise morphism lies over its class's recorded morphism to the
base. -/
theorem Fd.chartHom_comp_toBase_of_chartBaseHom (U : S.Opens) (P : RelativeProjData A)
    (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k)
    (hcb : Fd.chartBaseHom A U hU hk ≫ U.ι
      = (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).ι ≫ P.chart U hU ≫ P.toBase)
    (T : Scheme.{u}) (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU hk T ξ ≫ P.toBase = ξ.1 ≫ U.ι := by
  have hξ : ξ.1 = Fd.chartEquiv A U hU hk T ξ ≫ Fd.chartBaseHom A U hU hk := by
    refine Eq.trans (congrArg (fun z : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T => z.1)
      ((Fd.chartEquiv A U hU hk T).symm_apply_apply ξ).symm) ?_
    exact Fd.chartEquiv_symm_fst A U hU hk (Fd.chartEquiv A U hU hk T ξ)
  rw [hξ, Category.assoc, hcb, Fd.chartHom_eq_comp A U P hU hk T, Category.assoc]
  exact congrArg (fun z => Fd.chartEquiv A U hU hk T ξ ≫ z) (Category.assoc _ _ _)

/-! ### The converse for a nested pair -/

/-- For affine opens `Z ≤ U` of the base, a chart-wise class `η` over `U` and a morphism `g` to `Z`
lying over the same morphism to `S`, there is a chart-wise class over `Z` with the same image
under `...Fd.chartClassInv` and the same morphism into a relative homogeneous spectrum. -/
private theorem Fd.exists_chartClassInv_eq_chartHom_eq {Z : S.Opens} (U : S.Opens)
    (P : RelativeProjData A) (hZU : Z ≤ U) (hZ : IsAffineOpen Z) (hU : IsAffineOpen U)
    {k : ℕ} (hk : 0 < k) {T : Scheme.{u}} (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (g : T ⟶ Z.toScheme) (hg : g ≫ Z.ι = η.1 ≫ U.ι) :
    ∃ ηZ : Fd (situationAlgebra (A.restrict Z.ι)) (k : ℤ) T,
      Fd.chartClassInv A Z ηZ = Fd.chartClassInv A U η ∧
        Fd.chartHom A Z P hZ hk T ηZ = Fd.chartHom A U P hU hk T η := by
  obtain ⟨ηZ, hηZ⟩ := Fd.exists_chartClassInv_eq A Z (Fd.chartClassInv A U η) g
    (hg.trans (Fd.chartClassInv_fst A U η).symm)
  exact ⟨ηZ, hηZ, Fd.chartHom_eq_of_le A U P hZU hZ hU hk ηZ η hηZ⟩

/-- Let `Z ≤ U` be affine opens of the base and let `η_Z`, `η_U` be chart-wise classes over `Z`
and `U` on one test scheme whose morphisms into a relative homogeneous spectrum agree and which
record the same morphism to `S`. Then they have the same image under `...Fd.chartClassInv`. -/
theorem Fd.chartClassInv_eq_of_chartHom_eq_of_le {Z : S.Opens} (U : S.Opens)
    (P : RelativeProjData A) (hZU : Z ≤ U) (hZ : IsAffineOpen Z) (hU : IsAffineOpen U)
    {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (ηZ : Fd (situationAlgebra (A.restrict Z.ι)) (k : ℤ) T)
    (ηU : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (hbase : ηZ.1 ≫ Z.ι = ηU.1 ≫ U.ι)
    (h : Fd.chartHom A Z P hZ hk T ηZ = Fd.chartHom A U P hU hk T ηU) :
    Fd.chartClassInv A Z ηZ = Fd.chartClassInv A U ηU := by
  obtain ⟨ηZ', hηZ', hhZ'⟩ :=
    Fd.exists_chartClassInv_eq_chartHom_eq A U P hZU hZ hU hk ηU ηZ.1 hbase
  have : ηZ = ηZ' := Fd.chartHom_injective A Z P hZ hk T (h.trans hhZ'.symm)
  rw [this, hηZ']

/-! ### The converse for two arbitrary affine opens -/

/-- Let `U`, `V` be affine opens of `S`, `T` a test scheme, and let `η_U ∈ F_d(T)` for `𝒜|_U`
and `η_V ∈ F_d(T)` for `𝒜|_V` record the same morphism `T ⟶ S` and define the same morphism into
a relative homogeneous spectrum of `𝒜`. Then they are the chart-wise classes of one point of
`F_d(T)` for `𝒜`. -/
theorem Fd.chartClassInv_eq_of_chartHom_eq (U V : S.Opens) (P : RelativeProjData A)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (ηU : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (ηV : Fd (situationAlgebra (A.restrict V.ι)) (k : ℤ) T)
    (hbase : ηU.1 ≫ U.ι = ηV.1 ≫ V.ι)
    (h : Fd.chartHom A U P hU hk T ηU = Fd.chartHom A V P hV hk T ηV) :
    Fd.chartClassInv A U ηU = Fd.chartClassInv A V ηV := by
  classical
  refine Fd.eq_of_pullback_eq_of_cover
    (fun a : {Z : S.Opens // IsAffineOpen Z ∧ Z ≤ U ⊓ V} => (ηU.1 ≫ U.ι) ⁻¹ᵁ a.1)
    (fun x => ?_) _ _ (fun a => ?_)
  · have hmem : (ηU.1 ≫ U.ι).base x ∈ (U ⊓ V : S.Opens) := by
      refine ⟨?_, ?_⟩
      · rw [← Scheme.Opens.range_ι U]
        exact ⟨ηU.1.base x, by simp⟩
      · rw [show (ηU.1 ≫ U.ι).base x = (ηV.1 ≫ V.ι).base x from congrArg (fun z : T ⟶ S =>
          z.base x) hbase, ← Scheme.Opens.range_ι V]
        exact ⟨ηV.1.base x, by simp⟩
    obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZUV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hmem (U ⊓ V : S.Opens).isOpen
    exact ⟨⟨Z, hZ, hZUV⟩, hxZ⟩
  · obtain ⟨Z, hZ, hZUV⟩ := a
    have hZU : Z ≤ U := fun y hy => (hZUV hy).1
    have hZV : Z ≤ V := fun y hy => (hZUV hy).2
    set j := ((ηU.1 ≫ U.ι) ⁻¹ᵁ Z).ι with hj
    -- the two restricted chart-wise classes, read at `Z`
    obtain ⟨ηZ, hcU, hhU⟩ := Fd.exists_chartClassInv_eq_chartHom_eq A U P hZU hZ hU hk
      (Fd.pullback j ηU) ((ηU.1 ≫ U.ι) ∣_ Z) (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ Z)
    obtain ⟨ηZ', hcV, hhV⟩ := Fd.exists_chartClassInv_eq_chartHom_eq A V P hZV hZ hV hk
      (Fd.pullback j ηV) ((ηU.1 ≫ U.ι) ∣_ Z)
      (by rw [Fd.pullback_fst, Category.assoc, ← hbase]; exact morphismRestrict_ι _ Z)
    -- their chart-wise morphisms agree, so by one-open injectivity they are equal
    have hstep : ηZ = ηZ' := Fd.chartHom_injective A Z P hZ hk _ <| by
      rw [hhU, hhV, Fd.chartHom_pullback A U P hU hk j ηU, Fd.chartHom_pullback A V P hV hk j ηV, h]
    rw [← Fd.chartClassInv_pullback, ← Fd.chartClassInv_pullback, ← hcU, ← hcV, hstep]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
