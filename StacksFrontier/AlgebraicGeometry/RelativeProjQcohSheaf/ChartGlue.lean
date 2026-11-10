module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# The morphism `W ⟶ U_d` defined by a point of `F_d(W)`

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `d ≥ 1` and `X` a
relative homogeneous spectrum of `𝒜` ([Stacks, Tag 01NQ]) with structure morphism `f : X ⟶ S` and
relative degree-`d` open `U_d`. This file builds, for every test scheme `W` and every point
`ξ ∈ F_d(W)` of the functor of Section 01NS, the morphism `W ⟶ U_d` that `ξ` defines, and
proves it natural in `W`. It is the forward map of the bijection `F_d(W) ≃ Mor(W, U_d)` in the
proof of [Stacks, Tag 01NY].

## Implementation notes

Over the member `g⁻¹(U)` of the covering of `W` by the preimages of the affine opens of `S`, the
restriction of `ξ` comes from a chart-wise class
(`...RelativeProjQcohSheaf.Fd.exists_chartClassInv_eq`), whose chart-wise morphisms agree on
overlaps (`...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq`); they glue by
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover`.  Each lands in `U_d`
(`Fd.chartHom_range_le`), so the glued morphism factors through `U_d ⟶ X` by
`AlgebraicGeometry.IsOpenImmersion.lift`.

## Main results

* `...RelativeProjQcohSheaf.Fd.existsUnique_hom_of_chartHom`: the chart-wise morphisms of a
  point of `F_d(W)` glue to a unique morphism `W ⟶ X`.
* `...RelativeProjQcohSheaf.Fd.chartHom_range_le`: a chart-wise morphism lands in `U_d`.
* `...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen`: the forward map, as a unique
  morphism `W ⟶ U_d` restricting to the chart-wise morphisms.
* `...RelativeProjQcohSheaf.Fd.hom_degreeOpen_pullback`: the forward map is natural in the test
  scheme.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (P : RelativeProjData A) {k : ℕ}

/-- The preimages of the affine opens of the base cover a test scheme. -/
theorem exists_mem_preimage_affineOpen {W : Scheme.{u}} (g : W ⟶ S) (x : W) :
    ∃ a : {U : S.Opens // IsAffineOpen U}, x ∈ g ⁻¹ᵁ a.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base x)) isOpen_univ
  exact ⟨⟨U, hU⟩, hx⟩

/-- The restriction of a point of `F_d(W)` to each `g⁻¹(U)` comes from a chart-wise class. -/
private theorem exists_chartClassInv_eq_pullback {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    ∃ η : ∀ U : S.Opens, Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme,
      ∀ U, Fd.chartClassInv A U (η U) = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ := by
  classical
  choose η hη using fun U : S.Opens =>
    Fd.exists_chartClassInv_eq A U (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) (ξ.1 ∣_ U)
      (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U)
  exact ⟨η, hη⟩

/-- The chart-wise morphisms of a point of `F_d(W)` glue to a morphism `W ⟶ X`. -/
theorem Fd.existsUnique_hom_of_chartHom (hk : 0 < k) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    ∃! φ : W ⟶ P.scheme, ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ →
      (ξ.1 ⁻¹ᵁ U).ι ≫ φ = Fd.chartHom A U P hU hk _ η := by
  classical
  obtain ⟨η, hη⟩ := exists_chartClassInv_eq_pullback A ξ
  have key : ∀ (U V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (Y : W.Opens)
      (jU : Y.toScheme ⟶ (ξ.1 ⁻¹ᵁ U).toScheme) (jV : Y.toScheme ⟶ (ξ.1 ⁻¹ᵁ V).toScheme),
      jU ≫ (ξ.1 ⁻¹ᵁ U).ι = Y.ι → jV ≫ (ξ.1 ⁻¹ᵁ V).ι = Y.ι →
      jU ≫ Fd.chartHom A U P hU hk _ (η U) = jV ≫ Fd.chartHom A V P hV hk _ (η V) := by
    intro U V hU hV Y jU jV hjU hjV
    rw [← Fd.chartHom_pullback A U P hU hk jU, ← Fd.chartHom_pullback A V P hV hk jV]
    refine Fd.chartHom_eq_of_chartClassInv_eq A U P hU hV hk _ _ ?_
    rw [Fd.chartClassInv_pullback, Fd.chartClassInv_pullback, hη U, hη V,
      ← Fd.pullback_comp, ← Fd.pullback_comp, hjU, hjV]
  obtain ⟨φ, hφ, huniq⟩ := Scheme.existsUnique_hom_of_opens_cover
    (fun a : {U : S.Opens // IsAffineOpen U} => ξ.1 ⁻¹ᵁ a.1)
    (fun x => exists_mem_preimage_affineOpen ξ.1 x)
    (fun a => Fd.chartHom A a.1 P a.2 hk _ (η a.1))
    (fun a b => key a.1 b.1 a.2 b.2 _ _ _ (W.homOfLE_ι _) (W.homOfLE_ι _))
  refine ⟨φ, ?_, ?_⟩
  · intro U hU ηU hηU
    refine (hφ ⟨U, hU⟩).trans ?_
    refine Fd.chartHom_eq_of_chartClassInv_eq A U P hU hU hk _ _ ?_
    rw [hη U, hηU]
  · intro φ' hφ'
    exact huniq φ' fun a => hφ' a.1 a.2 (η a.1) (hη a.1)

/-! ### The glued morphism lands in the relative degree-`d` open -/

/-- A chart-wise morphism lands in the relative degree-`d` open `U_d`. -/
theorem Fd.chartHom_range_le (U : S.Opens) (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u})
    (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Set.range (Fd.chartHom A U P hU hk T η).base ⊆ (P.degreeOpen k : Set P.scheme) := by
  have h1 : Set.range (Fd.chartHom A U P hU hk T η).base
      ⊆ Set.range ((P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι).base := by
    change Set.range ((Fd.chartRelativeEquiv A U P hU hk T η
      ≫ (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι)).base ⊆ _
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  rw [Scheme.Opens.range_ι] at h1
  exact h1.trans fun _ hy => hy.2

/-- Every point `ξ ∈ F_d(W)` defines one and only one morphism `W ⟶ U_d` whose restriction to
each member `g⁻¹(U)` of the covering of `W` by the preimages of the affine opens of the base is
the chart-wise morphism of the chart-wise class of `ξ` there. -/
theorem Fd.existsUnique_hom_degreeOpen (hk : 0 < k) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    ∃! φ : W ⟶ (P.degreeOpen k).toScheme, ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ →
      (ξ.1 ⁻¹ᵁ U).ι ≫ φ ≫ (P.degreeOpen k).ι = Fd.chartHom A U P hU hk _ η := by
  classical
  obtain ⟨φ, hφ, huniq⟩ := Fd.existsUnique_hom_of_chartHom A P hk W ξ
  obtain ⟨η, hη⟩ := exists_chartClassInv_eq_pullback A ξ
  have hrange : Set.range φ.base ⊆ Set.range ((P.degreeOpen k).ι).base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := exists_mem_preimage_affineOpen ξ.1 y
    refine Fd.chartHom_range_le A P a.1 a.2 hk _ (η a.1)
      ⟨(⟨y, ha⟩ : (ξ.1 ⁻¹ᵁ a.1).toScheme), ?_⟩
    rw [← hφ a.1 a.2 (η a.1) (hη a.1)]
    rfl
  refine ⟨IsOpenImmersion.lift (P.degreeOpen k).ι φ hrange, ?_, ?_⟩
  · intro U hU ηU hηU
    rw [IsOpenImmersion.lift_fac]
    exact hφ U hU ηU hηU
  · intro φ' hφ'
    have hfac : φ' ≫ (P.degreeOpen k).ι = φ :=
      huniq _ fun U hU ηU hηU => (Category.assoc _ _ _).symm.trans (hφ' U hU ηU hηU)
    have : φ' ≫ (P.degreeOpen k).ι
        = IsOpenImmersion.lift (P.degreeOpen k).ι φ hrange ≫ (P.degreeOpen k).ι :=
      hfac.trans (IsOpenImmersion.lift_fac (P.degreeOpen k).ι φ hrange).symm
    exact (cancel_mono (P.degreeOpen k).ι).mp this

/-! ### The forward map is natural in the test scheme -/

/-- The glued morphism is natural in the test scheme: precomposing the morphism of a class
`ξ ∈ F_d(W)` with `h : W' ⟶ W` gives the morphism of the pullback class `h^*ξ ∈ F_d(W')`. -/
theorem Fd.hom_degreeOpen_pullback (hk : 0 < k) {W W' : Scheme.{u}} (h : W' ⟶ W)
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) (φ : W ⟶ (P.degreeOpen k).toScheme)
    (hφ : ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ →
      (ξ.1 ⁻¹ᵁ U).ι ≫ φ ≫ (P.degreeOpen k).ι = Fd.chartHom A U P hU hk _ η)
    (φ' : W' ⟶ (P.degreeOpen k).toScheme)
    (hφ' : ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ)
        ((Fd.pullback h ξ).1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι (Fd.pullback h ξ) →
      ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι ≫ φ' ≫ (P.degreeOpen k).ι
        = Fd.chartHom A U P hU hk _ η) :
    φ' = h ≫ φ := by
  classical
  obtain ⟨ψ, -, huniq⟩ := Fd.existsUnique_hom_degreeOpen A P hk W' (Fd.pullback h ξ)
  obtain ⟨η, hη⟩ := exists_chartClassInv_eq_pullback A ξ
  refine (huniq φ' hφ').trans (huniq (h ≫ φ) ?_).symm
  intro U hU ηU hηU
  have hj : (h ∣_ (ξ.1 ⁻¹ᵁ U)) ≫ (ξ.1 ⁻¹ᵁ U).ι
      = ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι ≫ h := morphismRestrict_ι h (ξ.1 ⁻¹ᵁ U)
  have step : ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι ≫ (h ≫ φ) ≫ (P.degreeOpen k).ι
      = (h ∣_ (ξ.1 ⁻¹ᵁ U)) ≫ (ξ.1 ⁻¹ᵁ U).ι ≫ φ ≫ (P.degreeOpen k).ι :=
    (congrArg (fun z => ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι ≫ z)
          (Category.assoc h φ (P.degreeOpen k).ι)).trans
      ((Category.assoc ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι h (φ ≫ (P.degreeOpen k).ι)).symm.trans
        ((congrArg (fun z => z ≫ φ ≫ (P.degreeOpen k).ι) hj.symm).trans
          (Category.assoc _ _ _)))
  refine step.trans ?_
  rw [hφ U hU (η U) (hη U),
    ← Fd.chartHom_pullback A U P hU hk (h ∣_ (ξ.1 ⁻¹ᵁ U)) (η U)]
  refine Fd.chartHom_eq_of_chartClassInv_eq A U P hU hU hk _ _ ?_
  rw [Fd.chartClassInv_pullback, hη U, ← Fd.pullback_comp, hj]
  exact (Fd.pullback_comp h ((Fd.pullback h ξ).1 ⁻¹ᵁ U).ι ξ).trans hηU.symm

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
