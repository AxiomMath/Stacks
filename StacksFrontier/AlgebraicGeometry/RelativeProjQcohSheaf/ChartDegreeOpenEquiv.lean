module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartBaseClause
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassScale
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartScale

/-!
# The bijection `F_d(W) ≃ Mor(W, U_d)` over a general base

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `d ≥ 1` and `X`
a relative homogeneous spectrum of `𝒜` ([Stacks, Tag 01NQ]) with relative degree-`d` open `U_d`.
This file proves that `U_d` represents `F_d`: for every test scheme `W` the glued morphism of
`...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen` is a bijection
`F_d(W) ≃ Mor(W, U_d)`, natural in `W` and compatible with the transitions `F_d → F_{a d}`.
This is the step of the proof of [Stacks, Tag 01NY] that descends [Stacks, Tag 01NU] along the
charts.

## Main results

* `...RelativeProjQcohSheaf.Fd.homDegreeOpen`: the forward map, as a function.
* `...RelativeProjQcohSheaf.Fd.degreeOpenEquiv`: the bijection `F_d(W) ≃ Mor(W, U_d)`.
* `...RelativeProjQcohSheaf.Fd.degreeOpenEquiv_pullback` and
  `...Fd.degreeOpenEquiv_scale`: its naturality and its compatibility with the transitions.
* `...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofCharts`: the representability data
  `...RelativeProjQcohSheaf.ProjDegreeRepresentation` over an arbitrary base.

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

/-! ### The forward map as a function -/

/-- The morphism `W ⟶ U_d` a point of `F_d(W)` defines, chosen from
`...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen`. -/
def Fd.homDegreeOpen (hk : 0 < k) {W : Scheme.{u}} (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    W ⟶ (P.degreeOpen k).toScheme :=
  (Fd.existsUnique_hom_degreeOpen A P hk W ξ).choose

/-- The defining property of `Fd.homDegreeOpen`: over the preimage of an affine open of the base
it is the chart-wise morphism. -/
theorem Fd.ι_homDegreeOpen (hk : 0 < k) {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) (U : S.Opens) (hU : IsAffineOpen U)
    (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme)
    (hη : Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) :
    (ξ.1 ⁻¹ᵁ U).ι ≫ Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι
      = Fd.chartHom A U P hU hk _ η :=
  (Fd.existsUnique_hom_degreeOpen A P hk W ξ).choose_spec.1 U hU η hη

/-- `Fd.homDegreeOpen` is the only morphism with that property. -/
theorem Fd.eq_homDegreeOpen (hk : 0 < k) {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) (φ : W ⟶ (P.degreeOpen k).toScheme)
    (hφ : ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ →
      (ξ.1 ⁻¹ᵁ U).ι ≫ φ ≫ (P.degreeOpen k).ι = Fd.chartHom A U P hU hk _ η) :
    φ = Fd.homDegreeOpen A P hk ξ :=
  (Fd.existsUnique_hom_degreeOpen A P hk W ξ).choose_spec.2 φ hφ

/-! ### Auxiliary gluing lemmas -/

/-- The two restrictions of a morphism out of `W` to `U ⊓ V` agree. -/
private theorem homOfLE_inf_ι_comp {W T : Scheme.{u}} (U V : W.Opens) (f : W ⟶ T) :
    (W.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ U.ι) ≫ f
      = (W.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ V.ι) ≫ f := by
  rw [W.homOfLE_ι, W.homOfLE_ι]

/-- Two morphisms out of `W` agreeing on the preimages of all affine opens of `S` are equal. -/
private theorem eq_of_ι_comp_eq_of_affine_cover {W T : Scheme.{u}} (g : W ⟶ S) (f f' : W ⟶ T)
    (h : ∀ U : S.Opens, IsAffineOpen U → (g ⁻¹ᵁ U).ι ≫ f = (g ⁻¹ᵁ U).ι ≫ f') : f = f' := by
  obtain ⟨_, -, huniq⟩ := Scheme.existsUnique_hom_of_opens_cover
    (fun a : {U : S.Opens // IsAffineOpen U} => g ⁻¹ᵁ a.1)
    (fun x => exists_mem_preimage_affineOpen g x)
    (fun a => (g ⁻¹ᵁ a.1).ι ≫ f') (fun a b => homOfLE_inf_ι_comp _ _ f')
  exact (huniq _ fun a => h a.1 a.2).trans (huniq _ fun _ => rfl).symm

/-- The pullback of a class of `F_d(W)` to each `ξ⁻¹ U` comes from a chart-wise class. -/
private theorem exists_chartClassInv_pullback {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    ∃ η : ∀ U : S.Opens, Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme,
      ∀ U, Fd.chartClassInv A U (η U) = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ := by
  choose η hη using fun U : S.Opens =>
    Fd.exists_chartClassInv_eq A U (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) (ξ.1 ∣_ U)
      (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U)
  exact ⟨η, hη⟩

/-! ### The forward map lies over the class's own morphism to the base -/

/-- The morphism a class defines lies over the morphism to `S` the class records. -/
theorem Fd.homDegreeOpen_comp_toBase (hk : 0 < k) {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι ≫ P.toBase = ξ.1 := by
  obtain ⟨η, hη⟩ := exists_chartClassInv_pullback A ξ
  refine eq_of_ι_comp_eq_of_affine_cover ξ.1 _ _ fun U hU => ?_
  rw [reassoc_of% Fd.ι_homDegreeOpen A P hk ξ U hU (η U) (hη U),
    Fd.chartHom_comp_toBase A U P hU hk _ (η U)]
  exact congrArg (fun z : Fd (situationAlgebra A) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme => z.1) (hη U)

/-! ### The forward map is injective -/

/-- The morphism a class defines determines the class. -/
theorem Fd.homDegreeOpen_injective (hk : 0 < k) (W : Scheme.{u}) :
    Function.Injective (Fd.homDegreeOpen A P hk (W := W)) := by
  classical
  rintro ⟨g, q⟩ ⟨g', q'⟩ h
  have hbase : g = g' :=
    (Fd.homDegreeOpen_comp_toBase A P hk (⟨g, q⟩ : Fd (situationAlgebra A) (k : ℤ) W)).symm.trans
      ((congrArg (fun z : W ⟶ (P.degreeOpen k).toScheme =>
          z ≫ (P.degreeOpen k).ι ≫ P.toBase) h).trans
        (Fd.homDegreeOpen_comp_toBase A P hk (⟨g', q'⟩ : Fd (situationAlgebra A) (k : ℤ) W)))
  subst hbase
  obtain ⟨η, hη⟩ := exists_chartClassInv_pullback A (⟨g, q⟩ : Fd (situationAlgebra A) (k : ℤ) W)
  obtain ⟨η', hη'⟩ := exists_chartClassInv_pullback A (⟨g, q'⟩ : Fd (situationAlgebra A) (k : ℤ) W)
  refine Fd.eq_of_pullback_eq_of_cover
    (fun a : {U : S.Opens // IsAffineOpen U} => g ⁻¹ᵁ a.1)
    (fun x => exists_mem_preimage_affineOpen g x) _ _ (fun a => ?_)
  obtain ⟨U, hU⟩ := a
  have key : Fd.chartHom A U P hU hk _ (η U) = Fd.chartHom A U P hU hk _ (η' U) := by
    rw [← Fd.ι_homDegreeOpen A P hk (⟨g, q⟩ : Fd (situationAlgebra A) (k : ℤ) W) U hU
        (η U) (hη U), h,
      Fd.ι_homDegreeOpen A P hk (⟨g, q'⟩ : Fd (situationAlgebra A) (k : ℤ) W) U hU
        (η' U) (hη' U)]
  exact (hη U).symm.trans
    ((congrArg (Fd.chartClassInv A U) (Fd.chartHom_injective A U P hU hk _ key)).trans (hη' U))

/-! ### The forward map is surjective -/

/-- Every morphism `W ⟶ U_d` is the morphism of a class of `F_d(W)`. -/
theorem Fd.homDegreeOpen_surjective (hk : 0 < k) (W : Scheme.{u}) :
    Function.Surjective (Fd.homDegreeOpen A P hk (W := W)) := by
  classical
  intro φ
  set g : W ⟶ S := φ ≫ (P.degreeOpen k).ι ≫ P.toBase with hgdef
  have hrange : ∀ U : S.Opens,
      Set.range (((g ⁻¹ᵁ U).ι ≫ φ ≫ (P.degreeOpen k).ι)).base
        ⊆ Set.range ((P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι).base := by
    intro U
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    exact ⟨y.2, (φ.base ((g ⁻¹ᵁ U).ι.base y)).2⟩
  have hex : ∀ a : {U : S.Opens // IsAffineOpen U},
      ∃ ηa : Fd (situationAlgebra (A.restrict a.1.ι)) (k : ℤ) (g ⁻¹ᵁ a.1).toScheme,
        Fd.chartHom A a.1 P a.2 hk _ ηa = (g ⁻¹ᵁ a.1).ι ≫ φ ≫ (P.degreeOpen k).ι := by
    intro a
    refine ⟨(Fd.chartRelativeEquiv A a.1 P a.2 hk _).symm
      (IsOpenImmersion.lift (P.toBase ⁻¹ᵁ a.1 ⊓ P.degreeOpen k).ι
        ((g ⁻¹ᵁ a.1).ι ≫ φ ≫ (P.degreeOpen k).ι) (hrange a.1)), ?_⟩
    show Fd.chartRelativeEquiv A a.1 P a.2 hk _ ((Fd.chartRelativeEquiv A a.1 P a.2 hk _).symm _)
          ≫ (P.toBase ⁻¹ᵁ a.1 ⊓ P.degreeOpen k).ι = _
    rw [Equiv.apply_symm_apply]
    exact IsOpenImmersion.lift_fac _ _ (hrange a.1)
  choose η hchart using hex
  obtain ⟨⟨gx, qx⟩, hξ⟩ := Fd.exists_amalgamation_opens (situationAlgebra A) (k : ℤ) W
    {U : S.Opens // IsAffineOpen U} (fun a => g ⁻¹ᵁ a.1)
    (fun x => exists_mem_preimage_affineOpen g x)
    (fun a => Fd.chartClassInv A a.1 (η a))
    (fun a b => by
      rw [← Fd.chartClassInv_pullback, ← Fd.chartClassInv_pullback]
      refine Fd.chartClassInv_eq_of_chartHom_eq_of_eq A a.1 b.1 P a.2 b.2 hk _ _ ?_
      rw [Fd.chartHom_pullback, Fd.chartHom_pullback, hchart a, hchart b]
      exact homOfLE_inf_ι_comp _ _ (φ ≫ (P.degreeOpen k).ι))
  have hfst : gx = g := by
    refine eq_of_ι_comp_eq_of_affine_cover g _ _ fun U hU => ?_
    refine (congrArg (fun z : Fd (situationAlgebra A) (k : ℤ) (g ⁻¹ᵁ U).toScheme => z.1)
      (hξ ⟨U, hU⟩)).trans ?_
    rw [Fd.chartClassInv_fst, ← Fd.chartHom_comp_toBase A U P hU hk _ (η ⟨U, hU⟩), hchart ⟨U, hU⟩]
    rfl
  subst hfst
  refine ⟨⟨g, qx⟩, (Fd.eq_homDegreeOpen A P hk _ φ ?_).symm⟩
  intro U hU ηU hηU
  have hcl : Fd.chartClassInv A U ηU = Fd.chartClassInv A U (η ⟨U, hU⟩) :=
    hηU.trans (hξ ⟨U, hU⟩)
  rw [Fd.chartClassInv_injective A U hcl, hchart ⟨U, hU⟩]

/-! ### The bijection -/

/-- The relative degree-`d` open `U_d` of a relative homogeneous spectrum of `𝒜` represents
`F_d`: the glued morphism of `...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen` is a
bijection `F_d(W) ≃ Mor(W, U_d)` for every test scheme `W`. -/
def Fd.degreeOpenEquiv (hk : 0 < k) (W : Scheme.{u}) :
    Fd (situationAlgebra A) (k : ℤ) W ≃ (W ⟶ (P.degreeOpen k).toScheme) :=
  Equiv.ofBijective (Fd.homDegreeOpen A P hk (W := W))
    ⟨Fd.homDegreeOpen_injective A P hk W, Fd.homDegreeOpen_surjective A P hk W⟩

@[simp] theorem Fd.degreeOpenEquiv_apply (hk : 0 < k) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    Fd.degreeOpenEquiv A P hk W ξ = Fd.homDegreeOpen A P hk ξ := rfl

/-- The bijection is natural in the test scheme. -/
theorem Fd.homDegreeOpen_pullback' (hk : 0 < k) {W W' : Scheme.{u}} (h : W' ⟶ W)
    (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    Fd.homDegreeOpen A P hk (Fd.pullback h ξ) = h ≫ Fd.homDegreeOpen A P hk ξ :=
  Fd.hom_degreeOpen_pullback A P hk h ξ (Fd.homDegreeOpen A P hk ξ)
    (fun U hU η hη => Fd.ι_homDegreeOpen A P hk ξ U hU η hη)
    (Fd.homDegreeOpen A P hk (Fd.pullback h ξ))
    (fun U hU η hη => Fd.ι_homDegreeOpen A P hk (Fd.pullback h ξ) U hU η hη)

/-! ### The compatibility with the transitions -/

/-- The transition `F_d → F_{a d}` is the inclusion `U_d ⊆ U_{a d}`. -/
theorem Fd.homDegreeOpen_scale (hk : 0 < k) {a : ℕ} (ha : 0 < a) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (k : ℤ) W)
    (hle : P.degreeOpen k ≤ P.degreeOpen (a * k)) :
    Fd.homDegreeOpen A P (Nat.mul_pos ha hk)
        (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) ξ)
      = Fd.homDegreeOpen A P hk ξ ≫ P.scheme.homOfLE hle := by
  classical
  obtain ⟨η, hη⟩ := exists_chartClassInv_pullback A ξ
  refine (Fd.eq_homDegreeOpen A P (Nat.mul_pos ha hk) _ _ ?_).symm
  intro U hU η' hη'
  have hscale : Fd.chartClassInv A U
      (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) (η U)) =
      Fd.chartClassInv A U η' := by
    rw [Fd.chartClassInv_scale, hη U, ← Fd.pullback_scale]
    exact hη'.symm
  refine Eq.trans ?_ (congrArg (Fd.chartHom A U P hU (Nat.mul_pos ha hk) _)
    (Fd.chartClassInv_injective A U hscale))
  refine Eq.trans ?_ (Fd.chartHom_scale A U P hU hk ha _ (η U)).symm
  refine Eq.trans ?_ (Fd.ι_homDegreeOpen A P hk ξ U hU (η U) (hη U))
  show (ξ.1 ⁻¹ᵁ U).ι ≫ (Fd.homDegreeOpen A P hk ξ ≫ P.scheme.homOfLE hle)
        ≫ (P.degreeOpen (a * k)).ι
      = (ξ.1 ⁻¹ᵁ U).ι ≫ Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι
  rw [Category.assoc, Scheme.homOfLE_ι]

/-! ### The bijection at an integer degree, and the hypothesis bundle -/

/-- `Fd.degreeOpenEquiv` with the degree an integer. -/
def Fd.degreeOpenEquiv' {d : ℤ} (hd : 0 < d) (W : Scheme.{u}) :
    Fd (situationAlgebra A) d W ≃ (W ⟶ (P.degreeOpen d.toNat).toScheme) :=
  Int.toNat_of_nonneg hd.le ▸ Fd.degreeOpenEquiv A P (k := d.toNat) (by omega) W

/-- The bijection at an integer degree is natural in the test scheme. -/
theorem Fd.degreeOpenEquiv'_pullback {d : ℤ} (hd : 0 < d) {W W' : Scheme.{u}} (h : W' ⟶ W)
    (ξ : Fd (situationAlgebra A) d W) :
    Fd.degreeOpenEquiv' A P hd W' (Fd.pullback h ξ) = h ≫ Fd.degreeOpenEquiv' A P hd W ξ := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  exact Fd.homDegreeOpen_pullback' A P (by exact_mod_cast hd) h ξ

/-- The bijection at an integer degree is compatible with the transitions. -/
theorem Fd.degreeOpenEquiv'_scale {d a : ℤ} (hd : 0 < d) (ha : 0 < a) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra A) d W)
    (hle : P.degreeOpen d.toNat ≤ P.degreeOpen (a * d).toNat) :
    Fd.degreeOpenEquiv' A P (mul_pos ha hd) W (Fd.scale ha ξ)
      = Fd.degreeOpenEquiv' A P hd W ξ ≫ P.scheme.homOfLE hle := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
  exact Fd.homDegreeOpen_scale A P (by exact_mod_cast hd) (by exact_mod_cast ha) W ξ _

/-- For a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜` and a relative homogeneous
spectrum of `𝒜`, for every `d ≥ 1` the open `U_d` represents `F_d`, naturally in the test scheme
and compatibly with the transitions. -/
def ProjDegreeRepresentation.ofCharts : ProjDegreeRepresentation A P where
  equiv _d hd W _ := Fd.degreeOpenEquiv' A P hd W
  equiv_pullback _ hd _ _ _ _ h ξ := Fd.degreeOpenEquiv'_pullback A P hd h ξ
  equiv_scale _ _ hd ha W _ ξ := Fd.degreeOpenEquiv'_scale A P hd ha W ξ _

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
