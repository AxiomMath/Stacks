module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartClass

/-!
# The top class of a family of equations on an open, for any number of equations

Let `X` be a scheme, `W ⊆ X` an open and `f₁, …, f_c ∈ Γ(W, 𝒪_W)`.  The top degree of the splice
of the extended alternating Čech complex of the `fᵢ` carries a canonical cocycle: the fraction
`s ↦ s / (f₁ ⋯ f_c)` when `c ≥ 1`, and the identity of `ℱ` when `c = 0`, where the complex is `ℱ`
in degree `0`.  Its class

`c_{W,f} : ℱ ⟶ i_*ℋ^c_T(ℱ)`

is the map of Stacks 0G7Q read on all of `X`.  This file records, for every `c`, the properties
of these classes that the glueing of Stacks 0G7T uses.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction (fractionHom supportCohomologySheaf supportCohomologySheafMap
  globalSmul)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

section Top

variable (W : X.Opens) (F : X.Modules)

/-- With no equations, the first term of the Čech complex is a zero object. -/
theorem isZero_cplx_X_one (f : Fin 0 → Γ(W.toScheme, ⊤)) (G : W.toScheme.Modules) :
    IsZero ((cplx f G).X 1) :=
  have : IsEmpty (CechCochains.OrdIndex (I := Fin 0) 0) :=
    Stacks.Perfect.CechSupportRepresentation.isEmpty_ordIndex_of_le le_rfl
  Stacks.Perfect.CechSupportRepresentation.isZero_pi_of_isEmpty _

/-- **The top cocycle of the splice**: the identity of `ℱ` for no equations and the fraction
`s ↦ s / (f₁ ⋯ f_c)` otherwise. -/
def chartTop : ∀ {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)), F ⟶ (chartSplice W f F).X c
  | 0, _ => 𝟙 F
  | _ + 1, f => chartFraction W f F

/-- The top cocycle is a cocycle: its composite with the differential out of degree `c`
vanishes. -/
theorem chartTop_comp_d : ∀ {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)),
    chartTop W F f ≫ (chartSplice W f F).d c (c + 1) = 0
  | 0, f => by
      refine (Category.id_comp _).trans ((chartSplice_d_zero W f F).trans ?_)
      have h0 : (cplx f ((res W).obj F)).d 0 1 = 0 := (isZero_cplx_X_one W f _).eq_of_tgt _ _
      refine (congrArg (fun g => unitW W F ≫ (push W).map g) h0).trans ?_
      exact (congrArg (fun g => unitW W F ≫ g) ((push W).map_zero _ _)).trans comp_zero
  | _ + 1, f => chartFraction_comp_d W f F

variable {T : Set X} (hT : IsClosed T)

/-- **The class `c_{W,f} : ℱ ⟶ i_*ℋ^c_T(ℱ)` of the top cocycle**, for any number `c` of
equations. -/
def topClass {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (hfT : chartSupport W f ⊆ T) :
    F ⟶ supportCohomologySheaf hT F (c : ℤ) :=
  augClass (chartSplice W f F) (𝟙 F) hT (cohomologySupportedOn_chartSplice_of_subset W F f hfT)
    c (chartTop W F f) (chartTop_comp_d W F f)

/-- For at least one equation, the top class is the class `chartClass` of the fraction. -/
theorem topClass_succ {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤)) (hfT : chartSupport W f ⊆ T) :
    topClass W F hT f hfT = chartClass W f F hT hfT :=
  rfl

/-- Equal families of equations have equal top classes. -/
theorem topClass_congr {c : ℕ} {f₁ f₂ : Fin c → Γ(W.toScheme, ⊤)} (h : f₁ = f₂)
    (h₁ : chartSupport W f₁ ⊆ T) (h₂ : chartSupport W f₂ ⊆ T) :
    topClass W F hT f₁ h₁ = topClass W F hT f₂ h₂ := by
  subst h
  rfl

end Top

/-! ### Restricting the equations -/

/-- The top class of the restrictions of the equations to an open `V ⊆ W` is the top class of
the equations on `W`. -/
theorem topClass_restrict {W V : X.Opens} (hVW : V ≤ W) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) : ∀ {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (hfT : chartSupport W f ⊆ T)
    (hfT' : chartSupport V (restrictEquations hVW f) ⊆ T),
    topClass V F hT (restrictEquations hVW f) hfT' = topClass W F hT f hfT
  | 0, f, hfT, hfT' => by
      have hc := augClass_comp (chartSplice W f F) (𝟙 F) hT
        (cohomologySupportedOn_chartSplice_of_subset W F f hfT) 0 (chartTop W F f)
        (chartTop_comp_d W F f) (𝟙 F) (chartRestrict hVW f F)
        ((Category.comp_id _).trans (chartRestrict_f_zero hVW f F))
        (cohomologySupportedOn_chartSplice_of_subset V F (restrictEquations hVW f) hfT')
      have he : chartTop V F (restrictEquations hVW f) =
          chartTop W F f ≫ (chartRestrict hVW f F).f 0 :=
        (Category.comp_id (𝟙 F)).symm.trans
          (congrArg (fun g => 𝟙 F ≫ g) (chartRestrict_f_zero hVW f F).symm)
      exact (augClass_congr _ _ hT _ 0 he _ _).trans hc
  | _ + 1, f, hfT, hfT' => chartClass_restrict hVW f F hT hfT hfT'

/-! ### Enlarging the closed subset -/

/-- For closed subsets `T ⊆ T'`, the top class for `T` followed by the change of support map
`ℋ^c_T(ℱ) ⟶ ℋ^c_{T'}(ℱ)` is the top class for `T'`. -/
theorem topClass_supportChange (W : X.Opens) (F : X.Modules) {T T' : Set X} (hT : IsClosed T)
    (hT' : IsClosed T') (hTT' : T ⊆ T') {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤))
    (hfT : chartSupport W f ⊆ T) :
    topClass W F hT f hfT ≫ supportChangeH hT hT' hTT' F (c : ℤ) =
      topClass W F hT' f (hfT.trans hTT') :=
  augClass_comp_supportChangeH _ _ hT hT' hTT' _ c _ _

/-! ### Naturality in the coefficient module -/

/-- The top cocycle is natural in the module: for `φ : ℱ ⟶ 𝒢` it commutes with the map of
splices induced by `φ`. -/
theorem chartTop_comp_chartSpliceMap (W : X.Opens) {F G : X.Modules} (φ : F ⟶ G) :
    ∀ {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)),
    chartTop W F f ≫ (chartSpliceMap W f φ).f c = φ ≫ chartTop W G f
  | 0, f => (Category.id_comp ((chartSpliceMap W f φ).f 0)).trans
      ((chartSpliceMap_f_zero W f φ).trans (Category.comp_id φ).symm)
  | _ + 1, f => chartFraction_comp_chartSpliceMap W f φ

/-- The top class is natural in the module: for `φ : ℱ ⟶ 𝒢`, composing `c_{W,f}` for `ℱ` with
the map `ℋ^c_T(ℱ) ⟶ ℋ^c_T(𝒢)` induced by `φ` equals `φ` followed by `c_{W,f}` for `𝒢`. -/
theorem topClass_natural (W : X.Opens) {F G : X.Modules} (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (hfT : chartSupport W f ⊆ T) :
    topClass W F hT f hfT ≫ supportCohomologySheafMap hT φ (c : ℤ) =
      φ ≫ topClass W G hT f hfT := by
  rw [topClass, topClass]
  refine Eq.trans ?_ (comp_augClass _ _ hT _ c _ _ φ).symm
  have hn := augClass_natural φ (𝟙 F) (𝟙 G) (chartSpliceMap W f φ)
    ((Category.comp_id _).trans ((chartSpliceMap_f_zero W f φ).trans (Category.id_comp φ).symm)) hT
    (cohomologySupportedOn_chartSplice_of_subset W F f hfT)
    (cohomologySupportedOn_chartSplice_of_subset W G f hfT) c (chartTop W F f)
    (chartTop_comp_d W F f)
  refine hn.symm.trans ?_
  exact augClass_congr _ _ hT _ c (chartTop_comp_chartSpliceMap W φ f) _ _

/-! ### The classes on sections over opens of the chart -/

section Sections

variable (V : X.Opens) (F : X.Modules) {T : Set X} (hT : IsClosed T)

/-- **Stacks 0G7S on sections**: if `g = a f` on `V` then on a section `s` over an open of `V`
the class of `f` is the class of `g` at `det(a) s`. -/
theorem topClass_app_det : ∀ {c : ℕ} (f g : Fin c → Γ(V.toScheme, ⊤))
    (a : Matrix (Fin c) (Fin c) Γ(V.toScheme, ⊤)) (_ : ∀ j, g j = ∑ i, a j i * f i)
    (hf : chartSupport V f ⊆ T) (hg : chartSupport V g ⊆ T) {U : X.Opens} (hU : U ≤ V)
    (s : Γ(F, U)),
    (topClass V F hT f hf).app U s = (topClass V F hT g hg).app U (restrictFun V hU a.det • s)
  | 0, f, g, a, _, hf, hg, U, hU, s => by
      have hfg : f = g := funext fun i => i.elim0
      subst hfg
      have h1 : restrictFun V hU a.det = 1 := by
        rw [Matrix.det_isEmpty]
        exact (X.presheaf.map _).hom.map_one
      rw [h1, one_smul]
  | _ + 1, f, g, a, ha, hf, hg, U, hU, s =>
      (congrArg (fun ψ => ψ.app U s) (chartClass_eq_twistedClass V F hT f g a ha hf hg)).trans
        (twistedClass_app V F hT g a.det hg hU s)

/-- **The class kills the multiples of the equations**, on sections over opens of the chart. -/
theorem topClass_app_smul_eq_zero {c : ℕ} (f : Fin c → Γ(V.toScheme, ⊤))
    (hf : chartSupport V f ⊆ T) (j : Fin c) {U : X.Opens} (hU : U ≤ V) (s : Γ(F, U)) :
    (topClass V F hT f hf).app U (restrictFun V hU (f j) • s) = 0 := by
  cases c with
  | zero => exact j.elim0
  | succ d => exact chartClass_app_smul_eq_zero V F hT f hf j hU s

end Sections

end Stacks.Perfect.ConormalClass
