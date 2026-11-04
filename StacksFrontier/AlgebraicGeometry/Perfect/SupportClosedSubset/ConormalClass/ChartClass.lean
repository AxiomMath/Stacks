module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartRestrict

/-!
# The class of the fraction of equations on an open, in the local cohomology of `X`

Let `X` be a scheme, `W ⊆ X` an open, `f₁, …, f_c ∈ Γ(W, 𝒪_W)` with `c ≥ 1` and `T ⊆ X` a closed
subset containing the complement of the principal opens of the `fᵢ` in `W`.  The fraction
cocycle `s ↦ s / (f₁ ⋯ f_c)` of the splice of the extended alternating Čech complex has a class

`c_{W,f} : ℱ ⟶ i_*ℋ^c_T(ℱ)`,

the map of Stacks 0G7Q read on all of `X`.  This file proves the properties of these classes
that the glueing of Stacks 0G7T uses:

* restricting the equations to a smaller open does not change the class;
* enlarging `T` composes the class with the change of support;
* the class is natural in `ℱ`;
* changing the equations by a matrix over the open multiplies the class by the determinant
  (Stacks 0G7S);
* on a section over an open of `W`, the class of a multiple of an equation vanishes.
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

section Class

variable (W : X.Opens) {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤)) (F : X.Modules)
  {T : Set X} (hT : IsClosed T) (hfT : chartSupport W f ⊆ T)

/-- The splice is supported on any closed subset containing `chartSupport`. -/
theorem cohomologySupportedOn_chartSplice_of_subset {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤))
    (hfT : chartSupport W f ⊆ T) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj ((chartSplice W f F).extend ComplexShape.embeddingUpNat)) :=
  cohomologySupportedOn_mono' hfT (cohomologySupportedOn_chartSplice W f F)

/-- **The class `c_{W,f} : ℱ ⟶ i_*ℋ^c_T(ℱ)` of the fraction `s / (f₁ ⋯ f_c)`.** -/
def chartClass : F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  augClass (chartSplice W f F) (𝟙 F) hT (cohomologySupportedOn_chartSplice_of_subset W F f hfT)
    (d + 1) (chartFraction W f F) (chartFraction_comp_d W f F)

end Class

/-- The class of a cocycle depends only on the cocycle. -/
theorem augClass_congr {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
    {T : Set X} (hT : IsClosed T)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
    (p : ℕ) {M : X.Modules} {u u' : M ⟶ L.X p} (h : u = u') (hu : u ≫ L.d p (p + 1) = 0)
    (hu' : u' ≫ L.d p (p + 1) = 0) :
    augClass L a hT hL p u hu = augClass L a hT hL p u' hu' := by
  subst h
  rfl

/-! ### Restricting the equations -/

section Restrict

variable {W V : X.Opens} (hVW : V ≤ W) {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
  (F : X.Modules) {T : Set X} (hT : IsClosed T)

/-- The support of the splice grows when the equations are restricted to a smaller open. -/
theorem chartSupport_subset_restrict {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) :
    chartSupport W f ⊆ chartSupport V (restrictEquations hVW f) := by
  intro x hx hxV
  apply hx
  obtain ⟨y, hy, rfl⟩ := hxV
  refine ⟨⟨y.1, hVW y.2⟩, ?_, rfl⟩
  have hy' := (Opens.mem_iSup).1 hy
  obtain ⟨k, hk⟩ := hy'
  refine (Opens.mem_iSup).2 ⟨k, ?_⟩
  have e1 := (Scheme.Opens.mem_basicOpen_toScheme (U := V) (V := ⊤)
    (r := restrictEquations hVW f k) (x := y)).1 hk
  have e2 := (Scheme.basicOpen_res X (f := f k) (homOfLE (image_top_le hVW)).op).le e1
  exact (Scheme.Opens.mem_basicOpen_toScheme (U := W) (V := ⊤) (r := f k)
    (x := ⟨y.1, hVW y.2⟩)).2 e2.2

/-- **Restricting the equations to a smaller open does not change the class.** -/
theorem chartClass_restrict (hfT : chartSupport W f ⊆ T)
    (hfT' : chartSupport V (restrictEquations hVW f) ⊆ T) :
    chartClass V (restrictEquations hVW f) F hT hfT' = chartClass W f F hT hfT := by
  rw [chartClass, chartClass]
  have hc := augClass_comp (chartSplice W f F) (𝟙 F) hT
    (cohomologySupportedOn_chartSplice_of_subset W F f hfT) (d + 1) (chartFraction W f F)
    (chartFraction_comp_d W f F) (𝟙 F) (chartRestrict hVW f F) (Category.comp_id _)
    (cohomologySupportedOn_chartSplice_of_subset V F (restrictEquations hVW f) hfT')
  refine Eq.trans ?_ hc
  exact augClass_congr _ _ hT _ (d + 1) (chartFraction_comp_chartRestrict hVW F f).symm _ _

end Restrict

/-! ### Enlarging the closed subset -/

/-- **Enlarging the closed subset composes the class with the change of support.** -/
theorem chartClass_supportChange (W : X.Opens) {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (F : X.Modules) {T T' : Set X} (hT : IsClosed T) (hT' : IsClosed T') (hTT' : T ⊆ T')
    (hfT : chartSupport W f ⊆ T) :
    chartClass W f F hT hfT ≫ supportChangeH hT hT' hTT' F ((d + 1 : ℕ) : ℤ) =
      chartClass W f F hT' (hfT.trans hTT') :=
  augClass_comp_supportChangeH _ _ hT hT' hTT' _ (d + 1) _ _

/-! ### Naturality in the coefficient module -/

section SpliceMap

variable (W : X.Opens) {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) {F G : X.Modules} (φ : F ⟶ G)

/-- In degree `0`, the map of complexes induced by `φ` commutes with the identifications of the
degree-zero terms with the restricted coefficient modules. -/
theorem cplxMap_f_zero_comp :
    (cplxMap f ((res W).map φ)).f 0 ≫
        (Iso.refl ((cplx f ((res W).obj G)).X 0) :
          (cplx f ((res W).obj G)).X 0 ≅ (res W).obj G).hom =
      (Iso.refl ((cplx f ((res W).obj F)).X 0) : (cplx f ((res W).obj F)).X 0 ≅ (res W).obj F).hom ≫
        (res W).map φ :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The map of splices induced by a map of coefficient modules. -/
def chartSpliceMap : chartSplice W f F ⟶ chartSplice W f G :=
  spliceMap W φ (K := cplx f ((res W).obj F)) (K' := cplx f ((res W).obj G))
    (Iso.refl ((cplx f ((res W).obj F)).X 0)) (Iso.refl ((cplx f ((res W).obj G)).X 0))
    (cplxMap f ((res W).map φ)) (cplxMap_f_zero_comp W f φ)

/-- In degree `0`, the map of splices induced by `φ` is `φ`. -/
theorem chartSpliceMap_f_zero : (chartSpliceMap W f φ).f 0 = φ :=
  rfl

end SpliceMap

section Natural

variable (W : X.Opens) {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤)) {F G : X.Modules}
  (φ : F ⟶ G) {T : Set X} (hT : IsClosed T) (hfT : chartSupport W f ⊆ T)

/-- The fraction cocycle is natural in the coefficient module. -/
theorem chartFraction_comp_chartSpliceMap :
    chartFraction W f F ≫ (chartSpliceMap W f φ).f (d + 1) = φ ≫ chartFraction W f G := by
  rw [chartFraction, chartFraction]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g => unitW W F ≫ g)
    ((push W).map_comp (fractionHom f ((res W).obj F) d)
      (prodMap f ((res W).map φ) d)).symm).trans ?_
  refine (congrArg (fun g => unitW W F ≫ (push W).map g)
    (Stacks.Perfect.SupportedFraction.fractionHom_naturality f ((res W).map φ) d)).trans ?_
  refine (congrArg (fun g => unitW W F ≫ g) ((push W).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun g => g ≫ (push W).map (fractionHom f ((res W).obj G) d))
    ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality φ).symm).trans ?_
  exact Category.assoc _ _ _

/-- **The class is natural in the coefficient module.** -/
theorem chartClass_natural :
    chartClass W f F hT hfT ≫ supportCohomologySheafMap hT φ ((d + 1 : ℕ) : ℤ) =
      φ ≫ chartClass W f G hT hfT := by
  rw [chartClass, chartClass]
  refine Eq.trans ?_ (comp_augClass _ _ hT _ (d + 1) _ _ φ).symm
  have hn := augClass_natural φ (𝟙 F) (𝟙 G) (chartSpliceMap W f φ)
    ((Category.comp_id _).trans (Category.id_comp _).symm) hT
    (cohomologySupportedOn_chartSplice_of_subset W F f hfT)
    (cohomologySupportedOn_chartSplice_of_subset W G f hfT) (d + 1) (chartFraction W f F)
    (chartFraction_comp_d W f F)
  refine hn.symm.trans ?_
  exact augClass_congr _ _ hT _ (d + 1) (chartFraction_comp_chartSpliceMap W f φ) _ _

end Natural

/-! ### Changing the equations by a matrix -/

section Determinant

variable (V : X.Opens) {d : ℕ} (F : X.Modules) {T : Set X} (hT : IsClosed T)

/-- The splice supports grow when equations are dropped from a family. -/
theorem chartSupport_subfamily {m n : ℕ} (e : Fin n → Γ(V.toScheme, ⊤)) (φ : Fin m ↪o Fin n) :
    chartSupport V e ⊆ chartSupport V (e ∘ φ) := by
  intro x hx hx'
  apply hx
  obtain ⟨y, hy, rfl⟩ := hx'
  refine ⟨y, ?_, rfl⟩
  obtain ⟨k, hk⟩ := (Opens.mem_iSup).1 hy
  exact (Opens.mem_iSup).2 ⟨φ k, hk⟩

/-- Pushed-forward maps composed after the unit are the unit followed by the pushed composite. -/
private theorem unitW_push_comp_push {M N : V.toScheme.Modules} (h : (res V).obj F ⟶ M)
    (k : M ⟶ N) :
    (unitW V F ≫ (push V).map h) ≫ (push V).map k = unitW V F ≫ (push V).map (h ≫ k) := by
  rw [Category.assoc, ← Functor.map_comp]

/-- A pushed-forward map after the unit is zero if the map before pushing is. -/
private theorem unitW_push_comp_push_eq_zero {M N : V.toScheme.Modules} (h : (res V).obj F ⟶ M)
    (k : M ⟶ N) (hk : h ≫ k = 0) : (unitW V F ≫ (push V).map h) ≫ (push V).map k = 0 := by
  rw [unitW_push_comp_push, hk]
  simp

/-- The fraction cocycle twisted by multiplication by a function on the open. -/
def twistedFraction (g : Fin (d + 1) → Γ(V.toScheme, ⊤)) (r : Γ(V.toScheme, ⊤)) :
    F ⟶ (chartSplice V g F).X (d + 1) :=
  unitW V F ≫ (push V).map (globalSmul r ((res V).obj F) ≫ fractionHom g ((res V).obj F) d)

/-- The twisted fraction cocycle is a cocycle. -/
theorem twistedFraction_comp_d (g : Fin (d + 1) → Γ(V.toScheme, ⊤)) (r : Γ(V.toScheme, ⊤)) :
    twistedFraction V F g r ≫ (chartSplice V g F).d (d + 1) (d + 1 + 1) = 0 := by
  rw [chartSplice_d_succ, twistedFraction]
  exact unitW_push_comp_push_eq_zero V F _ _ ((congrArg _
    (Stacks.Perfect.SupportedFraction.cplx_d_top_eq_zero g ((res V).obj F))).trans comp_zero)

/-- **The class of the twisted fraction cocycle** `s ↦ r s / (g₁ ⋯ g_c)`. -/
def twistedClass (g : Fin (d + 1) → Γ(V.toScheme, ⊤)) (r : Γ(V.toScheme, ⊤))
    (hgT : chartSupport V g ⊆ T) : F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  augClass (chartSplice V g F) (𝟙 F) hT (cohomologySupportedOn_chartSplice_of_subset V F g hgT)
    (d + 1) (twistedFraction V F g r) (twistedFraction_comp_d V F g r)

/-- Equal families of equations on an open have equal classes. -/
theorem chartClass_congr {f₁ f₂ : Fin (d + 1) → Γ(V.toScheme, ⊤)} (h : f₁ = f₂)
    (h₁ : chartSupport V f₁ ⊆ T) (h₂ : chartSupport V f₂ ⊆ T) :
    chartClass V f₁ F hT h₁ = chartClass V f₂ F hT h₂ := by
  subst h
  rfl

/-- Equal families of equations have equal twisted classes. -/
theorem twistedClass_congr {g₁ g₂ : Fin (d + 1) → Γ(V.toScheme, ⊤)} (h : g₁ = g₂)
    (r : Γ(V.toScheme, ⊤)) (h₁ : chartSupport V g₁ ⊆ T) (h₂ : chartSupport V g₂ ⊆ T) :
    twistedClass V F hT g₁ r h₁ = twistedClass V F hT g₂ r h₂ := by
  subst h
  rfl

variable (f g : Fin (d + 1) → Γ(V.toScheme, ⊤))
  (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(V.toScheme, ⊤))
  (ha : ∀ j, g j = ∑ i, a j i * f i)

/-- The splice of the mixed family maps to the splice of a subfamily. -/
def mixedSpliceMap (φ : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) :
    chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g) F ⟶
      chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘ φ) F :=
  spliceMap V (𝟙 F)
    (K := cplx (Stacks.Perfect.SupportedFraction.mixedEquations f g) ((res V).obj F))
    (K' := cplx (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘ φ) ((res V).obj F))
    (Iso.refl _) (Iso.refl _)
    (Stacks.Perfect.SupportedFraction.subfamilyCplxMap
      (Stacks.Perfect.SupportedFraction.mixedEquations f g) φ ((res V).obj F))
    (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- The mixed fraction cocycle of Stacks 0G7S. -/
def mixedFraction : F ⟶
    (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g) F).X (d + 1) :=
  unitW V F ≫ (push V).map (Stacks.Perfect.SupportedFraction.mixedFractionHom
    (Stacks.Perfect.SupportedFraction.mixedEquations f g) a ((res V).obj F))

include ha in
/-- If `g = a f`, the mixed fraction cocycle is a cocycle. -/
theorem mixedFraction_comp_d :
    mixedFraction V F f g a ≫
      (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g) F).d
        (d + 1) (d + 1 + 1) =
      0 := by
  obtain ⟨h0, -, -⟩ := Stacks.Perfect.SupportedFraction.mixedFractionHom_projections f g a
    ((res V).obj F) ha
  rw [chartSplice_d_succ, cplx_d_succ, mixedFraction]
  exact unitW_push_comp_push_eq_zero V F _ _ h0

include ha in
/-- If `g = a f`, the mixed fraction cocycle maps to the fraction cocycle of the first `d + 1`
equations of the mixed family, which are the `fᵢ`. -/
theorem mixedFraction_cast :
    mixedFraction V F f g a ≫ (mixedSpliceMap V F f g (Fin.castAddOrderEmb (d + 1))).f (d + 1) =
      chartFraction V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
        Fin.castAddOrderEmb (d + 1)) F := by
  obtain ⟨-, h1, -⟩ := Stacks.Perfect.SupportedFraction.mixedFractionHom_projections f g a
    ((res V).obj F) ha
  have : Mono (Stacks.Perfect.SupportedFraction.prodTermCongr
      (Stacks.Perfect.SupportedFraction.mixedEquations_comp_castAdd f g) ((res V).obj F) d) := by
    unfold Stacks.Perfect.SupportedFraction.prodTermCongr; infer_instance
  have hS1 := (cancel_mono (Stacks.Perfect.SupportedFraction.prodTermCongr
      (Stacks.Perfect.SupportedFraction.mixedEquations_comp_castAdd f g) ((res V).obj F) d)).1
    ((Category.assoc _ _ _).trans (h1.trans
      (Stacks.Perfect.SupportedFraction.fractionHom_prodTermCongr _ _ _).symm))
  exact (unitW_push_comp_push V F _ _).trans (congrArg (fun h => unitW V F ≫ (push V).map h) hS1)

include ha in
/-- If `g = a f`, the mixed fraction cocycle maps to the fraction cocycle of the last `d + 1`
equations of the mixed family, which are the `gⱼ`, twisted by `det a`. -/
theorem mixedFraction_nat :
    mixedFraction V F f g a ≫ (mixedSpliceMap V F f g (Fin.natAddOrderEmb (d + 1))).f (d + 1) =
      twistedFraction V F (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
        Fin.natAddOrderEmb (d + 1)) a.det := by
  obtain ⟨-, -, h2⟩ := Stacks.Perfect.SupportedFraction.mixedFractionHom_projections f g a
    ((res V).obj F) ha
  have : Mono (Stacks.Perfect.SupportedFraction.prodTermCongr
      (Stacks.Perfect.SupportedFraction.mixedEquations_comp_natAdd f g) ((res V).obj F) d) := by
    unfold Stacks.Perfect.SupportedFraction.prodTermCongr; infer_instance
  have hS2 := (cancel_mono (Stacks.Perfect.SupportedFraction.prodTermCongr
      (Stacks.Perfect.SupportedFraction.mixedEquations_comp_natAdd f g) ((res V).obj F) d)).1
    ((Category.assoc _ _ _).trans (h2.trans
      ((congrArg (fun h => globalSmul a.det ((res V).obj F) ≫ h)
        (Stacks.Perfect.SupportedFraction.fractionHom_prodTermCongr _ _ _).symm).trans
          (Category.assoc _ _ _).symm)))
  exact (unitW_push_comp_push V F _ _).trans (congrArg (fun h => unitW V F ≫ (push V).map h) hS2)

include ha in
/-- **Stacks 0G7S for the classes on an open**: if `g = a f` on `V`, the class of `s / (f₁ ⋯ f_c)`
is the class of `det(a) s / (g₁ ⋯ g_c)`. -/
theorem chartClass_eq_twistedClass (hf : chartSupport V f ⊆ T) (hg : chartSupport V g ⊆ T) :
    chartClass V f F hT hf = twistedClass V F hT g a.det hg := by
  have hcast := Stacks.Perfect.SupportedFraction.mixedEquations_comp_castAdd f g
  have hnat := Stacks.Perfect.SupportedFraction.mixedEquations_comp_natAdd f g
  have hf' : chartSupport V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
      Fin.castAddOrderEmb (d + 1)) ⊆ T := hcast.symm ▸ hf
  have hg' : chartSupport V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
      Fin.natAddOrderEmb (d + 1)) ⊆ T := hnat.symm ▸ hg
  have hm : chartSupport V (Stacks.Perfect.SupportedFraction.mixedEquations f g) ⊆ T :=
    (chartSupport_subfamily V _ (Fin.castAddOrderEmb (d + 1))).trans hf'
  have hA1 := augClass_comp (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g) F)
    (𝟙 F) hT (cohomologySupportedOn_chartSplice_of_subset V F _ hm) (d + 1)
    (mixedFraction V F f g a) (mixedFraction_comp_d V F f g a ha) (𝟙 F)
    (mixedSpliceMap V F f g (Fin.castAddOrderEmb (d + 1))) (Category.comp_id _)
    (cohomologySupportedOn_chartSplice_of_subset V F _ hf')
  have hA2 := augClass_comp (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g) F)
    (𝟙 F) hT (cohomologySupportedOn_chartSplice_of_subset V F _ hm) (d + 1)
    (mixedFraction V F f g a) (mixedFraction_comp_d V F f g a ha) (𝟙 F)
    (mixedSpliceMap V F f g (Fin.natAddOrderEmb (d + 1))) (Category.comp_id _)
    (cohomologySupportedOn_chartSplice_of_subset V F _ hg')
  refine (chartClass_congr V F hT hcast.symm hf hf').trans ?_
  refine Eq.trans ?_ (twistedClass_congr V F hT hnat a.det hg' hg)
  have hu1 : (mixedFraction V F f g a ≫
      (mixedSpliceMap V F f g (Fin.castAddOrderEmb (d + 1))).f (d + 1)) ≫
      (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
        Fin.castAddOrderEmb (d + 1)) F).d (d + 1) (d + 1 + 1) = 0 := by
    rw [mixedFraction_cast V F f g a ha]; exact chartFraction_comp_d _ _ _
  have hu2 : (mixedFraction V F f g a ≫
      (mixedSpliceMap V F f g (Fin.natAddOrderEmb (d + 1))).f (d + 1)) ≫
      (chartSplice V (Stacks.Perfect.SupportedFraction.mixedEquations f g ∘
        Fin.natAddOrderEmb (d + 1)) F).d (d + 1) (d + 1 + 1) = 0 := by
    rw [mixedFraction_nat V F f g a ha]; exact twistedFraction_comp_d _ _ _ _
  unfold chartClass twistedClass
  refine (augClass_congr _ _ hT _ (d + 1) (mixedFraction_cast V F f g a ha).symm
    (chartFraction_comp_d _ _ _) hu1).trans ?_
  refine hA1.trans (hA2.symm.trans ?_)
  exact augClass_congr _ _ hT _ (d + 1) (mixedFraction_nat V F f g a ha) hu2
    (twistedFraction_comp_d _ _ _ _)

end Determinant

/-! ### The classes on sections over opens of the chart -/

section Sections

variable (V : X.Opens) (F : X.Modules)

/-- A function on `V` restricted to an open of `X` contained in `V`. -/
def restrictFun {U : X.Opens} (hU : U ≤ V) (r : Γ(V.toScheme, ⊤)) : Γ(X, U) :=
  X.presheaf.map (homOfLE (show U ≤ V.ι ''ᵁ ⊤ by rw [V.ι_image_top]; exact hU)).op r

/-- Multiplication by a function on `V`, read on the restriction of a section to `V`, is the
restriction of the product with the restricted function. -/
theorem globalSmul_unitW {U : X.Opens} (hU : U ≤ V) (r : Γ(V.toScheme, ⊤)) (s : Γ(F, U)) :
    (globalSmul r ((res V).obj F)).app (V.ι ⁻¹ᵁ U)
        (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s : Γ(F, _)) =
      (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op (restrictFun V hU r • s) :
        Γ(F, _)) := by
  refine (Stacks.Perfect.SupportedFraction.globalSmul_app _ _ _ _).trans ?_
  refine (restrict_smul F V _ _ _).trans ?_
  refine Eq.trans ?_ (Scheme.Modules.map_smul F _ _ _).symm
  congr 1
  exact presheaf_map_eq_map_map X.presheaf _ _ _ r

variable {T : Set X} (hT : IsClosed T)

/-- On a section over an open of the chart, the twisted class is the class of the product with
the twisting function. -/
theorem twistedClass_app {d : ℕ} (g : Fin (d + 1) → Γ(V.toScheme, ⊤)) (r : Γ(V.toScheme, ⊤))
    (hg : chartSupport V g ⊆ T) {U : X.Opens} (hU : U ≤ V) (s : Γ(F, U)) :
    (twistedClass V F hT g r hg).app U s =
      (chartClass V g F hT hg).app U (restrictFun V hU r • s) := by
  refine augClass_app_eq _ _ hT _ (d + 1) (chartFraction V g F) (twistedFraction V F g r)
    _ _ U _ _ ?_
  exact congrArg ((fractionHom g ((res V).obj F) d).app (V.ι ⁻¹ᵁ U))
    (globalSmul_unitW V F hU r s)

/-- The class of a coboundary vanishes on sections. -/
theorem augClass_app_eq_zero {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
    (p : ℕ) {M : X.Modules} (u : M ⟶ L.X (p + 1)) (hu : u ≫ L.d (p + 1) (p + 1 + 1) = 0)
    (U : X.Opens) (s : Γ(M, U)) (y : Γ(L.X p, U)) (h : u.app U s = (L.d p (p + 1)).app U y) :
    (augClass L a hT hL (p + 1) u hu).app U s = 0 := by
  have hc : (L.liftCycles u (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hu).app U s =
      (L.toCycles p (p + 1)).app U y := by
    refine injective_app_of_mono (L.iCycles (p + 1)) U ?_
    have e1 := congrArg (fun ψ => ψ.app U s) (L.liftCycles_i u (p + 1 + 1)
      (CochainComplex.next ℕ (p + 1)) hu)
    have e2 := congrArg (fun ψ => ψ.app U y) (L.toCycles_i p (p + 1))
    exact e1.trans (h.trans e2.symm)
  have hπ := congrArg (fun ψ => ψ.app U y) (L.toCycles_comp_homologyπ p (p + 1))
  show (augHomology L a hT hL (p + 1)).app U ((L.homologyπ (p + 1)).app U
      ((L.liftCycles u (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hu).app U s)) = 0
  rw [hc]
  show (augHomology L a hT hL (p + 1)).app U
    ((L.toCycles p (p + 1) ≫ L.homologyπ (p + 1)).app U y) = 0
  rw [L.toCycles_comp_homologyπ p (p + 1)]
  show (augHomology L a hT hL (p + 1)).app U 0 = 0
  exact map_zero _

/-- **The class kills the multiples of the equations**, on sections over opens of the chart. -/
theorem chartClass_app_smul_eq_zero {d : ℕ} (f : Fin (d + 1) → Γ(V.toScheme, ⊤))
    (hf : chartSupport V f ⊆ T) (j : Fin (d + 1)) {U : X.Opens} (hU : U ≤ V) (s : Γ(F, U)) :
    (chartClass V f F hT hf).app U (restrictFun V hU (f j) • s) = 0 := by
  have hs := globalSmul_unitW V F hU (f j) s
  cases d with
  | zero =>
    refine augClass_app_eq_zero hT _ _ _ 0 _ _ U _ s ?_
    refine (congrArg ((fractionHom f ((res V).obj F) 0).app (V.ι ⁻¹ᵁ U)) hs.symm).trans ?_
    refine (congrArg (fun φ => φ.app (V.ι ⁻¹ᵁ U)
      (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s : Γ(F, _)))
      (Stacks.Perfect.SupportedFraction.globalSmul_comp_fractionHom_one f
        ((res V).obj F) j)).trans ?_
    exact (chartSplice_d_zero_app F f U s).symm
  | succ e =>
    refine augClass_app_eq_zero hT _ _ _ (e + 1) _ _ U _
      ((fractionHom f ((res V).obj F) e ≫
        Stacks.Perfect.SupportedFraction.signedFaceProjector f ((res V).obj F) j).app (V.ι ⁻¹ᵁ U)
        (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s : Γ(F, _))) ?_
    refine (congrArg ((fractionHom f ((res V).obj F) (e + 1)).app (V.ι ⁻¹ᵁ U)) hs.symm).trans ?_
    refine (congrArg (fun φ => φ.app (V.ι ⁻¹ᵁ U)
      (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s : Γ(F, _)))
      (Stacks.Perfect.SupportedFraction.globalSmul_comp_fractionHom_succ f
        ((res V).obj F) j)).trans ?_
    exact (chartSplice_d_succ_app F f e U _).symm

end Sections

end Stacks.Perfect.ConormalClass
