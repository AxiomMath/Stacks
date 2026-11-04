module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechMulData
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechQuasiIso
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalRightMul
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupElementwise
public import StacksFrontier.Homology.DerivedCategory.MapCyclesHomologyPi

/-!
# The cup product with a form from the base on de Rham cohomology

Let `f : X ⟶ Y` be a smooth morphism and `g : Y ⟶ S` with `Y` and `S` affine, and let `U` be a
finite family of opens of `X` with affine Čech intersections covering `X`. For a cocycle `x` of
`K = Tot(Č(U, Ω^•_{X/S}))` and a closed form `ν` of `Γ(Y, 𝒪_Y)` over `Γ(S, 𝒪_S)`, the class of
`x ∧ ν` in `H^*_{dR}(X/S)` is the cup product of the class of `x` with the class of the Čech
`0`-cocycle of the pull-backs of `ν` ([Stacks, Tag 0FUM], facts (4) and (5) of its proof).

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.sliceMul_eq_sectionsMul`: the coefficient pairing of the
  library's cup product on de Rham cohomology is the wedge product of forms.
* `AlgebraicGeometry.DeRhamKatzOdaCech.classMap_mulTot`: the class of `x ∧ ν` is the cup product
  of the class of `x` with the class of the Čech `0`-cocycle of the pull-backs of `ν`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section Transport

/-- For `h : A = B`, the component at `Z` of `Φ.map (eqToHom h)` sends `x` to an element
heterogeneously equal to `x`. -/
theorem heq_map_eqToHom_app {D C : Type*} [Category D] [Category C] {R : Type*} [Ring R]
    (Φ : D ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} R)) {A B : D} (h : A = B) (Z : Cᵒᵖ) (x : (Φ.obj A).obj Z) :
    HEq (((Φ.map (eqToHom h)).app Z).hom x) x := by
  subst h
  simp

/-- `SheafOfModules.gradedCast T h v` is heterogeneously equal to `v`. -/
theorem heq_gradedCast {ι : Type*} (T : ι → Type*) {i j : ι} (h : i = j) (v : T i) :
    HEq (SheafOfModules.gradedCast T h v) v := by
  subst h
  rfl

/-- For `h : M = N`, the component at `V` of `eqToHom h` sends a section `x` to an element
heterogeneously equal to `x`. -/
theorem heq_eqToHom_val_app {X : Scheme.{u}} {M N : X.Modules} (h : M = N) (V : X.Opens)
    (x : Γ(M, V)) : HEq ((eqToHom h).val.app (op V) x) x := by
  subst h
  rfl

/-- Restricting a section of `F` from `V₁` to `V₂` and then to `V₃` is restricting it from `V₁`
to `V₃`. -/
theorem presheaf_map_map_eq {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ V₃ : X.Opens} (i : V₂ ⟶ V₁)
    (j : V₃ ⟶ V₂) (k : V₃ ⟶ V₁) (w : Γ(F, V₁)) :
    F.presheaf.map j.op (F.presheaf.map i.op w) = F.presheaf.map k.op w := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (j ≫ i) k]

end Transport

/-- If `w` is a cocycle of `K` in degree `n`, then `toMor w` composed with the differential of `K`
is zero. -/
theorem toMor_comp_d_eq_zero {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {n : ℤ} (w : K.X n) (hw : (K.d n (n + 1)).hom w = 0) :
    Stacks.Cech.Hypercohomology.toMor w ≫ K.d n (n + 1) = 0 := by
  rw [Stacks.Cech.Hypercohomology.toMor_comp, hw]
  ext : 1
  exact LinearMap.ext_ring (by simp [Stacks.Cech.Hypercohomology.toMor])

/-- On elements, the differential of the restriction of scalars of `K` along `φ` is the
differential of `K`. -/
theorem restrictScalars_d_apply {R R' : Type u} [Ring R] [Ring R'] (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{u} R') ℤ) (n m : ℤ)
    (w : (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).X n) :
    ((((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).d n m).hom w =
      (K.d n m).hom w :=
  rfl

/-- **Homology commutes with restriction of scalars, on cocycle classes.** -/
theorem restrictScalarsHomologyIso_hom_cocycleClass {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (K : CochainComplex (ModuleCat.{u} R') ℤ) (n : ℤ)
    (w : (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).X n)
    (hwR :
      ((((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).d n (n + 1)).hom w = 0) :
    (restrictScalarsHomologyIso φ K n).hom.hom
        ((Stacks.Cech.Hypercohomology.cocycleClass n (Stacks.Cech.Hypercohomology.toMor w)
          (toMor_comp_d_eq_zero _ hwR)).hom 1) =
      (Stacks.Cech.Hypercohomology.cocycleClass n
          (Stacks.Cech.Hypercohomology.toMor (show K.X n from w))
          (toMor_comp_d_eq_zero (K := K) _
            ((restrictScalars_d_apply φ K n (n + 1) w).symm.trans hwR))).hom 1 := by
  set cR := ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K |>.liftCycles
    (Stacks.Cech.Hypercohomology.toMor w) (n + 1) (by simp) (toMor_comp_d_eq_zero _ hwR)
  set cK := K.liftCycles (Stacks.Cech.Hypercohomology.toMor (show K.X n from w)) (n + 1) (by simp)
    (toMor_comp_d_eq_zero (K := K) _ ((restrictScalars_d_apply φ K n (n + 1) w).symm.trans hwR))
  have hcc : ((K.sc n).mapCyclesIso (ModuleCat.restrictScalars φ)).hom.hom (cR.hom 1) =
      cK.hom 1 := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    have h1 := ConcreteCategory.congr_hom
      ((K.sc n).mapCyclesIso_hom_iCycles (ModuleCat.restrictScalars φ)) (cR.hom 1)
    have h2 := ConcreteCategory.congr_hom
      ((((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj K).liftCycles_i
        (Stacks.Cech.Hypercohomology.toMor w) (n + 1) (by simp) (toMor_comp_d_eq_zero _ hwR)) 1
    have h3 := ConcreteCategory.congr_hom (K.liftCycles_i
      (Stacks.Cech.Hypercohomology.toMor (show K.X n from w)) (n + 1) (by simp)
        (toMor_comp_d_eq_zero (K := K) _
          ((restrictScalars_d_apply φ K n (n + 1) w).symm.trans hwR))) 1
    simp only [ConcreteCategory.comp_apply, Stacks.Cech.Hypercohomology.toMor,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at h2 h3
    exact h1.trans (h2.trans ((one_smul R' (show K.X n from w)).symm.trans h3.symm))
  have h4 := ConcreteCategory.congr_hom
    (StacksDraft.DerivedCategoryHomology.mapCyclesIso_hom_map_homologyπ (K.sc n)
      (ModuleCat.restrictScalars φ)) (cR.hom 1)
  exact h4.symm.trans (congrArg (K.homologyπ n).hom hcc)

/-- The commutative ring structure on the global sections of `p⁻¹𝒪_S`, the coefficients of the
library's Čech cup product on de Rham cohomology. -/
abbrev baseSectionCommRing {X S : Scheme.{u}} (p : X ⟶ S) :
    CommRing (SectionRing (ringSheaf (baseSheaf p)) ⊤) :=
  Stacks.Cech.Refinement.sectionCommRing (baseSheaf p) ⊤

section Slice

attribute [local instance high] baseSectionCommRing

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The wedge product of the relative de Rham complex, as the pairing of the library's Čech cup
product. -/
abbrev deRhamPairing :=
  SheafOfModules.deRhamCechPairing (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))

/-- The component at `Z` of `(sliceExtendXIso p b).hom` sends `x` to an element heterogeneously
equal to `x`. -/
theorem heq_sliceExtendXIso_hom (b : ℕ) (Z : (Over (⊤ : X.Opens))ᵒᵖ)
    (x : ((sliceDeRhamComplexInt p).X (b : ℤ)).obj Z) :
    HEq (((sliceExtendXIso p b).hom.app Z).hom x) x :=
  heq_map_eqToHom_app (sectionsPresheafFunctor ⊤)
    (congrArg (HomologicalComplex.extend.X _) (ComplexShape.embeddingUpNat.r_eq_some rfl)) Z x

/-- The component at `Z` of `(sliceExtendXIso p b).inv` sends `x` to an element heterogeneously
equal to `x`. -/
theorem heq_sliceExtendXIso_inv (b : ℕ) (Z : (Over (⊤ : X.Opens))ᵒᵖ)
    (x : ((sliceDeRhamComplex p).X b).obj Z) :
    HEq (((sliceExtendXIso p b).inv.app Z).hom x) x :=
  heq_map_eqToHom_app (sectionsPresheafFunctor ⊤)
    (congrArg (HomologicalComplex.extend.X _) (ComplexShape.embeddingUpNat.r_eq_some rfl)).symm Z x

/-- **The wedge product on the slice de Rham complex**, read through the identification of the
`ℤ`-indexed complex with the `ℕ`-indexed one. -/
def sliceMul (a b c : ℕ) (h : a + b = c) (Z : (Over (⊤ : X.Opens))ᵒᵖ) :
    ((sliceDeRhamComplex p).X a).obj Z →+ ((sliceDeRhamComplex p).X b).obj Z →+
      ((sliceDeRhamComplex p).X c).obj Z :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => ((sliceExtendXIso p c).hom.app Z).hom
      ((((deRhamPairing p).μ a b c (by omega)).app Z).hom
        (((sliceExtendXIso p a).inv.app Z).hom x ⊗ₜ ((sliceExtendXIso p b).inv.app Z).hom y)))
      (fun y y' => by simp only [map_add, TensorProduct.tmul_add]))
    (fun x x' => by
      ext y
      simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

/-- `sliceMul p a b c h Z x y` is the pairing `deRhamPairing p` of `x` and `y`, transported along
`sliceExtendXIso p`. -/
theorem sliceMul_apply (a b c : ℕ) (h : a + b = c) (Z : (Over (⊤ : X.Opens))ᵒᵖ)
    (x : ((sliceDeRhamComplex p).X a).obj Z) (y : ((sliceDeRhamComplex p).X b).obj Z) :
    sliceMul p a b c h Z x y = ((sliceExtendXIso p c).hom.app Z).hom
      ((((deRhamPairing p).μ a b c (by omega)).app Z).hom
        (((sliceExtendXIso p a).inv.app Z).hom x ⊗ₜ ((sliceExtendXIso p b).inv.app Z).hom y)) :=
  rfl

/-- **The wedge product on the slice de Rham complex is the wedge product of forms.** -/
theorem sliceMul_eq_sectionsMul (a b : ℕ) (Z : (Over (⊤ : X.Opens))ᵒᵖ)
    (x : ((sliceDeRhamComplex p).X a).obj Z) (y : ((sliceDeRhamComplex p).X b).obj Z) :
    sliceMul p a b (a + b) rfl Z x y = sectionsMul p a b Z.unop.left x y := by
  rw [sliceMul_apply]
  refine eq_of_heq ((heq_sliceExtendXIso_hom p (a + b) Z _).trans ?_)
  refine (HEq.trans (heq_of_eq (Stacks.Cech.Hypercohomology.differentialGradedPairing_app_tmul
    (SheafOfModules.deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))) 0 a b _ _ Z _ _))
    ?_)
  refine (heq_gradedCast _ _ _).trans ?_
  refine (SheafOfModules.deRhamDifferentialGradedAlgebra_mul _ _ a b (op Z.unop.left) _ _ x y
    (heq_sliceExtendXIso_inv p a Z x) (heq_sliceExtendXIso_inv p b Z y)).trans ?_
  exact (heq_eqToHom_val_app _ _ _).symm

end Slice

/-! ### The base cochain of a closed form is a cocycle -/

section BaseCocycle

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{u}} {gR : R ⟶ A}
  (D : Stacks.KatzOda.Cech.ChartData (ι := ι) gR) {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (EP : Stacks.KatzOda.Cech.FormsData U D D.ψ D.ψ_ρ P)

omit [Fintype ι] [DecidableEq ι] in
/-- **The base cochain of a closed form is a cocycle** of the total Čech complex. -/
theorem totDTo_totSingle_baseCochain (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
    (hν : Stacks.KatzOda.dForms gR b ν = 0) :
    totDTo U P b (b + 1) rfl (totSingle U P b 0 b (by simp)
      (Stacks.KatzOda.Cech.baseCochain D EP b ν)) = 0 := by
  rw [totDTo_totSingle]
  have h1 : cechD U (P.X b) 0 (Stacks.KatzOda.Cech.baseCochain D EP b ν) = 0 := by
    funext t
    have hj : ∀ j : Fin 2, cres U (P.X b) (Fin.succAbove j) t
        (Stacks.KatzOda.Cech.baseCochain D EP b ν (t ∘ Fin.succAbove j)) =
          (EP.e b t).symm (Stacks.KatzOda.Cech.baseForm D b t ν) := fun j =>
      (EP.e b t).injective ((Stacks.KatzOda.Cech.e_cres_baseCochain D EP b ν 1 t _).trans
        (AddEquiv.apply_symm_apply _ _).symm)
    rw [cechD_apply, Fin.sum_univ_two, hj, hj]
    simp
  have h2 : cochainMap U (P.d b (b + 1)) 0 (Stacks.KatzOda.Cech.baseCochain D EP b ν) = 0 := by
    funext t
    refine (EP.e (b + 1) t).injective ?_
    rw [cochainMap_apply, EP.e_d, Pi.zero_apply, map_zero]
    show Stacks.KatzOda.dForms (D.ψ t) b
      ((EP.e b t) ((EP.e b t).symm (Stacks.KatzOda.Cech.baseForm D b t ν))) = 0
    rw [AddEquiv.apply_symm_apply, Stacks.KatzOda.Cech.dForms_baseForm, hν]
    exact Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_zero _ _ _ _ _
  rw [h1, h2, map_zero, map_zero, smul_zero, add_zero]

end BaseCocycle

/-! ### The elementwise comparison with the library's total Čech complex -/

section Comparison

attribute [local instance high] baseSectionCommRing

variable {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- The comparison of the elementwise total Čech complex of the opens with the one of the slice,
in degree `n`: restriction along the equalities of the Čech intersections. -/
abbrev sliceTot (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n) :
    TotX (coverObject U hU) (sliceDeRhamComplex p) n :=
  overTot U (fun _ => le_top) p.sectionsDeRhamComplex n z

/-- The comparison of Čech cochains of the opens with those of the slice. -/
abbrev sliceCochain (b q : ℕ) (y : Cochain U (p.sectionsDeRhamComplex.X b) q) :
    Cochain (coverObject U hU) ((sliceDeRhamComplex p).X b) q :=
  overCochain U (fun _ => le_top) p.sectionsDeRhamComplex b q y

/-- **The comparison of the elementwise total Čech complex with the library's**, elementwise:
restriction to the slice followed by the inverse of `totalCechIso`. -/
theorem cechIso_hom_f_apply (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n) :
    ((cechIso p U hU).hom.f n).hom z =
      (totalFrom (R := SectionRing (ringSheaf (baseSheaf p)) ⊤) (coverObject U hU)
        (sliceDeRhamComplexInt p) (sliceDeRhamComplex p)
        (sliceExtendXIso p) n).hom (sliceTot p U hU n z) := rfl

/-- **Restricting a cochain from the last vertex commutes with the comparison with the slice.** -/
theorem restrict_cres_last (b r : ℕ) (t : Fin (r + 1) → ι)
    (y : Cochain U (p.sectionsDeRhamComplex.X b) 0) :
    (Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map
        (homOfLE (le_of_eq (interOver_left_eq U (fun _ => le_top) t))).op
        (cres U (p.sectionsDeRhamComplex.X b) (fun _ : Fin 1 => Fin.last r) t
          (y (t ∘ fun _ : Fin 1 => Fin.last r))) =
      cres (coverObject U hU) ((sliceDeRhamComplex p).X b) (fun _ : Fin 1 => Fin.last r) t
        (sliceCochain p U hU b 0 y (t ∘ fun _ : Fin 1 => Fin.last r)) := by
  show (Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map _
      ((Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map
        (interMap U t (fun _ : Fin 1 => Fin.last r)).op (y (t ∘ fun _ : Fin 1 => Fin.last r))) =
    (Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map
      (interMap (coverObject U hU) t (fun _ : Fin 1 => Fin.last r)).left.op
      ((Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map
        (homOfLE (le_of_eq (interOver_left_eq U (fun _ => le_top) _))).op
        (y (t ∘ fun _ : Fin 1 => Fin.last r)))
  have h : (inter (coverObject U hU) t).left ≤ inter U (t ∘ fun _ : Fin 1 => Fin.last r) :=
    (le_of_eq (interOver_left_eq U (fun _ => le_top) t)).trans
      (interMap U t (fun _ : Fin 1 => Fin.last r)).le
  exact (presheaf_map_map_eq _ _ _ (homOfLE h) _).trans
    (presheaf_map_map_eq _ _ _ (homOfLE h) _).symm

/-- `sliceTot` sends the element of the total complex supported on the cochain `y` in bidegree
`(q, b)` to the element supported on `sliceCochain p U hU b q y`. -/
theorem sliceTot_totSingle (n : ℤ) (q b : ℕ) (h : (q : ℤ) + b = n)
    (y : Cochain U (p.sectionsDeRhamComplex.X b) q) :
    sliceTot p U hU n (totSingle U p.sectionsDeRhamComplex n q b h y) =
      totSingle (coverObject U hU) (sliceDeRhamComplex p) n q b h (sliceCochain p U hU b q y) := by
  funext ⟨⟨q', a⟩, hi⟩
  by_cases hqa : q' = q ∧ a = b
  · obtain ⟨rfl, rfl⟩ := hqa
    refine Eq.trans ?_ (totSingle_apply_self _ _ n q' a h _).symm
    exact congrArg (overCochain U (fun _ => le_top) p.sectionsDeRhamComplex a q')
      (totSingle_apply_self U _ n q' a h y)
  · refine Eq.trans ?_ (totSingle_apply_of_ne _ _ n q b h _ q' a hi hqa).symm
    exact (congrArg (overCochain U (fun _ => le_top) p.sectionsDeRhamComplex a q')
      (totSingle_apply_of_ne U _ n q b h y q' a hi hqa)).trans (map_zero _)

end Comparison

/-! ### Multiplication by a form from the base, on the slice -/

section MulTot

attribute [local instance high] baseSectionCommRing

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)

/-- **Multiplication by a form from the base, read on the slice, is right multiplication by its
base cochain** for the wedge product of the slice de Rham complex. -/
theorem sliceTot_mulTot (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    {m N : ℤ} (hN : m + b = N) (z : TotX U (f ≫ g).sectionsDeRhamComplex m) :
    sliceTot (f ≫ g) U hU N (Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
        (formsDataTotal f g U haff) b ν hN z) =
      rightMul (coverObject U hU) (sliceMul (f ≫ g)) b
        (sliceCochain (f ≫ g) U hU b 0 (Stacks.KatzOda.Cech.baseCochain (chartData f g U haff)
          (formsDataTotal f g U haff) b ν)) hN (sliceTot (f ≫ g) U hU m z) := by
  rw [← formsMulDataTotal_toFormsData]
  funext ⟨⟨r, c⟩, hj⟩
  by_cases hc : b ≤ c
  · obtain ⟨a, rfl⟩ : ∃ a, c = a + b := ⟨c - b, by omega⟩
    funext t
    refine Eq.trans ?_ (rightMul_apply_of_le _ _ b _ hN _ r (a + b) hj hc t).symm
    show (interRestrictUp U (fun _ => le_top) ((f ≫ g).sectionsDeRhamComplex.X (a + b)) t).hom
      (Stacks.KatzOda.Cech.mulTotAt _ _ b ν hN z r (a + b) hj t) = _
    rw [Stacks.KatzOda.Cech.mulTotAt_eq _ _ b ν hN z r a (a + b) rfl hj (by omega)]
    have key : ∀ (a' : ℕ) (e : a' = a) (h1 : a' + b = a + b) (h2 : (r : ℤ) + a' = m) Y,
        sliceMul (f ≫ g) a' b (a + b) h1 (op (inter (coverObject U hU) t))
            (sliceTot (f ≫ g) U hU m z ⟨(r, a'), h2⟩ t) Y =
          sliceMul (f ≫ g) a b (a + b) rfl (op (inter (coverObject U hU) t))
            (sliceTot (f ≫ g) U hU m z ⟨(r, a), by omega⟩ t) Y := by
      rintro _ rfl _ _ _
      rfl
    refine Eq.trans ?_ (key _ (by omega) _ _ _).symm
    beta_reduce
    rw [Stacks.KatzOda.Cech.mulAt_eq_mul, sliceMul_eq_sectionsMul]
    refine (sectionsMul_restrict (f ≫ g) a b
      (homOfLE (le_of_eq (interOver_left_eq U (fun _ => le_top) t))) _ _).trans ?_
    congr 1
    exact restrict_cres_last (f ≫ g) U hU b r t _
  · refine Eq.trans ?_ (rightMul_apply_of_lt _ _ b _ hN _ r c hj (by omega)).symm
    show (fun t => (interRestrictUp U (fun _ => le_top) ((f ≫ g).sectionsDeRhamComplex.X c)
      t).hom (Stacks.KatzOda.Cech.mulTotAt _ _ b ν hN z r c hj t)) = 0
    rw [Stacks.KatzOda.Cech.mulTotAt_of_lt _ _ b ν hN z r c hj (by omega)]
    funext t
    exact map_zero _

end MulTot


/-! ### The cup product of Čech classes on de Rham cohomology -/

section CupClasses

attribute [local instance high] baseSectionCommRing

open Stacks.Cech.Hypercohomology (cech cechClass cocycleClass toMor unitModule cechCup cup
  cup_eq cechCupClass_eq unitTensor toMor_comp toMor_apply_one_eq)

variable {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- The library's total Čech complex of the relative de Rham complex. -/
abbrev cechDeRham := (cech (baseSheaf p) U hU).obj (deRhamPlus p).obj

/-- The comparison of the two models of the de Rham cohomology. -/
abbrev hIso (n : ℤ) :=
  SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n

/-- **The cup product of the classes of two Čech cocycles is the class of their Čech cup
product.** -/
theorem deRhamCup_cechClass [IsAffineHom (pullback.diagonal (terminal.from X))] (m b N : ℤ)
    (h : m + b = N) (a : unitModule _ ⟶ (cechDeRham p U hU).X m)
    (ha : a ≫ (cechDeRham p U hU).d m (m + 1) = 0) (w : unitModule _ ⟶ (cechDeRham p U hU).X b)
    (hw : w ≫ (cechDeRham p U hU).d b (b + 1) = 0) :
    Scheme.Hom.deRhamCup p m b N h
        ((hIso p m).hom.hom (cechClass (baseSheaf p) U hU (deRhamPlus p) m
          (cocycleClass m a ha (1 : SectionRing (ringSheaf (baseSheaf p)) ⊤))))
        ((hIso p b).hom.hom (cechClass (baseSheaf p) U hU (deRhamPlus p) b
          (cocycleClass b w hw (1 : SectionRing (ringSheaf (baseSheaf p)) ⊤)))) =
      (hIso p N).hom.hom (cechClass (baseSheaf p) U hU (deRhamPlus p) N
        (cocycleClass N (unitTensor (baseSheaf p) ≫
          Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ m b N h a w ≫
            (cechCup (baseSheaf p) U hU (deRhamPairing p)).f N)
          (by rw [Category.assoc,
            Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ m b N h a w ha hw,
            comp_zero]) (1 : SectionRing (ringSheaf (baseSheaf p)) ⊤))) := by
  show (hIso p N).hom.hom (cup _ _ _ (deRhamPairing p) m b N h
      ((hIso p m).inv.hom ((hIso p m).hom.hom _)) ((hIso p b).inv.hom ((hIso p b).hom.hom _))) = _
  refine congrArg (fun t => (hIso p N).hom.hom t) ?_
  refine (congrArg₂ (cup _ _ _ (deRhamPairing p) m b N h) (Iso.hom_inv_id_apply _ _)
    (Iso.hom_inv_id_apply _ _)).trans ?_
  convert (Stacks.Cech.Hypercohomology.cup_cechClass_cocycleClass (O := baseSheaf p) U hU
    (Scheme.Hom.cechComputes_deRhamComplexPlus p) (Scheme.Hom.cechComputes_deRhamComplexPlus p)
    (deRhamPairing p) m b N h a ha w hw) using 1

end CupClasses

section Classes

open Stacks.Cech.Hypercohomology (cech cechClass cocycleClass toMor unitModule cechCup cup
  cup_eq cechCupClass_eq unitTensor toMor_comp toMor_apply_one_eq)

variable {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- The comparison `Θ` of the elementwise total Čech complex with the library's, in degree `n`. -/
abbrev Θ (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n) : (cechDeRham p U hU).X n :=
  ((cechIso p U hU).hom.f n).hom z

/-- The comparison `Θ` commutes with the differentials. -/
theorem Θ_d (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n) :
    ((((ModuleCat.restrictScalars (baseRingHom p)).mapHomologicalComplex _).obj
        (cechDeRham p U hU)).d n (n + 1)).hom (Θ p U hU n z) =
      Θ p U hU (n + 1) (((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom z) := by
  have h := ConcreteCategory.congr_hom ((cechIso p U hU).hom.comm n (n + 1)) z
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- `classMap p U hU n` is the homology map of `cechIso p U hU`, followed by
`restrictScalarsHomologyIso`, the Čech class map and `hIso p n`. -/
theorem classMap_apply (n : ℤ) (c : (cechTot U p.sectionsDeRhamComplex).homology n) :
    letI := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤
    (classMap p U hU n).hom c =
      (hIso p n).hom.hom ((cechClass (baseSheaf p) U hU (deRhamPlus p) n).hom
        ((restrictScalarsHomologyIso (baseRingHom p) _ n).hom.hom
          ((HomologicalComplex.homologyMap (cechIso p U hU).hom n).hom c))) :=
  rfl

/-- The comparison `Θ` sends a cocycle of the elementwise total Čech complex to a cocycle. -/
theorem Θ_cocycle (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n)
    (hz : ((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom z = 0) :
    ((((ModuleCat.restrictScalars (baseRingHom p)).mapHomologicalComplex _).obj
        (cechDeRham p U hU)).d n (n + 1)).hom (Θ p U hU n z) = 0 :=
  (Θ_d p U hU n z).trans (by simp only [hz]; exact map_zero _)

/-- The image under `classMap` of the class of a cocycle `z` is the image under `hIso` of the Čech
class of the cocycle `Θ p U hU n z`. -/
theorem classMap_cocycleClass (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n)
    (hz : ((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom z = 0) :
    (classMap p U hU n).hom ((cocycleClass n (toMor z) (toMor_comp_d_eq_zero _ hz)).hom 1) =
      (hIso p n).hom.hom ((cechClass (baseSheaf p) U hU (deRhamPlus p) n).hom
        ((cocycleClass n (toMor (Θ p U hU n z)) (toMor_comp_d_eq_zero (K := cechDeRham p U hU) _
          ((restrictScalars_d_apply (baseRingHom p) _ n (n + 1) _).symm.trans
            (Θ_cocycle p U hU n z hz)))).hom 1)) := by
  let := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤
  have h1 := congrArg (fun φ => φ.hom 1)
    (Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap (cechIso p U hU).hom n (toMor z)
      (toMor_comp_d_eq_zero _ hz))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Stacks.Cech.Hypercohomology.toMor_comp]
    at h1
  rw [classMap_apply, h1]
  congr 2
  exact restrictScalarsHomologyIso_hom_cocycleClass (baseRingHom p) _ n _ (Θ_cocycle p U hU n z hz)

end Classes


/-! ### Multiplication by a form from the base is the Čech cup product -/

section CupMulTot

attribute [local instance high] baseSectionCommRing

open Stacks.Cech.Hypercohomology (cech cechCup toMor unitModule unitTensor)

/-- The coefficient pairing of the library's cup product is the wedge product of the slice de
Rham complex. -/
theorem sliceExtendXIso_deRhamPairing {X S : Scheme.{u}} (p : X ⟶ S) (a b : ℕ)
    (V : (Over (⊤ : X.Opens))ᵒᵖ) (x : ((sliceDeRhamComplexInt p).X a).obj V)
    (y : ((sliceDeRhamComplexInt p).X b).obj V) :
    ((sliceExtendXIso p (a + b)).hom.app V).hom
        ((((deRhamPairing p).μ a b (a + b) rfl).app V).hom (x ⊗ₜ y)) =
      sliceMul p a b (a + b) rfl V (((sliceExtendXIso p a).hom.app V).hom x)
        (((sliceExtendXIso p b).hom.app V).hom y) := by
  rw [sliceMul_apply, Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply]
  rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)

/-- The base cochain of a form, as an element of the elementwise total Čech complex. -/
abbrev baseTot (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g))) :
    TotX U (f ≫ g).sectionsDeRhamComplex b :=
  totSingle U _ b 0 b (by simp)
    (Stacks.KatzOda.Cech.baseCochain (chartData f g U haff) (formsDataTotal f g U haff) b ν)

/-- `Θ` of the product of `z` with the form `ν` is the image under `totalFrom` of the right
multiplication of `sliceTot z` by the base cochain of `ν` on the slice. -/
theorem Θ_mulTot_eq (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    {m N : ℤ} (hN : m + b = N) (z : TotX U (f ≫ g).sectionsDeRhamComplex m) :
    Θ (f ≫ g) U hU N (Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
        (formsDataTotal f g U haff) b ν hN z) =
      (totalFrom (R := SectionRing (ringSheaf (baseSheaf (f ≫ g))) ⊤) (coverObject U hU)
        (sliceDeRhamComplexInt (f ≫ g)) (sliceDeRhamComplex (f ≫ g)) (sliceExtendXIso (f ≫ g))
          N).hom (rightMul (coverObject U hU) (sliceMul (f ≫ g)) b
            (sliceCochain (f ≫ g) U hU b 0 (Stacks.KatzOda.Cech.baseCochain (chartData f g U haff)
              (formsDataTotal f g U haff) b ν)) hN (sliceTot (f ≫ g) U hU m z)) :=
  (cechIso_hom_f_apply (f ≫ g) U hU N _).trans (congrArg _
    (sliceTot_mulTot f g U haff hU b ν hN z))

/-- The Čech cup product of `x` and `y` on the slice is the same whether the total Čech complex
is formed from `sliceDeRhamComplexInt p` or from the sections complex of `deRhamPlus p`. -/
theorem cup_spelling_eq {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens)
    (hU : ⊤ = ⨆ i, U i) (m b N : ℤ) (hN : m + b = N)
    (x : ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
      (SectionRing (ringSheaf (baseSheaf p)) ⊤)).obj (sliceDeRhamComplexInt p)).X m)
    (y : ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
      (SectionRing (ringSheaf (baseSheaf p)) ⊤)).obj (sliceDeRhamComplexInt p)).X b) :
    (ιTot (coverObject U hU) (sliceDeRhamComplexInt p) (sliceDeRhamComplexInt p) m b N hN ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (deRhamPairing p)).f N).hom (tmulHom x y) =
      (ιTot (coverObject U hU) ((Stacks.Cech.Refinement.sectionsComplex (baseSheaf p)).obj
          (deRhamPlus p).obj) ((Stacks.Cech.Refinement.sectionsComplex (baseSheaf p)).obj
          (deRhamPlus p).obj) m b N hN ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (deRhamPairing p)).f N).hom
        (tmulHom (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
            (SectionRing (ringSheaf (baseSheaf p)) ⊤)).obj
              ((Stacks.Cech.Refinement.sectionsComplex (baseSheaf p)).obj (deRhamPlus p).obj)).X m
            from x)
          (show ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
            (SectionRing (ringSheaf (baseSheaf p)) ⊤)).obj
              ((Stacks.Cech.Refinement.sectionsComplex (baseSheaf p)).obj (deRhamPlus p).obj)).X b
            from y)) :=
  rfl

/-- `Θ` of the product of `z` with the form `ν` is the Čech cup product on the slice of the image
of `z` with the image of the base cochain of `ν`. -/
theorem Θ_mulTot_eq_cup (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    {m N : ℤ} (hN : m + b = N) (z : TotX U (f ≫ g).sectionsDeRhamComplex m) :
    Θ (f ≫ g) U hU N (Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
        (formsDataTotal f g U haff) b ν hN z) =
      (ιTot (coverObject U hU) (sliceDeRhamComplexInt (f ≫ g)) (sliceDeRhamComplexInt (f ≫ g))
          m b N hN ≫ (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
            (deRhamPairing (f ≫ g))).f N).hom
        (tmulHom ((totalFrom (R := SectionRing (ringSheaf (baseSheaf (f ≫ g))) ⊤)
            (coverObject U hU) (sliceDeRhamComplexInt (f ≫ g)) (sliceDeRhamComplex (f ≫ g))
            (sliceExtendXIso (f ≫ g)) m).hom (sliceTot (f ≫ g) U hU m z))
          ((totalFrom (R := SectionRing (ringSheaf (baseSheaf (f ≫ g))) ⊤)
            (coverObject U hU) (sliceDeRhamComplexInt (f ≫ g)) (sliceDeRhamComplex (f ≫ g))
            (sliceExtendXIso (f ≫ g)) b).hom (totSingle (coverObject U hU)
              (sliceDeRhamComplex (f ≫ g)) b 0 b (by simp) (sliceCochain (f ≫ g) U hU b 0
                (Stacks.KatzOda.Cech.baseCochain (chartData f g U haff)
                  (formsDataTotal f g U haff) b ν))))) :=
  (Θ_mulTot_eq f g U haff hU b ν hN z).trans (totalFrom_rightMul (coverObject U hU)
    (sliceMul (f ≫ g)) (sliceExtendXIso (f ≫ g)) (sliceExtendXIso (f ≫ g))
    (sliceExtendXIso (f ≫ g)) (deRhamPairing (f ≫ g)) (sliceExtendXIso_deRhamPairing (f ≫ g))
    (isZero_sliceDeRhamComplexInt_X (f ≫ g)) b hN _ _)

/-- **The library's Čech cup product of the comparisons of two cochains**, the second of Čech
degree `0`, is the generic Čech cup product of their images in the slice. -/
theorem cup_Θ_eq {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens)
    (hU : ⊤ = ⨆ i, U i) (b : ℕ) {m N : ℤ} (hN : m + b = N) (z : TotX U p.sectionsDeRhamComplex m)
    (y : Cochain U (p.sectionsDeRhamComplex.X b) 0) :
    (unitTensor (baseSheaf p) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ m b N hN
          (toMor (Θ p U hU m z)) (toMor (Θ p U hU b (totSingle U _ b 0 b (by simp) y))) ≫
        (cechCup (baseSheaf p) U hU (deRhamPairing p)).f N).hom 1 =
      (ιTot (coverObject U hU) (sliceDeRhamComplexInt p) (sliceDeRhamComplexInt p) m b N hN ≫
        (Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) _
          (deRhamPairing p)).f N).hom
        (tmulHom ((totalFrom (R := SectionRing (ringSheaf (baseSheaf p)) ⊤) (coverObject U hU)
            (sliceDeRhamComplexInt p) (sliceDeRhamComplex p) (sliceExtendXIso p) m).hom
              (sliceTot p U hU m z))
          ((totalFrom (R := SectionRing (ringSheaf (baseSheaf p)) ⊤) (coverObject U hU)
            (sliceDeRhamComplexInt p) (sliceDeRhamComplex p) (sliceExtendXIso p) b).hom
              (sliceTot p U hU b (totSingle U _ b 0 b (by simp) y)))) :=
  Stacks.Cech.Hypercohomology.unitTensor_cupPair_toMor_cechCup
      (baseSheaf p) U hU (deRhamPairing p) m b N hN _ _

/-- **Multiplication by a form from the base is the Čech cup product with its base cochain**, on
the library's total Čech complex. -/
theorem Θ_mulTot (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    {m N : ℤ} (hN : m + b = N) (z : TotX U (f ≫ g).sectionsDeRhamComplex m) :
    Θ (f ≫ g) U hU N (Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
        (formsDataTotal f g U haff) b ν hN z) =
      (unitTensor (baseSheaf (f ≫ g)) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ m b N hN
          (toMor (Θ (f ≫ g) U hU m z)) (toMor (Θ (f ≫ g) U hU b (baseTot f g U haff b ν))) ≫
        (cechCup (baseSheaf (f ≫ g)) U hU (deRhamPairing (f ≫ g))).f N).hom 1 := by
  refine (Θ_mulTot_eq_cup f g U haff hU b ν hN z).trans (Eq.trans ?_
    (cup_Θ_eq (f ≫ g) U hU b hN z _).symm)
  exact congrArg _ (congrArg (tmulHom _) (congrArg _ (sliceTot_totSingle (f ≫ g) U hU b 0 b
    (by simp) (Stacks.KatzOda.Cech.baseCochain (chartData f g U haff) (formsDataTotal f g U haff)
      b ν)).symm))

/-- `toMor` of `Θ` of the product of `z` with the form `ν` is the cup product of `toMor (Θ z)`
with `toMor (Θ (baseTot f g U haff b ν))`. -/
theorem toMor_Θ_mulTot (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    {m N : ℤ} (hN : m + b = N) (z : TotX U (f ≫ g).sectionsDeRhamComplex m) :
    toMor (Θ (f ≫ g) U hU N (Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
        (formsDataTotal f g U haff) b ν hN z)) =
      unitTensor (baseSheaf (f ≫ g)) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules _) _ _ m b N hN
          (toMor (Θ (f ≫ g) U hU m z)) (toMor (Θ (f ≫ g) U hU b (baseTot f g U haff b ν))) ≫
        (cechCup (baseSheaf (f ≫ g)) U hU (deRhamPairing (f ≫ g))).f N :=
  (congrArg toMor (Θ_mulTot f g U haff hU b ν hN z)).trans
    (Stacks.Cech.Hypercohomology.toMor_apply_one_eq _)

end CupMulTot

/-! ### The cup product with a closed form from the base on de Rham cohomology -/

section CupTheorem

open Stacks.Cech.Hypercohomology (cocycleClass toMor)

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)

/-- The product of a cocycle `z` with a closed form `ν` from the base is a cocycle. -/
theorem mulTot_cocycle (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    (hν : Stacks.KatzOda.dForms (baseMap g) b ν = 0) (m : ℕ)
    (z : TotX U (f ≫ g).sectionsDeRhamComplex m)
    (hz : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d m (m + 1)).hom z = 0) :
    ((cechTot U (f ≫ g).sectionsDeRhamComplex).d ((m : ℤ) + b) ((m : ℤ) + b + 1)).hom
      (Stacks.KatzOda.Cech.mulTot (chartData f g U haff) (formsDataTotal f g U haff) b ν rfl z) =
        0 := by
  rw [cechTot_d_apply' U _ rfl, Stacks.KatzOda.Cech.totDTo_mulTot, ← cechTot_d_apply' U _ rfl, hz,
    hν, Stacks.KatzOda.Cech.mulTot_zero, Stacks.KatzOda.Cech.mulTot_zero_form, smul_zero,
    add_zero]

/-- The base cochain `baseTot f g U haff b ν` of a closed form `ν` is a cocycle. -/
theorem baseTot_cocycle (b : ℕ) (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    (hν : Stacks.KatzOda.dForms (baseMap g) b ν = 0) :
    ((cechTot U (f ≫ g).sectionsDeRhamComplex).d b (b + 1)).hom (baseTot f g U haff b ν) = 0 := by
  rw [cechTot_d_apply' U _ rfl]
  exact totDTo_totSingle_baseCochain _ _ b ν hν

/-- **The class of `x ∧ ν` is the cup product of the classes of `x` and of `ν`** ([Stacks,
Tag 0FUM], facts (3)--(5) of its proof): for a cocycle `x` of degree `m` of
`K = Tot(Č(U, Ω^•_{X/S}))` and a closed form `ν` of degree `b` of `Γ(Y, 𝒪_Y)` over `Γ(S, 𝒪_S)`,
the class in `H^{m+b}_{dR}(X/S)` of the product `x ∧ ν` is the cup product of the class of `x`
with the class of the Čech `0`-cocycle of the pull-backs of `ν`. -/
theorem classMap_mulTot [IsAffineHom (pullback.diagonal (terminal.from X))] (b : ℕ)
    (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)))
    (hν : Stacks.KatzOda.dForms (baseMap g) b ν = 0) (m : ℕ)
    (z : TotX U (f ≫ g).sectionsDeRhamComplex m)
    (hz : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d m (m + 1)).hom z = 0) :
    (classMap (f ≫ g) U hU ((m : ℤ) + b)).hom ((cocycleClass ((m : ℤ) + b)
        (toMor (Stacks.KatzOda.Cech.mulTot (chartData f g U haff) (formsDataTotal f g U haff) b ν
          rfl z)) (toMor_comp_d_eq_zero _ (mulTot_cocycle f g U haff b ν hν m z hz))).hom 1) =
      Scheme.Hom.deRhamCup (f ≫ g) m b ((m : ℤ) + b) rfl
        ((classMap (f ≫ g) U hU m).hom
          ((cocycleClass m (toMor z) (toMor_comp_d_eq_zero _ hz)).hom 1))
        ((classMap (f ≫ g) U hU b).hom ((cocycleClass b (toMor (baseTot f g U haff b ν))
          (toMor_comp_d_eq_zero _ (baseTot_cocycle f g U haff b ν hν))).hom 1)) := by
  rw [classMap_cocycleClass (f ≫ g) U hU _ _ (mulTot_cocycle f g U haff b ν hν m z hz),
    classMap_cocycleClass (f ≫ g) U hU _ _ hz,
    classMap_cocycleClass (f ≫ g) U hU _ _ (baseTot_cocycle f g U haff b ν hν)]
  refine Eq.trans ?_ (deRhamCup_cechClass (f ≫ g) U hU m b _ rfl _ _ _ _).symm
  simp only [toMor_Θ_mulTot f g U haff hU b ν rfl z]
  rfl

end CupTheorem

end AlgebraicGeometry.DeRhamKatzOdaCech

end
