module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetFromStepQuotient
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepTargetQuotient
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeSummandLeibnizModStep
public import StacksFrontier.AlgebraicGeometry.DeRham.PulledBackFormsComparisonEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The square of Section 0FMK above the cut

For `f : X ⟶ Y` over `S`, a cut `k` and `n = k + 1 + j`, this file proves that the degreewise
comparison `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` of the `k`-th graded piece of the
filtration of `Ω^•_{X/S}` with the target complex `f^{-1}Ω^k_{Y/S}[-k] ⊗ Ω^•_{X/Y}` commutes
with the differentials in degree `n`: the square above the cut of [Stacks, Section 0FMK].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage

universe u

/-! ### Equations left to the kernel

The tactics `kernel_rfl` and `kernel_hrfl` close an equation `a = b` (resp. `HEq a b`) by
`Eq.refl a` (resp. `HEq.refl a`) without unifying `a` with `b` in the elaborator: the definitional
check is made by the kernel when the declaration is added, which rejects a wrong use. -/

open Lean Elab Tactic Meta in
/-- Close a goal `a = b` with `Eq.refl a`, leaving the check that `a` and `b` are definitionally
equal to the kernel. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  match ty.eq? with
  | some (_, a, _) =>
    g.assign (← mkExpectedTypeHint (← mkEqRefl a) ty)
    replaceMainGoal []
  | none => throwError "kernel_rfl: the goal is not an equation"

open Lean Elab Tactic Meta in
/-- Close a goal `HEq a b` with `HEq.refl a`, leaving the check that `a` and `b` (and their types)
are definitionally equal to the kernel. -/
elab "kernel_hrfl" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  match ty.heq? with
  | some (_, a, _, _) =>
    g.assign (← mkExpectedTypeHint (← mkHEqRefl a) ty)
    replaceMainGoal []
  | none => throwError "kernel_hrfl: the goal is not a heterogeneous equation"

namespace Stacks.CategoryTheory

/-- **The comparison of two presentations of a subobject, followed by its inclusion**, at
generic objects: for a monomorphism `ι : F ⟶ K'`, an isomorphism `e : K' ≅ R.obj Z` and a
subobject `Q` of `Z` whose transport along `R` and `e⁻¹` contains `ι`, the composite of the four
identifications with `R.map Q.arrow` is `ι ≫ e.hom`. -/
theorem underlyingIso_inv_comp_ofLE_comp_mapObjIso_comp_arrow {C D : Type*}
    [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Category D] (R : D ⥤ C)
    [R.PreservesMonomorphisms] {F K' : C} {Z : D} (ι : F ⟶ K') (hι : Mono ι) (e : K' ≅ R.obj Z)
    (Q : Subobject Z)
    (h : Subobject.mk ι ≤ (Subobject.map e.inv).obj ((mapSubobjects R Z).obj Q)) :
    (@Subobject.underlyingIso _ _ _ _ ι hι).inv ≫ Subobject.ofLE _ _ h ≫
        (Subobject.mapObjIso e.inv ((mapSubobjects R Z).obj Q)).hom ≫
          (Stacks.GradedPieceImage.mapSubobjectsObjIso R Q).hom ≫ R.map Q.arrow = ι ≫ e.hom := by
  have h1 : R.map Q.arrow = (Stacks.GradedPieceImage.mapSubobjectsObjIso R Q).inv ≫
      ((mapSubobjects R Z).obj Q).arrow :=
    (Stacks.GradedPieceImage.mapSubobjectsObjIso_inv_arrow R Q).symm
  have h2 : ((mapSubobjects R Z).obj Q).arrow =
      ((mapSubobjects R Z).obj Q).arrow ≫ e.inv ≫ e.hom := by simp
  rw [h1, Iso.hom_inv_id_assoc, h2, Subobject.mapObjIso_hom_arrow_assoc,
    Subobject.ofLE_arrow_assoc, Subobject.underlyingIso_arrow_assoc]

/-- **A morphism whose image is a given subobject factors through it by an epimorphism**, at
generic objects of an abelian category, with the subobject presented as `ι` transported along
an isomorphism `e`: if `mk ι = e⁻¹(X)` and `imageSubobject S = X`, then `S = z ≫ ι ≫ e.hom` for
an epimorphism `z`. -/
theorem exists_epi_comp_comp_hom_eq {C : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Abelian C] {P F K' K : C} (ι : F ⟶ K') (hι : Mono ι) (e : K' ≅ K)
    (X : Subobject K) (S : P ⟶ K) (h : @Subobject.mk _ _ _ _ ι hι = (Subobject.map e.inv).obj X)
    (hS : imageSubobject S = X) : ∃ z : P ⟶ F, Epi z ∧ z ≫ ι ≫ e.hom = S := by
  have h' : imageSubobject (S ≫ e.inv) = @Subobject.mk _ _ _ _ ι hι := by
    rw [h, ← hS]
    exact (Stacks.CategoryTheory.map_imageSubobject S e.inv).symm
  refine ⟨factorThruImageSubobject (S ≫ e.inv) ≫ (Subobject.isoOfEq _ _ h').hom ≫
    (@Subobject.underlyingIso _ _ _ _ ι hι).hom, inferInstance, ?_⟩
  simp [Subobject.underlyingIso_hom_comp_eq_mk_assoc, Subobject.isoOfEq_hom]

/-- **A chain map followed by a degreewise identification**, at generic objects: if `ι` commutes
with the differentials (`h₁`) and `e₀`, `e₁` carry `d_X` to `d_Ω` (`h₂`), then
`d_F ≫ ι₁ ≫ e₁ = (ι₀ ≫ e₀) ≫ d_Ω`. -/
theorem comp_comp_hom_eq_of_comm {C : Type*} [_root_.CategoryTheory.Category C]
    {F₀ F₁ K₀ K₁ Ω₀ Ω₁ : C} (dF : F₀ ⟶ F₁) (ι₀ : F₀ ⟶ K₀) (ι₁ : F₁ ⟶ K₁) (dX : K₀ ⟶ K₁)
    (e₀ : K₀ ≅ Ω₀) (e₁ : K₁ ≅ Ω₁) (dΩ : Ω₀ ⟶ Ω₁) (h₁ : ι₀ ≫ dX = dF ≫ ι₁)
    (h₂ : e₀.inv ≫ dX ≫ e₁.hom = dΩ) : dF ≫ ι₁ ≫ e₁.hom = (ι₀ ≫ e₀.hom) ≫ dΩ := by
  rw [← h₂, ← reassoc_of% h₁]
  simp

/-- A morphism killed by `π`, followed by a transport along a reflexive equation, is still killed
by `π`. -/
theorem comp_eqToHom_comp_eq_zero {C : Type*} [_root_.CategoryTheory.Category C]
    [Limits.HasZeroMorphisms C] {X Y Z : C} (a : X ⟶ Y) (π : Y ⟶ Z) (ha : a ≫ π = 0)
    (h : Y = Y) : (a ≫ eqToHom h) ≫ π = 0 := by
  simp [ha]

/-- The first reading of the square above the cut, at generic objects: an epimorphism `z` onto
the step, followed by the projection onto the graded piece and the comparison, is the source
`E`, by the monomorphy of `M`. -/
theorem comp_comp_eq_of_mono_readings {C : Type*} [_root_.CategoryTheory.Category C]
    {Q F G T V U W : C} (z : Q ⟶ F) (p : F ⟶ G) (i : G ⟶ T) (M : T ⟶ V) (hM : Mono M)
    (st : F ⟶ U) (ar : U ⟶ W) (π : W ⟶ V) (ιe : F ⟶ W) (E : Q ⟶ T) (S : Q ⟶ W)
    (hL : p ≫ i ≫ M = st ≫ ar ≫ π) (hSA : st ≫ ar = ιe) (hstar : E ≫ M = S ≫ π)
    (hZ : z ≫ ιe = S) : z ≫ p ≫ i = E := by
  refine hM.right_cancellation _ _ ?_
  rw [Category.assoc, Category.assoc, hL, hstar, ← hZ, ← hSA]
  simp only [Category.assoc]

/-- The left-hand side of the square above the cut on the source, at generic objects of a
preadditive category: the differential `hE` of `E` (its sign the composite with `ε • 𝟙`) and the
reading `hstar'` of `E'`. -/
theorem comp_d_comp_eq_smul_of_readings {C : Type*} [_root_.CategoryTheory.Category C]
    [Preadditive C] {Q Q' T T' V' W' : C} (E : Q ⟶ T) (dT : T ⟶ T') (M' : T' ⟶ V')
    (δ : Q ⟶ Q') (E' : Q' ⟶ T') (S' : Q' ⟶ W') (π' : W' ⟶ V') (ε : ℤ)
    (hE : E ≫ dT = δ ≫ E' ≫ (ε • 𝟙 T')) (hstar' : E' ≫ M' = S' ≫ π') :
    E ≫ dT ≫ M' = ε • (δ ≫ S' ≫ π') := by
  rw [reassoc_of% hE]
  simp only [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, hstar']

/-- The right-hand side of the square above the cut on the source, at generic objects: the
reading `hL'` of the graded-piece side, the identification `hSA'` of the inclusion of the step,
its chain-map property `hCM` and the factorization `hZ`. -/
theorem comp_d_comp_eq_of_readings {C : Type*} [_root_.CategoryTheory.Category C]
    {Q F F' G' T' V' U' W W' : C} (z : Q ⟶ F) (dF : F ⟶ F') (p' : F' ⟶ G') (i' : G' ⟶ T')
    (M' : T' ⟶ V') (st' : F' ⟶ U') (ar' : U' ⟶ W') (π' : W' ⟶ V') (ιe : F ⟶ W)
    (ιe' : F' ⟶ W') (dW : W ⟶ W') (S : Q ⟶ W)
    (hL' : p' ≫ i' ≫ M' = st' ≫ ar' ≫ π') (hSA' : st' ≫ ar' = ιe')
    (hCM : dF ≫ ιe' = ιe ≫ dW) (hZ : z ≫ ιe = S) :
    z ≫ dF ≫ p' ≫ i' ≫ M' = S ≫ dW ≫ π' := by
  rw [hL', ← Category.assoc st', hSA', reassoc_of% hCM, ← hZ]
  simp only [Category.assoc]

/-- **The square above the cut, at generic objects**: for an epimorphism `z` and a monomorphism
`M'`, the readings `h₁`, `h₂`, `h₃` and the equation `h₄` give `p ≫ i ≫ dT = dF ≫ p' ≫ i'`. -/
theorem comp_comp_d_eq_of_cancel {C : Type*} [_root_.CategoryTheory.Category C]
    {Q F F' G G' T T' V' : C} (z : Q ⟶ F) (hz : Epi z) (p : F ⟶ G) (i : G ⟶ T) (dT : T ⟶ T')
    (dF : F ⟶ F') (p' : F' ⟶ G') (i' : G' ⟶ T') (M' : T' ⟶ V') (hM' : Mono M') (E : Q ⟶ T)
    (L R : Q ⟶ V') (h₁ : z ≫ p ≫ i = E) (h₂ : E ≫ dT ≫ M' = L)
    (h₃ : z ≫ dF ≫ p' ≫ i' ≫ M' = R) (h₄ : R = L) :
    p ≫ (i ≫ dT) = dF ≫ p' ≫ i' := by
  refine hz.left_cancellation _ _ (hM'.right_cancellation _ _ ?_)
  simp only [Category.assoc]
  rw [h₃, h₄, ← h₂, ← h₁]
  simp only [Category.assoc]

/-- A differential with its sign written as the composite with `ε • 𝟙`, followed by `M'`. -/
theorem comp_comp_eq_smul_of_eq_comp_smul_id {C : Type*} [_root_.CategoryTheory.Category C]
    [Preadditive C] {Q Q' T T' V' : C} (E : Q ⟶ T) (dT : T ⟶ T') (M' : T' ⟶ V')
    (δ : Q ⟶ Q') (E' : Q' ⟶ T') (ε : ℤ) (hE : E ≫ dT = δ ≫ E' ≫ (ε • 𝟙 T')) :
    E ≫ dT ≫ M' = ε • (δ ≫ E' ≫ M') :=
  comp_d_comp_eq_smul_of_readings E dT M' δ E' E' M' ε hE rfl

/-- An equation `E ≫ dT = δ ≫ E' ≫ σ`, followed by `M'`. -/
theorem comp_comp_eq_of_eq_comp_comp {C : Type*} [_root_.CategoryTheory.Category C]
    {Q Q' T T' V' : C} (E : Q ⟶ T) (dT : T ⟶ T') (M' : T' ⟶ V')
    (δ : Q ⟶ Q') (E' : Q' ⟶ T') (σ : T' ⟶ T') (hE : E ≫ dT = δ ≫ E' ≫ σ) :
    E ≫ dT ≫ M' = δ ≫ E' ≫ σ ≫ M' := by
  rw [reassoc_of% hE]

/-- The sign of a differential, written as the composite with `σ = ε • 𝟙`, pulled out after a
reading `hstar'` of `E'`. -/
theorem comp_comp_comp_eq_smul_of_eq_smul_id {C : Type*} [_root_.CategoryTheory.Category C]
    {_ : Preadditive C} {Q Q' T' V' : C} (x : Q ⟶ Q') (E' : Q' ⟶ T') (σ : T' ⟶ T')
    (M' : T' ⟶ V') {W' : C} (S' : Q' ⟶ W') (π' : W' ⟶ V') (ε : ℤ) (hσ : σ = ε • 𝟙 T')
    (hstar : x ≫ E' ≫ M' = x ≫ S' ≫ π') :
    x ≫ E' ≫ σ ≫ M' = ε • (x ≫ S' ≫ π') := by
  rw [hσ, Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, hstar]

/-- A sign written as the composite with `ε • 𝟙`, moved out to the front. -/
theorem eq_smul_comp_of_eq_comp_smul_id {C : Type*} [_root_.CategoryTheory.Category C]
    {_ : Preadditive C} {Q Q' T T' : C} (E : Q ⟶ T) (dT : T ⟶ T') (δ : Q ⟶ Q') (E' : Q' ⟶ T')
    (ε : ℤ) (hE : E ≫ dT = δ ≫ E' ≫ (ε • 𝟙 T')) : E ≫ dT = ε • (δ ≫ E') := by
  rw [hE, Preadditive.comp_zsmul, Category.comp_id, Preadditive.comp_zsmul]

/-- `E ≫ dT = ε • (δ ≫ E')` followed by `M'`, and `E'` read through `M'`. -/
theorem comp_comp_eq_smul_of_eq_smul {C : Type*} [_root_.CategoryTheory.Category C]
    {_ : Preadditive C} {Q Q' T T' V' W' : C} (E : Q ⟶ T) (dT : T ⟶ T') (M' : T' ⟶ V')
    (δ : Q ⟶ Q') (E' : Q' ⟶ T') (S' : Q' ⟶ W') (π' : W' ⟶ V') (ε : ℤ)
    (hE : E ≫ dT = ε • (δ ≫ E')) (hstar : δ ≫ E' ≫ M' = δ ≫ S' ≫ π') :
    E ≫ dT ≫ M' = ε • (δ ≫ S' ≫ π') := by
  rw [reassoc_of% hE, Preadditive.zsmul_comp, Category.assoc, hstar]

/-- A sign written as the composite with `σ = ε • 𝟙`, pulled out. -/
theorem comp_comp_comp_eq_smul_of_eq_smul_id' {C : Type*} [_root_.CategoryTheory.Category C]
    [Preadditive C] {Q Q' T' V' : C} (x : Q ⟶ Q') (E' : Q' ⟶ T') (σ : T' ⟶ T')
    (M' : T' ⟶ V') (ε : ℤ) (hσ : σ = ε • 𝟙 T') :
    x ≫ E' ≫ σ ≫ M' = ε • (x ≫ E' ≫ M') :=
  comp_comp_comp_eq_smul_of_eq_smul_id x E' σ M' E' M' ε hσ rfl

/-- **The sign bridge of the square above the cut**, at generic objects of a preadditive category.
The Leibniz rule `hL` reads `X = ε • (dL ≫ (aL ≫ bL ≫ xL) ≫ v)` with its scalar action `instL`
(which `hiL` identifies with the one of the category), the reading `hstar` of `E₁` after `dE` is
`dE ≫ (a' ≫ b' ≫ x') ≫ v'`, and the differential of the target `hE` carries the sign as the
composite with `σ = ε • 𝟙`. Given that the two presentations agree piece by piece (`hQ` … `hv`)
and that `X` is the right-hand side `Rr` of the reading `h₃`, the right-hand side of `h₃` is the
right-hand side of `hE`. -/
theorem eq_comp_comp_comp_of_leibniz {C : Type*} [_root_.CategoryTheory.Category C]
    [Preadditive C] {Q V T' Q₁ Q₂ W₁ W₂ A₁ A₂ B₁ B₂ : C}
    {X Rr e₁ z₃ : Q ⟶ V} {dL : Q ⟶ Q₁} {aL : Q₁ ⟶ A₁} {bL : A₁ ⟶ B₁} {xL : B₁ ⟶ W₁}
    {v : W₁ ⟶ V} {dE : Q ⟶ Q₂} {a' : Q₂ ⟶ A₂} {b' : A₂ ⟶ B₂} {x' : B₂ ⟶ W₂}
    {v' : W₂ ⟶ V} {E₁ : Q₂ ⟶ T'} {σ : T' ⟶ T'} {M : T' ⟶ V} {ε : ℤ}
    {instL : HSMul ℤ (Q ⟶ V) (Q ⟶ V)}
    (h₃ : z₃ = Rr) (hE : e₁ = dE ≫ E₁ ≫ σ ≫ M)
    (hstar : dE ≫ E₁ ≫ M = dE ≫ (a' ≫ b' ≫ x') ≫ v')
    (hL : X = @HSMul.hSMul _ _ _ instL ε (dL ≫ (aL ≫ bL ≫ xL) ≫ v))
    (hiL : ∀ x : Q ⟶ V, @HSMul.hSMul _ _ _ instL ε x = SMul.smul ε x)
    (hR : X = Rr) (hQ : Q₁ = Q₂) (hA : A₁ = A₂) (hB : B₁ = B₂) (hW : W₁ = W₂)
    (hd : HEq dL dE) (ha : HEq aL a') (hb : HEq bL b') (hx : HEq xL x')
    (hv : HEq v v') (hσ : σ = ε • 𝟙 T') : Rr = dE ≫ E₁ ≫ σ ≫ M := by
  subst hQ hA hB hW hσ hR
  obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hv
  rw [hL, ← hstar]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp]
  exact hiL _

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degree-`n` term of the `k`-th step, read in `F^kΩ^n_{X/S}` and included into
`Ω^n_{X/S}`, is the degree-`n` component of the inclusion of the step into `Ω^•_{X/S}`**,
followed by the identification of the degree-`n` term of the extension by zero,
`n = k + 1 + m`. -/
theorem stepXToExteriorFiltration_comp_arrow (k m : ℕ) :
    stepXToExteriorFiltration f g k m ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k).arrow =
      ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + m : ℕ) : ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) :
            ℤ)) rfl).hom := by
  exact Stacks.CategoryTheory.underlyingIso_inv_comp_ofLE_comp_mapObjIso_comp_arrow
      (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))) _
    (by exact CochainComplex.mono_ι_app_f (deRhamSmoothFiltration f g) (op (k : ℤ)) ((k + 1 + m : ℕ)
        : ℤ)) _ _ _


/-- **The `(k, j + 1)` summand of the wedge map factors through the degree-`n` term of the `k`-th
step by an epimorphism**, `n = k + 1 + j`. -/
theorem exists_epi_comp_ι_app_f_eq_summand (k j : ℕ) :
    ∃ z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).obj
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + j : ℕ) : ℤ),
      Epi z ∧ z ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + j : ℕ) :
          ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + j) (i' := ((k + 1 + j : ℕ) :
            ℤ)) rfl).hom = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u,
            u} ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫
            g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom) := by
  exact Stacks.CategoryTheory.exists_epi_comp_comp_hom_eq _
    (by exact CochainComplex.mono_ι_app_f (deRhamSmoothFiltration f g) (op (k : ℤ)) ((k + 1 + j : ℕ)
        : ℤ)) _ _ _
    (mk_ι_app_f_eq f g k (k + 1 + j) (by omega))
    (AlgebraicGeometry.SheafOfModules.imageSubobject_summand_eq_exteriorImageFiltration
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
      (pulledBackDifferentialsAlgebras f g) (Scheme.Hom.relativeDifferentialsShortComplex f
          g).f (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
      (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
      k (j + 1) (k + 1 + j) (add_add_one_eq_add_one_add k j)
      (by exact epi_pulledBackFormsComparison_tensor_comp_laxComparison f g k (j + 1)))


/-- **The inclusion of the `k`-th step into `Ω^•_{X/S}` is a chain map**, read through the
identifications of the degree-`n` terms of the extension by zero, `n = k + 1 + j`. -/
theorem d_comp_ι_app_f_comp_extendXIso_hom (k j : ℕ) :
    ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j
        + 1) : ℕ) : ℤ) ≫
        ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + (j + 1))
            (i' := ((k + 1 + (j + 1) : ℕ) : ℤ)) rfl).hom =
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + j : ℕ) : ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + j) (i' := ((k + 1 + j : ℕ) :
            ℤ)) rfl).hom) ≫
        (AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).d (k + 1 + j) (k + 1 + (j + 1)) :=
  Stacks.CategoryTheory.comp_comp_hom_eq_of_comm _ _ _ _ _ _ _
    (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).comm ((k + 1 + j : ℕ) : ℤ) ((k + 1
        + (j + 1) : ℕ) : ℤ))
    (Stacks.CategoryTheory.extendXIso_inv_comp_extend_d_comp_hom _ _ rfl rfl)


/-- The `(k + 1, j + 1)` wedge product, restricted to `(f∘g)^{-1}𝒪_S`, is killed by the projection
onto `Ω^{n+1}_{X/S}/F^{k+1}Ω^{n+1}_{X/S}`, `n = k + 1 + j`. -/
theorem restrictScalars_map_prodWedgeHomOfEq_comp_toStepQuotient (k j : ℕ) :
    (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (pulledBackDifferentialsAlgebras f g)
        (Scheme.Hom.deRhamAlgebras (f ≫ g)) (Scheme.Hom.deRhamAlgebras (f ≫
        g)) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) (j + 1)
      (k + 1 + j + 1) (by
          omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) (j + 1))) = 0 :=
          by
  refine Eq.trans ((_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
      AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
      AlgebraicGeometry.inverseImageStructureMap (f ≫
      g)))).map (Stacks.CategoryTheory.comp_eqToHom_comp_eq_zero _ _
    (cokernel.condition _) _)) ?_
  exact (_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
      AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map_zero _ _

/-- The first reading of the square above the cut: on an epimorphism `z` onto the degree-`n`
term of the step through which the `(k, j + 1)` summand factors, the projection onto the graded
piece followed by the comparison is `E_j`, `n = k + 1 + j`. -/
theorem comp_grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom [Smooth f] (k j : ℕ)
    (z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).obj
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ⟶ ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + j
        : ℕ) : ℤ)) (hZ : z ≫ (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1
        + j : ℕ) : ℤ) ≫ ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras
        (f ≫ g)) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f
        ≫ g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + j) (i' := ((k + 1 + j : ℕ) :
        ℤ)) rfl).hom) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom)) :
    z ≫ (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ)) (deRhamSmoothFiltration f g)).f ((k
        + 1 + j : ℕ) : ℤ) ≫ (gradedPieceXIsoGradedTargetX f g k j).hom = stepSummandToGradedTarget f
        g k j :=
  Stacks.CategoryTheory.comp_comp_eq_of_mono_readings _ _ _ _
    (mono_gradedTargetXToStepQuotient f g k j) _ _ _ _ _ _
    (grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient f g k j)
    (stepXToExteriorFiltration_comp_arrow f g k j)
    (stepSummandToGradedTarget_comp_toStepQuotient f g k j) hZ

/-- `(E_j)` followed by `M_{j+1}`. -/
theorem stepSummandToGradedTarget_comp_d_comp_toStepQuotient_eq (k j : ℕ) [Smooth f] :
    stepSummandToGradedTarget f g k j ≫ ((gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1
        + (j + 1) : ℕ) : ℤ)) ≫ (gradedTargetXToStepQuotient f g k (j + 1)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f
          ≫ g) (j + 1))) ≫ stepSummandToGradedTarget f g k (j + 1) ≫ ((-1 : ℤ) ^ k • 𝟙
          ((gradedTargetComplex f g k).X ((k + 1 + (j + 1) : ℕ) :
          ℤ))) ≫ (gradedTargetXToStepQuotient f g k (j + 1)) :=
  Stacks.CategoryTheory.comp_comp_eq_of_eq_comp_comp _ _ _ _ _ _
    (stepSummandToGradedTarget_comp_d f g k j)

/-- The right-hand side of the square above the cut on the source: the differential of the step
followed by the projection, the comparison and the reading into the quotient is the summand
followed by the de Rham differential and the projection. -/
theorem comp_d_comp_grMapπ_f_comp_toStepQuotient [Smooth f] (k j : ℕ)
    (z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).obj
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ⟶ ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + j
        : ℕ) : ℤ)) (hZ : z ≫ (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1
        + j : ℕ) : ℤ) ≫ ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras
        (f ≫ g)) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f
        ≫ g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + j) (i' := ((k + 1 + j : ℕ) :
        ℤ)) rfl).hom) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom)) :
    z ≫ ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 +
        (j + 1) : ℕ) : ℤ) ≫ (FilteredObject.grMapπ (FilteredObject.succHom (k :
        ℤ)) (deRhamSmoothFiltration f g)).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom ≫ gradedTargetXToStepQuotient f g k (j +
        1) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom) ≫
              (AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).d (k + 1 + j) (k + 1 + (j + 1)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
              AlgebraicGeometry.inverseImageStructureMap (f ≫
              g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) (j + 1))) :=
  Stacks.CategoryTheory.comp_d_comp_eq_of_readings _ _ _ _ _ _ _ _ _ _ _ _
    (grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient f g k (j + 1))
    (stepXToExteriorFiltration_comp_arrow f g k (j + 1))
    (d_comp_ι_app_f_comp_extendXIso_hom f g k j) hZ

/-- `(★_{j+1})` after `1 ⊗ d`. -/
theorem formsDifferential_comp_stepSummandToGradedTarget_comp_toStepQuotient [Smooth f] (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f ≫
        g) (j + 1))) ≫ stepSummandToGradedTarget f g k (j + 1) ≫ (gradedTargetXToStepQuotient f g k
        (j + 1)) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f ≫ g) (j + 1)))
        ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1 + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1 + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k (j + 1))).hom) ≫
              (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
              AlgebraicGeometry.inverseImageStructureMap (f ≫
              g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) (j + 1))) :=
  congrArg (fun t => (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
      S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f ≫ g) (j + 1))) ≫
      t) (stepSummandToGradedTarget_comp_toStepQuotient f g k (j + 1))

/-- **The square of Section 0FMK above the cut**: on the `k`-th graded piece, in degree
`n = k + 1 + j`, the comparison `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` carries the
differential of the graded piece to the differential of the target complex. -/
theorem grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom_comp_d [Smooth f] (k j : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) ≫
        ((gradedPieceXIsoGradedTargetX f g k j).hom ≫
          (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ)) =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom := by
  obtain ⟨z, hz, hZ⟩ := exists_epi_comp_ι_app_f_eq_summand f g k j
  have hL := AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_of_comp_eq_zero
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
    (pulledBackDifferentialsAlgebras f g) (Scheme.Hom.relativeDifferentialsShortComplex f g).f
    (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
    (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
    k (j + 1) (k + 1 + j) (add_add_one_eq_add_one_add k j) _
    (restrictScalars_map_prodWedgeHomOfEq_comp_toStepQuotient f g k j)
  have hstar := formsDifferential_comp_stepSummandToGradedTarget_comp_toStepQuotient f g k j
  have H3 := comp_d_comp_grMapπ_f_comp_toStepQuotient f g k j z hZ
  have HE := stepSummandToGradedTarget_comp_d_comp_toStepQuotient_eq f g k j
  have H1 := comp_grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom f g k j z hZ
  have h4 := Stacks.CategoryTheory.eq_comp_comp_comp_of_leibniz (h₃ := H3) (hE := HE)
    (hstar := hstar) (hL := hL) (hiL := fun _ => by kernel_rfl) (hR := rfl) (hQ := by kernel_rfl)
    (hA := by kernel_rfl) (hB := by kernel_rfl) (hW := by kernel_rfl) (hd := by kernel_hrfl)
    (ha := by kernel_hrfl) (hb := by kernel_hrfl) (hx := by kernel_hrfl) (hv := by kernel_hrfl)
    (hσ := rfl)
  exact Stacks.CategoryTheory.comp_comp_d_eq_of_cancel z hz _ _ _ _ _ _ _
    (mono_gradedTargetXToStepQuotient f g k (j + 1)) _ _ _ H1 HE H3 h4

end Stacks.DeRhamSmooth

end
