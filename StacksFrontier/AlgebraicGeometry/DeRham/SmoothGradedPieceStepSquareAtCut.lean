module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquareAbove
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquares
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The square of Section 0FMK at the cut

For `f : X ⟶ Y` smooth over `S` and a cut `k`, this file proves the ingredients of the square of
[Stacks, Section 0FMK] in the degree of the cut: the square asserts that the comparison
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut` of the degree-`k` term of the `k`-th
graded piece with the degree-`k` term of the target complex commutes with the differentials into
degree `k + 1`. Both sides are read after the monomorphism
`Stacks.DeRhamSmooth.gradedTargetXToStepQuotient` at `j = 0`, on the `(k, 0)` summand of the
wedge map.

## Main results

* `Stacks.DeRhamSmooth.cutSource_comp_cutWedgeSource_comp_mixedTensor_inv`: the surjection `w`
  of Section 50.12 onto the cut source, followed by the identifications of Tags 01CI and 08DE, is
  the body `E'_cut` of `Stacks.DeRhamSmooth.stepSummandToGradedTarget` in degree zero.
* `Stacks.DeRhamSmooth.cutSourceToTarget_comp_d`: `E'_cut` followed by `1 ⊗ d_{X/Y}` is
  `1 ⊗ d_{X/S}` followed by `Stacks.DeRhamSmooth.stepSummandToGradedTarget` at `j = 0`.
* `Stacks.DeRhamSmooth.exteriorPieceZeroIsoUnit_hom_comp_relativeDifferentialFormsZeroIso_inv`:
  in degree zero, `Ω^0_{X/S} ⟶ Ω^0_{X/Y}` is the identification of both with `𝒪_X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)

universe u

namespace SheafOfModules.GradedAlgebra
universe w

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A unital homomorphism in degree zero is the composite of the two identifications with the
unit sheaf**: for graded algebras `A`, `B` whose degree-zero pieces are identified with `R` by
isomorphisms carrying the algebra unit to `1`, the degree-zero component of any unital
homomorphism `A ⟶ B` is `e₁.hom ≫ e₂.inv`. -/
theorem unitalHom_app_zero_eq {A B : GradedAlgebra.{w, w} R}
    (e₁ : A.piece 0 ≅ SheafOfModules.unit R)
    (he₁ : ∀ U : Cᵒᵖ, e₁.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U))
    (e₂ : B.piece 0 ≅ SheafOfModules.unit R)
    (he₂ : ∀ U : Cᵒᵖ, e₂.hom.val.app U (B.one.eval U) = (1 : R.obj.obj U))
    (g : UnitalHom A B) : g.app 0 = e₁.hom ≫ e₂.inv := by
  have hsec : ∀ (U : Cᵒᵖ) (c : R.obj.obj U),
      e₂.hom.val.app U ((g.app 0).val.app U (e₁.inv.val.app U c)) = c := by
    intro U c
    refine Eq.trans (congrArg (fun z => e₂.hom.val.app U ((g.app 0).val.app U z))
      (inv_pieceZeroIsoUnit_apply A e₁ he₁ U c)) ?_
    refine Eq.trans (congrArg (e₂.hom.val.app U) (map_smul _ c (A.one.eval U))) ?_
    refine Eq.trans (congrArg (fun z => e₂.hom.val.app U (c • z)) (g.map_one U)) ?_
    exact pieceZeroIsoUnit_smul_one B e₂ he₂ U c
  have key : e₁.inv ≫ g.app 0 ≫ e₂.hom = 𝟙 (SheafOfModules.unit R) :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext (hsec U)))
  simpa using e₁.hom ≫= key =≫ e₂.inv

end SheafOfModules.GradedAlgebra

namespace Stacks.CategoryTheory

/-- A morphism `w` into the target of an isomorphism `e`, carried back along `e⁻¹` and then along
a morphism `ι` that `e⁻¹` turns into `m ≫ e'⁻¹`, and read through `e'`, is `w ≫ m`. -/
theorem comp_inv_comp_comp_hom_eq {C : Type*} [_root_.CategoryTheory.Category C]
    {P W F K Ω : C} (w : P ⟶ W) (e : F ≅ W) (ι : F ⟶ K) (m : W ⟶ Ω) (e' : K ≅ Ω)
    (S : P ⟶ Ω) (hinv : e.inv ≫ ι = m ≫ e'.inv) (hS : w ≫ m = S) :
    (w ≫ e.inv) ≫ ι ≫ e'.hom = S := by
  rw [Category.assoc, reassoc_of% hinv, Iso.inv_hom_id, Category.comp_id, hS]

/-- **A naturality square and a triangle, pasted**, at generic objects: if `n ≫ e' = e ≫ m` and
`x₁ ≫ x₂ ≫ x₃ ≫ e = y₁ ≫ y₂`, then `(x₁ ≫ x₂ ≫ x₃ ≫ n) ≫ e' = y₁ ≫ y₂ ≫ m`. -/
theorem comp_comp_comp_comp_hom_eq_of_naturality {C : Type*} [_root_.CategoryTheory.Category C]
    {Q A₁ A₂ A₃ A₄ B₁ B₂ Y₁ : C} (x₁ : Q ⟶ A₁) (x₂ : A₁ ⟶ A₂) (x₃ : A₂ ⟶ A₃) (n : A₃ ⟶ A₄)
    (e' : A₄ ⟶ B₂) (e : A₃ ⟶ B₁) (m : B₁ ⟶ B₂) (y₁ : Q ⟶ Y₁) (y₂ : Y₁ ⟶ B₁)
    (hn : n ≫ e' = e ≫ m) (ht : x₁ ≫ x₂ ≫ x₃ ≫ e = y₁ ≫ y₂) :
    (x₁ ≫ x₂ ≫ x₃ ≫ n) ≫ e' = y₁ ≫ y₂ ≫ m := by
  simp only [Category.assoc, hn]
  rw [reassoc_of% ht]

/-- **A lax comparison crossed by naturality, then an inverse pair cancelled**, at generic
objects: from `w = r ≫ s ≫ L₁`, `c = c₁ ≫ c₂`, the naturality square `s ≫ L₁ = L₀ ≫ n`,
`n ≫ c₁ = 𝟙` and `c₂ = m`, conclude `w ≫ c = r ≫ L₀ ≫ m`. -/
theorem comp_eq_comp_comp_of_lax_naturality {C : Type*} [_root_.CategoryTheory.Category C]
    {Q P₁ P₂ X₁ X₀ Y : C} (w : Q ⟶ X₁) (c : X₁ ⟶ Y) (r : Q ⟶ P₁) (s : P₁ ⟶ P₂)
    (L₁ : P₂ ⟶ X₁) (L₀ : P₁ ⟶ X₀) (n : X₀ ⟶ X₁) (c₁ : X₁ ⟶ X₀) (c₂ m : X₀ ⟶ Y)
    (hw : w = r ≫ s ≫ L₁) (hc : c = c₁ ≫ c₂) (hnl : s ≫ L₁ = L₀ ≫ n) (hnc : n ≫ c₁ = 𝟙 X₀)
    (hm : c₂ = m) : w ≫ c = r ≫ L₀ ≫ m := by
  subst hw hc hm
  simp only [Category.assoc]
  rw [reassoc_of% hnl, reassoc_of% hnc]

/-- The images under `R` of the components at `N` of `TX.map p` and `TX.map p'` compose to the
identity when `p ≫ p' = 𝟙`. -/
theorem map_app_comp_map_app_eq_id {C D : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] (R : D ⥤ C) (TX : D ⥤ D ⥤ D) {M₀ M₁ : D} (N : D)
    (p : M₀ ⟶ M₁) (p' : M₁ ⟶ M₀) (hp : p ≫ p' = 𝟙 M₀) :
    R.map ((TX.map p).app N) ≫ R.map ((TX.map p').app N) = 𝟙 _ := by
  rw [← R.map_comp, ← NatTrans.comp_app, ← TX.map_comp, hp, TX.map_id, NatTrans.id_app, R.map_id]

/-- A morphism followed by `e⁻¹`: if `w ≫ h = Z` and `E ≫ e.hom = Z`, then `w ≫ h ≫ e.inv = E`. -/
theorem comp_comp_inv_eq_of_comp_hom {C : Type*} [_root_.CategoryTheory.Category C]
    {Q W W₁ E : C} (w : Q ⟶ W) (h : W ⟶ W₁) (e : E ≅ W₁) (Ec : Q ⟶ E) (Z : Q ⟶ W₁)
    (hl : w ≫ h = Z) (hr : Ec ≫ e.hom = Z) : w ≫ h ≫ e.inv = Ec := by
  rw [← Category.assoc, hl, ← hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The cut-source reading carries `1 ⊗ d_{X/S}` to the differential of the target**, at
generic objects. With `θ ⊗ 1`, the change of coefficients `a`, the lax comparison and `1 ⊗ q`,
the naturality squares `hnat₁`, `hnat₂` of the lax comparison and the commutation `key` of `q`
with the differentials give
`(θ ⊗ 1 ≫ a₁ ≫ lax₁ ≫ q₁) ≫ Df ≫ i₂ = (1 ⊗ dS) ≫ (θ ⊗ 1 ≫ a₂ ≫ lax₂ ≫ q₂ ≫ i₂)`. -/
theorem comp_comp_eq_formsDifferential_comp_of_lax {C D : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] (F : C ⥤ C ⥤ C) (G : D ⥤ D) (R : D ⥤ C)
    {P P' N₁ N₂ T₂ : C} {U₁ U₂ V₁ V₂ : D}
    (θ : P ⟶ P') (dS : N₁ ⟶ N₂) (a₁ : N₁ ⟶ R.obj U₁) (a₂ : N₂ ⟶ R.obj U₂)
    (lax₁ : (F.obj P').obj (R.obj U₁) ⟶ R.obj (G.obj U₁))
    (lax₂ : (F.obj P').obj (R.obj U₂) ⟶ R.obj (G.obj U₂))
    (lax₃ : (F.obj P').obj (R.obj V₂) ⟶ R.obj (G.obj V₂))
    (q₁ : U₁ ⟶ V₁) (q₂ : U₂ ⟶ V₂) (Df : V₁ ⟶ V₂) (i₂ : R.obj (G.obj V₂) ⟶ T₂)
    (hnat₁ : (F.obj P').map (R.map (q₁ ≫ Df)) ≫ lax₃ = lax₁ ≫ R.map (G.map (q₁ ≫ Df)))
    (hnat₂ : (F.obj P').map (R.map q₂) ≫ lax₃ = lax₂ ≫ R.map (G.map q₂))
    (key : a₁ ≫ R.map (q₁ ≫ Df) = dS ≫ a₂ ≫ R.map q₂) :
    ((F.map θ).app N₁ ≫ (F.obj P').map a₁ ≫ lax₁ ≫ R.map (G.map q₁)) ≫ R.map (G.map Df) ≫ i₂ =
      (F.obj P).map dS ≫ ((F.map θ).app N₂ ≫ (F.obj P').map a₂ ≫ lax₂ ≫
        R.map (G.map q₂) ≫ i₂) := by
  have e₁ : lax₁ ≫ R.map (G.map q₁) ≫ R.map (G.map Df) =
      (F.obj P').map (R.map (q₁ ≫ Df)) ≫ lax₃ := by
    rw [hnat₁, Functor.map_comp, Functor.map_comp]
  have e₂ : (F.obj P').map a₁ ≫ (F.obj P').map (R.map (q₁ ≫ Df)) =
      (F.obj P').map dS ≫ (F.obj P').map a₂ ≫ (F.obj P').map (R.map q₂) := by
    rw [← Functor.map_comp, key, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, reassoc_of% hnat₂, ← NatTrans.naturality_assoc]

/-- **The left-hand side of the square at the cut on its source**, at generic objects of a
preadditive category: if `w ≫ a ≫ b = Ec` and `Ec ≫ c ≫ t = δ ≫ E`, then
`(w ≫ e⁻¹) ≫ (e ≫ a ≫ b ≫ (ε • c) ≫ t) ≫ M = δ ≫ E ≫ (ε • 𝟙) ≫ M`. -/
theorem comp_inv_comp_comp_smul_eq {C : Type*} [_root_.CategoryTheory.Category C] [Preadditive C]
    {Q F W W₁ W₂ W₃ T V Q' : C} (w : Q ⟶ W) (e : F ≅ W) (a : W ⟶ W₁) (b : W₁ ⟶ W₂)
    (c : W₂ ⟶ W₃) (t : W₃ ⟶ T) (M : T ⟶ V) (δ : Q ⟶ Q') (E : Q' ⟶ T) (Ec : Q ⟶ W₂) (ε : ℤ)
    (hii : w ≫ a ≫ b = Ec) (hiii : Ec ≫ c ≫ t = δ ≫ E) :
    (w ≫ e.inv) ≫ (e.hom ≫ a ≫ b ≫ (ε • c) ≫ t) ≫ M = δ ≫ E ≫ (ε • 𝟙 T) ≫ M := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.id_comp]
  rw [reassoc_of% hii, reassoc_of% hiii]

/-- **The square at the cut, at generic objects**, from its two readings on an epimorphism `z`
after a monomorphism `M`: `z ≫ LHS ≫ M = L`, `z ≫ dF ≫ p' ≫ i' ≫ M = R` and `R = L` give
`LHS = dF ≫ p' ≫ i'`. -/
theorem eq_comp_comp_of_cancel {C : Type*} [_root_.CategoryTheory.Category C]
    {Q F F' G' T V : C} (z : Q ⟶ F) (hz : Epi z) (LHS : F ⟶ T) (dF : F ⟶ F') (p' : F' ⟶ G')
    (i' : G' ⟶ T) (M : T ⟶ V) (hM : Mono M) (L R : Q ⟶ V) (h₁ : z ≫ LHS ≫ M = L)
    (h₃ : z ≫ dF ≫ p' ≫ i' ≫ M = R) (h₄ : R = L) : LHS = dF ≫ p' ≫ i' := by
  refine hz.left_cancellation _ _ (hM.right_cancellation _ _ ?_)
  simp only [Category.assoc]
  rw [h₁, h₃, h₄]

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The inclusion of the `k`-th step into `Ω^•_{X/S}` is a chain map at the cut**, read through
the identifications of the degree-`k` and degree-`k + 1` terms of the extension by zero. -/
theorem d_comp_ι_app_f_comp_extendXIso_hom_atCut (k : ℕ) :
    ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) :
        ℤ) ≫
        ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + 0 : ℕ) : ℤ) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).extendXIso ComplexShape.embeddingUpNat (i := k + 1 + 0) (i' := ((k + 1 + 0 : ℕ)
              : ℤ)) rfl).hom =
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k : ℕ) : ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k) (i' := ((k : ℕ) : ℤ)) rfl).hom) ≫
        (AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).d k (k + 1 + 0) :=
  Stacks.CategoryTheory.comp_comp_hom_eq_of_comm _ _ _ _ _ _ _
    (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).comm ((k : ℕ) : ℤ) ((k + 1 + 0 :
        ℕ) : ℤ))
    (Stacks.CategoryTheory.extendXIso_inv_comp_extend_d_comp_hom _ _ rfl rfl)

/-- The `(k + 1, 0)` wedge product, restricted to `(f∘g)^{-1}𝒪_S`, is killed by the projection
onto `Ω^{k+1}_{X/S}/F^{k+1}Ω^{k+1}_{X/S}`. -/
theorem restrictScalars_map_prodWedgeHomOfEq_comp_toStepQuotient_atCut (k : ℕ) :
    (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (pulledBackDifferentialsAlgebras f g)
        (Scheme.Hom.deRhamAlgebras (f ≫ g)) (Scheme.Hom.deRhamAlgebras (f ≫
        g)) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) 0
      (k + 1) (by
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
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) 0)) = 0 := by
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

/-- The right-hand side of the square at the cut on the source: on a morphism `z` into the
degree-`k` term of the step through which the `(k, 0)` summand factors, the differential of the
step followed by the projection, the comparison and the reading into the quotient is the summand
followed by the de Rham differential and the projection. -/
theorem comp_d_comp_grMapπ_f_comp_toStepQuotient_atCut [Smooth f] (k : ℕ)
    (z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).obj
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ⟶
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k : ℕ) : ℤ))
    (hZ : z ≫ (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k : ℕ) : ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k) (i' := ((k : ℕ) : ℤ)) rfl).hom) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X 0) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (Nat.add_zero k)).hom)) :
    z ≫ ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ)
        : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ)) (deRhamSmoothFiltration f g)).f ((k
            + 1 + 0 : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k 0).hom ≫ gradedTargetXToStepQuotient f g k 0 =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X 0) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (Nat.add_zero k)).hom) ≫
              (AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).d k (k + 1 + 0) ≫
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
            g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) 0)) :=
  Stacks.CategoryTheory.comp_d_comp_eq_of_readings _ _ _ _ _ _ _ _ _ _ _ _
    (grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient f g k 0)
    (stepXToExteriorFiltration_comp_arrow f g k 0)
    (d_comp_ι_app_f_comp_extendXIso_hom_atCut f g k) hZ


/-- **The `(k, 0)` summand of the wedge map, read on the source of the wedge-product morphism at
the cut**: the surjection `w = (c_k ⊗ 1) ≫ lax` of Section 50.12 onto the source of
`Stacks.DeRhamSmooth.cutProdWedgeHom`, carried into the degree-`k` term of the step by
`Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource` and included into `Ω^k_{X/S}`, is the
summand. -/
theorem cutSource_comp_inv_comp_ι_app_f_comp_extendXIso_hom [Smooth f] (k : ℕ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
            ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
            g)).exteriorPower 0)) ≫
        (filtrationXIsoCutWedgeSource f g k).inv) ≫
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k : ℕ) : ℤ) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
            g)))).extendXIso ComplexShape.embeddingUpNat (i := k) (i' := ((k : ℕ) : ℤ)) rfl).hom) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X 0) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (Nat.add_zero k)).hom) :=
  Stacks.CategoryTheory.comp_inv_comp_comp_hom_eq _ _ _ _ _ _
    (filtrationXIsoCutWedgeSource_inv_arrow f g k)
    (AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp (Scheme.Hom.deRhamAlgebras
        (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
      (pulledBackDifferentialsAlgebras f g) (Scheme.Hom.relativeDifferentialsShortComplex f
          g).f (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
      (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
      k 0 k (Nat.add_zero k)).symm

/-- The surjection of Section 50.12 onto the source of the wedge-product morphism at the cut,
carried into the degree-`k` term of the step, is an epimorphism. -/
theorem epi_cutSource_comp_inv [Smooth f] (k : ℕ) :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
            ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
            g)).exteriorPower 0)) ≫
        (filtrationXIsoCutWedgeSource f g k).inv) :=
  @epi_comp _ _ _ _ _ _
    (by exact epi_pulledBackFormsComparison_tensor_comp_laxComparison f g k 0)
    _ (by exact @CategoryTheory.IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv
        (filtrationXIsoCutWedgeSource f g k)))

/-- **In degree zero, `Ω^0_{X/S} ⟶ Ω^0_{X/Y}` is the identification of both with `𝒪_X`**: the
degree-zero component of `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom` is
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit` followed by the inverse
of `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`. -/
theorem exteriorPieceZeroIsoUnit_hom_comp_relativeDifferentialFormsZeroIso_inv :
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂).exteriorPieceZeroIsoUnit.hom ≫ (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv =
        ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((0 : ℕ) : ℤ)) :=
  (SheafOfModules.GradedAlgebra.unitalHom_app_zero_eq _ (_root_.SheafOfModules.ringedSpaceAlgebras
      X.toRingedSpace (Scheme.Hom.relativeDifferentialsShortComplex f
      g).X₂).exteriorPieceZeroIsoUnit_one _
    (Scheme.Hom.deRhamAlgebras f).exteriorPieceZeroIsoUnit_one _).symm


/-- **The cut-source reading followed by [Stacks, Tag 08DE]**: the composite `E'_cut` of
`θ ⊗ 1`, the triangle of restrictions of scalars, the lax comparison along
`(f∘g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` and `1 ⊗ q` (`q : Ω^0_{X/S} ⟶ Ω^0_{X/Y}`), followed by
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso`, is `c ⊗ 1`, the lax comparison along
`(f∘g)^{-1}𝒪_S ⟶ 𝒪_X` and `1 ⊗ q`. -/
theorem cutSourceToTarget_comp_mixedTensor_hom (k : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsToTarget f g k)).app ((pushforward
        (toInverseImageBase (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
        k))).map ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
        g.toLRSHom.toShHom) (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase
        f)).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 :
        ℕ) : ℤ))) ≫ (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        (formsToRelativeCochain f g
        0))) ≫ (gradedSourceMixedTensorCoefficientIso f g k (Scheme.Hom.relativeDifferentialForms f
        ((0 : ℕ) : ℤ))).hom = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)).map (relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (k
        : ℤ)))).app ((pushforward (toInverseImageBase (f ≫ g))).obj
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ)) ≫ (pushforward
        (toInverseImageBase (f ≫ g))).map (((Stacks.SheafOfModules.Tensor.sheafTensor
        X.toRingedSpace.sheaf).obj ((Scheme.Modules.pullback
        f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ)))).map ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((0 : ℕ) : ℤ)))) := by
  have hn := gradedSourceMixedTensorCoefficientIso_naturality f g k
      ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((0 : ℕ) : ℤ))
  have ht := pulledBackFormsToTarget_tensor_comp_mixedTensor f g k
      (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))
  have h := Stacks.CategoryTheory.comp_comp_comp_comp_hom_eq_of_naturality
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)))
    _ _ _ _ ((gradedSourceMixedTensorCoefficientIso f g k (Scheme.Hom.relativeDifferentialForms f
        ((0 : ℕ) : ℤ))).hom) _ _ _ _ hn ht
  exact h

/-- **The surjection of Section 50.12 at the cut, followed by
`Stacks.DeRhamSmooth.cutWedgeSourceIsoPullbackTensor`**, is `c ⊗ 1`, the lax comparison along
`(f∘g)^{-1}𝒪_S ⟶ 𝒪_X` and `1 ⊗ q`. -/
theorem cutSource_comp_map_cutWedgeSourceIsoPullbackTensor_hom (k : ℕ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower 0))) ≫ (pushforward (toInverseImageBase (f ≫ g))).map
        (cutWedgeSourceIsoPullbackTensor f g
        k).hom = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase (f
        ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ)) ≫ (pushforward
        (toInverseImageBase (f ≫ g))).map (((Stacks.SheafOfModules.Tensor.sheafTensor
        X.toRingedSpace.sheaf).obj ((Scheme.Modules.pullback
        f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ)))).map ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((0 : ℕ) : ℤ)))) := by
  have hw : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
      CommRingCat.{u} (f ≫
      g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
      ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
      g)))).X 0) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
      CommRingCat.{u} (f ≫
      g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
      ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
      g)).exteriorPower 0))) = ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
      S.sheaf)).map (relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (k :
      ℤ)))).app ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
      g)))).X 0) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (pulledBackFormsIso f g k).hom)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X 0) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
            ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
            g)).exteriorPower 0) :=
    (congrArg (fun t => NatTrans.app t _ ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)
  have hc : (pushforward (toInverseImageBase (f ≫ g))).map (cutWedgeSourceIsoPullbackTensor f g
      k).hom =
      (pushforward (toInverseImageBase (f ≫ g))).map (((Stacks.SheafOfModules.Tensor.sheafTensor
          X.toRingedSpace.sheaf).map (Scheme.Modules.exteriorPowerPullbackIso f
          (Scheme.Hom.relativeDifferentials g) (k : ℤ)).inv).app ((Scheme.Hom.deRhamAlgebras (f ≫
          g)).exteriorPower 0)) ≫
        (pushforward (toInverseImageBase (f ≫ g))).map (((Stacks.SheafOfModules.Tensor.sheafTensor
            X.toRingedSpace.sheaf).obj ((Scheme.Modules.pullback
            f).obj (Scheme.Hom.relativeDifferentialForms g (k :
            ℤ)))).map ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f
            g).X₂).exteriorPieceZeroIsoUnit.hom ≫ (Scheme.Hom.relativeDifferentialFormsZeroIso
            f).inv)) :=
    Functor.map_comp _ _ _
  have hnl := AlgebraicGeometry.SheafOfModules.laxComparison_naturality_left (X :=
      X.toRingedSpace) (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))
      (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)) ((Scheme.Hom.deRhamAlgebras (f ≫
          g)).exteriorPower 0) (pulledBackFormsIso f g k).hom
  have hnc := Stacks.CategoryTheory.map_app_comp_map_app_eq_id
      (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫
      g)))) (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
      ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower 0)
    (pulledBackFormsIso f g k).hom (Scheme.Modules.exteriorPowerPullbackIso f
        (Scheme.Hom.relativeDifferentials g) (k : ℤ)).inv
    (Scheme.Modules.exteriorPowerPullbackIso f (Scheme.Hom.relativeDifferentials g) (k :
        ℤ)).hom_inv_id
  have hm := congrArg (fun t => (pushforward (toInverseImageBase (f ≫ g))).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map t))
    (exteriorPieceZeroIsoUnit_hom_comp_relativeDifferentialFormsZeroIso_inv f g)
  have h := Stacks.CategoryTheory.comp_eq_comp_comp_of_lax_naturality
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)))
    _ _ _ _ _ _ _ _ _ _ hw hc hnl hnc hm
  refine Eq.trans h ?_
  kernel_rfl

/-- **The cut source, read in the target of Section 0FMK**: the surjection `w` of Section
50.12 at the cut followed by `Stacks.DeRhamSmooth.cutWedgeSourceIsoPullbackTensor` and the inverse
of `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` is the composite `E'_cut` of
`θ ⊗ 1`, the triangle of restrictions of scalars, the lax comparison and `1 ⊗ q`, the body of
`Stacks.DeRhamSmooth.stepSummandToGradedTarget` in degree zero. -/
theorem cutSource_comp_cutWedgeSource_comp_mixedTensor_inv (k : ℕ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower 0))) ≫ (pushforward (toInverseImageBase (f ≫ g))).map
        (cutWedgeSourceIsoPullbackTensor f g k).hom ≫ (gradedSourceMixedTensorCoefficientIso f g k
        (Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) :
        ℤ))).inv = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u,
        u} ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsToTarget f g k)).app ((pushforward
        (toInverseImageBase (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
        k))).map ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
        g.toLRSHom.toShHom) (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase
        f)).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 :
        ℕ) : ℤ))) ≫ (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        (formsToRelativeCochain f g 0))) :=
  Stacks.CategoryTheory.comp_comp_inv_eq_of_comp_hom _ _ _ _ _
    (cutSource_comp_map_cutWedgeSourceIsoPullbackTensor_hom f g k)
    (cutSourceToTarget_comp_mixedTensor_hom f g k)

/-- **The differential at the cut on its source**: `E'_cut` followed by `1 ⊗ d_{X/Y}` and the
identification of degree `k + 1` of the target is `1 ⊗ d_{X/S}` followed by
`Stacks.DeRhamSmooth.stepSummandToGradedTarget` at `j = 0`. -/
theorem cutSourceToTarget_comp_d (k : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsToTarget f g k)).app ((pushforward
        (toInverseImageBase (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
        k))).map ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) :
        ℤ))) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
        g.toLRSHom.toShHom) (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase
        f)).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 :
        ℕ) : ℤ))) ≫ (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        (formsToRelativeCochain f g
        0))) ≫ (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        ((deRhamCochainXIso f 0).inv ≫ (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
        (deRhamCochainXIso f (0 +
        1)).hom)) ≫ (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (add_add_one_eq_add_one_add k
        0)).inv =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f
          ≫ g) 0)) ≫ stepSummandToGradedTarget f g k 0 := by
  have n₁ := laxComparison_pulledBackTargetForms_naturality f g k (formsToRelativeCochain f g 0 ≫
      ((deRhamCochainXIso f 0).inv ≫ (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
      (deRhamCochainXIso f (0 + 1)).hom))
  have n₂ := laxComparison_pulledBackTargetForms_naturality f g k (formsToRelativeCochain f g (0 +
      1))
  have key := formsToRelativeCochain_comm_d f g 0
  have h := Stacks.CategoryTheory.comp_comp_eq_formsDifferential_comp_of_lax
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)))
    (D := Modules (inverseImageBase f))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)) (pulledBackTargetFormsTensor f g k) (coefficientRestriction f g)
    (pulledBackFormsToTarget f g k) _ _ _ _ _ _ _ _ _
    (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (add_add_one_eq_add_one_add k 0)).inv n₁ n₂ key
  refine Eq.trans h ?_
  kernel_rfl

end Stacks.DeRhamSmooth

end
