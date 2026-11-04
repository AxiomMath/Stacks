module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSourceIsoMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiMultiplicative
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitComparison
public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiReadingQuasicoherentIsoMul
public import StacksFrontier.Tactic.HEqCongr

/-!
# `ψ` of Stacks 084D is multiplicative, given the multiplicativity on the atlas

Let `X = U/R` be a presentation of an algebraic space and `D(M_n)` modules descended from
quasi-coherent modules `M_n` on the scheme of `U`.  A morphism `ψ_n : Y_n ⟶ D(M_n)` descended from
a chart morphism `φ_n : c^*Y_n ⟶ M_n^a` (`AlgebraicGeometry.Space.presentationDescendedIntoHom`)
carries a multiplication of the `Y_n` to the descended multiplication of the `D(M_n)`
(`AlgebraicGeometry.Space.presentationDescendedMul`) as soon as the chart morphisms carry the
inverse image of the multiplication of the `Y_n` to the attached multiplication; likewise for the
units.  This is how the multiplicativity of the homomorphism `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of
Stacks 084D is reduced to its multiplicativity on the atlas.

## Main results

* `AlgebraicGeometry.Space.presentationDescendedIntoHom_mul`: **descended morphisms into
  descended modules carry a multiplication to the descended multiplication**, if they do so on the
  atlas.
* `AlgebraicGeometry.Space.presentationDescendedIntoHom_unit`: the same for units.
* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_oneHom`,
  `AlgebraicGeometry.Space.oneHom_etalePointAlgebra`: **the unit of the pullback of a sheaf of
  graded algebras along a morphism of algebraic spaces (in particular to a scheme point) is the
  pulled-back unit** `𝒪 ≅ f^*𝒪 ⟶ f^*𝒜_0` (Stacks 03LU).
* `AlgebraicGeometry.Space.representedTensorChartMul_comp_map_hom_of_comp_eq`: the module
  attached by Stacks 03DX (2) to a multiplicative square is a multiplicative square.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint_mul`,
  `AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint_one`: **`ψ` on the atlas
  carries the multiplication and the unit of `c^*π^*𝒜` to those attached to the twists**, given
  the same for `ψ` of Tag 01NR on the scheme of `U ×_X P`
  (`AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeMulCompat`,
  `AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeUnitCompat`).
* `RelativeProjSituation.psiSourceMul_comp_psiTwistHom_of_psiChartSchemeMulCompat`,
  `RelativeProjSituation.psiSourceUnit_comp_psiTwistHom_of_psiChartSchemeUnitCompat`:
  **`ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of Stacks 084D is multiplicative and unital**, given the same on
  the scheme of `U ×_X P`.

## Implementation notes

The descent statements are proved at free variables from an abstract statement about a functor
between monoidal categories (the inverse image along the atlas), so that their instances in
Situation 0849 are the types of their proofs and no two spellings of a concrete composite are
compared.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

section Abstract

variable {𝒩 ℳ : Type*} [Category 𝒩] [MonoidalCategory 𝒩] [Category ℳ] [MonoidalCategory ℳ]
  (F : 𝒩 ⥤ ℳ)

/-- **A functor identity for the multiplicativity of descended morphisms**: if `F(ψ_n)` read
through `χ_n` is `φ_n`, the multiplication `μ` read through `χ` is `T_D ≫ (χ_i ⊗ χ_j) ≫ M`, and the
`φ_n` carry `T_Y⁻¹ ≫ F(m)` to `M`, then `F(m ≫ ψ_k) = F((ψ_i ⊗ ψ_j) ≫ μ)`. -/
theorem map_comp_eq_map_tensorHom_comp_of_chart {Yi Yj Yk Di Dj Dk : 𝒩} {Ci Cj Ck : ℳ}
    (mY : Yi ⊗ Yj ⟶ Yk) (ψi : Yi ⟶ Di) (ψj : Yj ⟶ Dj) (ψk : Yk ⟶ Dk) (μ : Di ⊗ Dj ⟶ Dk)
    (χi : F.obj Di ≅ Ci) (χj : F.obj Dj ≅ Cj) (χk : F.obj Dk ≅ Ck)
    (φi : F.obj Yi ⟶ Ci) (φj : F.obj Yj ⟶ Cj) (φk : F.obj Yk ⟶ Ck)
    (TY : F.obj (Yi ⊗ Yj) ≅ F.obj Yi ⊗ F.obj Yj) (TD : F.obj (Di ⊗ Dj) ≅ F.obj Di ⊗ F.obj Dj)
    (M : Ci ⊗ Cj ⟶ Ck)
    (hnat : F.map (ψi ⊗ₘ ψj) ≫ TD.hom = TY.hom ≫ (F.map ψi ⊗ₘ F.map ψj))
    (hψi : F.map ψi ≫ χi.hom = φi) (hψj : F.map ψj ≫ χj.hom = φj)
    (hψk : F.map ψk ≫ χk.hom = φk)
    (hμ : F.map μ ≫ χk.hom = TD.hom ≫ (χi.hom ⊗ₘ χj.hom) ≫ M)
    (h : TY.inv ≫ F.map mY ≫ φk = (φi ⊗ₘ φj) ≫ M) :
    F.map (mY ≫ ψk) = F.map ((ψi ⊗ₘ ψj) ≫ μ) := by
  rw [← cancel_mono χk.hom, F.map_comp, F.map_comp, Category.assoc, Category.assoc, hψk, hμ,
    reassoc_of% hnat, tensorHom_comp_tensorHom_assoc, hψi, hψj, ← h, Iso.hom_inv_id_assoc]

omit [MonoidalCategory 𝒩] [MonoidalCategory ℳ] in
/-- **A functor identity for the unitality of descended morphisms**: if `F(ψ)` read through `χ`
is `φ`, the unit `ν` read through `χ` is `T.hom ≫ N`, and `φ` carries `T⁻¹ ≫ F(e)` to `N`, then
`F(e ≫ ψ) = F(ν)`. -/
theorem map_comp_eq_map_of_chart {O Y D : 𝒩} {C : ℳ} {O' : ℳ} (e : O ⟶ Y) (ψ : Y ⟶ D)
    (ν : O ⟶ D) (χ : F.obj D ≅ C) (φ : F.obj Y ⟶ C) (T : F.obj O ≅ O') (N : O' ⟶ C)
    (hψ : F.map ψ ≫ χ.hom = φ) (hν : F.map ν ≫ χ.hom = T.hom ≫ N)
    (h : T.inv ≫ F.map e ≫ φ = N) :
    F.map (e ≫ ψ) = F.map ν := by
  rw [← cancel_mono χ.hom, F.map_comp, Category.assoc, hψ, hν, ← h, Iso.hom_inv_id_assoc]

/-- **A multiplicative chart identity from the same identity in another spelling**: if
`(x ≫ y) ≫ σ ≫ ε = ((σ_i ≫ ε_i) ⊗ (σ_j ≫ ε_j)) ≫ r`, then `x' ≫ y' ≫ φ = (φ_i ⊗ φ_j) ≫ r'` for
morphisms `x'`, `y'`, `φ`, `φ_i`, `φ_j`, `r'` heterogeneously equal to `x`, `y`, `σ ≫ ε`,
`σ_i ≫ ε_i`, `σ_j ≫ ε_j`, `r`, so that the two spellings are compared one factor at a time. -/
theorem comp_comp_eq_tensorHom_comp_of_heq {ℳ : Type*} {_ : Category ℳ} {_ : MonoidalCategory ℳ}
    {Si Sj b c d e ai aj : ℳ} {x : Si ⊗ Sj ⟶ b} {y : b ⟶ c} {σ : c ⟶ d} {ε : d ⟶ e}
    {σi : Si ⟶ ai} {σj : Sj ⟶ aj} {ei ej : ℳ} {εi : ai ⟶ ei} {εj : aj ⟶ ej}
    {r : ei ⊗ ej ⟶ e} (h : (x ≫ y) ≫ σ ≫ ε = ((σi ≫ εi) ⊗ₘ (σj ≫ εj)) ≫ r)
    {b' c' e' Si' Sj' ei' ej' : ℳ} (x' : Si' ⊗ Sj' ⟶ b') (y' : b' ⟶ c') (φ : c' ⟶ e')
    (φi : Si' ⟶ ei') (φj : Sj' ⟶ ej') (r' : ei' ⊗ ej' ⟶ e')
    (hb : b' = b) (hc : c' = c) (he : e' = e) (hSi : Si' = Si) (hSj : Sj' = Sj)
    (hei : ei' = ei) (hej : ej' = ej) (hx : HEq x' x) (hy : HEq y' y) (hφ : HEq φ (σ ≫ ε))
    (hφi : HEq φi (σi ≫ εi)) (hφj : HEq φj (σj ≫ εj)) (hr : HEq r' r) :
    x' ≫ y' ≫ φ = (φi ⊗ₘ φj) ≫ r' := by
  subst hb hc he hSi hSj hei hej
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hφi
  obtain rfl := eq_of_heq hφj
  obtain rfl := eq_of_heq hr
  simpa only [Category.assoc] using h

/-- **A unital chart identity from the same identity in another spelling**: if
`(x ≫ y) ≫ σ ≫ ε = r`, then `x' ≫ y' ≫ φ = r'` for morphisms `x'`, `y'`, `φ`, `r'`
heterogeneously equal to `x`, `y`, `σ ≫ ε`, `r`. -/
theorem comp_comp_eq_of_comp_comp_heq {C : Type*} {_ : Category C} {O b c d e : C} {x : O ⟶ b}
    {y : b ⟶ c} {σ : c ⟶ d} {ε : d ⟶ e} {r : O ⟶ e} (h : (x ≫ y) ≫ σ ≫ ε = r)
    {O' b' c' e' : C} (x' : O' ⟶ b') (y' : b' ⟶ c') (φ : c' ⟶ e') (r' : O' ⟶ e')
    (hO : O' = O) (hb : b' = b) (hc : c' = c) (he : e' = e) (hx : HEq x' x) (hy : HEq y' y)
    (hφ : HEq φ (σ ≫ ε)) (hr : HEq r' r) :
    x' ≫ y' ≫ φ = r' := by
  subst hO hb hc he
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hr
  simpa only [Category.assoc] using h

end Abstract

attribute [local instance] modulesMonoidalCategory

section Descent

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {Mi Mj Mk : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τi : quasicoherentPullbackObj B S hS P.target Mi ⟶ quasicoherentPullbackObj B S hS P.source Mi)
  (hci : PresentationSchemeCocycle P Mi τi) (hui : PresentationSchemeUnit P Mi τi)
  (τj : quasicoherentPullbackObj B S hS P.target Mj ⟶ quasicoherentPullbackObj B S hS P.source Mj)
  (hcj : PresentationSchemeCocycle P Mj τj) (huj : PresentationSchemeUnit P Mj τj)
  (τk : quasicoherentPullbackObj B S hS P.target Mk ⟶ quasicoherentPullbackObj B S hS P.source Mk)
  (hck : PresentationSchemeCocycle P Mk τk) (huk : PresentationSchemeUnit P Mk τk)

/-- **Descended morphisms into descended modules carry a multiplication to the descended
multiplication, if they do so on the atlas.**  Let `ψ_n : Y_n ⟶ D(M_n)` (`n = i, j, k`) be
descended from chart morphisms `φ_n : c^*Y_n ⟶ M_n^a` and `μ : D(M_i) ⊗ D(M_j) ⟶ D(M_k)` a
multiplication whose inverse image along the atlas is the attached multiplication of
`m : M_i ⊗ M_j ⟶ M_k` (for instance `AlgebraicGeometry.Space.presentationDescendedMul`, by
`AlgebraicGeometry.Space.presentationDescendedMul_spec`).  If
`c^*Y_i ⊗ c^*Y_j ≅ c^*(Y_i ⊗ Y_j) ⟶ c^*Y_k` followed by `φ_k` is `(φ_i ⊗ φ_j)` followed by the
attached multiplication `M_i^a ⊗ M_j^a ⟶ M_k^a`, then `m_Y ≫ ψ_k = (ψ_i ⊗ ψ_j) ≫ μ`. -/
theorem presentationDescendedIntoHom_mul
    (m : quasicoherentTensorObj B S hS P.U Mi Mj ⟶ Mk)
    (μ : (presentationDescendedModule P Mi τi hci hui).obj ⊗
        (presentationDescendedModule P Mj τj hcj huj).obj ⟶
      (presentationDescendedModule P Mk τk hck huk).obj)
    (hμ : (modulePullback B S hS (presentationAtlas P)).map μ ≫
        (presentationDescendedModuleChartIso P Mk τk hck huk).hom =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P Mi τi hci hui).obj
          (presentationDescendedModule P Mj τj hcj huj).obj).hom ≫
        ((presentationDescendedModuleChartIso P Mi τi hci hui).hom ⊗ₘ
          (presentationDescendedModuleChartIso P Mj τj hcj huj).hom) ≫
        representedTensorChartMul B S hS m)
    (Yi Yj Yk : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (φi : (modulePullback B S hS (presentationAtlas P)).obj Yi.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj Mi).obj)
    (hφi : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Yi.obj)
      (presentationSchemeTransition P Mi τi) φi)
    (φj : (modulePullback B S hS (presentationAtlas P)).obj Yj.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj Mj).obj)
    (hφj : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Yj.obj)
      (presentationSchemeTransition P Mj τj) φj)
    (φk : (modulePullback B S hS (presentationAtlas P)).obj Yk.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj Mk).obj)
    (hφk : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Yk.obj)
      (presentationSchemeTransition P Mk τk) φk)
    (mY : Yi.obj ⊗ Yj.obj ⟶ Yk.obj)
    (h : (modulePullbackTensorIso B S hS (presentationAtlas P) Yi.obj Yj.obj).inv ≫
        (modulePullback B S hS (presentationAtlas P)).map mY ≫ φk =
      (φi ⊗ₘ φj) ≫ representedTensorChartMul B S hS m) :
    mY ≫ presentationDescendedIntoHom P τk hck huk Yk φk hφk =
      (presentationDescendedIntoHom P τi hci hui Yi φi hφi ⊗ₘ
          presentationDescendedIntoHom P τj hcj huj Yj φj hφj) ≫ μ := by
  have := Yi.property
  have := Yj.property
  have := isQuasicoherentOnSite_presentationDescendedModule P Mk τk hck huk
  have := isQuasicoherentOnSite_tensorObj B S hS X.obj X.property Yi.obj Yj.obj
  exact presentationAtlas_map_injective P
    (map_comp_eq_map_tensorHom_comp_of_chart (modulePullback B S hS (presentationAtlas P)) mY _ _ _
      _ (presentationDescendedModuleChartIso P Mi τi hci hui)
      (presentationDescendedModuleChartIso P Mj τj hcj huj)
      (presentationDescendedModuleChartIso P Mk τk hck huk) φi φj φk
      (modulePullbackTensorIso B S hS (presentationAtlas P) Yi.obj Yj.obj)
      (modulePullbackTensorIso B S hS (presentationAtlas P)
        (presentationDescendedModule P Mi τi hci hui).obj
        (presentationDescendedModule P Mj τj hcj huj).obj)
      (representedTensorChartMul B S hS m)
      (modulePullbackTensorIso_hom_naturality B S hS (presentationAtlas P) _ _)
      (presentationDescendedIntoHom_spec P τi hci hui Yi φi hφi)
      (presentationDescendedIntoHom_spec P τj hcj huj Yj φj hφj)
      (presentationDescendedIntoHom_spec P τk hck huk Yk φk hφk)
      hμ h)

/-- **Descended morphisms into descended modules carry a unit to the descended unit, if they do
so on the atlas.**  Let `ψ : Y ⟶ D(M_k)` be descended from a chart morphism `φ : c^*Y ⟶ M_k^a`
and `ν_D : 𝒪_X ⟶ D(M_k)` the descended unit of `ν : 𝒪_U ⟶ M_k`.  If
`𝒪 ≅ c^*𝒪_X ⟶ c^*Y` followed by `φ` is the attached morphism `𝒪 ≅ (𝒪_U)^a ⟶ M_k^a`, then
`e ≫ ψ = ν_D`. -/
theorem presentationDescendedIntoHom_unit
    (ν : quasicoherentUnitObj B S hS P.U ⟶ Mk)
    (hbt : RepresentedC3UnitCompat B S hS P.target)
    (hbs : RepresentedC3UnitCompat B S hS P.source)
    (hm : (quasicoherentPullbackUnitIso B S hS P.target).inv ≫
        quasicoherentPullbackMap B S hS P.target ν ≫ τk =
      (quasicoherentPullbackUnitIso B S hS P.source).inv ≫
        quasicoherentPullbackMap B S hS P.source ν)
    (Y : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (φ : (modulePullback B S hS (presentationAtlas P)).obj Y.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj Mk).obj)
    (hφ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Y.obj)
      (presentationSchemeTransition P Mk τk) φ)
    (e : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ Y.obj)
    (h : (modulePullbackUnitIso B S hS (presentationAtlas P)).inv ≫
        (modulePullback B S hS (presentationAtlas P)).map e ≫ φ =
      representedUnitChartHom B S hS ν) :
    e ≫ presentationDescendedIntoHom P τk hck huk Y φ hφ =
      presentationDescendedUnit P τk hck huk ν hbt hbs hm :=
  @presentationAtlas_map_injective _ _ _ _ P _ _ (SheafOfModules.isQuasicoherentOnSite_unit _)
    (isQuasicoherentOnSite_presentationDescendedModule P Mk τk hck huk) _ _
    (map_comp_eq_map_of_chart (modulePullback B S hS (presentationAtlas P)) e _ _
      (presentationDescendedModuleChartIso P Mk τk hck huk) φ
      (modulePullbackUnitIso B S hS (presentationAtlas P)) (representedUnitChartHom B S hS ν)
      (presentationDescendedIntoHom_spec P τk hck huk Y φ hφ)
      (presentationDescendedUnit_spec P τk hck huk ν hbt hbs hm) h)

end Descent

section SpacesUnit

/- The sheafification instances of the small étale site at the universe of the modules. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The unit of the pullback of a sheaf of graded algebras is the pulled-back unit** (Stacks
03LU for a morphism of algebraic spaces): for `f : X ⟶ Y` and a sheaf of graded algebras `𝒜` on
`Y`, `𝒪_X ≅ f^*𝒪_Y ⟶ f^*𝒜_0` is the unit of `f^*𝒜`.  The unit companion of
`AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_mulSheaf`. -/
theorem modulePullbackUnitIso_inv_comp_map_oneHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y)) (f : X ⟶ Y) :
    (modulePullbackUnitIso B S hS f).inv ≫
        (modulePullback B S hS f).map (SheafOfModules.GradedAlgebra.oneHom A) =
      SheafOfModules.GradedAlgebra.oneHom
        ((Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull
          (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).obj A) :=
  (Stacks.Sheaves.GradedAlgebraPullback.oneHom_toposPullbackGradedAlgebra
    (smallEtaleRingedToposModulesHom B S hS f) A).symm

/-- **The unit of the restriction of a sheaf of graded algebras to a scheme point is the
pulled-back unit**: for `u : T ⟶ X`, the unit of `u^*𝒜`
(`AlgebraicGeometry.Space.etalePointAlgebra`) is `𝒪 ≅ u^*𝒪_X ⟶ u^*𝒜_0`. -/
theorem oneHom_etalePointAlgebra
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y.1) :
    SheafOfModules.GradedAlgebra.oneHom (etalePointAlgebra A T f) =
      (modulePullbackUnitIso B S hS (pointHom f)).inv ≫
        (modulePullback B S hS (pointHom f)).map (SheafOfModules.GradedAlgebra.oneHom A) :=
  (modulePullbackUnitIso_inv_comp_map_oneHom A (pointHom f)).symm

end SpacesUnit

/-- The attached multiplication `M^a ⊗ N^a ⟶ K^a` of a morphism `m : M ⊗ N ⟶ K` is, by
definition, the inverse of the tensor identification of Stacks 03DX (2) followed by `m^a`. -/
theorem representedTensorChartMul_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U : BigFppfOver B S hS}
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    representedTensorChartMul B S hS m =
      (representedQuasicoherentSchemeTensorIso B S hS U M N).inv ≫
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom :=
  rfl

section ChartMul

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U : BigFppfOver B S hS}

/-- **The module attached by Stacks 03DX (2) to a multiplicative square is a multiplicative
square**: if `m ≫ a_k = (a_i ⊗ a_j) ≫ n` for morphisms of quasi-coherent modules on the scheme of
`U`, then the attached multiplications satisfy `m^a ≫ a_k^a = (a_i^a ⊗ a_j^a) ≫ n^a`. -/
theorem representedTensorChartMul_comp_map_hom_of_comp_eq
    {Mi Mj Mk Ni Nj Nk : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U Mi Mj ⟶ Mk)
    (n : quasicoherentTensorObj B S hS U Ni Nj ⟶ Nk) (ai : Mi ⟶ Ni) (aj : Mj ⟶ Nj)
    (ak : Mk ⟶ Nk) (h : m ≫ ak = quasicoherentTensorHom B S hS U ai aj ≫ n) :
    representedTensorChartMul B S hS m ≫
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map ak).hom =
      MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map ai).hom
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map aj).hom ≫
        representedTensorChartMul B S hS n := by
  have nat := representedQuasicoherentSchemeTensorIso_hom_naturality B S hS U ai aj
  have h' := congrArg (fun t => ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
    t).hom) h
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at h'
  have nat' : (representedQuasicoherentSchemeTensorIso B S hS U Mi Mj).inv ≫
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
        (quasicoherentTensorHom B S hS U ai aj)).hom =
      MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map ai).hom
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map aj).hom ≫
        (representedQuasicoherentSchemeTensorIso B S hS U Ni Nj).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 nat).trans (Category.assoc _ _ _))
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) h').trans
    (((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _) nat')).trans
      (Category.assoc _ _ _)))

/-- **The module attached by Stacks 03DX (2) to a unital triangle is a unital triangle**: if
`u ≫ a = ν` for morphisms of quasi-coherent modules on the scheme of `U` out of `𝒪_U`, then the
attached morphisms satisfy `u^a ≫ a^a = ν^a`
(`AlgebraicGeometry.Space.representedUnitChartHom`). -/
theorem representedUnitChartHom_comp_map_hom_of_comp_eq
    {K N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (u : quasicoherentUnitObj B S hS U ⟶ K) (a : K ⟶ N) (ν : quasicoherentUnitObj B S hS U ⟶ N)
    (h : u ≫ a = ν) :
    representedUnitChartHom B S hS u ≫
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map a).hom =
      representedUnitChartHom B S hS ν := by
  have h' := congrArg (fun t => ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
    t).hom) h
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at h'
  exact (Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t) h')

end ChartMul


section ZariskiUnit

/- The sheafification instances of the small étale site at the universe of the modules. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The identification `u^*𝒜_0 ≅ (Z_0)^a` carries the pulled-back unit to the unit of the
Zariski reading**: for a sheaf of graded algebras `𝒜` on `X` with quasi-coherent pieces and a
scheme point `u : T ⟶ X`, the identification of `u^*𝒜` with the modules attached to its Zariski
readings carries `𝒪 ≅ u^*𝒪 ⟶ u^*𝒜_0` to the unit of the Zariski reading of `u^*𝒜`
(`AlgebraicGeometry.Space.ZariskiReadingIsoOneCompat`).  This is
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso_oneHom` with the unit of `u^*𝒜` read as
the pulled-back unit (`AlgebraicGeometry.Space.oneHom_etalePointAlgebra`). -/
theorem zariskiReadingIsoOneCompat_modulePullbackUnitIso_inv_comp_map_oneHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite) (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X.1) :
    ZariskiReadingIsoOneCompat B S hS T (etalePointAlgebra A T f)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f 0)
      ((modulePullbackUnitIso B S hS (pointHom f)).inv ≫
        (modulePullback B S hS (pointHom f)).map (SheafOfModules.GradedAlgebra.oneHom A))
      (ObjectProperty.homMk
        (SheafOfModules.GradedAlgebra.oneHom (zariskiReading T (etalePointAlgebra A T f)))) :=
  (congrArg (fun e => e ≫ (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece 0)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f 0)).hom)
    (oneHom_etalePointAlgebra A T f).symm).trans
    (zariskiReadingQuasicoherentIso_oneHom T (etalePointAlgebra A T f)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f))

end ZariskiUnit

namespace RelativeProjSituation

section Psi

attribute [local irreducible] CategoryTheory.yoneda

/- The sheafification instances of the small étale site at the universe of the modules. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (s : RelativeProjSituation.{u, m})

/-- **The multiplication of the source `π^*𝒜` of `ψ`**: `π^*𝒜_i ⊗ π^*𝒜_j ≅ π^*(𝒜_i ⊗ 𝒜_j) ⟶
π^*𝒜_{i+j}`, the inverse image of the multiplication of `𝒜` read through Stacks 03EL; it is the
multiplication of the pullback of `𝒜` as a sheaf of graded algebras
(`AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_mulSheaf`). -/
def psiSourceMul (i j : ℤ) :
    (s.psiSourceQcoh i).obj ⊗ (s.psiSourceQcoh j).obj ⟶ (s.psiSourceQcoh (i + j)).obj :=
  (modulePullbackTensorIso s.site s.base s.containsBase s.relativeProjSpaceHom
      (s.shrink.algebra.piece i) (s.shrink.algebra.piece j)).inv ≫
    (modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).map
      ((modulesTensorObjIso s.site s.base s.containsBase s.space.1 s.space.2
          (s.shrink.algebra.piece i) (s.shrink.algebra.piece j)).hom ≫
        SheafOfModules.GradedAlgebra.mulSheaf s.shrink.algebra i j)

/-- **The unit of the source `π^*𝒜` of `ψ`**: `𝒪_P ≅ π^*𝒪_X ⟶ π^*𝒜_0`, the inverse image of the
unit of `𝒜` read through Stacks 03LU; it is the unit of the pullback of `𝒜` as a sheaf of graded
algebras (`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_oneHom`). -/
def psiSourceUnit :
    SheafOfModules.unit (structureRingSheaf s.site s.base s.containsBase
        ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩) ⟶
      (s.psiSourceQcoh 0).obj :=
  (modulePullbackUnitIso s.site s.base s.containsBase s.relativeProjSpaceHom).inv ≫
    (modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).map
      (SheafOfModules.GradedAlgebra.oneHom s.shrink.algebra)

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **`ψ` of Tag 01NR on the scheme of `U ×_X P` is multiplicative**, as an equation of
quasi-coherent modules on that scheme: `π_U^*Z_i ⊗ π_U^*Z_j ≅ π_U^*(Z_i ⊗ Z_j) ⟶ π_U^*Z_{i+j}`
(the multiplication of the Zariski reading `Z` of `u^*𝒜`) followed by `ψ_{i+j}`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`) is `ψ_i ⊗ ψ_j`
followed by the multiplication of the twists. -/
def PsiChartSchemeMulCompat (i j : ℕ) : Prop :=
  ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
      (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
      (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ))
      (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ))).inv ≫
    quasicoherentPullbackMap s.site s.base s.containsBase
      (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
          (zariskiReading Px.U (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace))
          (i : ℤ) (j : ℤ)) :
        quasicoherentTensorObj s.site s.base s.containsBase Px.U
            (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ))
            (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ)) ⟶
          presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
            ((i : ℤ) + (j : ℤ)))) ≫
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace (i + j)) :
      quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
          (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
            ((i + j : ℕ) : ℤ)) ⟶
        s.twistPieceQcoh Px.U Px.toSpace ((i + j : ℕ) : ℤ)) =
    quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace i) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (i : ℤ))
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace j) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (j : ℤ)) ≫
      s.twistPieceMul Px.U Px.toSpace (i : ℤ) (j : ℤ)

/-- **`ψ` of Tag 01NR on the scheme of `U ×_X P` is unital**, as an equation of quasi-coherent
modules on that scheme: `𝒪 ≅ π_U^*𝒪_U ⟶ π_U^*Z_0` (the pulled-back unit of the Zariski reading `Z`
of `u^*𝒜`) followed by `ψ_0` is the unit of the twists. -/
def PsiChartSchemeUnitCompat : Prop :=
  ((quasicoherentPullbackUnitIso s.site s.base s.containsBase
      (s.relativeProjPoints.fibreHom Px.U Px.toSpace)).inv ≫
    quasicoherentPullbackMap s.site s.base s.containsBase
      (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom
        (zariskiReading Px.U (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace))) :
        quasicoherentUnitObj s.site s.base s.containsBase Px.U ⟶
          presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent 0)) ≫
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace 0) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
            (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
              ((0 : ℕ) : ℤ)) ⟶
          s.twistPieceQcoh Px.U Px.toSpace ((0 : ℕ) : ℤ)) =
    s.twistPieceUnit Px.U Px.toSpace

/-- **`ψ` on the atlas is multiplicative, factor by factor**: if `ψ` of Tag 01NR on the scheme of
`U ×_X P` is multiplicative
(`AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeMulCompat`), then `σ_n ≫ E(ψ_n)`
(`σ_n = AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`)
carries the multiplication of `c^*π^*𝒜` to the multiplication attached to the twists.  The
algebraic space of `U ×_X P` is spelled as the represented algebraic space of the fibre; the
statement is the type of its proof. -/
theorem psiChartSourceIso_hom_comp_mul (i j : ℕ) (hB : s.PsiChartSchemeMulCompat Px i j) :
    type_of% (mulSquare_comp _ _ _ _ _ _ _ _ _
      (s.psiChartSourceIso_hom_mul Px (i : ℤ) (j : ℤ) _
        (zariskiReadingQuasicoherentIso_mulSheaf Px.U
          (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace)
          (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
            Px.toSpace) (i : ℤ) (j : ℤ)))
      (representedTensorChartMul_comp_map_hom_of_comp_eq _ _ _ _ _ hB)) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    (s.psiChartSourceIso_hom_mul Px (i : ℤ) (j : ℤ) _
      (zariskiReadingQuasicoherentIso_mulSheaf Px.U
        (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace)
        (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
          Px.toSpace) (i : ℤ) (j : ℤ)))
    (representedTensorChartMul_comp_map_hom_of_comp_eq _ _ _ _ _ hB)

/-- **`ψ` on the atlas is multiplicative** (the chart identity of
`AlgebraicGeometry.Space.presentationDescendedIntoHom_mul` for `ψ`): if `ψ` of Tag 01NR on the
scheme of `U ×_X P` is multiplicative, then
`c^*π^*𝒜_i ⊗ c^*π^*𝒜_j ≅ c^*(π^*𝒜_i ⊗ π^*𝒜_j) ⟶ c^*π^*𝒜_{i+j}` followed by `ψ_{i+j}` on the
atlas (`AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint`) is `ψ_i ⊗ ψ_j` on the
atlas followed by the multiplication attached to the multiplication of the twists. -/
theorem psiChartHomOfAdjoint_mul (i j : ℕ) (hB : s.PsiChartSchemeMulCompat Px i j) :
    (modulePullbackTensorIso s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
        (s.psiSourceQcoh (i : ℤ)).obj (s.psiSourceQcoh (j : ℤ)).obj).inv ≫
      (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        (s.psiSourceMul (i : ℤ) (j : ℤ)) ≫
      s.psiChartHomOfAdjoint Px (i + j) =
    (s.psiChartHomOfAdjoint Px i ⊗ₘ s.psiChartHomOfAdjoint Px j) ≫
      representedTensorChartMul s.site s.base s.containsBase
        (s.twistPieceMul Px.U Px.toSpace (i : ℤ) (j : ℤ)) := by
  unfold psiChartHomOfAdjoint
  refine comp_comp_eq_tensorHom_comp_of_heq (s.psiChartSourceIso_hom_comp_mul Px i j hB)
    _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | with_reducible rfl
    | (refine eq_of_heq ?_; heq_congr)
    | heq_congr

/-- **`ψ` of Stacks 084D is multiplicative, given that `ψ` of Tag 01NR on the scheme of `U ×_X P`
is**: `π^*𝒜_i ⊗ π^*𝒜_j ≅ π^*(𝒜_i ⊗ 𝒜_j) ⟶ π^*𝒜_{i+j}` followed by `ψ_{i+j}` is `ψ_i ⊗ ψ_j`
followed by the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the twists
(`AlgebraicGeometry.Space.presentationDescendedIntoHom_mul` on the presentation `P = P_U/P_R`). -/
theorem psiSourceMul_comp_psiTwistHom_of_psiChartSchemeMulCompat (i j : ℕ)
    (hB : s.PsiChartSchemeMulCompat Px i j) :
    s.psiSourceMul (i : ℤ) (j : ℤ) ≫ s.psiTwistHom Px (i + j) =
      (s.psiTwistHom Px i ⊗ₘ s.psiTwistHom Px j) ≫ s.twistAlgebraMul Px (i : ℤ) (j : ℤ) := by
  refine presentationDescendedIntoHom_mul
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.twistTransition Px (i : ℤ)) (s.presentationSchemeCocycle_twistTransition Px (i : ℤ))
    (s.presentationSchemeUnit_twistTransition Px (i : ℤ))
    (s.twistTransition Px (j : ℤ)) (s.presentationSchemeCocycle_twistTransition Px (j : ℤ))
    (s.presentationSchemeUnit_twistTransition Px (j : ℤ))
    (s.twistTransition Px ((i + j : ℕ) : ℤ))
    (s.presentationSchemeCocycle_twistTransition Px ((i + j : ℕ) : ℤ))
    (s.presentationSchemeUnit_twistTransition Px ((i + j : ℕ) : ℤ))
    (s.twistPieceMul Px.U Px.toSpace (i : ℤ) (j : ℤ)) (s.twistAlgebraMul Px (i : ℤ) (j : ℤ))
    (s.twistAlgebraMul_spec Px (i : ℤ) (j : ℤ))
    (s.psiSourceQcoh (i : ℤ)) (s.psiSourceQcoh (j : ℤ)) (s.psiSourceQcoh ((i + j : ℕ) : ℤ))
    (s.psiChartHomOfAdjoint Px i) (s.transitionCommutes_psiChartHomOfAdjoint Px i)
    (s.psiChartHomOfAdjoint Px j) (s.transitionCommutes_psiChartHomOfAdjoint Px j)
    (s.psiChartHomOfAdjoint Px (i + j)) (s.transitionCommutes_psiChartHomOfAdjoint Px (i + j))
    (s.psiSourceMul (i : ℤ) (j : ℤ)) ?_
  refine eq_of_heq (HEq.trans ?_ (HEq.trans
    (heq_of_eq (s.psiChartHomOfAdjoint_mul Px i j hB)) ?_)) <;> heq_congr

/-- **`ψ` on the atlas is unital, factor by factor**: if `ψ` of Tag 01NR on the scheme of
`U ×_X P` is unital (`AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeUnitCompat`),
then `σ_0 ≫ E(ψ_0)` carries the unit of `c^*π^*𝒜` to the morphism attached to the unit of the
twists.  The statement is the type of its proof. -/
theorem psiChartSourceIso_hom_comp_one (hB : s.PsiChartSchemeUnitCompat Px) :
    type_of% (unitSquare_comp _ _ _ _ _
      (s.psiChartSourceIso_hom_one Px _
        (zariskiReadingIsoOneCompat_modulePullbackUnitIso_inv_comp_map_oneHom s.shrink.algebra
          s.shrink.isQuasicoherent Px.U Px.toSpace))
      (representedUnitChartHom_comp_map_hom_of_comp_eq _ _ _ hB)) :=
  unitSquare_comp _ _ _ _ _
    (s.psiChartSourceIso_hom_one Px _
      (zariskiReadingIsoOneCompat_modulePullbackUnitIso_inv_comp_map_oneHom s.shrink.algebra
        s.shrink.isQuasicoherent Px.U Px.toSpace))
    (representedUnitChartHom_comp_map_hom_of_comp_eq _ _ _ hB)

/-- **`ψ` on the atlas is unital** (the chart identity of
`AlgebraicGeometry.Space.presentationDescendedIntoHom_unit` for `ψ`): if `ψ` of Tag 01NR on the
scheme of `U ×_X P` is unital, then `𝒪 ≅ c^*𝒪_P ⟶ c^*π^*𝒜_0` followed by `ψ_0` on the atlas is
the morphism attached to the unit of the twists. -/
theorem psiChartHomOfAdjoint_one (hB : s.PsiChartSchemeUnitCompat Px) :
    (modulePullbackUnitIso s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).inv ≫
      (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        s.psiSourceUnit ≫
      s.psiChartHomOfAdjoint Px 0 =
    representedUnitChartHom s.site s.base s.containsBase (s.twistPieceUnit Px.U Px.toSpace) := by
  unfold psiChartHomOfAdjoint
  refine comp_comp_eq_of_comp_comp_heq (s.psiChartSourceIso_hom_comp_one Px hB)
    _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | with_reducible rfl
    | (refine eq_of_heq ?_; heq_congr)
    | heq_congr

/-- **`ψ` of Stacks 084D is unital, given that `ψ` of Tag 01NR on the scheme of `U ×_X P` is**:
`𝒪_P ≅ π^*𝒪_X ⟶ π^*𝒜_0` followed by `ψ_0` is the unit `𝒪_P ⟶ 𝒪_P(0)` of the twists
(`AlgebraicGeometry.Space.presentationDescendedIntoHom_unit` on the presentation
`P = P_U/P_R`). -/
theorem psiSourceUnit_comp_psiTwistHom_of_psiChartSchemeUnitCompat
    (hB : s.PsiChartSchemeUnitCompat Px) :
    s.psiSourceUnit ≫ s.psiTwistHom Px 0 = s.twistAlgebraUnit Px :=
  presentationDescendedIntoHom_unit
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.twistTransition Px 0) (s.presentationSchemeCocycle_twistTransition Px 0)
    (s.presentationSchemeUnit_twistTransition Px 0) (s.twistPieceUnit Px.U Px.toSpace)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (s.relativeProjPoints.spacePresentation_unit_transition Px
      s.isAlgebraicSpace_relativeProjFunctor (s.twistTransition Px 0)
      (s.twistPieceUnit Px.U Px.toSpace)
      ((s.relativeProjPoints.transitionUnitCompat_iff Px s.isAlgebraicSpace_relativeProjFunctor
        (s.twistTransition Px 0) (s.twistPieceUnit Px.U Px.toSpace)).1
        (s.transitionUnitCompat_twistTransition Px)))
    (s.psiSourceQcoh 0) (s.psiChartHomOfAdjoint Px 0)
    (s.transitionCommutes_psiChartHomOfAdjoint Px 0) s.psiSourceUnit
    (s.psiChartHomOfAdjoint_one Px hB)

end Psi

end RelativeProjSituation


end AlgebraicGeometry.Space

end
