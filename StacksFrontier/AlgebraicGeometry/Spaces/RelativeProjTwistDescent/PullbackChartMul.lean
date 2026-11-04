module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPsi
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SpaceBaseDescentTensor

/-!
# Inverse images of multiplications read through chart identifications

Let `c'' ≫ h = Y ≫ c` be a commutative square of algebraic spaces, `𝒯_i ⊗ 𝒯_j ⟶ 𝒯_{i+j}` a
multiplication of `𝒪`-modules on the target of `h`, and `e_n : h^*𝒯_n ≅ 𝒢_n` identifications
which on `c''` are read, through the identification `c''^*h^*𝒯 ≅ Y^*c^*𝒯` along the square, from
chart identifications of `c^*𝒯_n`.  This file shows that the `e_n` carry the inverse image of the
multiplication, read through Stacks 03EL, to a multiplication of the `𝒢_n`, as soon as the chart
identifications carry the multiplications to one another and the inverse image along `c''` is
faithful; and the same for units, read through Stacks 03LU.  This is the step of the base change
clause of Stacks 084D which identifies the base change of `⨁_n 𝒪_P(n)` with the graded algebra
of Stacks 01NR, and not only its pieces.

## Main results

* `AlgebraicGeometry.Space.pullbackSquareHom_tensor`,
  `AlgebraicGeometry.Space.pullbackSquareHom_unit`: the identification along a square is
  compatible with Stacks 03EL and with Stacks 03LU.
* `AlgebraicGeometry.Space.modulePullback_map_representedTensorChartMul_comp`: for a morphism `g`
  of the site, the inverse image along `g` of the multiplication `M^a ⊗ N^a ⟶ K^a` attached to a
  scheme multiplication is the attached multiplication of the pulled-back modules, through
  identifications carrying the pulled-back scheme multiplication to another one.
* `AlgebraicGeometry.Space.modulePullback_map_representedUnitChartHom_comp`: the same for units.
* `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_comp_of_chart` and
  `AlgebraicGeometry.Space.pullbackUnitIso_inv_comp_map_comp_of_chart`: **identifications read
  from chart identifications carry multiplications and units to multiplications and units.**

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory


/-! ### Abstract shapes -/

section Abstract

/-- The abstract shape of `AlgebraicGeometry.Space.pullbackSquareHom_unit`. -/
private theorem comp_eq_of_unit_readings {C : Type*} [Category C] {a b b' d o o' o'' : C}
    (cH : a ⟶ b) (pT : b ⟶ b') (cI : b' ⟶ d) (cH₂ : d ⟶ b') (hinv : cI ≫ cH₂ = 𝟙 b')
    (U₁ : b ⟶ o) (U₂ : b' ⟶ o) (p : a ⟶ o'') (q : o'' ⟶ o) (r : d ⟶ o') (t : o' ⟶ o)
    (h₁ : cH ≫ U₁ = p ≫ q) (h₂ : cH₂ ≫ U₂ = r ≫ t) (h₃ : pT ≫ U₂ = U₁)
    (sq : a ⟶ d) (hsq : sq = cH ≫ pT ≫ cI) :
    sq ≫ r ≫ t = p ≫ q := by
  subst hsq
  rw [Category.assoc, Category.assoc, ← h₂, reassoc_of% hinv, h₃, h₁]

/-- If `Pg` carries `TU.hom` to a reading `s` of an iso `TR` through `c ≫ es`, then `Pg.map TU.inv`
followed by `c` is `s ≫ TR.inv ≫ es'`, where `es'` is a retraction of `es`. -/
private theorem map_inv_comp_eq_of_readings {CU CV : Type*} [Category CU] [Category CV]
    (Pg : CU ⥤ CV) {A B : CU} {X Y Z : CV} (TU : A ≅ B) (c : Pg.obj A ⟶ X) (s : Pg.obj B ⟶ Y)
    (es : X ⟶ Z) (es' : Z ⟶ X) (hes : es ≫ es' = 𝟙 _) (TR : Z ≅ Y)
    (hb : Pg.map TU.hom ≫ s = c ≫ es ≫ TR.hom) : Pg.map TU.inv ≫ c = s ≫ TR.inv ≫ es' := by
  rw [← cancel_epi (Pg.map TU.hom), ← Pg.map_comp_assoc, Iso.hom_inv_id, Pg.map_id,
    Category.id_comp, reassoc_of% hb, Iso.hom_inv_id_assoc, hes, Category.comp_id]

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_representedTensorChartMul_comp`. -/
private theorem tensorChartMul_comp_of_readings {CU CV : Type*} [Category CU] [MonoidalCategory CU]
    [Category CV] [MonoidalCategory CV] (Pg : CU ⥤ CV) {AM AN AK AMN : CU}
    (TU : AMN ≅ AM ⊗ AN) (Am : AMN ⟶ AK) (sA : Pg.obj (AM ⊗ AN) ≅ Pg.obj AM ⊗ Pg.obj AN)
    {MV NV KV MNV QS M' N' K' Q' : CV}
    (cM : Pg.obj AM ≅ MV) (cN : Pg.obj AN ≅ NV) (cK : Pg.obj AK ≅ KV) (cMN : Pg.obj AMN ≅ MNV)
    (es : MNV ⟶ QS) (es' : QS ⟶ MNV) (hes : es ≫ es' = 𝟙 _) (TRs : QS ≅ MV ⊗ NV)
    (ms : MNV ⟶ KV) (ΘM : MV ⟶ M') (ΘN : NV ⟶ N') (ΘK : KV ⟶ K') (TR' : Q' ≅ M' ⊗ N')
    (q : QS ⟶ Q') (m' : Q' ⟶ K')
    (hb : Pg.map TU.hom ≫ sA.hom ≫ (cM.hom ⊗ₘ cN.hom) = cMN.hom ≫ es ≫ TRs.hom)
    (ns : Pg.map Am ≫ cK.hom = cMN.hom ≫ ms) (hm : es' ≫ ms ≫ ΘK = q ≫ m')
    (hT : q ≫ TR'.hom = TRs.hom ≫ (ΘM ⊗ₘ ΘN))
    (f : AM ⊗ AN ⟶ AK) (hf : f = TU.inv ≫ Am) (f' : M' ⊗ N' ⟶ K') (hf' : f' = TR'.inv ≫ m') :
    Pg.map f ≫ cK.hom ≫ ΘK = sA.hom ≫ ((cM.hom ≫ ΘM) ⊗ₘ (cN.hom ≫ ΘN)) ≫ f' := by
  subst hf hf'
  have h1 := map_inv_comp_eq_of_readings Pg TU cMN.hom _ es es' hes TRs hb
  have hT' : TRs.inv ≫ q = (ΘM ⊗ₘ ΘN) ≫ TR'.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hT, Iso.hom_inv_id, Category.comp_id]
  rw [Pg.map_comp, Category.assoc, reassoc_of% ns, reassoc_of% h1, hm, reassoc_of% hT']
  simp only [tensorHom_comp_tensorHom_assoc]

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_representedUnitChartHom_comp`. -/
private theorem unitChartHom_comp_of_readings {CU CV : Type*} [Category CU] [Category CV]
    (Pg : CU ⥤ CV) {AO OU AK : CU} (TU : AO ≅ OU) (Au : AO ⟶ AK) {OV OV' KV QS K' : CV}
    (sA : Pg.obj OU ≅ OV) (cO : Pg.obj AO ≅ OV') (cK : Pg.obj AK ≅ KV)
    (es : OV' ⟶ QS) (es' : QS ⟶ OV') (hes : es ≫ es' = 𝟙 _) (TRs : QS ≅ OV)
    (ms : OV' ⟶ KV) (ΘK : KV ⟶ K') (ν' : QS ⟶ K')
    (hb : Pg.map TU.hom ≫ sA.hom = cO.hom ≫ es ≫ TRs.hom)
    (ns : Pg.map Au ≫ cK.hom = cO.hom ≫ ms) (hm : es' ≫ ms ≫ ΘK = ν')
    (f : OU ⟶ AK) (hf : f = TU.inv ≫ Au) (f' : OV ⟶ K') (hf' : f' = TRs.inv ≫ ν') :
    Pg.map f ≫ cK.hom ≫ ΘK = sA.hom ≫ f' := by
  subst hf hf'
  have h1 := map_inv_comp_eq_of_readings Pg TU cO.hom _ es es' hes TRs hb
  rw [Pg.map_comp, Category.assoc, reassoc_of% ns, reassoc_of% h1, hm]

/-- A functor carries an equation `a⁻¹ ≫ b ≫ c = d ≫ e` to the equation of the images. -/
private theorem map_inv_comp_eq_of_eq {E D : Type*} [Category E] [Category D] (G : E ⥤ D)
    {P Q K K' T : E} (a : P ≅ Q) (b : P ⟶ K) (c : K ⟶ K') (d : Q ⟶ T) (e : T ⟶ K')
    (h : a.inv ≫ b ≫ c = d ≫ e) : G.map a.inv ≫ G.map b ≫ G.map c = G.map d ≫ G.map e := by
  rw [← G.map_comp, ← G.map_comp, ← G.map_comp, h]

/-- A functor carries an equation `a⁻¹ ≫ b ≫ c = d` to the equation of the images. -/
private theorem map_inv_comp_eq_of_eq' {E D : Type*} [Category E] [Category D] (G : E ⥤ D)
    {P Q K K' : E} (a : P ≅ Q) (b : P ⟶ K) (c : K ⟶ K') (d : Q ⟶ K')
    (h : a.inv ≫ b ≫ c = d) : G.map a.inv ≫ G.map b ≫ G.map c = G.map d := by
  rw [← G.map_comp, ← G.map_comp, h]

/-- The abstract shape of `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_comp_of_chart`:
`F` is the inverse image along `c''`, `G` the inverse image along `Y`, `s` the identifications
along the square. -/
private theorem mul_comp_eq_of_chart_readings {CW CU D : Type*} [Category CW] [MonoidalCategory CW]
    [Category CU] [MonoidalCategory CU] [Category D] [MonoidalCategory D] (F : CW ⥤ D)
    (G : CU ⥤ D)
    {hTi hTj hTij hTk Gi Gj Gk : CW} (tI : hTij ≅ hTi ⊗ hTj) (hμ : hTij ⟶ hTk)
    (ei : hTi ⟶ Gi) (ej : hTj ⟶ Gj) (ek : hTk ⟶ Gk) (μG : Gi ⊗ Gj ⟶ Gk)
    {cTi cTj cTij cTk Ki Kj Kk : CU} (tc : cTij ≅ cTi ⊗ cTj) (cμ : cTij ⟶ cTk)
    (κi : cTi ⟶ Ki) (κj : cTj ⟶ Kj) (κk : cTk ⟶ Kk) (μK : Ki ⊗ Kj ⟶ Kk)
    (hcμ : cμ ≫ κk = tc.hom ≫ (κi ⊗ₘ κj) ≫ μK)
    {Li Lj Lk : D} (ℓi : G.obj Ki ⟶ Li) (ℓj : G.obj Kj ⟶ Lj) (ℓk : G.obj Kk ⟶ Lk)
    (μL : Li ⊗ Lj ⟶ Lk)
    (tY : G.obj (Ki ⊗ Kj) ⟶ G.obj Ki ⊗ G.obj Kj) (tY' : G.obj (cTi ⊗ cTj) ⟶ G.obj cTi ⊗ G.obj cTj)
    (hnY : G.map (κi ⊗ₘ κj) ≫ tY = tY' ≫ (G.map κi ⊗ₘ G.map κj))
    (hℓ : G.map μK ≫ ℓk = tY ≫ (ℓi ⊗ₘ ℓj) ≫ μL)
    (si : F.obj hTi ⟶ G.obj cTi) (sj : F.obj hTj ⟶ G.obj cTj) (sij : F.obj hTij ⟶ G.obj cTij)
    (sk : F.obj hTk ⟶ G.obj cTk)
    (hnat : F.map hμ ≫ sk = sij ≫ G.map cμ)
    (tF : F.obj (hTi ⊗ hTj) ⟶ F.obj hTi ⊗ F.obj hTj)
    (hsq : F.map tI.hom ≫ tF ≫ (si ⊗ₘ sj) = sij ≫ G.map tc.hom ≫ tY')
    (ρi : F.obj Gi ⟶ Li) (ρj : F.obj Gj ⟶ Lj) (ρk : F.obj Gk ≅ Lk)
    (tFG : F.obj (Gi ⊗ Gj) ⟶ F.obj Gi ⊗ F.obj Gj)
    (hρ : F.map μG ≫ ρk.hom = tFG ≫ (ρi ⊗ₘ ρj) ≫ μL)
    (hnc : F.map (ei ⊗ₘ ej) ≫ tFG = tF ≫ (F.map ei ⊗ₘ F.map ej))
    (χi : F.obj hTi ⟶ Li) (χj : F.obj hTj ⟶ Lj) (χk : F.obj hTk ⟶ Lk)
    (hei : F.map ei ≫ ρi = χi) (hej : F.map ej ≫ ρj = χj) (hek : F.map ek ≫ ρk.hom = χk)
    (hχi : χi = si ≫ G.map κi ≫ ℓi) (hχj : χj = sj ≫ G.map κj ≫ ℓj)
    (hχk : χk = sk ≫ G.map κk ≫ ℓk)
    (hinj : ∀ φ ψ : hTi ⊗ hTj ⟶ Gk, F.map φ = F.map ψ → φ = ψ) :
    tI.inv ≫ hμ ≫ ek = (ei ⊗ₘ ej) ≫ μG := by
  subst hχi hχj hχk
  refine hinj _ _ ((Iso.cancel_iso_hom_right _ _ ρk).1 ?_)
  have hGμ : G.map cμ ≫ G.map κk ≫ ℓk =
      G.map tc.hom ≫ tY' ≫ (G.map κi ⊗ₘ G.map κj) ≫ (ℓi ⊗ₘ ℓj) ≫ μL := by
    rw [← G.map_comp_assoc, hcμ, G.map_comp, G.map_comp, Category.assoc, Category.assoc, hℓ,
      reassoc_of% hnY]
  calc F.map (tI.inv ≫ hμ ≫ ek) ≫ ρk.hom
      = F.map tI.inv ≫ (F.map hμ ≫ sk) ≫ G.map κk ≫ ℓk := by
        rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, hek, Category.assoc]
    _ = F.map tI.inv ≫ (sij ≫ G.map tc.hom ≫ tY') ≫ (G.map κi ⊗ₘ G.map κj) ≫ (ℓi ⊗ₘ ℓj) ≫
          μL := by
        rw [hnat, Category.assoc, hGμ]
        simp only [Category.assoc]
    _ = tF ≫ ((si ≫ G.map κi ≫ ℓi) ⊗ₘ (sj ≫ G.map κj ≫ ℓj)) ≫ μL := by
        rw [← hsq]
        simp only [Category.assoc, tensorHom_comp_tensorHom_assoc]
        rw [Iso.map_inv_hom_id_assoc]
    _ = F.map ((ei ⊗ₘ ej) ≫ μG) ≫ ρk.hom := by
        rw [F.map_comp, Category.assoc, hρ, reassoc_of% hnc, tensorHom_comp_tensorHom_assoc,
          hei, hej]

/-- The abstract shape of `AlgebraicGeometry.Space.pullbackUnitIso_inv_comp_map_comp_of_chart`. -/
private theorem unit_comp_eq_of_chart_readings {CW CU D : Type*} [Category CW] [Category CU]
    [Category D] (F : CW ⥤ D) (G : CU ⥤ D) {hO OW hT GT : CW} (tI : hO ≅ OW) (hν : hO ⟶ hT)
    (e : hT ⟶ GT) (νG : OW ⟶ GT) {cO OU cT K : CU} (uc : cO ⟶ OU) (cν : cO ⟶ cT) (κ : cT ⟶ K)
    (νK : OU ⟶ K) (hcν : cν ≫ κ = uc ≫ νK) {L OD : D} (ℓ : G.obj K ⟶ L) (uY : G.obj OU ⟶ OD)
    (νL : OD ⟶ L) (hℓ : G.map νK ≫ ℓ = uY ≫ νL)
    (sO : F.obj hO ⟶ G.obj cO) (sT : F.obj hT ⟶ G.obj cT)
    (hnat : F.map hν ≫ sT = sO ≫ G.map cν) (uF : F.obj OW ⟶ OD)
    (hsq : sO ≫ G.map uc ≫ uY = F.map tI.hom ≫ uF)
    (ρ : F.obj GT ≅ L) (hρ : F.map νG ≫ ρ.hom = uF ≫ νL)
    (χ : F.obj hT ⟶ L) (he : F.map e ≫ ρ.hom = χ) (hχ : χ = sT ≫ G.map κ ≫ ℓ)
    (hinj : ∀ φ ψ : OW ⟶ GT, F.map φ = F.map ψ → φ = ψ) :
    tI.inv ≫ hν ≫ e = νG := by
  subst hχ
  refine hinj _ _ ((Iso.cancel_iso_hom_right _ _ ρ).1 ?_)
  calc F.map (tI.inv ≫ hν ≫ e) ≫ ρ.hom
      = F.map tI.inv ≫ (F.map hν ≫ sT) ≫ G.map κ ≫ ℓ := by
        rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, he, Category.assoc]
    _ = F.map tI.inv ≫ (sO ≫ G.map uc ≫ uY) ≫ νL := by
        rw [hnat, Category.assoc, ← G.map_comp_assoc, hcν, G.map_comp, Category.assoc, hℓ]
        simp only [Category.assoc]
    _ = F.map νG ≫ ρ.hom := by
        rw [hsq, hρ, Category.assoc, Iso.map_inv_hom_id_assoc]

end Abstract

/-! ### The identification along a square, tensor products and units -/

section Square

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
  (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c)

/-- **The identification `c''^*h^*𝒯 ≅ Y^*c^*𝒯` along a square is compatible with Stacks 03EL.** -/
theorem pullbackSquareHom_tensor (T₁ T₂ : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS c'').map (modulePullbackTensorIso B S hS h T₁ T₂).hom ≫
        (modulePullbackTensorIso B S hS c'' _ _).hom ≫
          (pullbackSquareHom c'' c h Y hY T₁ ⊗ₘ pullbackSquareHom c'' c h Y hY T₂) =
      pullbackSquareHom c'' c h Y hY (T₁ ⊗ T₂) ≫
        (modulePullback B S hS Y).map (modulePullbackTensorIso B S hS c T₁ T₂).hom ≫
          (modulePullbackTensorIso B S hS Y _ _).hom := by
  rw [pullbackSquareHom_eq_comp, pullbackSquareHom_eq_comp, pullbackSquareHom_eq_comp]
  exact unflatten_tensor_of_readings _ _ _ _ _ _ _ _ _
    (modulePullbackCompInv_comp_compHom B S hS Y c (T₁ ⊗ T₂))
    (modulePullbackCompHom_comp_compInv B S hS Y c T₁)
    (modulePullbackCompHom_comp_compInv B S hS Y c T₂) _ _ _ _ _ _ _ _ _
    (modulePullbackCompHom_tensor B S hS c'' h T₁ T₂)
    (modulePullbackCompHom_tensor B S hS Y c T₁ T₂)
    (pullbackTransport_tensor B S hS hY T₁ T₂)

/-- **The identification `c''^*h^*𝒪 ≅ Y^*c^*𝒪` along a square is compatible with Stacks 03LU.** -/
theorem pullbackSquareHom_unit :
    pullbackSquareHom c'' c h Y hY (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePullback B S hS Y).map (modulePullbackUnitIso B S hS c).hom ≫
          (modulePullbackUnitIso B S hS Y).hom =
      (modulePullback B S hS c'').map (modulePullbackUnitIso B S hS h).hom ≫
        (modulePullbackUnitIso B S hS c'').hom :=
  comp_eq_of_unit_readings _ _ _ _ (modulePullbackCompInv_comp_compHom B S hS Y c _) _ _ _ _ _ _
    (modulePullbackCompHom_unit B S hS c'' h) (modulePullbackCompHom_unit B S hS Y c)
    (pullbackTransport_unit B S hS hY) _ (pullbackSquareHom_eq_comp c'' c h Y hY _)

end Square

/-! ### Inverse images of attached multiplications and units -/

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V U : BigFppfOver B S hS} (g : V ⟶ U)

/-- **The inverse image of an attached multiplication is the attached multiplication of the
pulled-back modules.**  For a morphism `g : V ⟶ U` of the site, a scheme multiplication
`m : M ⊗ N ⟶ K` on `U` and morphisms `Θ` from the inverse images along `g` carrying the
pulled-back multiplication, read through Stacks 03EL, to a multiplication `m'` on `V`, the inverse
image along `g` of `M^a ⊗ N^a ⟶ K^a`, followed by the identification `g^*K^a ≅ (g^*K)^a` and
`Θ^a`, is Stacks 03EL followed by the same identifications of the factors and
`M'^a ⊗ N'^a ⟶ K'^a`; given the compatibility of Stacks 03DX (2) with inverse images along `g`. -/
theorem modulePullback_map_representedTensorChartMul_comp
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {M' N' K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) (m' : quasicoherentTensorObj B S hS V M' N' ⟶ K')
    (ΘM : quasicoherentPullbackObj B S hS g M ⟶ M') (ΘN : quasicoherentPullbackObj B S hS g N ⟶ N')
    (ΘK : quasicoherentPullbackObj B S hS g K ⟶ K')
    (hb : RepresentedC3TensorCompat B S hS g M N)
    (hm : (quasicoherentPullbackTensorIso B S hS g M N).inv ≫
        quasicoherentPullbackMap B S hS g m ≫ ΘK =
      quasicoherentTensorHom B S hS V ΘM ΘN ≫ m') :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedTensorChartMul B S hS m) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom =
    (modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom ≫
      (((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘM).hom) ⊗ₘ
        ((modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘN).hom)) ≫
      representedTensorChartMul B S hS m' :=
  tensorChartMul_comp_of_readings (modulePullback B S hS (representedSpaceMap B S hS g))
    (representedQuasicoherentSchemeTensorIso B S hS U M N)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom
    (modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj)
    (modulePullbackRepresentedQuasicoherentIso B S hS g M)
    (modulePullbackRepresentedQuasicoherentIso B S hS g N)
    (modulePullbackRepresentedQuasicoherentIso B S hS g K)
    (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentTensorObj B S hS U M N))
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackTensorIso B S hS g M N).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackTensorIso B S hS g M N).inv).hom
    (congrArg (fun x => x.hom) ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
      (quasicoherentPullbackTensorIso B S hS g M N)).hom_inv_id)
    (representedQuasicoherentSchemeTensorIso B S hS V (quasicoherentPullbackObj B S hS g M)
      (quasicoherentPullbackObj B S hS g N))
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackMap B S hS g m)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘM).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘN).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom
    (representedQuasicoherentSchemeTensorIso B S hS V M' N')
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentTensorHom B S hS V ΘM ΘN)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map m').hom
    hb (modulePullbackRepresentedQuasicoherentIso_naturality B S hS g m)
    (congrArg (fun x => x.hom) (map_inv_comp_eq_of_eq
      (representedQuasicoherentSchemeEquivalence B S hS V).functor
      (quasicoherentPullbackTensorIso B S hS g M N) (quasicoherentPullbackMap B S hS g m) ΘK
      (quasicoherentTensorHom B S hS V ΘM ΘN) m' hm))
    (representedQuasicoherentSchemeTensorIso_hom_naturality B S hS V ΘM ΘN)
    (representedTensorChartMul B S hS m) rfl (representedTensorChartMul B S hS m') rfl

/-- **The inverse image of an attached unit is the attached unit of the pulled-back module.**
For a morphism `g : V ⟶ U` of the site, a scheme morphism `ν : 𝒪_U ⟶ K` and `Θ : g^*K ⟶ K'`
carrying the pulled-back `ν`, read through Stacks 03LU, to `ν' : 𝒪_V ⟶ K'`, the inverse image
along `g` of `𝒪 ⟶ K^a`, followed by `g^*K^a ≅ (g^*K)^a` and `Θ^a`, is Stacks 03LU followed by
`𝒪 ⟶ K'^a`; given the compatibility of Stacks 03DX (2) for `𝒪` with inverse images along `g`. -/
theorem modulePullback_map_representedUnitChartHom_comp
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (ν : quasicoherentUnitObj B S hS U ⟶ K) (ν' : quasicoherentUnitObj B S hS V ⟶ K')
    (ΘK : quasicoherentPullbackObj B S hS g K ⟶ K')
    (hb : RepresentedC3UnitCompat B S hS g)
    (hν : (quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g ν ≫ ΘK =
      ν') :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedUnitChartHom B S hS ν) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom =
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).hom ≫
      representedUnitChartHom B S hS ν' :=
  unitChartHom_comp_of_readings (modulePullback B S hS (representedSpaceMap B S hS g))
    (representedQuasicoherentSchemeUnitIso B S hS U)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map ν).hom
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g))
    (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentUnitObj B S hS U))
    (modulePullbackRepresentedQuasicoherentIso B S hS g K)
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).inv).hom
    (congrArg (fun x => x.hom) ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
      (quasicoherentPullbackUnitIso B S hS g)).hom_inv_id)
    (representedQuasicoherentSchemeUnitIso B S hS V)
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackMap B S hS g ν)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ν').hom
    hb (modulePullbackRepresentedQuasicoherentIso_naturality B S hS g ν)
    (congrArg (fun x => x.hom) (map_inv_comp_eq_of_eq'
      (representedQuasicoherentSchemeEquivalence B S hS V).functor
      (quasicoherentPullbackUnitIso B S hS g) (quasicoherentPullbackMap B S hS g ν) ΘK ν' hν))
    (representedUnitChartHom B S hS ν) rfl (representedUnitChartHom B S hS ν') rfl

end Represented

/-! ### Identifications read from chart identifications -/

section Assembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
  (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c)

/-- **Identifications read from chart identifications carry multiplications to
multiplications.**  Let `c'' ≫ h = Y ≫ c` be a square of algebraic spaces with `c''^*` faithful
on morphisms `h^*𝒯_i ⊗ h^*𝒯_j ⟶ 𝒢_k`, `μ : 𝒯_i ⊗ 𝒯_j ⟶ 𝒯_k` on the target of `h`, read along `c`
through `κ` as `μ_K`, `μ_K` read along `Y` through `ℓ` as `μ_L`, and `μ_𝒢` on the source of `h`,
read along `c''` through `ρ` as `μ_L` too.  If `e_n : h^*𝒯_n ⟶ 𝒢_n` is read on `c''` through `ρ`
as the identification along the square followed by `κ` and `ℓ`, then `e` carries the inverse
image of `μ`, read through Stacks 03EL, to `μ_𝒢`. -/
theorem pullbackTensorIso_inv_comp_map_comp_of_chart
    {Ti Tj Tk : Modules.{u, u} B S hS X.1 X.2} (μ : Ti ⊗ Tj ⟶ Tk)
    {Ki Kj Kk : Modules.{u, u} B S hS U.1 U.2}
    (κi : (modulePullback B S hS c).obj Ti ⟶ Ki) (κj : (modulePullback B S hS c).obj Tj ⟶ Kj)
    (κk : (modulePullback B S hS c).obj Tk ⟶ Kk) (μK : Ki ⊗ Kj ⟶ Kk)
    (hμ : (modulePullback B S hS c).map μ ≫ κk =
      (modulePullbackTensorIso B S hS c Ti Tj).hom ≫ (κi ⊗ₘ κj) ≫ μK)
    {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    (ℓi : (modulePullback B S hS Y).obj Ki ⟶ Li) (ℓj : (modulePullback B S hS Y).obj Kj ⟶ Lj)
    (ℓk : (modulePullback B S hS Y).obj Kk ⟶ Lk) (μL : Li ⊗ Lj ⟶ Lk)
    (hℓ : (modulePullback B S hS Y).map μK ≫ ℓk =
      (modulePullbackTensorIso B S hS Y Ki Kj).hom ≫ (ℓi ⊗ₘ ℓj) ≫ μL)
    {Gi Gj Gk : Modules.{u, u} B S hS X''.1 X''.2}
    (ρi : (modulePullback B S hS c'').obj Gi ⟶ Li) (ρj : (modulePullback B S hS c'').obj Gj ⟶ Lj)
    (ρk : (modulePullback B S hS c'').obj Gk ≅ Lk) (μG : Gi ⊗ Gj ⟶ Gk)
    (hρ : (modulePullback B S hS c'').map μG ≫ ρk.hom =
      (modulePullbackTensorIso B S hS c'' Gi Gj).hom ≫ (ρi ⊗ₘ ρj) ≫ μL)
    (ei : (modulePullback B S hS h).obj Ti ⟶ Gi) (ej : (modulePullback B S hS h).obj Tj ⟶ Gj)
    (ek : (modulePullback B S hS h).obj Tk ⟶ Gk)
    (χi : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Ti) ⟶ Li)
    (χj : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Tj) ⟶ Lj)
    (χk : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Tk) ⟶ Lk)
    (hei : (modulePullback B S hS c'').map ei ≫ ρi = χi)
    (hej : (modulePullback B S hS c'').map ej ≫ ρj = χj)
    (hek : (modulePullback B S hS c'').map ek ≫ ρk.hom = χk)
    (hχi : χi = pullbackSquareHom c'' c h Y hY Ti ≫ (modulePullback B S hS Y).map κi ≫ ℓi)
    (hχj : χj = pullbackSquareHom c'' c h Y hY Tj ≫ (modulePullback B S hS Y).map κj ≫ ℓj)
    (hχk : χk = pullbackSquareHom c'' c h Y hY Tk ≫ (modulePullback B S hS Y).map κk ≫ ℓk)
    (hinj : ∀ φ ψ : (modulePullback B S hS h).obj Ti ⊗ (modulePullback B S hS h).obj Tj ⟶ Gk,
      (modulePullback B S hS c'').map φ = (modulePullback B S hS c'').map ψ → φ = ψ) :
    (modulePullbackTensorIso B S hS h Ti Tj).inv ≫ (modulePullback B S hS h).map μ ≫ ek =
      (ei ⊗ₘ ej) ≫ μG :=
  mul_comp_eq_of_chart_readings (modulePullback B S hS c'') (modulePullback B S hS Y)
    (modulePullbackTensorIso B S hS h Ti Tj) ((modulePullback B S hS h).map μ) ei ej ek μG
    (modulePullbackTensorIso B S hS c Ti Tj) ((modulePullback B S hS c).map μ) κi κj κk μK hμ
    ℓi ℓj ℓk μL (modulePullbackTensorIso B S hS Y Ki Kj).hom
    (modulePullbackTensorIso B S hS Y _ _).hom
    (modulePullbackTensorIso_hom_naturality B S hS Y κi κj) hℓ
    (pullbackSquareHom c'' c h Y hY Ti) (pullbackSquareHom c'' c h Y hY Tj)
    (pullbackSquareHom c'' c h Y hY (Ti ⊗ Tj)) (pullbackSquareHom c'' c h Y hY Tk)
    (pullbackSquareHom_naturality c'' c h Y hY μ) (modulePullbackTensorIso B S hS c'' _ _).hom
    (pullbackSquareHom_tensor c'' c h Y hY Ti Tj) ρi ρj ρk
    (modulePullbackTensorIso B S hS c'' Gi Gj).hom hρ
    (modulePullbackTensorIso_hom_naturality B S hS c'' ei ej) χi χj χk hei hej hek hχi hχj hχk
    hinj

/-- **Identifications read from chart identifications carry units to units.**  In the situation
of `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_comp_of_chart`, for
`ν : 𝒪 ⟶ 𝒯` read along `c` through `κ` as `ν_K`, `ν_K` read along `Y` through `ℓ` as `ν_L` and
`ν_𝒢 : 𝒪 ⟶ 𝒢` read along `c''` through `ρ` as `ν_L`, `e` carries the inverse image of `ν`, read
through Stacks 03LU, to `ν_𝒢`. -/
theorem pullbackUnitIso_inv_comp_map_comp_of_chart
    {T : Modules.{u, u} B S hS X.1 X.2}
    (ν : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ T)
    {K : Modules.{u, u} B S hS U.1 U.2} (κ : (modulePullback B S hS c).obj T ⟶ K)
    (νK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶ K)
    (hν : (modulePullback B S hS c).map ν ≫ κ = (modulePullbackUnitIso B S hS c).hom ≫ νK)
    {L : Modules.{u, u} B S hS U''.1 U''.2} (ℓ : (modulePullback B S hS Y).obj K ⟶ L)
    (νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L)
    (hℓ : (modulePullback B S hS Y).map νK ≫ ℓ = (modulePullbackUnitIso B S hS Y).hom ≫ νL)
    {G : Modules.{u, u} B S hS X''.1 X''.2} (ρ : (modulePullback B S hS c'').obj G ≅ L)
    (νG : SheafOfModules.unit (structureRingSheaf B S hS X'') ⟶ G)
    (hρ : (modulePullback B S hS c'').map νG ≫ ρ.hom = (modulePullbackUnitIso B S hS c'').hom ≫ νL)
    (e : (modulePullback B S hS h).obj T ⟶ G)
    (χ : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ⟶ L)
    (he : (modulePullback B S hS c'').map e ≫ ρ.hom = χ)
    (hχ : χ = pullbackSquareHom c'' c h Y hY T ≫ (modulePullback B S hS Y).map κ ≫ ℓ)
    (hinj : ∀ φ ψ : SheafOfModules.unit (structureRingSheaf B S hS X'') ⟶ G,
      (modulePullback B S hS c'').map φ = (modulePullback B S hS c'').map ψ → φ = ψ) :
    (modulePullbackUnitIso B S hS h).inv ≫ (modulePullback B S hS h).map ν ≫ e = νG :=
  unit_comp_eq_of_chart_readings (modulePullback B S hS c'') (modulePullback B S hS Y)
    (hO := (modulePullback B S hS h).obj (SheafOfModules.unit (structureRingSheaf B S hS X)))
    (OW := SheafOfModules.unit (structureRingSheaf B S hS X''))
    (hT := (modulePullback B S hS h).obj T) (GT := G)
    (cO := (modulePullback B S hS c).obj (SheafOfModules.unit (structureRingSheaf B S hS X)))
    (OU := SheafOfModules.unit (structureRingSheaf B S hS U))
    (cT := (modulePullback B S hS c).obj T)
    (K := K) (L := L) (OD := SheafOfModules.unit (structureRingSheaf B S hS U''))
    (modulePullbackUnitIso B S hS h) ((modulePullback B S hS h).map ν) e νG
    (modulePullbackUnitIso B S hS c).hom ((modulePullback B S hS c).map ν) κ νK hν ℓ
    (modulePullbackUnitIso B S hS Y).hom νL hℓ
    (pullbackSquareHom c'' c h Y hY (SheafOfModules.unit (structureRingSheaf B S hS X)))
    (pullbackSquareHom c'' c h Y hY T) (pullbackSquareHom_naturality c'' c h Y hY ν)
    (modulePullbackUnitIso B S hS c'').hom
    (pullbackSquareHom_unit c'' c h Y hY) ρ hρ χ he hχ hinj

end Assembly

end AlgebraicGeometry.Space

end
